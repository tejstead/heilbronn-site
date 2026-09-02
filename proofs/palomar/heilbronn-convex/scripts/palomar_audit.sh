#!/usr/bin/env bash

# Static Palomar preflight for the staged unified n = 3,...,8 package.
# This script deliberately does not invoke Lean, Lake, Comparator, or NanoDa.
# With no argument it audits the project containing this script (the script
# directory itself, or its parent when installed below scripts/). One directory
# argument selects another project tree. PALOMAR_REPOSITORY_ROOT may name the
# enclosing repository root for a nested-project submission; when it is unset,
# the selected project is also treated as the repository root.

set -u
set -o pipefail
export LC_ALL=C

script_dir=$(CDPATH= cd -P -- "$(dirname -- "$0")" && pwd)
if [ "$#" -gt 1 ]; then
  printf 'Usage: %s [PACKAGE_DIRECTORY]\n' "$0" >&2
  exit 2
fi
if [ "$#" -eq 1 ]; then
  project_input=$1
else
  if [ "${script_dir##*/}" = scripts ]; then
    project_input="$script_dir/.."
  else
    project_input=$script_dir
  fi
fi
if [ ! -d "$project_input" ] || [ -L "$project_input" ]; then
  printf 'Project path must be a real directory, not a symlink: %s\n' "$project_input" >&2
  exit 2
fi
project_dir=$(CDPATH= cd -P -- "$project_input" && pwd)
if [ -z "$project_dir" ] || [ "$project_dir" = / ]; then
  printf 'Refusing to audit an empty or filesystem-root project path.\n' >&2
  exit 2
fi

repository_input=${PALOMAR_REPOSITORY_ROOT:-$project_dir}
if [ ! -d "$repository_input" ] || [ -L "$repository_input" ]; then
  printf 'Repository path must be a real directory, not a symlink: %s\n' "$repository_input" >&2
  exit 2
fi
repository_dir=$(CDPATH= cd -P -- "$repository_input" && pwd)
if [ -z "$repository_dir" ] || [ "$repository_dir" = / ]; then
  printf 'Refusing to audit an empty or filesystem-root repository path.\n' >&2
  exit 2
fi
case "$project_dir/" in
  "$repository_dir/"*) ;;
  *)
    printf 'Selected project is not contained in the repository root: %s (repository %s)\n' \
      "$project_dir" "$repository_dir" >&2
    exit 2
    ;;
esac

printf 'AUDIT PROJECT ROOT: %s\n' "$project_dir"
printf 'AUDIT REPOSITORY ROOT: %s\n' "$repository_dir"
challenge="$project_dir/HeilbronnChallenge.lean"
comparator="$project_dir/comparator.json"
formalization="$project_dir/formalization.yaml"
readme="$project_dir/README.md"
audit_tmp=$(mktemp -d "${TMPDIR:-/tmp}/palomar-unified-audit.XXXXXX") || exit 2
trap 'rm -rf -- "$audit_tmp"' EXIT

# Materialize checked, NUL-delimited traversals once. Later gates consume these
# manifests, so an unreadable/failed traversal cannot silently look like an
# empty, clean source tree through process-substitution exit-status loss.
tree_entries="$audit_tmp/tree_entries.nul"
tree_files="$audit_tmp/tree_files.nul"
tree_lean="$audit_tmp/tree_lean.nul"
if ! find -P "$project_dir" -mindepth 1 \
    \( -name .git \) -prune -o -print0 > "$tree_entries" ||
   ! find -P "$project_dir" -mindepth 1 \
    \( -name .git \) -prune -o -type f -print0 > "$tree_files" ||
   ! find -P "$project_dir" -mindepth 1 \
    \( -name .git \) -prune -o -type f -name '*.lean' -print0 > "$tree_lean"; then
  printf 'Could not traverse the audited source tree: %s\n' "$project_dir" >&2
  exit 2
fi

# Palomar's checkout-size and compiled-artifact checks apply to the complete
# submitted repository, not only to a selected nested Lean project. Reuse the
# project manifests in standalone mode and otherwise traverse the explicit
# repository root separately. Symbolic links are entries but not regular files,
# matching the policy's exclusion of them from the 500 MiB byte count.
repository_entries=$tree_entries
repository_files=$tree_files
if [ "$repository_dir" != "$project_dir" ]; then
  repository_entries="$audit_tmp/repository_entries.nul"
  repository_files="$audit_tmp/repository_files.nul"
  if ! find -P "$repository_dir" -mindepth 1 \
      \( -name .git \) -prune -o -print0 > "$repository_entries" ||
     ! find -P "$repository_dir" -mindepth 1 \
      \( -name .git \) -prune -o -type f -print0 > "$repository_files"; then
    printf 'Could not traverse the audited repository tree: %s\n' "$repository_dir" >&2
    exit 2
  fi
fi

# The Challenge uses ordinary Lean comments and strings. Produce a same-line-
# count lexical view with their contents blanked so code-looking text in a
# block comment cannot masquerade as a declaration or placeholder. This is a
# controlled static lexer, not a replacement for Lean elaboration.
challenge_scan=$challenge
if [ -f "$challenge" ] && command -v ruby >/dev/null 2>&1; then
  challenge_scan="$audit_tmp/HeilbronnChallenge.code.lean"
  if ! ruby -e '
    source = File.binread(ARGV.fetch(0))
    output = String.new(capacity: source.bytesize, encoding: Encoding::BINARY)
    index = 0
    block_depth = 0
    line_comment = false
    string_literal = false
    escaped = false
    while index < source.bytesize
      byte = source.getbyte(index)
      following = index + 1 < source.bytesize ? source.getbyte(index + 1) : nil
      if line_comment
        if byte == 10
          output << byte
          line_comment = false
        else
          output << 32
        end
      elsif block_depth > 0
        if byte == 47 && following == 45
          output << "  "
          block_depth += 1
          index += 1
        elsif byte == 45 && following == 47
          output << "  "
          block_depth -= 1
          index += 1
        elsif byte == 10
          output << byte
        else
          output << 32
        end
      elsif string_literal
        if byte == 10
          output << byte
          escaped = false
        else
          output << 32
          if escaped
            escaped = false
          elsif byte == 92
            escaped = true
          elsif byte == 34
            string_literal = false
          end
        end
      elsif byte == 47 && following == 45
        output << "  "
        block_depth = 1
        index += 1
      elsif byte == 45 && following == 45
        output << "  "
        line_comment = true
        index += 1
      elsif byte == 34
        output << 32
        string_literal = true
      else
        output << byte
      end
      index += 1
    end
    raise "unterminated block comment" unless block_depth.zero?
    raise "unterminated string literal" if string_literal
    File.binwrite(ARGV.fetch(1), output)
  ' "$challenge" "$challenge_scan"; then
    printf 'Could not produce the controlled lexical Challenge view.\n' >&2
    exit 2
  fi
fi

failed_items=""
warned_items=""

pass_item() {
  printf '[PASS] item %s: %s\n' "$1" "$2"
}

warn_item() {
  printf '[WARN] item %s: %s\n' "$1" "$2"
  warned_items="${warned_items}${warned_items:+ }$1"
}

fail_item() {
  printf '[FAIL] item %s: %s\n' "$1" "$2"
  failed_items="${failed_items}${failed_items:+ }$1"
}

file_bytes() {
  wc -c < "$1" | tr -d '[:space:]'
}

# Item 1: the Challenge is small and its only direct import is Mathlib.
if [ ! -f "$challenge" ]; then
  fail_item 1 "HeilbronnChallenge.lean is missing"
else
  challenge_bytes=$(file_bytes "$challenge")
  challenge_lines=$(awk 'END { print NR }' "$challenge")
  direct_imports=$(sed -n 's/^[[:space:]]*import[[:space:]][[:space:]]*//p' "$challenge_scan")
  if [ "$challenge_bytes" -ge 102400 ] || [ "$challenge_lines" -ge 1000 ]; then
    fail_item 1 "Challenge is ${challenge_bytes} bytes and ${challenge_lines} lines; strict caps are under 102400 bytes and under 1000 lines"
  elif [ "$direct_imports" != "Mathlib" ]; then
    fail_item 1 "expected exactly one direct import, Mathlib; found: ${direct_imports:-<none>}"
  elif [ "$challenge_bytes" -ge 32768 ] || [ "$challenge_lines" -ge 300 ]; then
    warn_item 1 "Challenge is ${challenge_bytes} bytes and ${challenge_lines} lines, at or above the 32768-byte/300-line warning threshold"
  else
    pass_item 1 "Challenge is ${challenge_bytes} bytes and ${challenge_lines} lines and imports only Mathlib"
  fi
fi

# Item 2: symlinks and special filesystem objects are not permitted within the
# selected project. Repository-level symlinks outside the project are excluded
# from Item 4's size count and do not stand in for any required sentinel.
symlink_list="$audit_tmp/symlinks.txt"
special_list="$audit_tmp/special.txt"
: > "$symlink_list"
: > "$special_list"
symlink_count=0
special_count=0
while IFS= read -r -d '' entry; do
  if [ -L "$entry" ]; then
    symlink_count=$((symlink_count + 1))
    printf '%q\n' "$entry" >> "$symlink_list"
  elif [ ! -f "$entry" ] && [ ! -d "$entry" ]; then
    special_count=$((special_count + 1))
    printf '%q\n' "$entry" >> "$special_list"
  fi
done < "$tree_entries"
if [ "$symlink_count" -ne 0 ] || [ "$special_count" -ne 0 ]; then
  fail_item 2 "$symlink_count selected-project symlink(s) and $special_count selected-project special filesystem object(s) found"
  sed 's/^/  FORBIDDEN symlink: /' "$symlink_list"
  sed 's/^/  FORBIDDEN special object: /' "$special_list"
else
  pass_item 2 "no symlinks or special filesystem objects found in the selected project"
fi

# Item 3: reject compiled files and conventional build/cache directories in the
# selected project. In nested mode, also reject compiled files and committed
# .lake directories elsewhere in the submitted repository, without applying
# generic names such as build/ to unrelated repository source directories.
artifact_list="$audit_tmp/artifacts.txt"
repository_artifact_list="$audit_tmp/repository_artifacts.txt"
: > "$artifact_list"
: > "$repository_artifact_list"
artifact_count=0
repository_artifact_count=0
shopt -s nocasematch
while IFS= read -r -d '' entry; do
  base=${entry##*/}
  forbidden_artifact=0
  if [ -d "$entry" ]; then
    case "$base" in
      .lake|build|_build|dist|out|target|node_modules|__pycache__|.cache|\
      .pytest_cache|.mypy_cache|.ruff_cache|.venv|venv)
        forbidden_artifact=1
        ;;
    esac
  elif [ -f "$entry" ]; then
    case "$base" in
      *.olean|*.olean.private|*.olean.server|*.ilean|*.bc|*.ir|*.o|*.obj|\
      *.a|*.so|*.dylib|*.dll|*.exe|*.class|*.pyc|*.pyo|*.wasm|*.rlib|*.trace)
        forbidden_artifact=1
        ;;
    esac
  fi
  if [ "$forbidden_artifact" -eq 1 ]; then
    artifact_count=$((artifact_count + 1))
    printf '%q\n' "$entry" >> "$artifact_list"
  fi
done < "$tree_entries"

if [ "$repository_dir" != "$project_dir" ]; then
  while IFS= read -r -d '' entry; do
    case "$entry/" in
      "$project_dir/"*) continue ;;
    esac
    base=${entry##*/}
    forbidden_repository_artifact=0
    if [ -d "$entry" ] && [ "$base" = .lake ]; then
      forbidden_repository_artifact=1
    elif [ -f "$entry" ]; then
      case "$base" in
        *.olean|*.olean.private|*.olean.server|*.ilean|*.a|*.bc|*.dll|*.dylib|\
        *.ir|*.o|*.obj|*.so|*.trace)
          forbidden_repository_artifact=1
          ;;
      esac
    fi
    if [ "$forbidden_repository_artifact" -eq 1 ]; then
      repository_artifact_count=$((repository_artifact_count + 1))
      printf '%q\n' "$entry" >> "$repository_artifact_list"
    fi
  done < "$repository_entries"
fi
shopt -u nocasematch
if [ "$artifact_count" -ne 0 ] || [ "$repository_artifact_count" -ne 0 ]; then
  fail_item 3 "$artifact_count selected-project build/cache artifact(s) and $repository_artifact_count repository-level compiled/.lake artifact(s) found"
  sed 's/^/  FORBIDDEN project artifact: /' "$artifact_list"
  sed 's/^/  FORBIDDEN repository artifact: /' "$repository_artifact_list"
else
  pass_item 3 "no selected-project build/cache artifacts or repository-level compiled/.lake artifacts found"
fi

# Item 4: Palomar's 500 MiB limit covers the complete checked-out repository,
# excluding Git metadata and symbolic links, even when the Lean project is
# selected below the repository root.
repository_bytes=0
repository_file_count=0
while IFS= read -r -d '' source_file; do
  bytes=$(file_bytes "$source_file")
  repository_bytes=$((repository_bytes + bytes))
  repository_file_count=$((repository_file_count + 1))
done < "$repository_files"

project_bytes=0
project_file_count=0
if [ "$repository_dir" != "$project_dir" ]; then
  while IFS= read -r -d '' source_file; do
    bytes=$(file_bytes "$source_file")
    project_bytes=$((project_bytes + bytes))
    project_file_count=$((project_file_count + 1))
  done < "$tree_files"
fi

if [ "$repository_bytes" -ge 524288000 ]; then
  if [ "$repository_dir" = "$project_dir" ]; then
    fail_item 4 "repository snapshot is ${repository_bytes} bytes across ${repository_file_count} files; cap is under 524288000 bytes"
  else
    fail_item 4 "repository snapshot is ${repository_bytes} bytes across ${repository_file_count} files (selected project ${project_bytes} bytes across ${project_file_count} files); cap is under 524288000 bytes"
  fi
else
  if [ "$repository_dir" = "$project_dir" ]; then
    pass_item 4 "repository snapshot is ${repository_bytes} bytes across ${repository_file_count} regular files; selected project is repository root"
  else
    pass_item 4 "repository snapshot is ${repository_bytes} bytes across ${repository_file_count} regular files; selected project is ${project_bytes} bytes across ${project_file_count} regular files"
  fi
fi

# Item 5: registry-side metadata files are present and below their own caps.
size_failures=""
check_size_cap() {
  label=$1
  path=$2
  cap=$3
  if [ ! -f "$path" ]; then
    size_failures="${size_failures}${size_failures:+; }${label} missing"
    return
  fi
  bytes=$(file_bytes "$path")
  if [ "$bytes" -ge "$cap" ]; then
    size_failures="${size_failures}${size_failures:+; }${label} ${bytes} bytes, strict cap under ${cap}"
  fi
}
check_size_cap "formalization.yaml" "$formalization" 262144
check_size_cap "comparator.json" "$comparator" 1048576
if [ ! -f "$readme" ]; then
  size_failures="${size_failures}${size_failures:+; }README.md missing"
fi
if [ -n "$size_failures" ]; then
  fail_item 5 "$size_failures"
else
  pass_item 5 "formalization.yaml and comparator.json are below their caps; README.md is present"
fi

# Canonical 29-name surface. Comparing both the JSON and the Challenge against
# this list catches a coordinated accidental rename, not merely disagreement
# between two files that drifted in different directions.
expected_targets="$audit_tmp/expected_targets.txt"
cat > "$expected_targets" <<'EOF'
HeilbronnChallenge.heilbronn_convex_three_upper_bound
HeilbronnChallenge.heilbronn_convex_three_attained
HeilbronnChallenge.heilbronn_convex_three
HeilbronnChallenge.heilbronn_convex_three_unique
HeilbronnChallenge.heilbronn_convex_four_upper_bound
HeilbronnChallenge.heilbronn_convex_four_attained
HeilbronnChallenge.heilbronn_convex_four
HeilbronnChallenge.heilbronn_convex_four_unique
HeilbronnChallenge.P5_root_existsUnique
HeilbronnChallenge.heilbronn_convex_five_upper_bound
HeilbronnChallenge.heilbronn_convex_five_attained
HeilbronnChallenge.heilbronn_convex_five
HeilbronnChallenge.heilbronn_convex_five_unique
HeilbronnChallenge.heilbronn_convex_six_upper_bound
HeilbronnChallenge.heilbronn_convex_six_attained
HeilbronnChallenge.heilbronn_convex_six
HeilbronnChallenge.heilbronn_convex_six_unique
HeilbronnChallenge.heilbronn_convex_seven_upper_bound
HeilbronnChallenge.heilbronn_convex_seven_attained
HeilbronnChallenge.heilbronn_convex_seven
HeilbronnChallenge.heilbronn_convex_seven_family_attains
HeilbronnChallenge.heilbronn_convex_seven_real_family_inequivalent
HeilbronnChallenge.heilbronn_convex_seven_optimizer_classification
HeilbronnChallenge.heilbronn_convex_seven_infinite_optimizers
HeilbronnChallenge.P8_root_existsUnique
HeilbronnChallenge.heilbronn_convex_eight_upper_bound
HeilbronnChallenge.heilbronn_convex_eight_attained
HeilbronnChallenge.heilbronn_convex_eight
HeilbronnChallenge.heilbronn_convex_eight_unique
EOF

# Item 6: Comparator JSON and Challenge declarations have exactly that surface.
item6_errors=""
json_targets="$audit_tmp/json_targets.txt"
challenge_targets="$audit_tmp/challenge_targets.txt"
invalid_names="$audit_tmp/invalid_names.txt"
duplicate_names="$audit_tmp/duplicate_names.txt"
: > "$json_targets"
: > "$challenge_targets"
: > "$invalid_names"
: > "$duplicate_names"

if ! command -v jq >/dev/null 2>&1; then
  item6_errors="jq is required"
elif [ ! -f "$comparator" ]; then
  item6_errors="comparator.json is missing"
elif ! jq -e '
    type == "object" and
    ((keys | sort) == (["challenge_module", "definition_names", "enable_nanoda",
      "permitted_axioms", "solution_module", "theorem_names"] | sort)) and
    (.challenge_module == "HeilbronnChallenge") and
    (.solution_module == "HeilbronnSolution") and
    (.enable_nanoda == true) and
    (.theorem_names | type == "array" and length == 29 and
      all(.[]; type == "string" and length > 0)) and
    (.definition_names == []) and
    (.permitted_axioms | type == "array")
  ' "$comparator" >/dev/null 2>&1; then
  item6_errors="comparator.json does not have the exact unified module/configuration shape"
else
  raw_key_count=$(grep -Eo '"(challenge_module|solution_module|enable_nanoda|theorem_names|definition_names|permitted_axioms)"[[:space:]]*:' \
    "$comparator" | wc -l | tr -d '[:space:]')
  if [ "$raw_key_count" -ne 6 ]; then
    item6_errors="comparator.json must contain each of its six canonical top-level keys exactly once"
  fi
  for comparator_key in challenge_module solution_module enable_nanoda theorem_names definition_names permitted_axioms; do
    key_count=$(grep -Eo "\"${comparator_key}\"[[:space:]]*:" "$comparator" | \
      wc -l | tr -d '[:space:]')
    if [ "$key_count" -ne 1 ]; then
      item6_errors="${item6_errors}${item6_errors:+; }key ${comparator_key} occurs ${key_count} times"
    fi
  done
  jq -r '.theorem_names[]' "$comparator" > "$json_targets"
  grep -Ev "^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$" \
    "$json_targets" > "$invalid_names" || true
  sort "$json_targets" | uniq -d > "$duplicate_names"
  if [ -s "$invalid_names" ]; then
    item6_errors="invalid Lean declaration name(s) in comparator.json"
  elif [ -s "$duplicate_names" ]; then
    item6_errors="duplicate theorem name(s) in comparator.json"
  fi
fi

if [ ! -f "$challenge" ]; then
  item6_errors="${item6_errors}${item6_errors:+; }HeilbronnChallenge.lean is missing"
else
  namespace_count=$(awk '$1 == "namespace" && $2 == "HeilbronnChallenge" && NF == 2 { count += 1 } END { print count + 0 }' "$challenge_scan")
  namespace_end_count=$(awk '$1 == "end" && $2 == "HeilbronnChallenge" && NF == 2 { count += 1 } END { print count + 0 }' "$challenge_scan")
  if [ "$namespace_count" -ne 1 ] || [ "$namespace_end_count" -ne 1 ]; then
    item6_errors="${item6_errors}${item6_errors:+; }expected exactly one namespace/end pair for HeilbronnChallenge"
  fi
  awk '
    /^[[:space:]]*theorem[[:space:]]+/ {
      name = $0
      sub(/^[[:space:]]*theorem[[:space:]]+/, "", name)
      sub(/[[:space:](\[{:].*$/, "", name)
      print "HeilbronnChallenge." name
    }
  ' "$challenge_scan" > "$challenge_targets"
fi

expected_sorted="$audit_tmp/expected_sorted.txt"
json_sorted="$audit_tmp/json_sorted.txt"
challenge_sorted="$audit_tmp/challenge_sorted.txt"
LC_ALL=C sort "$expected_targets" > "$expected_sorted"
LC_ALL=C sort "$json_targets" > "$json_sorted"
LC_ALL=C sort "$challenge_targets" > "$challenge_sorted"
if ! cmp -s "$expected_sorted" "$json_sorted"; then
  item6_errors="${item6_errors}${item6_errors:+; }Comparator theorem set differs from canonical 29-name surface"
  printf '  COMPARATOR/CANONICAL DIFFERENCE:\n'
  comm -3 "$expected_sorted" "$json_sorted" | sed 's/^/    /'
fi
if ! cmp -s "$expected_targets" "$json_targets"; then
  item6_errors="${item6_errors}${item6_errors:+; }Comparator theorem order differs from the canonical order"
fi
if ! cmp -s "$expected_sorted" "$challenge_sorted"; then
  item6_errors="${item6_errors}${item6_errors:+; }Challenge theorem declarations differ from canonical 29-name surface"
  printf '  CHALLENGE/CANONICAL DIFFERENCE:\n'
  comm -3 "$expected_sorted" "$challenge_sorted" | sed 's/^/    /'
fi
if ! cmp -s "$expected_targets" "$challenge_targets"; then
  item6_errors="${item6_errors}${item6_errors:+; }Challenge theorem order differs from the canonical order"
fi
if [ -n "$item6_errors" ]; then
  fail_item 6 "$item6_errors"
else
  pass_item 6 "Comparator and Challenge agree exactly with the canonical 29 theorem names; definition_names is empty"
fi

# Item 7: the Comparator axiom allowlist is exact and source declares no custom
# axioms/constants. This is static only; Comparator later checks dependencies.
item7_errors=""
expected_axioms="$audit_tmp/expected_axioms.txt"
actual_axioms="$audit_tmp/actual_axioms.txt"
custom_axioms="$audit_tmp/custom_axioms.txt"
unsafe_declarations="$audit_tmp/unsafe_declarations.txt"
direct_sorryax="$audit_tmp/direct_sorryax.txt"
printf '%s\n' Classical.choice Quot.sound propext | LC_ALL=C sort > "$expected_axioms"
: > "$actual_axioms"
: > "$custom_axioms"
: > "$unsafe_declarations"
: > "$direct_sorryax"
if command -v jq >/dev/null 2>&1 && [ -f "$comparator" ]; then
  jq -r '.permitted_axioms[]? // empty' "$comparator" | LC_ALL=C sort > "$actual_axioms"
else
  item7_errors="cannot read permitted_axioms"
fi
if ! cmp -s "$expected_axioms" "$actual_axioms"; then
  item7_errors="${item7_errors}${item7_errors:+; }permitted_axioms is not exactly propext, Quot.sound, Classical.choice"
fi
while IFS= read -r -d '' lean_file; do
  grep -Hn -E "^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|public|local|noncomputable|unsafe|meta)[[:space:]]+)*(axiom|axioms|constant)[[:space:]]+[A-Za-z_][A-Za-z0-9_'.]*[[:space:]]*(:|\(|\{|\[)" \
    "$lean_file" >> "$custom_axioms" || true
  grep -Hn -E "^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|public|local|noncomputable|meta)[[:space:]]+)*unsafe[[:space:]]+(def|theorem|lemma|opaque|instance)[[:space:]]" \
    "$lean_file" >> "$unsafe_declarations" || true
  grep -F -Hn 'sorryAx' "$lean_file" >> "$direct_sorryax" || true
done < "$tree_lean"
if [ -s "$custom_axioms" ]; then
  item7_errors="${item7_errors}${item7_errors:+; }custom axiom/constant declaration(s) found"
  sed 's/^/  FORBIDDEN declaration: /' "$custom_axioms"
fi
if [ -s "$unsafe_declarations" ]; then
  item7_errors="${item7_errors}${item7_errors:+; }unsafe declaration(s) found"
  sed 's/^/  FORBIDDEN unsafe declaration: /' "$unsafe_declarations"
fi
if [ -s "$direct_sorryax" ]; then
  item7_errors="${item7_errors}${item7_errors:+; }direct sorryAx occurrence(s) found"
  sed 's/^/  FORBIDDEN sorryAx: /' "$direct_sorryax"
fi
if [ -n "$item7_errors" ]; then
  fail_item 7 "$item7_errors"
else
  pass_item 7 "axiom allowlist is exact; no custom axiom/constant, unsafe declaration, or direct sorryAx occurs in Lean source"
fi

# Item 8: placeholders occur exactly once in each selected Challenge theorem,
# and nowhere else. The Solution must ultimately replace all of these holes.
allowed_sites="$audit_tmp/allowed_sites.txt"
allowed_names="$audit_tmp/allowed_names.txt"
forbidden_sites="$audit_tmp/forbidden_sites.txt"
: > "$allowed_sites"
: > "$allowed_names"
: > "$forbidden_sites"
while IFS= read -r -d '' lean_file; do
  classified="$audit_tmp/classified.txt"
  challenge_mode=0
  placeholder_scan=$lean_file
  if [ "$lean_file" = "$challenge" ]; then
    challenge_mode=1
    placeholder_scan=$challenge_scan
  fi
  awk -v challenge_mode="$challenge_mode" '
    {
      line = $0
      decl = line
      sub(/^[[:space:]]*/, "", decl)
      while (decl ~ /^@\[[^]]*\][[:space:]]*/) {
        sub(/^@\[[^]]*\][[:space:]]*/, "", decl)
      }
      while (decl ~ /^(private|protected|public|local|noncomputable|unsafe|meta)[[:space:]]+/) {
        sub(/^(private|protected|public|local|noncomputable|unsafe|meta)[[:space:]]+/, "", decl)
      }

      if (decl ~ /^theorem[[:space:]]+/) {
        active_kind = "theorem"
        active_name = decl
        sub(/^theorem[[:space:]]+/, "", active_name)
        sub(/[[:space:](\[{:].*$/, "", active_name)
      } else if (decl ~ /^(def|lemma|abbrev|opaque|axiom|axioms|constant|instance|example|structure|class|inductive|coinductive)[[:space:]]+/) {
        active_kind = "other"
        active_name = decl
        sub(/^[^[:space:]]+[[:space:]]+/, "", active_name)
        sub(/[[:space:](\[{:].*$/, "", active_name)
      } else if (decl ~ /^(namespace|section|end)([[:space:]]|$)/) {
        active_kind = ""
        active_name = ""
      }

      has_placeholder = line ~ /(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)/
      if (has_placeholder) {
        if (challenge_mode == 1 && active_kind == "theorem" &&
            line ~ /^[[:space:]]*sorry[[:space:]]*$/) {
          printf "candidate\t%d\t%s\t%s\n", NR, active_kind, active_name
          active_kind = ""
          active_name = ""
        } else {
          printf "forbidden\t%d\t%s\t%s\n", NR, active_kind, active_name
        }
      }
    }
  ' "$placeholder_scan" > "$classified"

  while IFS="$(printf '\t')" read -r classification line_no decl_kind decl_name; do
    [ -n "$line_no" ] || continue
    full_name="HeilbronnChallenge.$decl_name"
    relative=${lean_file#"$project_dir/"}
    if [ "$classification" = candidate ] && [ "$lean_file" = "$challenge" ] && \
        [ "$decl_kind" = theorem ] && \
        grep -Fxq "$full_name" "$expected_targets"; then
      printf '%s:%s: theorem %s\n' "$relative" "$line_no" "$decl_name" >> "$allowed_sites"
      printf '%s\n' "$full_name" >> "$allowed_names"
    else
      printf '%s:%s: %s %s (%s)\n' "$relative" "$line_no" \
        "${decl_kind:-unclassified}" "${decl_name:-unknown}" "$classification" >> "$forbidden_sites"
    fi
  done < "$classified"
done < "$tree_lean"

allowed_count=$(wc -l < "$allowed_sites" | tr -d '[:space:]')
forbidden_count=$(wc -l < "$forbidden_sites" | tr -d '[:space:]')
LC_ALL=C sort "$allowed_names" > "$audit_tmp/allowed_names_sorted.txt"
if [ "$forbidden_count" -ne 0 ]; then
  fail_item 8 "$forbidden_count forbidden placeholder site(s); $allowed_count permitted site(s)"
  sed 's/^/  FORBIDDEN placeholder: /' "$forbidden_sites"
elif [ "$allowed_count" -ne 29 ] || \
    ! cmp -s "$expected_sorted" "$audit_tmp/allowed_names_sorted.txt"; then
  fail_item 8 "expected exactly one placeholder in each of the 29 selected Challenge theorems; found $allowed_count"
else
  pass_item 8 "each selected Challenge theorem has exactly one standalone sorry, with no other sorry/admit token in Lean source"
fi

# Item 9: reject Palomar-forbidden reduction shortcuts in Lean source. Scan
# Lean rather than prose, so a documentation warning can name a forbidden
# mechanism without being misclassified as its use.
ban_native="native_""decide"
ban_reduce="Lean.ofReduce""Bool"
banned_hits="$audit_tmp/banned_hits.txt"
: > "$banned_hits"
while IFS= read -r -d '' lean_file; do
  grep -I -F -Hn -e "$ban_native" -e "$ban_reduce" \
    "$lean_file" >> "$banned_hits" || true
done < "$tree_lean"
if [ -s "$banned_hits" ]; then
  banned_count=$(wc -l < "$banned_hits" | tr -d '[:space:]')
  fail_item 9 "$banned_count forbidden reduction mechanism occurrence(s) found in Lean source"
  sed 's/^/  FORBIDDEN reduction: /' "$banned_hits"
else
  pass_item 9 "no ${ban_native} or ${ban_reduce} occurrence appears in Lean source"
fi

# Item 10: parse metadata and enforce the current source-based provenance shape.
yaml_result="$audit_tmp/yaml_result.txt"
if ! command -v ruby >/dev/null 2>&1; then
  fail_item 10 "Ruby is required to parse formalization.yaml"
elif ruby -ryaml -e '
  def nonblank_string?(value)
    value.is_a?(String) && !value.strip.empty?
  end

  def reject_duplicate_keys(node, path = "$")
    case node
    when Psych::Nodes::Mapping
      seen = {}
      node.children.each_slice(2) do |key_node, value_node|
        raise "non-scalar mapping key at #{path}" unless key_node.is_a?(Psych::Nodes::Scalar)
        key = key_node.value
        raise "duplicate YAML key #{key.inspect} at #{path}" if seen.key?(key)
        seen[key] = true
        reject_duplicate_keys(value_node, "#{path}.#{key}")
      end
    when Psych::Nodes::Sequence
      node.children.each_with_index do |child, index|
        reject_duplicate_keys(child, "#{path}[#{index}]")
      end
    end
  end

  document = Psych.parse_file(ARGV.fetch(0))
  raise "empty YAML document" unless document && document.root
  reject_duplicate_keys(document.root)
  data = YAML.safe_load(File.read(ARGV.fetch(0)), permitted_classes: [], aliases: false)
  raise "document root is not a mapping" unless data.is_a?(Hash)
  raise "version is not v0.4" unless data["version"] == "v0.4"
  project = data["project"]
  raise "project is missing" unless project.is_a?(Hash)
  %w[name description license].each do |key|
    raise "project.#{key} is missing" unless nonblank_string?(project[key])
  end
  raise "project.license is not MIT" unless project["license"] == "MIT"
  %w[authors responsible_maintainers].each do |key|
    value = project[key]
    raise "project.#{key} is invalid" unless
      value.is_a?(Array) && !value.empty? && value.all? { |x| nonblank_string?(x) }
  end
  raise "classification is missing" unless data["classification"].is_a?(Hash)
  methods = data.dig("automation", "methods")
  raise "automation.methods is invalid" unless
    methods.is_a?(Array) && !methods.empty? && methods.all? { |x| x.is_a?(Hash) && nonblank_string?(x["method"]) }
  raise "review.status is invalid" unless nonblank_string?(data.dig("review", "status"))
  sources = data["sources"]
  raise "sources is invalid" unless sources.is_a?(Array) && !sources.empty?
  relationships = %w[formalizes adapts independently-proves background other]
  types = ["paper", "book", "web discussion", "folklore", "original-proof", "other"]
  sources.each do |source|
    raise "source entry is not a mapping" unless source.is_a?(Hash)
    raise "source title is invalid" unless nonblank_string?(source["title"])
    raise "source relationship is invalid" unless relationships.include?(source["relationship"])
    raise "source type is invalid" unless types.include?(source["type"])
    if source["relationship"] == "other" && !nonblank_string?(source["note"])
      raise "source relationship other requires an explanatory note"
    end
  end
  raise "source-based entry contains original-proof" if
    sources.any? { |source| source["type"] == "original-proof" }
  substantive = sources.count do |source|
    %w[formalizes adapts independently-proves].include?(source["relationship"])
  end
  raise "source-based entry has no substantive source" if substantive.zero?
  puts "v0.4 metadata parses; derived origin source-based; #{sources.length} sources, #{substantive} substantive"
' "$formalization" > "$yaml_result" 2>&1; then
  pass_item 10 "$(tr '\n' ' ' < "$yaml_result" | sed 's/[[:space:]]*$//')"
else
  fail_item 10 "metadata validation failed: $(tr '\n' ' ' < "$yaml_result" | sed 's/[[:space:]]*$//')"
fi

# Item 11: source relationships cannot be finalized mechanically. The README
# carries an explicit state marker. Final submission preflight should set
# PALOMAR_REQUIRE_FROZEN_PROVENANCE=1, which converts a provisional marker into
# a failure until the actual n = 6 and n = 7 proof routes have been compared
# against the cited sources.
provenance_status=""
if [ -f "$readme" ]; then
  provenance_status=$(sed -n \
    -e 's/^<!-- palomar-provenance-route-status: provisional -->$/provisional/p' \
    -e 's/^<!-- palomar-provenance-route-status: frozen -->$/frozen/p' \
    "$readme")
fi
case "$provenance_status" in
  frozen)
    pass_item 11 "provenance-route relationship review is marked frozen"
    ;;
  provisional)
    if [ "${PALOMAR_REQUIRE_FROZEN_PROVENANCE:-${PALOMAR_REQUIRE_COMPLETE_PACKAGE:-0}}" = 1 ]; then
      fail_item 11 "provenance is still provisional; freeze relationships after auditing the final n = 6 and n = 7 proof routes"
    else
      warn_item 11 "provenance relationships are provisional; rerun with PALOMAR_REQUIRE_FROZEN_PROVENANCE=1 for submission preflight"
    fi
    ;;
  *)
    fail_item 11 "README.md must contain exactly one provenance-route status marker"
    ;;
esac

# Item 12: distinguish a coherent staging surface from a submission layout that
# is structurally ready for the official tools. Lake and theorem sentinels live
# at the selected project root. Palomar's single submission license always lives
# at repository root, including when the project is nested. A nested project-
# root license is rejected here as an assembly error rather than silently
# carrying a redundant second copy into the final snapshot.
item12_errors=""
submission_ready=0
for required_file in HeilbronnSolution.lean lean-toolchain lake-manifest.json; do
  if [ ! -f "$project_dir/$required_file" ] || [ -L "$project_dir/$required_file" ]; then
    item12_errors="${item12_errors}${item12_errors:+; }${required_file} missing or not a regular non-symlink file"
  fi
done

lakefile_count=0
for lakefile_candidate in "$project_dir/lakefile.toml" "$project_dir/lakefile.lean"; do
  if [ -f "$lakefile_candidate" ] && [ ! -L "$lakefile_candidate" ]; then
    lakefile_count=$((lakefile_count + 1))
    lakefile_bytes=$(file_bytes "$lakefile_candidate")
    if [ "$lakefile_bytes" -ge 1048576 ]; then
      item12_errors="${item12_errors}${item12_errors:+; }${lakefile_candidate##*/} is ${lakefile_bytes} bytes; strict cap is under 1048576"
    fi
  fi
done
if [ "$lakefile_count" -ne 1 ]; then
  item12_errors="${item12_errors}${item12_errors:+; }expected exactly one project-root lakefile.toml or lakefile.lean, found ${lakefile_count}"
fi

license_count=0
license_path=""
shopt -s nocasematch
while IFS= read -r -d '' entry; do
  relative=${entry#"$repository_dir/"}
  if [ "$relative" = "$entry" ]; then
    continue
  fi
  case "$relative" in
    */*) continue ;;
  esac
  case "$relative" in
    license|license.md|license.markdown|license.txt|\
    licence|licence.md|licence.markdown|licence.txt|\
    copying|copying.md|copying.markdown|copying.txt|\
    unlicense|unlicense.md|unlicense.markdown|unlicense.txt|\
    ofl|ofl.md|ofl.markdown|ofl.txt)
      license_count=$((license_count + 1))
      license_path=$entry
      ;;
  esac
done < "$repository_entries"

nested_license_count=0
if [ "$repository_dir" != "$project_dir" ]; then
  while IFS= read -r -d '' entry; do
    relative=${entry#"$project_dir/"}
    if [ "$relative" = "$entry" ]; then
      continue
    fi
    case "$relative" in
      */*) continue ;;
    esac
    case "$relative" in
      license|license.md|license.markdown|license.txt|\
      licence|licence.md|licence.markdown|licence.txt|\
      copying|copying.md|copying.markdown|copying.txt|\
      unlicense|unlicense.md|unlicense.markdown|unlicense.txt|\
      ofl|ofl.md|ofl.markdown|ofl.txt)
        nested_license_count=$((nested_license_count + 1))
        ;;
    esac
  done < "$tree_entries"
fi
shopt -u nocasematch
if [ "$license_count" -ne 1 ]; then
  item12_errors="${item12_errors}${item12_errors:+; }expected exactly one recognized repository-root license entry, found ${license_count}"
elif [ ! -f "$license_path" ] || [ -L "$license_path" ]; then
  item12_errors="${item12_errors}${item12_errors:+; }repository-root license is not a regular non-symlink file"
elif [ "$(file_bytes "$license_path")" -ge 1048576 ]; then
  item12_errors="${item12_errors}${item12_errors:+; }repository-root license exceeds the strict 1 MiB cap"
elif [ ! -s "$license_path" ]; then
  item12_errors="${item12_errors}${item12_errors:+; }repository-root license is empty"
elif ! command -v ruby >/dev/null 2>&1; then
  item12_errors="${item12_errors}${item12_errors:+; }Ruby is required to validate repository-root license UTF-8"
elif ! ruby -e '
    source = File.binread(ARGV.fetch(0))
    source.force_encoding(Encoding::UTF_8)
    exit(source.valid_encoding? && !source.include?("\0") ? 0 : 1)
  ' "$license_path"; then
  item12_errors="${item12_errors}${item12_errors:+; }repository-root license is not valid non-NUL UTF-8 text"
fi
if [ "$nested_license_count" -ne 0 ]; then
  item12_errors="${item12_errors}${item12_errors:+; }selected nested project contains ${nested_license_count} conventional license entry/entries; the submission license must remain only at repository root"
fi

if [ -z "$item12_errors" ]; then
  submission_ready=1
  if [ "$repository_dir" = "$project_dir" ]; then
    pass_item 12 "standalone submission sentinels and repository-root license are present"
  else
    pass_item 12 "nested-project sentinels and repository-root license are present, with no redundant project-root license"
  fi
elif [ "${PALOMAR_REQUIRE_COMPLETE_PACKAGE:-0}" = 1 ]; then
  fail_item 12 "$item12_errors"
else
  warn_item 12 "staging tree is not yet a complete submission layout: $item12_errors"
fi

# Item 13: every non-Mathlib import reachable from the Challenge and Solution
# roots resolves to an exact, case-sensitive local source file. This catches a
# source-only package that omits a transitive module even when cached oleans
# allowed an earlier build tree to proceed. The package intentionally reaches
# external Lean code only through Mathlib; a different unresolved prefix is an
# error rather than something silently assumed to be an external dependency.
closure_result="$audit_tmp/import_closure.txt"
closure_root_errors=""
for closure_root in HeilbronnChallenge.lean HeilbronnSolution.lean; do
  if [ ! -f "$project_dir/$closure_root" ] || [ -L "$project_dir/$closure_root" ]; then
    closure_root_errors="${closure_root_errors}${closure_root_errors:+; }${closure_root} missing or not a regular non-symlink file"
  fi
done

if [ -n "$closure_root_errors" ]; then
  if [ "${PALOMAR_REQUIRE_COMPLETE_PACKAGE:-0}" = 1 ]; then
    fail_item 13 "transitive import closure not checked: $closure_root_errors"
  else
    warn_item 13 "transitive import closure not checked in staging mode: $closure_root_errors"
  fi
elif ! command -v ruby >/dev/null 2>&1; then
  fail_item 13 "Ruby is required to check transitive local import closure"
elif ruby - "$project_dir" "$tree_lean" > "$closure_result" 2>&1 <<'RUBY'
  project_dir = ARGV.fetch(0)
  manifest = ARGV.fetch(1)
  project_prefix = project_dir.end_with?(File::SEPARATOR) ?
    project_dir : project_dir + File::SEPARATOR
  module_files = {}
  casefolded_modules = {}
  errors = []

  File.binread(manifest).split("\0").reject(&:empty?).each do |path|
    unless path.start_with?(project_prefix) && path.end_with?('.lean')
      errors << "invalid Lean source path in traversal manifest: #{path.inspect}"
      next
    end
    relative = path.delete_prefix(project_prefix)
    components = relative.delete_suffix('.lean').split(File::SEPARATOR)
    unless components.all? { |part| part.match?(/\A[A-Za-z_][A-Za-z0-9_']*\z/) }
      errors << "cannot map local Lean source to a canonical module name: #{relative}"
      next
    end
    module_name = components.join('.')
    if module_files.key?(module_name)
      errors << "duplicate local Lean module #{module_name}"
      next
    end
    folded = module_name.downcase
    if casefolded_modules.key?(folded) && casefolded_modules[folded] != module_name
      errors << "case-folding module collision: #{casefolded_modules[folded]} and #{module_name}"
      next
    end
    module_files[module_name] = path
    casefolded_modules[folded] = module_name
  end

  # Read only the Lean module header. Imports are required to use the pinned
  # Lean 4.33 one-command-per-line forms
  #   [public] [meta] import [all] A.B
  # with canonical ASCII module names. Unsupported import-like syntax fails
  # closed instead of disappearing from the dependency graph.
  def header_imports(path)
    source = File.binread(path)
    if source.bytesize >= 3 && source.byteslice(0, 3) == "\xEF\xBB\xBF".b
      source = source.byteslice(3, source.bytesize - 3)
    end
    imports = []
    block_depth = 0
    identifier = "[A-Za-z_][A-Za-z0-9_']*"
    module_name = "#{identifier}(?:\\.#{identifier})*"
    import_line = Regexp.new(
      "\\A(?:public\\s+)?(?:meta\\s+)?import(?:\\s+all)?\\s+(#{module_name})\\z")
    import_like = /\A(?:[A-Za-z_][A-Za-z0-9_']*\s+)*import(?:\s|\z)/

    source.each_line.with_index(1) do |raw_line, line_no|
      code = String.new(capacity: raw_line.bytesize, encoding: Encoding::BINARY)
      index = 0
      while index < raw_line.bytesize
        byte = raw_line.getbyte(index)
        following = index + 1 < raw_line.bytesize ? raw_line.getbyte(index + 1) : nil
        if block_depth > 0
          if byte == 47 && following == 45
            code << '  '
            block_depth += 1
            index += 1
          elsif byte == 45 && following == 47
            code << '  '
            block_depth -= 1
            index += 1
          elsif byte == 10 || byte == 13
            code << byte
          else
            code << 32
          end
        elsif byte == 47 && following == 45
          code << '  '
          block_depth = 1
          index += 1
        elsif byte == 45 && following == 45
          break
        else
          code << byte
        end
        index += 1
      end

      stripped = code.strip
      next if stripped.empty? || stripped == 'module' || stripped == 'prelude'
      if (match = stripped.match(import_line))
        imports << [match[1], line_no]
      elsif stripped.match?(import_like)
        raise "unsupported import syntax in #{path}:#{line_no}: #{stripped}"
      else
        # Lean imports belong to the module header, so the first other command
        # ends the only region in which import directives may occur.
        return imports
      end
    end
    raise "unterminated block comment in #{path}" unless block_depth.zero?
    imports
  end

  roots = %w[HeilbronnChallenge HeilbronnSolution]
  roots.each do |root|
    errors << "missing required root module #{root}" unless module_files.key?(root)
  end

  visited = {}
  queue = roots.select { |root| module_files.key?(root) }
  import_edges = 0
  mathlib_edges = 0
  begin
    until queue.empty?
      current = queue.shift
      next if visited[current]
      visited[current] = true
      importer = module_files.fetch(current)
      header_imports(importer).each do |imported, line_no|
        import_edges += 1
        if module_files.key?(imported)
          queue << imported
        elsif imported == 'Mathlib' || imported.start_with?('Mathlib.')
          mathlib_edges += 1
        else
          relative = importer.delete_prefix(project_prefix)
          expected = imported.tr('.', File::SEPARATOR) + '.lean'
          errors << "#{relative}:#{line_no}: unresolved non-Mathlib import #{imported} (expected local file #{expected})"
        end
      end
    end
  rescue StandardError => error
    errors << error.message
  end

  unless errors.empty?
    warn errors.uniq.sort.join("\n")
    exit 1
  end
  unreachable = module_files.length - visited.length
  puts "roots=2; reachable local modules=#{visited.length}; " \
    "import edges=#{import_edges}; ignored Mathlib edges=#{mathlib_edges}; " \
    "unreachable local sources=#{unreachable}"
RUBY
then
  pass_item 13 "$(tr '\n' ' ' < "$closure_result" | sed 's/[[:space:]]*$//')"
else
  fail_item 13 "transitive local import closure failed: $(tr '\n' ' ' < "$closure_result" | sed 's/[[:space:]]*$//')"
fi

if [ -n "$failed_items" ]; then
  printf 'AUDIT RESULT: FAIL (items: %s)\n' "$failed_items"
  exit 1
fi

if [ -n "$warned_items" ]; then
  printf 'AUDIT WARNINGS: %s\n' "$warned_items"
fi
printf 'STATIC AUDIT ONLY: run the official Comparator, axiom inspection, and forced NanoDa before submission.\n'
if [ "$submission_ready" -eq 1 ]; then
  printf 'AUDIT RESULT: PASS (static submission-layout checks only)\n'
else
  printf 'AUDIT RESULT: PASS (staging consistency only; not submission-ready)\n'
fi
