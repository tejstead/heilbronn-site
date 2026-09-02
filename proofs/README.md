# Formal proofs

Curated, source-only formalization snapshots live below `proofs/`. Projects
prepared for the Palomar registry use the layout
`proofs/palomar/<project-name>/`.

A Palomar submission is pinned by three things: this public repository, an
exact 40-character Git commit SHA, and the repository-relative path to the
project's `comparator.json`. That makes the reviewed source immutable and
reproducible even when `main` later advances.

Only source, verifier metadata, and human-readable verification notes belong
here. Lean build products and dependency caches such as `.lake/`, `.olean`,
and `.ilean` files are intentionally excluded. The repository-root
[MIT license](../LICENSE) applies to these projects.
