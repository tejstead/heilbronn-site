PY := .venv/bin/python

.PHONY: build test serve serve-caddy deploy sync-sources sync-friedman clean check-submission

build:
	$(PY) -m build

test:
	$(PY) -m pytest tests/ -q
	node --test tests/test_verifier_js.mjs

serve:
	$(PY) -m http.server -d dist 8080

# Production-identical serving: precompressed siblings + cache headers.
serve-caddy:
	docker run --rm \
	  -v "$(PWD)/dist":/srv:ro \
	  -v "$(PWD)/deploy/Caddyfile.local":/etc/caddy/Caddyfile:ro \
	  -p 8081:8081 caddy:2-alpine

deploy:
	deploy/deploy.sh

sync-sources:
	$(PY) build/sync_sources.py

sync-friedman:
	$(PY) scripts/friedman_sync.py

# Verify a coordinate submission the same way the PR workflow does:
#   make check-submission DIRS=data/sources/external/square-n17
check-submission:
	python3 scripts/check_submission.py $(DIRS)

clean:
	rm -rf dist
