# heilbronn-site

Static site for the Heilbronn problem, served at
<https://math.tejstead.com/heilbronn>. An enhanced take on Erich Friedman's
[Packing Center pages](https://erich-friedman.github.io/packing/) (squares,
triangles, convex regions; n = 3–35): downloadable exact coordinates, an
interactive symmetry/congruence viewer, a client-side verifier, proof links,
and per-n record history.

Everything is generated ahead of time on a laptop; the server only serves
static files (precompressed, long-cached). No JS except the viewer and
verifier enhancements — every page works fully with JS disabled.

## Layout

- `data/sources/` — vendored upstream inputs, each with `ATTRIBUTION.md`
- `data/curated/` — hand-maintained provenance, references, overrides
- `data/canonical/` — the unified per-configuration JSONs (ingest output, committed)
- `build/` — the generator: ingest → verify → derive → render → downloads → compress
- `reconstruct/` — laptop-only optimization to recover unpublished configurations
- `templates/`, `assets/` — jinja2 templates, CSS, vanilla JS
- `deploy/` — Caddy site snippets + `deploy.sh` (rsync + graceful reload)
- `landing/` — the tejstead.com apex page

## Commands

```
make build        # full site into dist/
make test         # pytest + node --test golden fixtures
make serve        # quick preview at :8080
make serve-caddy  # production-identical preview at :8081
make deploy       # build, rsync to the box, reload Caddy
```

Deploys are also continuous: every push to `main` is built by the
`publish-site` workflow into a rolling release tarball, which the server
pulls every 5 minutes (`deploy/site-pull.sh`, cron) — so a merged PR is
live within ~10 minutes with no laptop involved. `make deploy` remains for
instant manual pushes and is still required for Caddyfile changes.

## Data provenance

Values, credits, and symmetry labels are facts recorded from Erich Friedman's
pages (snapshot in `data/sources/friedman/`); all figures are regenerated from
coordinates — none of his images are copied. Coordinates come from
[TejSteadQC/heilbronn-configurations](https://github.com/TejSteadQC/heilbronn-configurations),
[spiralulam/heilbronn](https://github.com/spiralulam/heilbronn) (MIT),
[google-deepmind/alphaevolve_results](https://github.com/google-deepmind/alphaevolve_results),
published exact constructions, or local reconstruction (labeled as such).

## License

Code is [MIT](LICENSE). Vendored data under `data/sources/` carries its own
attribution — see the `ATTRIBUTION.md` next to each source.
