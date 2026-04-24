# Deploying Blueprint & API Docs

The project site at `sirui-lu.com/TNLean/` is served from the `gh-pages` branch.
Each deploy updates only its own files — blueprint deploys preserve `/docs/` and vice versa.

## Local Preview (no push)

```bash
# Build and preview blueprint locally
cd blueprint
leanblueprint web
leanblueprint serve        # opens http://localhost:8000

# Build blueprint PDF
leanblueprint pdf          # output: blueprint/print/print.pdf

# Build and preview API docs locally
cd docbuild && lake build TNLean:docs
cd .lake/build/doc && python3 -m http.server 8080   # opens http://localhost:8080
```

## Deploy Blueprint (fast)

Builds `leanblueprint pdf/web` and pushes blueprint + homepage to `gh-pages`.
Does not touch `/docs/` — existing API docs are preserved.

```bash
./scripts/deploy-blueprint.sh
```

Takes seconds if blueprint is already built, a couple of minutes otherwise.

## Deploy Blueprint + API Docs (full)

Builds everything and pushes to `gh-pages`, including `/docs/` API documentation.

```bash
./scripts/deploy-docs.sh
```

The first run is slow (hours) because `lake build TNLean:docs` in `docbuild/`
needs to elaborate the full codebase including Mathlib for doc-gen4.
Subsequent runs are incremental — only changed files are re-elaborated.

To generate API docs without deploying:

```bash
cd docbuild && lake build TNLean:docs
# Output: docbuild/.lake/build/doc/
```

## CI Workflows

| Workflow | Trigger | What it does |
|----------|---------|-------------|
| `blueprint.yml` | Every push to `main` | Builds blueprint, pushes to `gh-pages` |
| `docgen.yml` | Weekly (Sunday 06:00 UTC) + manual | Full build + API docs, pushes to `gh-pages` |

To manually trigger docgen from the CLI:

```bash
gh workflow run "Full documentation" --repo LionSR/TNLean --ref main
```

## Site Structure on `gh-pages`

```
/                    ← Jekyll homepage (home_page/)
/blueprint/          ← leanblueprint web output
/blueprint.pdf       ← leanblueprint PDF
/docs/               ← doc-gen4 API documentation
/badges/             ← Shields.io endpoint JSON for README status badges
```

## Setup

GitHub Pages must be configured to deploy from the `gh-pages` branch:

**Settings > Pages > Source: Deploy from a branch > `gh-pages` / `/ (root)`**
