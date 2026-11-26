# Deploying Blueprint & API Docs

The project site at `sirui-lu.com/TNLean/` is served from the `gh-pages` branch.
Each deploy updates only its own files — blueprint deploys preserve `/docs/` and vice versa.

## Local Preview (no push)

```bash
# Materialize the pinned diagram package.
python3 scripts/fetch_tenkz.py

# Build and preview blueprint locally
cd blueprint
leanblueprint web
leanblueprint serve        # opens http://localhost:8000

# Build blueprint PDF
leanblueprint pdf          # output: blueprint/print/print.pdf

# Build the FT-MPS blueprint volume
cd ..
./scripts/build_blueprint_ch01_12.sh  # output: blueprint/print/print12.pdf

# Build and preview API docs locally
cd docbuild && lake build TNLean:docs
cd .lake/build/doc && python3 -m http.server 8080   # opens http://localhost:8080
```

## Deploy Blueprint (fast)

Builds the full PDF and web blueprint and the separate FT-MPS volume in
GitHub Actions and deploys them with the homepage. Existing API docs are
preserved. Local builds cannot publish; trigger the workflow instead:

```bash
gh workflow run blueprint.yml --repo LionSR/TNLean --ref main
```

## Deploy Blueprint + API Docs (full)

Builds everything in GitHub Actions, including the `/docs/` API documentation,
and deploys it:

```bash
gh workflow run docgen.yml --repo LionSR/TNLean --ref main
```

The first run is slow (hours) because `lake build TNLean:docs` in `docbuild/`
needs to elaborate the full codebase including Mathlib for doc-gen4.
Subsequent runs are incremental — only changed files are re-elaborated.

`docbuild/` shares the root package directory, so `docbuild/lake-manifest.json`
must pin the same revisions as `lake-manifest.json`. After any dependency bump,
run `lake update` inside `docbuild/` in the same pull request; PR CI enforces
this with `scripts/check_docbuild_manifest.py`.

To generate API docs without deploying:

```bash
cd docbuild && lake build TNLean:docs
# Output: docbuild/.lake/build/doc/
```

## CI Workflows

| Workflow | Trigger | What it does |
|----------|---------|-------------|
| `blueprint.yml` | Nightly, called by `nightly.yml` (19:23 UTC) + manual | Builds blueprint, deploys Pages |
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
/blueprint-ch01-12.pdf ← FT-MPS blueprint PDF
/docs/               ← doc-gen4 API documentation
/badges/             ← Shields.io endpoint JSON for README status badges
```

## Setup

GitHub Pages must be configured to deploy from the `gh-pages` branch:

**Settings > Pages > Source: Deploy from a branch > `gh-pages` / `/ (root)`**
