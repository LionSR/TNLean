# tenkz Phase 3 — demolition checklist

The single-PR removal of the old `tex/tn/` system, executable once Phase 2
(chapter-by-chapter inlining) completes.  This is the tracked form of the
delete list in `DESIGN.md` §Phase 3; the entry-by-entry migration ledger is
`MIGRATION-MAP.md`.  Nothing on this list survives in any form.

## Preconditions (Phase-2 exit)

- [ ] `grep -r '\\TN[A-Z]' blueprint/src/chapter/` is empty (every legacy
      macro call inlined; countdown badge reads 0).
- [ ] Every `tenkz-compat.tex` entry is at remaining-use count zero.

## Delete — TeX (`tex/tn/`, 5,929 lines, whole directory)

| File | Lines |
|---|---:|
| `tex/tn/tn_catalogue.tex` (114 `\TNDeclareDiagram` registrations + roles/profiles/contexts metadata) | 2,213 |
| `tex/tn/tn_library.tex` (v/p/m×route connect macros, trivalent macros, motif constructors) | 1,440 |
| `tex/tn/tn_core.tex` (old port registry incl. `morphism`, old `.tnlog`, raw-`\def` layout profiles) | 763 |
| `tex/tn/tn_motifs_peps.tex` (incl. 7 hand-digitized region polygons) | 787 |
| `tex/tn/tn_motifs_mpdo.tex` | 281 |
| `tex/tn/tn_motifs_symmetry.tex` | 149 |
| `tex/tn/tn_atoms.tex` (hand-synced atom registry) | 148 |
| `tex/tn/tn_slide_catalogue.tex` + the parallel Slide* interface (`dark` theme replaces it) | 139 |
| `tex/tn/tikzlibrarytn.code.tex` (loader stub) | 9 |
| `tenkz-compat.tex` (the Phase-1 shim itself, deleted last) | — |

## Delete — Python (the registry pipeline)

| File | Lines | Note |
|---|---:|---|
| `blueprint/src/Packages/tn_diagrams.py` | 2,258 | per-macro plasTeX class manufacture, role/profile/contexts assert-equal checks, `_assert_no_chapter_local_tikz`, `assert_repeated_topologies_are_motifs`; the hash/cache/jinja core already survives inside `tenkz_pic.py` |
| `scripts/check_tn_references.py` | 242 | checks the old catalogue's call sites |
| `scripts/build_tn_gallery.py` | 385 | derives the gallery from the old registry; the auto-extracted per-chapter gallery (G15) replaces it |

## Rewire — build plumbing

- [ ] `blueprint/src/web.tex`: `\usepackage{tn_diagrams}` → `\usepackage{tenkz_pic}`
      (plasTeX package swap; `packages-dirs=Packages` in `plastex.cfg` is unchanged).
- [ ] `blueprint/src/latexmkrc`: `TEXINPUTS` `../../tex/tn//` → `../../tex/tenkz//`.
- [ ] CI: `blueprint.yml` and `lint-blueprint.yml` steps invoking
      `Packages/tn_diagrams.py` → tenkz equivalents; every `tex/tn/**` path
      filter (`blueprint.yml`, `lint-blueprint.yml`, `blueprint-prose-review.yml`,
      `claude-code-review.yml`) and `find … tex/tn` invocation → `tex/tenkz`.

## Exit criteria

- [ ] `grep -r '\\TN[A-Z]' blueprint/src/` is empty.
- [ ] `git grep -l 'tex/tn/'` and `git grep -l 'tn_diagrams'` are empty.
- [ ] Blueprint print (latexmk) and web (plasTeX) builds are green; the
      B1–B8 corpus and the gallery pixel set render unchanged.
