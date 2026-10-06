# Mixed L/F-symbol blueprint and diagram validation

## Scope

The new leaf is `blueprint/src/chapter/ch30_mpo_mixed_symbols.tex`.
It links all 24 public declarations in `MixedEndpointTripleMaps`,
`MixedEndpointMPOActionSymbols`, and `MixedEndpointMPOFusionSymbols`.
The mathematical statements distinguish arbitrary-map normalized-trace
coefficients from the separately assumed endpoint analysis F-moves.
The leaf allows zero dimensions and multiplicities, states the
source-oriented L and F contractions, and explains whole-parameter L
inheritance without mixed-state injectivity.

Source: GLM23, `Papers/2203.12563/REsubmission.tex`, lines 1667–1685,
with `Agammasym`, `eq:F_symbol2`, and `Fsymbolsdef`;
`Papers/NOTICE.md` identifies arXiv:2203.12563v3 and CC BY 4.0.

## Exact diagram contribution

- **2 new marked `tenkzequation` rows, 4 native panels.**
- `TENKZ-MIXED-SYMBOLS-L`: actual sequential-analysis/fusion-synthesis
  product, including all three contracted virtual legs.
- `TENKZ-MIXED-SYMBOLS-F`: actual mixed analysis F-move, with rows
  `(e,mu,nu)` and columns `(f,lambda,sigma)`.
- Expected boundary signatures: two panels with one west and one east
  open leg; two panels with one west and three east open legs.

## Focused checks

Run from the worktree root, using the existing warmed environment:

```sh
source /workspace/shared/glm23-env.sh
PYTHONDONTWRITEBYTECODE=1 MKTEXFMT=0 MKTEXTFM=0 MKTEXPK=0 \
  TENKZ_ROOT=/workspace/shared/TNLean-glm23-work/.deps/tenkz \
  python3 scripts/test_tenkz_mixed_symbols.py \
  --output-dir /tmp/tnlean-mixed-symbols-20261006
```

The tenkz checkout was verified at
`08a6493f3605dcf2ca5b512823ccb2698dfc027b`, matching `tenkz.toml`.
Both the production-wrapper compilation and the independent native hard
signature check passed, each with zero hard or advisory findings.
The production PDF was rendered and inspected: all labels and contractions
were legible, with no overlap or clipping. No overfull/underfull boxes or
warnings appeared in the focused TeX logs.

The source regression also passed: exact ownership of all 24 public
source declarations, existing cross-references, 2 rows/4 panels, and
rejection of all 8 mutations (third contraction, analysis/synthesis
roles, left/right fusion order, transposed F coefficient, an invented
adjoint, and the third external leg). Chapter labels were checked unique.
`git diff --check` passed.

The machine-readable record is
`/tmp/tnlean-mixed-symbols-20261006/validation.json`; its adjacent files
contain the native `.tex`, `.pdf`, `.tnlog`, and stdout logs.
`--source-only` runs without TeX. The optional `--web-root` and `--browser`
flags inspect already-built strict output and its desktop/mobile layout.

## Remaining validation

This focused check neither runs Lean nor certifies proofs. No checked
blueprint markers are present. No router, workflow, glossary, proof file,
existing audit, dependency, or build cache was changed by this work.
Full declaration validation, strict web/PDF builds, aggregate browser
checks, routing, and publication remain with the coordinating task.
