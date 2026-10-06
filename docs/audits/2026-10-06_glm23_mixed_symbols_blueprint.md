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

## Initial focused-validation boundary

The initial focused check neither ran Lean nor certified proofs and did not
add checked markers. The exact-tree CI evidence below supersedes that
initial proof-status limitation.

## Exact-tree CI validation and checked owners, 2026-10-06

[PR #8716](https://github.com/LionSR/TNLean/pull/8716) passed all eight
engineering checks at head `866ecede0a71a5617699023f250604abcd64a097`.
Its tested merge `b61da9527f101cada0c87fa1889c03009c53acc8` has the same
tree, `72d41a91226aad75e9f713fe718f0fdad39503a2`. The immutable
[CI run](https://github.com/LionSR/TNLean/actions/runs/37409746063) and
[build job](https://github.com/LionSR/TNLean/actions/runs/37409746063/job/112095291464)
validate the four production modules (936 lines) and final three regression
files, including all nineteen standard-foundation guards. The four new
module times were 7.9, 6.4, 7.4, and 11.0 seconds.

On that evidence, the two leaves now mark all nine statements and their
seven proofs checked, covering the 28 uniquely owned new declarations.
This documentation-only update preserves every production and regression
byte and the mathematical hypotheses. Three-site normality, chosen-symbol
alignment, and the assumed endpoint analysis relations retain their stated
scopes; no mixed weak-Hopf realization, integral, or phase classification
is supplied by these markers. Fresh local rendering is recorded separately
and is not the basis for Lean proof status.

## Checked-marker rendering verification, 2026-10-06

The exact changed leaves were copied into a focused, reference-closed fixture
with the unchanged production macros and renderer. Tool versions were
texra-blueprint 0.3.8 (commit `65434add8b88bc6a22c701521baa3abec2369341`),
plasTeX 3.1, and the pinned Tenkz commit
`08a6493f3605dcf2ca5b512823ccb2698dfc027b`. TeX formats were regenerated
from installed official sources in a separate workspace tree; no Lean
build, elaboration, or Lean-cache mutation was performed.

The ten-page XeLaTeX PDF includes both leaves and twelve exact context
excerpts. All mathematical pages and diagrams were visually inspected.
The final TeX log has no unresolved references or over/underfull boxes.
Strict web generation and generated-source checks pass: six HTML files,
28 new declaration links, nine checked statements, seven checked proofs,
four equation rows, and nine SVGs (eight new panels plus one context panel).
The normality and symbol native wrapper/signature checks pass with zero
hard or advisory findings. The normality regression also passes 1,446
exact coefficient equalities, all 49 three-letter matrix-unit certificates,
seven source and six arithmetic mutations; the symbol regression rejects
all eight source mutations.

Full blueprint/source synchronization with the pinned QICLean source has
no missing references, stale declaration-list entries, or duplicate owners.
Reverse coverage, reader-facing prose, and whitespace checks pass. All
production, regression, workflow, router, and dependency bytes are unchanged
from the exact tested public head.

The web renderer used its existing XeLaTeX/PDF/pdftocairo fallback because
`dvisvgm` is absent. Local browser layout validation is **not passed**: the
ordinary Playwright launch failed because its Chromium headless-shell
executable is absent. No browser/security workaround or weakening of the
fail-closed CI checks was made. LuaLaTeX was also unavailable locally because
the installed tree lacks `luaotfload-main`; the successful PDF route was
XeLaTeX. These focused local results do not claim a fresh full-volume build
or a fresh exact-head CI run for the documentation-only commit.

Artifact SHA-256 values:

- Focused PDF: `be425615e19724f9721b339b8d69733d341e8e6887d75cceba5c6f8378ade8c7`.
- Generated chapter HTML: `ee0692117333556ff06ff646b24e42a75646c0148968a906f023e7558729ddd2`.
- `ch30_mpo_mixed_normality.tex`: `ab52477bc32d70395a101f223e1d5d4421d3f9d7b1b8e667ed5d6f24259865ce`.
- `ch30_mpo_mixed_symbols.tex`: `8ce00b6b7d9cd6eac55aac123cf290235c2a8b80f0968f03f424e71fa436924a`.
