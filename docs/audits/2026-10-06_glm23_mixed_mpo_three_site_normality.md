# Three-site normality of the mixed MPO

## Source and scope

The source is Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`Papers/2203.12563/REsubmission.tex`, with version and license recorded in
`Papers/NOTICE.md`:

- `eq:orthoV`: biorthogonal analysis and synthesis;
- lines 1584–1601: the square-physical state support and mixed construction;
- lines 1600–1631: the crossed action-map contractions;
- lines 1667–1685: the additional aligned L- and F-symbol setting;
- lines 1687–1689: the one-site injectivity discussion.

The new result concerns the actual `mixedEndpointMPO`, and concludes
injectivity after blocking **three** sites. Its isolated assumptions are
positive state-bond dimensions and common multiplicity, injectivity of both
endpoint MPO tensors, and biorthogonality of both endpoint action-map pairs.
It does not assume any state tensor, exact action reconstruction, L- or
F-symbol alignment, or ambient completeness. It is not a formalization of
the source's one-site assertion in its full categorical setting.

For a rectangular matrix X, biorthogonality gives

    V₀ν (Σμ W₀μ X V₁μ) W₁ν = X.

Taking X to be a nonzero matrix unit produces a nonzero entry in a crossed
mixed-MPO letter. Exchanging the endpoints gives the other crossed corner.
Endpoint MPO injectivity supplies all diagonal matrix units in the
one-letter span. If Cᵤᵥ is a nonzero crossed entry, then

    Eₐᵤ C Eᵥᵦ = Cᵤᵥ Eₐᵦ.

Dividing by Cᵤᵥ supplies every crossed matrix unit in the exact three-letter
span. Diagonal units have the same length because Eₐᵦ = Eₐᵦ Eᵦᵦ Eᵦᵦ.
Thus that span is the full operator-bond matrix algebra.

A separate source-facing consequence derives positive multiplicity from
one endpoint's positive MPO bond, injective MPO, injective square-physical
state tensor, and exact action decomposition. The D² state letters are a
basis; a zero-copy action would make every MPO coefficient vanish. The
mixed exact-action result requires injectivity only of A₀, together with
both exact action decompositions and both MPO injectivities. Injectivity
of A₁ is not added.

The one-site assertion is neither imported as a premise nor refuted here.
A numerical example satisfying only isolated assumptions is not a
counterexample to the paper's full aligned categorical setting. No
uncertified full-source counterexample is included.

## Blueprint ownership

`blueprint/src/chapter/ch30_mpo_mixed_normality.tex` has three theorem nodes
and three mathematical proofs. The first node owns both the three-site
result and its immediate normality consequence. Its four declaration links
are, in namespace `MPSTensor.MPOSymmetry`:

- `isNBlkInjective_mixedEndpointMPO_three`
- `isNormal_mixedEndpointMPO`
- `multiplicity_pos_of_injective_endpoint_action`
- `isNBlkInjective_mixedEndpointMPO_three_of_exact_action`

The signatures were compared against the production source. All four have
exactly one owner in the new leaf. Checked statement and proof markers now follow the exact-tree CI evidence
recorded below. Diagram, coefficient, and presentation checks alone do not
justify those markers.

## Regression coverage

`scripts/test_tenkz_mixed_normality.py` uses the existing mixed-action
matrix helpers and Python's exact `Fraction` arithmetic. No dependency is
added. The Tenkz checkout is the unchanged pin
`08a6493f3605dcf2ca5b512823ccb2698dfc027b`.

The two displayed equalities are substantive contractions: five ordered
rectangular factors recover X, and three factors isolate a crossed matrix
unit. Each has adjacent formula, leg, contraction, and boundary comments.
The native check compiles their actual production print wrapper, then
separately runs the hard Tenkz boundary-signature comparison. Both modes
check atom/wire counts, all open labels, and the absence of hidden grid or
trace connections. Both pass with zero audit findings.

Seven source mutations are rejected: endpoint and multiplicity changes,
a changed contraction wire, a changed open index, an omitted sandwich
coefficient, an incorrect matrix-unit index, and an invented adjoint.

Exact coefficient tests perform 1,446 equalities for
(D₀,D₁,χ₀,χ₁,m) = (2,3,3,4,2), (3,2,2,3,1), and (1,2,3,4,2).
Both crossed directions are checked, with every rectangular matrix unit
and an additional dense rational X. Independent invertible state and MPO
bond gauges give non-adjoint maps; their biorthogonality is checked before
use. Six arithmetic mutations are detected: a missing multiplicity term,
a permuted multiplicity pairing, analysis replaced by synthesis transpose,
state-first rather than MPO-first flattening, exchanged physical row/input
indices, and a doubled coefficient.

A separate actual-constructor fixture uses D=(2,3), χ=(3,4), m=2, with
625 physical-pair letters. The endpoint operator letters include every
matrix unit. Their exact word-span ranks at lengths one, two, and three
are respectively **27, 45, and 49**, the last equal to (3+4)². All 49
matrix units also have directly checked three-letter certificates whose
factors are actual letters. Omitting the reciprocal crossed coefficient
fails. With empty crossed contractions the three-letter rank is only 25,
which records why positive multiplicity is needed.

This fixture tests the core isolated assumptions. It supplies neither
exact action on injective state tensors nor a fusion category, aligned
L-symbols, or F-symbols. It is finite regression evidence, not a Lean proof
or a counterexample to the full source setting.

## Presentation and source checks

A focused six-page PDF was rendered using the production preamble and
three exact supporting statement excerpts. Every page was visually
inspected, including the two affected mathematical pages and all four
panels. The final PDF log has no warnings, unresolved references,
overfull boxes, or underfull boxes.

The unchanged strict `texra-blueprint web` command passes on the focused
source. The production XeLaTeX/PDF/pdftocairo vector fallback supplies all
four SVGs because dvisvgm is absent. The regression finds two equation
wrappers, four image files, all four declaration links exactly once, valid
paragraph structure, no visible raw Tenkz, and no unresolved reference.
An initial focused build failed to locate `tenkz_paths` after copying the
production package directory; adding the production scripts directory to
PYTHONPATH resolved it without altering a renderer or failure gate.
The web bibliography was generated with the unchanged `texra-blueprint bbl`
command; this avoids the unresolved citation produced by copying the print
BibTeX bibliography, whose entries lack explicit web labels.

Pinned latexindent formatting is idempotent. Python compilation, Tenkz
source lint, reference/declaration ownership checks, and whitespace checks
pass. All local references resolve to unique labels.

Playwright is absent from the local blueprint environment. No browser
launch, MathJax runtime check, or desktop/mobile layout pass is claimed.
The real fail-closed option is retained for CI:

    python3 scripts/test_tenkz_mixed_normality.py --web-root blueprint/web --browser

It uses the repository's existing layout assertion at 1,440 and 360 pixels,
waits for actual MathJax completion and loaded images, and propagates
missing-dependency, launch, rendering, and layout failures.

No Lean build or probe, canonical-cache mutation, remote publication,
shared router/workflow change, or pin change was performed in this
isolated documentation worktree. These checks are not a whole-blueprint
build, `checkdecls`, aggregate-import build, or exact-head CI result.

## Integration

The documentation branch starts at `313fb03e2661aa26696cd20c83d9d7ff9400e6bb`.
The integrating owner should:

1. Include `chapter/ch30_mpo_mixed_normality` from
   `blueprint/src/chapter/ch30_mpo_symmetry_basics.tex` after the existing
   mixed-action subsection (or after mixed fusion if that leaf is stacked).
2. Add this regression beside `test_tenkz_mixed_action.py` in both blueprint
   workflows' native/browser commands and relevant path/change filters.
   Preserve the explicit `--browser` option in the web jobs.
3. Integrate the separate Lean module and regression, regenerate imports
   and declaration lists, and run their normal verification gates.
4. Add checked markers only from the corresponding final source checks,
   then verify the exact integrated tree in CI.

For a focused rerun with Tenkz already fetched:

    python3 scripts/test_tenkz_mixed_normality.py --output-dir /tmp/mixed-normality

For generated HTML without claiming browser execution:

    python3 scripts/test_tenkz_mixed_normality.py --web-root blueprint/web

## Combined-package integration checkpoint, 2026-10-06

The three-site normality production file and regression are integrated
without byte changes. Their SHA-256 values are respectively
`a82228dc43207801293af4f5a1c2c5b620f61257a836d1a178624f884b902c7e` and
`9c3bbd1c51a9cb3d2c880b3bd03ba3bcf8b07a1b5ae7eaabbe2e5e2e4daaf1cf`.
The exact-body strict Lean probe, including all four standard-axiom guards,
passed with exit zero and no diagnostics. This is a local elaboration
check; the integrated aggregate build and exact-head CI were pending at
that checkpoint and have since passed as recorded below.

The integration adds the production aggregator import, the existing strict
regression loop entry, the chapter inclusion, and native/browser diagram
checks to the existing workflows. The chapter-wide equation fixture grows
from seven to nine two-picture rows, accounting for the two new identities.
The normality arithmetic and native Tenkz tests pass in this integrated
worktree. The source-scope distinction is recorded in
`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.

This package is being combined with inheritance of the actual mixed
operator's L- and F-symbols. Those additional theorems have their own
validation record; the checked normality theorem does not imply their
proofs have passed. The paper's full phase-classification and weak-Hopf
realization obligations remain open.

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
