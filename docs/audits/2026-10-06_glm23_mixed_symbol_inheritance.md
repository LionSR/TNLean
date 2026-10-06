# Actual mixed L- and F-symbol inheritance

## Source and convention

The source is Garre-Rubio, Lootens, and Molnár,
[arXiv:2203.12563v3](https://arxiv.org/abs/2203.12563v3),
`Papers/2203.12563/REsubmission.tex`, lines 1667–1685. `Papers/NOTICE.md`
identifies this exact version and its CC BY 4.0 license.

The source first requires equality of the chosen endpoint L and F symbols.
It then states that the action tensors of `Agammasym` retain the common L
symbols throughout the path, and that the displayed mixed fusion tensors
satisfy `Fsymbolsdef` with the common endpoint F matrix.

The L matrix here is the existing `MPOTensor.actionLMatrix`, with sequential
rows `(z,i,j)` and fusion-then-action columns `(c,k,μ)`. The F matrix is the
existing `MPOTensor.fusionFMatrix`: left-tree analysis followed by right-tree
synthesis, with rows `(e,mu,nu)` and columns `(f,lambda,sigma)`. The source
orientation correction recorded in
`docs/paper-gaps/glm23_multiplicity_l_indices.tex` is preserved. No inverse
or transposed F convention is substituted.

## Actual matrices and contractions

The action maps are exactly `mixedEndpointMPOAnalysis` and
`mixedEndpointMPOSynthesis`, already used by
`isBiorthogonalDecomposition_mixedEndpointInterpolation`. The fusion maps
are exactly `mixedEndpointMPOFusionAnalysis` and
`mixedEndpointMPOFusionSynthesis`, used by the existing actual mixed fusion
decomposition. Every virtual direct-sum leg independently selects its
endpoint sector. Two composed maps can therefore be nonzero only when all
three incoming legs and the outgoing leg choose the same endpoint.

`MixedEndpointTripleMaps.lean` packages this one elementary support
calculation. Its analysis-synthesis product is the rectangular block matrix
with the two endpoint products on its diagonal and zero off-diagonal
corners. It does not posit a comparison matrix, tensor decomposition,
scalarity, or a symbol identity.

`MixedEndpointMPOActionSymbols.lean` proves that the actual sequential
analysis and fusion-then-action synthesis have this support. The resulting
cross product is exactly the two-block endpoint product. Taking its
normalized trace gives

    Lmixed = (D₀ + D₁)⁻¹ (D₀ L₀ + D₁ L₁).

Consequently `L₀ = L₁` implies `Lmixed = L₀`. If `D₀ + D₁ = 0`,
both endpoint dimensions vanish and all three raw matrices are zero;
otherwise the nonzero total dimension cancels.
The underlying action maps contain no interpolation parameter. They are the
same maps acting on the actual mixed state at every real γ, including γ=0
and γ=1. The regression pairs the actual decomposition at arbitrary γ with
this coefficient equality. No injectivity of either mixed endpoint state
is asserted or used.

`MixedEndpointMPOFusionSymbols.lean` names the exact tree contractions in
the existing raw F definition. It proves their mixed support and obtains

    Fmixed(a,b,c,d) = (χ₀(d) + χ₁(d))⁻¹
      (χ₀(d) F₀(a,b,c,d) + χ₁(d) F₁(a,b,c,d)).

Equality of the chosen endpoint raw F matrices gives the same matrix for
the actual mixed fusion maps. The analysis F-move is then lifted by the
same matching-sector calculation. Its premises are the two endpoint
F-move equations with their own actual raw F coefficients and equality of
those endpoint raw coefficients; no mixed F-move is assumed.

## Hypothesis audit

- Endpoint operator dimensions are independent for every label. The action
  result has independent endpoint state dimensions and a single state
  block, exactly as the existing mixed constructor.
- The dimension-weighted identities need no positivity. An empty final
  bond has zero trace, so multiplying its normalized trace by dimension
  still recovers its trace.
- Identification with a common raw coefficient also needs no positivity.
  The zero-total-dimension case is handled by the vanishing endpoint raw
  traces; cancellation is used only in the nonzero case.
- Fusion and action multiplicities may vanish. No argument selects a
  distinguished multiplicity coordinate or assumes a symbol entry is
  nonzero.
- The algebraic identities hold for arbitrary chosen endpoint maps. They
  therefore apply, without new restrictions, to the source's endpoint
  decomposition maps. No mixed injectivity, completeness, adjoint closure,
  or support-equality assumption is introduced.
- The F-move lift starts from endpoint F-move equations. It does not derive
  endpoint coherence from unrelated tensor data. The new weighted raw F
  theorem itself requires no endpoint F-move premise.
- Equality of raw L/F matrices remains already-aligned source data.
  Deriving that alignment from gauge-equivalent symbol classes is separate.

## New declarations

Shared support module:

- `mixedEndpointTripleEquiv`
- `mixedEndpointTripleAnalysis`, `mixedEndpointTripleSynthesis`
- `mixedEndpointTripleAnalysis_mul_synthesis`
- `mixedEndpointTripleAnalysis_trace_mul_synthesis`
- `finDimension_mul_normalizedTrace`
- `mixedEndpointTripleAnalysis_normalizedTrace_mul_synthesis`

Actual action symbols:

- `mixedEndpoint_sequentialActionAnalysis`
- `mixedEndpoint_fusionThenActionSynthesis`
- `mixedEndpoint_actionTree_cross`
- `actionLMatrix_mixedEndpoint`
- `actionLMatrix_mixedEndpoint_eq_of_eq`

Actual fusion symbols:

- `MPOTensor.fusionLeftTreeAnalysis`
- `MPOTensor.fusionRightTreeAnalysis`
- `MPOTensor.fusionRightTreeSynthesis`
- `MPOTensor.fusionFMatrix_eq_inv_dim_mul_trace`
- `mixedEndpointMPOFusionAnalysis_sum_apply`
- `mixedEndpointMPOFusionSynthesis_sum_apply`
- `mixedEndpointMPOFusion_leftTreeAnalysis`
- `mixedEndpointMPOFusion_rightTreeAnalysis`
- `mixedEndpointMPOFusion_rightTreeSynthesis`
- `mixedEndpointMPOFusion_fusionFMatrix_eq_weighted`
- `mixedEndpointMPOFusion_fusionFMatrix_of_eq`
- `mixedEndpointMPOFusion_fusionFMatrix_analysis`

Unqualified declarations above are in `MPSTensor.MPOSymmetry`.

## Validation and integration

The two new `TNLeanTest` modules exercise actual matrix definitions,
source-oriented coordinates, independent dimensions, empty endpoint bonds,
zero multiplicities, the whole-parameter action statement, and the actual
F-move lift. Standard-axiom guards cover the substantive proof dependencies.

An independent exact-rational coordinate fixture checks 32 common L/F
entries with endpoint dimensions 1 and 2. Its asymmetric F entries 196 and
225 distinguish the source orientation from a transpose. With unequal
endpoint F coefficients 100 and 400, the mixed coefficient is 300, which
rejects the unweighted mean 250. These are checks of the actual chosen-map
contractions; they assert no tensor decomposition or endpoint F-move. The
Lean checks below remain authoritative for the general theorems.

The exact production proof snapshot was checked by the serial one-thread,
no-artifact combined probe 5 on 2026-10-06. All production declarations and
all 15 standard-axiom guards passed. The proof source bytes match preservation
commit `0819cc25742c7aa23e8bc004cb24dcba57311cd6`. The immutable local
source/pin/import manifest, log, exit status, and terminal timestamp use
`/workspace/shared/glm23-symbol-probe5` as their prefix. The run took 1,145
seconds, predominantly import loading (about 1,100 seconds).

The strict combined run nevertheless exited 1: its only 12 diagnostics were
unused names `a,b,c` in four constant-dimension Pi binders in the final
empty-multiplicity F regression. Those binder names were changed to anonymous
binders afterward. No production theorem, proof, guard, option, or limit was
changed. The renamed test still requires separate-module strict CI; this
local result is not reported as an overall strict regression pass.

Earlier launcher 1 failed before Lean invocation because `/usr/bin/time`
was absent. Probe 4 exposed the coordinate simplifications repaired before
probe 5 and is not successful evidence. No local module build, canonical
source/cache mutation, or checked blueprint marker is claimed.

Full separate-module validation and router/workflow/blueprint integration
belong to the coordinating task. This package changes only new proof,
regression, and audit files. It proves neither source one-site mixed-MPO
injectivity nor Hamiltonian commutation, physical adjoints, or full phase
classification.

## Coherent normality/symbol integration, 2026-10-06

The package is combined with the independently checked three-site normality
result on the verified mixed-fusion base PR #8714. There are four new
production modules (936 lines), three regressions with nineteen
standard-foundation guards, and 28 uniquely owned public declarations.
All production and regression bytes match their respective final source
manifests. The normality probe passed strictly; the symbol probe passed all
production proofs and fifteen guards but failed only on unused names in
constant-dimension test binders, subsequently made anonymous. The final
separate-module build and repaired regression remain pending exact-head CI.

The two mathematical leaves add four equation rows / eight Tenkz panels.
The chapter-wide browser expectation grows from seven to eleven rows;
all existing checks and explicit browser gates are retained. The combined
focused strict web build, declaration/reverse synchronization, native
contraction and mutation checks, generated HTML, module policies, prose,
formatting and whitespace checks pass. The 10-page focused PDF was rendered
and its main mathematical pages and all diagrams inspected. A small inline
formula overflow was repaired in prose; final PDF logs have no warnings,
unresolved references, overfull or underfull boxes. The source-gap reference
uses the existing bibliography entry. These local rendering checks do not
replace the full blueprint/browser CI run.

Independent read-only review found no mathematical or source-faithfulness
blocker: the final-bond weights, source F orientation, zero-dimension
branches, three-site normality argument, and actual endpoint-to-mixed
F-move were checked. The leaves remain unchecked until actual separate-module
compilation. No equality of gauge classes is silently replaced by equality
of chosen coefficients, and no physical adjoint or phase-classification
conclusion is claimed.
