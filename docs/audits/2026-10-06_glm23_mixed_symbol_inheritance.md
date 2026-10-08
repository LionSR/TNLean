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
