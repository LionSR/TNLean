# MPU fusion and dagger source audit

<!-- TNLEAN_EXTERNAL_SOURCE_RANGES: 1706.07329v2 1002-1060,1011-1017,3121-3168,3124-3133,3137-3139,3142-3144,3147-3152,3156-3162,3168,3815-4034,3839,3865,3935-3938,3973-3976,3993-4005,4029-4033 -->
<!-- TNLEAN_EXTERNAL_SOURCE_RANGES: 2405.00439v2 343-377,358,358-364,359-364 -->

This note pins the external tensor results invoked in
`Papers/2502.20257/main.tex:1403--1678`.  It is a source-audit prerequisite for
issue #7281 and its implementation children; it does not formalize
`eq:fusion_1`, `eq:fusion_2`, or `prop:zetas`.

## Sources and notation

The primary sources used here are:

| Source | Audited passage | Source archive SHA-256 |
|---|---|---|
| Molnár--Ge--Schuch--Cirac, [arXiv:1706.07329v2](https://arxiv.org/abs/1706.07329) | `cornerproblem.tex:3121--3168`, with definitions at `1002--1060` and proof details at `3815--4034` | `045a2a94589c6d4f82946bc9a1b4322ebd5109882355356191f462b3d362b23e` |
| Garre-Rubio--Schuch, [arXiv:2405.00439v2](https://arxiv.org/abs/2405.00439) | `MPU-DW.tex:343--377`, especially Theorem 1 and its footnote at lines 358--364 | `166ce15a174167772f53d53b7ed15438fdf799717e053b128f612a264d3f8bb4` |
| MPU gauging paper | `Papers/2502.20257/main.tex:1403--1678` | repository source |

The exact external artifacts, extracted-file digests, and every cited subrange
are recorded in `Papers/external_sources.toml`. Running
`python3 scripts/verify_external_paper_sources.py --fetch` recovers
`cornerproblem.tex` under ignored `build/paper-sources/1706.07329/` output and
checks the unchanged vendored file `Papers/2405.00439/MPU-DW.tex` against the
official archive.

Fix $g,h\in G$.  Write

\[
  A=A_{g,h}:=\mathcal U_{gh},\qquad
  B=B_{g,h}:=\mathcal U_g\mathcal U_h,
\]

where a physical letter of either tensor is a ket--bra pair.  Algebraically,
the faithful TNLean choices are

```text
A := U_gh.toMPSTensor
B := (MPOTensor.mulTensor U_g U_h).toMPSTensor.
```

Thus $A^a$ is a $D_{gh}\times D_{gh}$ matrix and $B^a$ is a
$(D_gD_h)\times(D_gD_h)$ matrix.  For a word
$\mathbf a=(a_1,\ldots,a_n)$, write
$A^{\mathbf a}=A^{a_1}\cdots A^{a_n}$, and similarly for $B$.

The reduction matrices of arXiv:1706.07329 are

\[
 V:\mathbb C^{D_gD_h}\longrightarrow\mathbb C^{D_{gh}},\qquad
 W:\mathbb C^{D_{gh}}\longrightarrow\mathbb C^{D_gD_h}.
\]

The paper's diagrammatic convention is

\[
  F^<_{g,h}=V,\qquad F^>_{g,h}=W.
\]

This orientation is fixed by `eq:fusion_2`: its empty-word case is
$F^<F^>=VW=1_{D_{gh}}$, and its nonempty cases are

\[
  F^<_{g,h}B^{\mathbf a}F^>_{g,h}=A^{\mathbf a}.
\]

## The exact reduction theorem

### Existence

Proposition 20 (`thm:reductionexist`) of arXiv:1706.07329v2 states the
following.  Let $A$ be a **normal** MPS tensor, where normal means that its
transfer completely positive map is primitive (`cornerproblem.tex:1011--1017`),
and let $B$ be arbitrary.  If

\[
  V_n(B)=\lambda^n V_n(A)
\]

at every physical chain length, then matrices $V,W$ exist such that

\[
  VW=1,
  \qquad
  VB^{\mathbf a}W=A^{\mathbf a}
\]

for every word $\mathbf a$ (`cornerproblem.tex:3124--3133`).  The pair
$(V,W)$ is called a **reduction** (`cornerproblem.tex:3137--3139`).  In the
MPU application the operator representation law gives exact equality, so the
specialization has the source scalar $\lambda=1$.  The source applies the
proposition to the product tensor explicitly at
`cornerproblem.tex:3168`.

The printed proposition is false when $\lambda\ne1$.  In the scalar example
$D=d=1$, take $A^1=1$, $B^1=2$, and $\lambda=2$.  Then
$V_n(B)=2^nV_n(A)$ at every positive length, but $VW=1$ would force
$VB^1W=2$, contrary to the printed conclusion $VB^1W=A^1=1$.  The proof
silently replaces proportionality by equality: it says that $A$ and $B$
generate the same state at `cornerproblem.tex:3839`, `3865`, and again at
`3973--3976`.  For $\lambda\ne0$, applying the equality case to
$\lambda^{-1}B$ instead gives the corrected word relation

\[
  VB^{\mathbf a}W=\lambda^{|\mathbf a|}A^{\mathbf a}.
\]

The case $\lambda=0$ is degenerate and does not admit this rescaling.  This
false-source defect is recorded in
`docs/paper-gaps/mgsc18_reduction_proportionality_scalar.tex`.  It does not
affect the MPU application, which uses $\lambda=1$ and hence exactly the
equality case proved by the source.

The source writes the state-family hypothesis for $n\in\mathbb N$ without
declaring whether zero is included.  Its intended rectangular application
forces the chain lengths here to be positive: at length zero the coefficient
is the bond dimension, while the source permits the bond dimensions of $A$ and
$B$ to differ; the proof separately observes that the reduction equation at
length zero is $VW=1$ (`cornerproblem.tex:3935--3938`).  Reading the hypothesis
as TNLean's all-natural-length `MPSTensor.SameMPV₂` would therefore add a
condition absent from the intended application.  Its faithful existing
interface is
`MPSTensor.SameMPV₂Pos`.  The reduction conclusion itself includes the empty
word, giving $VW=1$.

For the present application the target tensor $A$ is already injective.
Garre-Rubio--Schuch therefore use the injective specialization below.  There is
no need to replace the cited theorem by a route through canonical BNT or MPDO
fusion data.

### Residual algebra and nilpotency length

Proposition 21 of arXiv:1706.07329v2 defines the residual letters

\[
  N^a:=B^a-WA^aV

\]

and proves that the nonunital algebra they generate is nilpotent
(`cornerproblem.tex:3142--3144`).  Definition 8 calls the least $N_0$ such
that

\[
  N^{a_1}\cdots N^{a_n}=0
  \quad\text{for every }n\geq N_0
\]

the **nilpotency length** of the selected reduction
(`cornerproblem.tex:3147--3152`).  It is a property of $(A,B,V,W)$, not the
injectivity length of $A$, not a property of $B$ alone, and not either of
the source-cut ranks $r[U]$ and $\ell[U]$ in arXiv:1703.09188.

Lemma `lem:B_expand` expands a word in $B$ into a residual prefix, one
reduced $A$-word, and a residual suffix
(`cornerproblem.tex:3993--4005`).  Together with Definition 8 it gives the
exterior identity represented by `eq:fusion_1`: if the two exterior
$B$-words have length $m\geq N_0$, then

\[
  B^{\mathbf p}F^> A^{\mathbf c}F^<B^{\mathbf q}
  =B^{\mathbf p\mathbf c\mathbf q},
  \qquad
  |\mathbf p|=|\mathbf q|=m,
\]

with $|\mathbf c|=n+1$.  Proposition 20 itself gives `eq:fusion_2`; the
residual expansion and its nilpotency bound are additionally load-bearing for
`eq:fusion_1`.

### Uniqueness

Theorem 22 (`thm:uniqueness`) of arXiv:1706.07329v2 compares two reductions
$(V,W)$ and $(\widetilde V,\widetilde W)$ of the same $B$ to the same
normal $A$.  If both nilpotency lengths are at most $N_0$, there is a
scalar $\lambda$ such that, for every word of the printed length
$n>2N_0$,

\[
  VB^{\mathbf a}=\lambda\widetilde V B^{\mathbf a},\qquad
  B^{\mathbf a}W=\lambda^{-1}B^{\mathbf a}\widetilde W
\]

(`cornerproblem.tex:3156--3162`).  The proof later writes $n\geq2N_0$
(`cornerproblem.tex:4029--4033`); an implementation citing Theorem 22 must use
the printed strict inequality unless that off-by-one strengthening is proved
separately.

This is **boundary-dressed uniqueness**.  Neither Theorem 22 nor the
Garre-Rubio--Schuch specialization says
$V=\lambda\widetilde V$ and
$W=\lambda^{-1}\widetilde W$ as bare rectangular matrices.  Consequently,
`main.tex:1500--1504` is justified as a reciprocal rescaling action which
preserves the fusion equations, but the cited theorem alone does not classify
all bare fusion tensors by that action.  Any such cancellation theorem would
be an additional result.

## The nilpotency-length-one specialization

Theorem 1 of arXiv:2405.00439v2 is explicitly described as an informal
compilation of the preceding results.  It assumes $A$ injective, places no
condition on $B$, and, under equality of the generated MPS, supplies
$(V,\widehat V)$ such that

\[
  VB^i\widehat V=A^i,\qquad
  B^i\widehat V A^jVB^k=B^iB^jB^k,\qquad
  V\widehat V=1.
\]

For two such pairs it concludes only

\[
  VB^i=\lambda\widetilde V B^i,
  \qquad
  B^i\widehat V=\lambda^{-1}B^i\widetilde{\widehat V},
\]

and hence $VB^i\widetilde{\widehat V}=\lambda A^i$
(`MPU-DW.tex:359--364`).  Here

\[
  \widehat V=W=F^>,\qquad V=F^<.
\]

Theorem 1 writes $|\psi_A\rangle=|\psi_B\rangle$ without an explicit
quantifier over chain lengths and calls its own statement informal.  In the
MPU application, the all-positive-length family equality comes instead from
the representation law.  Proposition 20 remains the rigorous existence
anchor; Theorem 1 records the length-one local form used by the later dagger
calculation.

The footnote at `MPU-DW.tex:358` says that this statement assumes the
off-diagonal nilpotency length is one and that blocking can always achieve
this.  The same assertion is repeated at
`Papers/2502.20257/main.tex:1498`.  It is not part of Proposition 20,
Definition 8, or Theorem 22, and neither audited source states a theorem that
chooses one blocking length simultaneously for every pair in a finite group.
After #7321 supplies representation-level common blocking and the properties
stable under further blocking, #7322 owns this reduction-dependent finite
common block for the selected family of reductions.

The dependence on length one is therefore:

| Conclusion | Nilpotency length one required? |
|---|---|
| Existence of $V,W$, $VW=1$, and `eq:fusion_2` | no |
| `eq:fusion_1` with exterior length $m\geq N_0$ | no; it uses the actual $N_0$ |
| The one-letter residual equality $B^i=WA^iV$ | yes |
| The local three-letter identity in Garre-Rubio--Schuch Theorem 1 | yes |
| Its one-letter boundary-dressed uniqueness statement | yes |
| The dagger-reflected comparison used in `prop:zetas` | yes in the cited proof, which invokes that specialization |

## Dagger and leg order

The dagger of an MPO must generate the adjoint operator without reflecting the
spatial word.  The existing declaration with this behavior is
`MPOTensor.physicalAdjointTensor`:

\[
  (\mathcal U^\dagger)^{ij}_{\beta\alpha}
    =\overline{\mathcal U^{ji}_{\beta\alpha}}.
\]

`MPOTensor.mpo_physicalAdjointTensor` proves that its periodic operator is the
conjugate transpose of the original one.  By contrast,
`MPOTensor.adjointTensor` conjugate-transposes each virtual matrix and therefore
reverses the physical/spatial word order in word evaluation; it gives the
global adjoint only with a spatial reflection and is not the convention of
`main.tex:1552--1662`.

The same passage distinguishes two operations on the square inverse gauge:
$T_g^\dagger$ is conjugate transpose, whereas
$T_{g^{-1}}^*$ in `eq:intro_sigma` is entrywise complex conjugation.  In
Lean these must be represented separately by `Matrix.conjTranspose` and
entrywise mapping by `starRingEnd ℂ`; the matrix `Star` operation must not be
used for the latter, since it includes transposition.

At `main.tex:1647--1662`, the daggered fusion tensors are specifically

\[
  (F^<_{h^{-1},g^{-1}})^\dagger,
  \qquad
  (F^>_{h^{-1},g^{-1}})^\dagger.
\]

Here dagger means complex conjugation together with exchanging the legs on
each side, equivalently reflection about a horizontal axis.  On rectangular
matrices this includes conjugate transpose.  The order reversal
$(g,h)\mapsto(h^{-1},g^{-1})$ is forced by
$(U_gU_h)^\dagger=U_{h^{-1}}U_{g^{-1}}$.  Since `MPOTensor.mulTensor`
encodes its product bond as `Fin (D_g * D_h)` through `finProdFinEquiv`, the
formal comparison must also reindex the pair by `Equiv.prodComm`; it is not a
definitional equality.

TNLean already transports normalized canonical-form-II data through this
physical adjoint.  In particular,
`MPOTensor.normalizedFlattening_physicalAdjointTensor` identifies the
normalized flattening with a physically reindexed entrywise conjugate, while
`MPSTensor.CPSVCanonicalFormIIData.physicalAdjointNormalizedFlattening` and
`MPSTensor.IsCPSVCanonicalFormII.physicalAdjointNormalizedFlattening` transport
the data and predicate.  These declarations in
`TNLean/MPS/MPU/PhysicalAdjointCanonicalForm.lean` are the canonical-form input
for #7323 and must be reused.

No public TNLean declaration currently packages a rectangular fusion tensor
with its dagger operation or proves that `physicalAdjointTensor` reverses
`mulTensor` up to the product-bond swap.
`TNLean/MPS/MPU/CompositionRanks.lean` contains only private analogues
`reindexBond`, `bondSwapEquiv`, and `mulTensor_physicalFlip_swap` for a
physical flip.  They are evidence for the required coordinate convention,
not a reusable dagger theorem.

The two comparisons drawn in `prop:zetas` contain an adjacent MPU letter.
They should therefore be stated as the one-letter boundary-dressed comparisons
provided by Garre-Rubio--Schuch Theorem 1, after transporting by the
$T_g$-gauges and the product-bond swap.  They must not first be strengthened
to equality of bare fusion matrices.  This is the exact tensor input from
which #7324 may derive the displayed $\zeta$-relations.

## TNLean and QICLean declaration map

| Paper object or fact | Existing declaration | Match and boundary |
|---|---|---|
| Four-legged MPU tensor | `MPOTensor` and `MPOTensor.toMPSTensor`, `TNLean/MPS/MPDO/Defs.lean` | Exact raw doubled-physical-index MPS view. |
| Product tensor $B_{g,h}$ | `MPOTensor.mulTensor`, `MPOTensor.mpo_mulTensor`, `TNLean/MPS/MPDO/OperatorProduct.lean` | Exact contraction over the middle physical index and exact operator multiplication. |
| Vectorized coefficient | `MPSTensor.mpv_toMPSTensor_pairConfig`, `TNLean/MPS/MPDO/VerticalCF.lean` | Identifies MPO matrix entries with raw flattened MPS coefficients. |
| Equality for different bond dimensions | `MPSTensor.SameMPV₂Pos`, `TNLean/MPS/Defs.lean` | Correct positive-length interface.  `SameMPV₂` includes the empty chain and is too strong here. |
| Injective $A$ | `Kraus.IsInjective`, `QICLean/Kraus/Injectivity.lean`; `MPOTensor.IsInjective`, `TNLean/MPS/MPDO/SimpleLocalInverseMaps.lean` | Exact spanning/left-inverse notion after raw flattening. |
| Source normal tensor | `MPSTensor.IsPrimitivePaper`, `TNLean/Wielandt/Primitivity/Definitions.lean`; `MPSTensor.HasEventuallyFullKrausRank`, `TNLean/Wielandt/Primitivity/Definitions.lean`; `Kraus.HasEventuallyFullWordSpan` and `Kraus.IsNormal`, `QICLean/Kraus/Injectivity.lean` | `IsPrimitivePaper` is the existing unnormalized vector-spreading formulation of transfer primitivity, so this predicate must be reused rather than duplicated.  `HasEventuallyFullKrausRank` is equivalent to `Kraus.IsNormal` by `hasEventuallyFullKrausRank_iff_isNormal`.  The available reverse bridge `primitivePaper_iff_hasEventuallyFullKrausRank` assumes left-canonical normalization, and `Kraus.hasEventuallyFullWordSpan_iff_exists_pos_of_isTP` similarly assumes trace preservation.  Thus the exact source predicate exists, while normalization transport to the word-span APIs remains an explicit boundary.  The present target uses the injective specialization. |
| MPU property | `MPOTensor.IsMPU`, `TNLean/MPS/MPU/Basic.lean` | Existing predicate is unitarity for every $N>1$.  The 2025 paper says every chain length; #7321 must retain this convention difference. |
| Raw versus normalized flattening | `MPOTensor.toMPSTensor`, `TNLean/MPS/MPDO/Defs.lean`; `MPOTensor.normalizedFlattening`, `TNLean/MPS/MPU/TransferMatrix.lean`; `normalizedFlattening_mulTensor_apply`, `TNLean/MPS/MPU/CompositionFlattening.lean` | The cited reduction vectorizes the raw MPO tensor.  `normalizedFlattening` is the separate arXiv:1703.09188 transfer normalization; its composition formula carries an explicit $\sqrt d$. |
| Paper's simple MPU tensor | `MPOTensor.IsMPUSimple`, `TNLean/MPS/MPU/Simple.lean` | Matches arXiv:1703.09188 Definition III.2; unrelated to MPDO simplicity. |
| Canonical form used for a unitary inverse gauge | `MPSTensor.CPSVCanonicalFormIIData`, `TNLean/MPS/CanonicalForm/Definitions.lean`; `MPSTensor.IsLeftCanonical`, `TNLean/MPS/Core/CanonicalNormalization.lean` | The unitary-gauge API uses left-canonical irreducible tensors.  `MPSTensor.IsMPUCanonicalForm` in `TNLean/MPS/MPU/MPUCanonicalForm.lean` also permits multiblock periodic data and is too broad by itself for the injective one-block hypothesis at `main.tex:1552`. |
| Physical blocking | `MPOTensor.blockTensor`, `toMPSTensor_blockTensor`, `blockTensor_mulTensor`, and `mpo_blockTensor_eq_reindex`, `TNLean/MPS/MPDO/PhysicalBlocking.lean` | Reusable blocking and product compatibility.  No theorem transports a chosen reduction's residual algebra or produces one common length with nilpotency length one. |
| Normal/canonical representative | `MPOTensor.IsMPU.exists_reduced_cfii_representative`, `TNLean/MPS/MPU/ReducedCanonicalRepresentative.lean` | Gives a smaller-bond CFII representative with the same positive-length MPO.  It does not give rectangular reduction matrices back to the original tensor. |
| Same-bond injective fundamental theorem | `MPSTensor.fundamentalTheorem_singleBlock`, `TNLean/MPS/FundamentalTheorem/Basic.lean` | Gives a square invertible gauge only when the bond dimensions already agree.  It is not Proposition 20. |
| Unitary canonical gauge | `MPSTensor.exists_unitaryConj_gaugePhase_of_leftCanonical_irreducible`, `TNLean/MPS/FundamentalTheorem/UnitaryGauge.lean` | Reusable for #7323 after the required same-bond, left-canonical, irreducible data are established; it does not construct a rectangular fusion reduction. |
| Physical dagger | `MPOTensor.physicalAdjointTensor` and `mpo_physicalAdjointTensor`, `TNLean/MPS/MPDO/PhysicalAdjoint.lean` | Correct global-adjoint convention without spatial reflection. |
| Canonical form under physical dagger | `MPOTensor.normalizedFlattening_physicalAdjointTensor`, `MPSTensor.CPSVCanonicalFormIIData.physicalAdjointNormalizedFlattening`, and `MPSTensor.IsCPSVCanonicalFormII.physicalAdjointNormalizedFlattening`, `TNLean/MPS/MPU/PhysicalAdjointCanonicalForm.lean` | Exact normalized-flattening identity and reusable transport of literal canonical-form-II data and its predicate.  This is the existing input for #7323; it does not itself reverse a product tensor or define a dagger on rectangular fusion legs. |
| Existing MPU residual algebra | `MPOTensor.residualGeneratorSet`, `MPOTensor.residualAlgebra`, `MPOTensor.IsMPU.residualAlgebra_list_prod_eq_zero`, and `MPOTensor.IsMPU.prod_residualSlice_doubleLayerTensor_eq_zero`, `TNLean/MPS/MPU/ResidualAlgebra.lean` | These are the arXiv:1703.09188 physical-adjoint double-layer residual slices used in `blockingsimple`.  They are not the selected-reduction residual letters $N^a=B^a-WA^aV$ of arXiv:1706.07329 Proposition 21 and cannot serve as their definition or nilpotency theorem. |
| Nil matrix algebra bound | `NonUnitalSubalgebra.matrix_list_prod_eq_zero_of_forall_isNilpotent`, `QICLean/Algebra/NilMatrixSubalgebra.lean` | Reusable after constructing the residual nonunital algebra.  It does not supply Proposition 20, Proposition 21, Definition 8, or Theorem 22. |

The following objects are genuinely missing:

1. a rectangular `Reduction` datum with $VW=1$ and all-word reduction;
2. its residual family and `nilpotencyLength` (this name must not reuse the
   notation $\ell[U]$);
3. the exterior residual-expansion identity and boundary-dressed uniqueness;
4. transport of reductions under physical blocking, including the theorem
   reducing a finite family of nilpotency lengths to one;
5. a public product-bond reindexing API and physical-adjoint/product reversal;
6. the rectangular fusion-leg dagger and its exact leg swap.

No declaration named `Reduction` or `nilpotencyLength`, and no theorem with the
content of Proposition 20 or Theorem 22, was found in TNLean or its current
QICLean dependency.  The existing `MPOTensor.residualAlgebra` has a different
generator family and is intentionally excluded from this claim; only its
generic QICLean nil-matrix engine is reusable for a newly constructed
selected-reduction residual algebra.

## Boundary with the 2017 MPU development

The work under #5704 is reusable, but it represents a different factorization.
`MPOTensor.SourceFactors` in `TNLean/MPS/MPU/SourceFactors.lean` stores the six
two-site source-cut factors $X_1,Y_1,Z_1,X_2,Y_2,Z_2$.
`MPOTensor.SourceFactors.sourceU`, `sourceV`, and their global counterparts in
`TNLean/MPS/MPU/SourceUV.lean` construct the three-legged gates $u,v$ of
arXiv:1703.09188.  These factor one simple MPU tensor across its two-site
source cuts.  They are not the rectangular reduction $V,W$ from the product
tensor $\mathcal U_g\mathcal U_h$ to $\mathcal U_{gh}$, and their one-sided
inverse identities do not imply Proposition 20 or Theorem 22.

Issue #5856 concerns the four-way equivalence between MPU simplicity, the
source-rank equality $r[U]\ell[U]=d^2$, and unitarity of those source gates.
It is load-bearing wherever #7321 or #7325 uses the 2017 three-legged standard
form.  It is not a prerequisite for the cited MPS reduction theorem itself and
must not be used as a substitute proof of fusion existence or uniqueness.

## Implementation consequences

- #7321 owns only the representation-level common blocking and the
  elementwise simple, injective, and one-block-canonical properties stable
  under further common blocking.  It does not own a `Reduction`, a residual
  family, a nilpotency length, or the fusion existential.
- #7322 should first formalize the reusable rectangular MPS reduction API from
  the equality specialization ($\lambda=1$) of Proposition 20, Proposition 21,
  Definition 8, `lem:B_expand`, and Theorem 22, then choose one reduction for
  every $(g,h)$ and prove its block and product-reindex transport.  It owns the
  additional finite-family common block which makes those selected residual
  letters vanish at length one, and only then constructs the fusion/anomaly
  data.  Uniqueness must remain in the boundary-dressed form printed by the
  source.
- #7323 may reuse the physical-adjoint canonical-form transport, the same-bond
  fundamental theorem, and the canonical unitary-gauge refinement for $T_g$;
  it must use `physicalAdjointTensor`, not `adjointTensor`.
- #7324 must implement the product-bond order reversal and compare the
  dagger-reflected reductions in the one-letter, boundary-dressed form of
  Garre-Rubio--Schuch Theorem 1 before deriving $\zeta$.
- #7325 may depend on #5856 when it invokes source $u,v$ and their exact leg
  orientations; that dependency does not flow backward into the reduction
  theorem.

No Blueprint status is changed by this audit: all named tensor results in its
scope remain implementation work owned by the children of #7281.
