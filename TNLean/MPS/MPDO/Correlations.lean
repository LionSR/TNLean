/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SectorTrace

/-!
# Positive-gap length and distance independence for matrix product density operators

This file records the mixed-state counterpart of the two-observable transfer
formula in arXiv:1606.00608, equation `Corr`, lines 490--496, and proves the
positive-gap correlation independence underlying the CID discussion at lines
433--500 and the mixed-state assertion following Definition `DefinitionZCL`,
lines 735--742.

The observable insertion is the existing matrix
`verticalLoopWith M O = ∑ i, j, O j i • M i j`. The two complementary gap
lengths are used directly, avoiding truncated subtraction in the source
exponents.

## Main definitions and results

* `MPOTensor.periodicTwoPointCorrelation`: the unnormalized periodic
  two-observable contraction.
* `MPOTensor.periodicTwoPointCorrelation_positiveWrapGaps_independent`:
  literal physical-trace idempotence gives ring-length independence when the
  fixed middle gap is arbitrary and the compared wrapping gaps are positive.
* `MPOTensor.periodicTwoPointCorrelation_positiveGaps_independent`: the
  corresponding fixed-ring distance-independence result when all compared
  complementary gaps are positive.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  equation `Corr`, lines 490--496, and Definition `DefinitionZCL` with the
  following prose, lines 735--742
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- The unnormalized periodic two-point correlation function of an MPO tensor,
with one-site observables $O_1,O_2$ and complementary gap lengths
$g_{\mathrm{mid}},g_{\mathrm{wrap}}$:

\[
  C_M(O_1,O_2;g_{\mathrm{mid}},g_{\mathrm{wrap}})
  = \operatorname{tr}\!\left(
      \mathbb E_{O_1}\mathcal T_M^{g_{\mathrm{mid}}}
      \mathbb E_{O_2}\mathcal T_M^{g_{\mathrm{wrap}}}\right).
\]

Here
$\mathbb E_O=\sum_{i,j}O_{ji}M^{ij}$ is `verticalLoopWith M O` and
$\mathcal T_M=\sum_iM^{ii}$ is `physTraceTransfer M`. The order and index
orientation are those of arXiv:1606.00608, equation `Corr`, lines 490--496.
In the source notation,
$g_{\mathrm{mid}}=n_2-n_1-1$,
$g_{\mathrm{wrap}}=N+n_1-n_2-1$, and the ring has length
$g_{\mathrm{mid}}+g_{\mathrm{wrap}}+2$.

The contraction is not divided by the trace of the generated operator. This
matches the source at lines 735--742; normalization is introduced only later,
at lines 792--793, for entropic quantities. -/
noncomputable def periodicTwoPointCorrelation (M : MPOTensor d D)
    (O₁ O₂ : Matrix (Fin d) (Fin d) ℂ) (middleGap wrapGap : ℕ) : ℂ :=
  Matrix.trace
    (verticalLoopWith M O₁ * physTraceTransfer M ^ middleGap *
      verticalLoopWith M O₂ * physTraceTransfer M ^ wrapGap)

/-- Literal zero correlation length makes the periodic two-point correlation
independent of the ring length at fixed observable separation, provided the
compared wrapping gaps are positive.

If $g_{\mathrm{wrap}},g'_{\mathrm{wrap}}>0$, then Definition 4.2 of
arXiv:1606.00608 gives
$\mathcal T_M^{g_{\mathrm{wrap}}}=\mathcal T_M^{g'_{\mathrm{wrap}}}$.
The middle gap is unchanged and may be zero. In the source notation from
equation `Corr`, $g_{\mathrm{mid}}=n_2-n_1-1$ and
$g_{\mathrm{wrap}}=N+n_1-n_2-1$, so this is the length-independence assertion
for MPDO correlations at lines 740--742, including adjacent marked sites.

**Scope restriction (positive varied wrapping gaps):** Idempotence identifies
every positive power of $\mathcal T_M$, but does not identify
$\mathcal T_M^0=1$ with $\mathcal T_M$. Hence the theorem does not compare a
zero wrapping gap with a positive one. This boundary is documented in
`docs/paper-gaps/cpsv16_mpdo_zcl_correlation_length_boundary.tex`. -/
theorem periodicTwoPointCorrelation_positiveWrapGaps_independent
    (M : MPOTensor d D) (hZCL : IsPhysicalTraceIdempotent M)
    (O₁ O₂ : Matrix (Fin d) (Fin d) ℂ)
    (middleGap wrapGap wrapGap' : ℕ)
    (hwrapGap : 0 < wrapGap) (hwrapGap' : 0 < wrapGap') :
    periodicTwoPointCorrelation M O₁ O₂ middleGap wrapGap =
      periodicTwoPointCorrelation M O₁ O₂ middleGap wrapGap' := by
  unfold periodicTwoPointCorrelation
  have hwrapPow : physTraceTransfer M ^ wrapGap = physTraceTransfer M :=
    hZCL.pow_eq hwrapGap.ne'
  have hwrapPow' : physTraceTransfer M ^ wrapGap' = physTraceTransfer M :=
    hZCL.pow_eq hwrapGap'.ne'
  rw [hwrapPow, hwrapPow']

/-- Literal zero correlation length makes the periodic two-point correlation
independent of both complementary gap lengths when all compared gaps are
positive.

If $g_{\mathrm{mid}},g_{\mathrm{wrap}},g'_{\mathrm{mid}},
g'_{\mathrm{wrap}}>0$, then Definition 4.2 of arXiv:1606.00608 gives
$\mathcal T_M^r=\mathcal T_M$ for each of the four exponents, so the two
contractions agree. If the two gap sums are equal, this is correlation
independence under changing the observable distance on a fixed ring while the
observables are nonadjacent on both complementary arcs, as in the CID
discussion at lines 433--500.

**Scope restriction (positive gaps varied in the distance comparison):**
Positivity of all four gaps is the exact boundary of this distance-comparison
argument: idempotence identifies every positive power of $\mathcal T_M$, but
does not identify $\mathcal T_M^0=1$ with $\mathcal T_M$. The unrestricted
source/CID reading involving a zero complementary gap is not claimed. This
boundary is documented in
`docs/paper-gaps/cpsv16_mpdo_zcl_correlation_length_boundary.tex`. -/
theorem periodicTwoPointCorrelation_positiveGaps_independent
    (M : MPOTensor d D) (hZCL : IsPhysicalTraceIdempotent M)
    (O₁ O₂ : Matrix (Fin d) (Fin d) ℂ)
    (middleGap wrapGap middleGap' wrapGap' : ℕ)
    (hmiddleGap : 0 < middleGap) (hwrapGap : 0 < wrapGap)
    (hmiddleGap' : 0 < middleGap') (hwrapGap' : 0 < wrapGap') :
    periodicTwoPointCorrelation M O₁ O₂ middleGap wrapGap =
      periodicTwoPointCorrelation M O₁ O₂ middleGap' wrapGap' := by
  unfold periodicTwoPointCorrelation
  have hmiddlePow : physTraceTransfer M ^ middleGap = physTraceTransfer M :=
    hZCL.pow_eq hmiddleGap.ne'
  have hwrapPow : physTraceTransfer M ^ wrapGap = physTraceTransfer M :=
    hZCL.pow_eq hwrapGap.ne'
  have hmiddlePow' : physTraceTransfer M ^ middleGap' = physTraceTransfer M :=
    hZCL.pow_eq hmiddleGap'.ne'
  have hwrapPow' : physTraceTransfer M ^ wrapGap' = physTraceTransfer M :=
    hZCL.pow_eq hwrapGap'.ne'
  rw [hmiddlePow, hwrapPow, hmiddlePow', hwrapPow']

end MPOTensor
