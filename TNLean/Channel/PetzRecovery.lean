/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OperatorSchmidt
import TNLean.Analysis.CfcConjugation
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.KrausCPTP
import TNLean.Channel.MarginalSupportAbsorption
import TNLean.Channel.TensorMap

/-!
# A trace-preserving Petz transpose channel for a partial trace

This file constructs the Petz transpose map associated with a positive
semidefinite reference matrix and the partial trace over a right tensor factor.
It first proves the source formula on the support of the reference marginal,
then completes it on the orthogonal complement by a measure-and-prepare term.
For a normalized reference, the completed map is trace-preserving completely
positive, agrees with the source formula on supported inputs, and recovers the
reference matrix.

## Main declarations

* `Matrix.partialTraceRightPetzMap`: the raw Petz transpose map for the right
  partial trace.
* `Matrix.partialTraceRightPetzMap_isKrausCP`: complete positivity.
* `Matrix.partialTraceRightPetzMap_trace`: the support trace identity.
* `Matrix.partialTraceRightPetzComplementMap`: the complementary
  measure-and-prepare term.
* `Matrix.partialTraceRightPetzComplementMap_isKrausCP`: complete positivity
  of the complementary term.
* `Matrix.partialTraceRightPetzComplementMap_trace`: the complementary trace
  identity.
* `Matrix.partialTraceRightPetzChannel`: the support formula completed by the
  complementary measure-and-prepare term.
* `Matrix.partialTraceRightPetzChannel_isKrausCPTP`: the completed map is a
  channel for a normalized reference.
* `Matrix.partialTraceRightPetzChannel_apply_of_supported`: agreement with the
  support formula on supported inputs.
* `Matrix.partialTraceRightPetzMap_partialTraceRight`: recovery of the
  reference matrix.
* `Matrix.partialTraceRightPetzChannel_partialTraceRight`: recovery by the
  completed channel.
* `Matrix.productTensorReference`: a general product reference with canonical
  reassociation.
* `Matrix.partialTraceRightPetzMap_productTensor_kronecker`: elementary-tensor
  raw factorization with support compression on the first factor.
* `Matrix.partialTraceRightPetzMap_productTensor`: the corresponding global
  linear-map factorization.
* `Matrix.partialTraceRightPetzMap_productTensor_apply_of_left_supported`:
  identity-tensored recovery on inputs supported in the first factor.
* `Matrix.partialTraceRightPetzMap_productTensor_of_posDef_left`: global
  identity-tensored recovery when the first factor is positive definite.
* `Matrix.maximallyMixedTensorReference`: the maximally mixed tensor-product
  reference from HJPW equation (10), with reassociated product indices.
* `Matrix.partialTraceLeft_maximallyMixedTensorReference`: the retained
  marginal of the maximally mixed tensor reference.
* `Matrix.trace_maximallyMixedTensorReference`: the reference trace identity.
* `Matrix.supportProj_partialTraceRight_maximallyMixedTensorReference`: the
  factorization of the marginal support projector.
* `Matrix.partialTraceRightPetzMap_maximallyMixedTensor_kronecker`:
  factorization of the raw Petz map on elementary tensors.
* `Matrix.partialTraceRightPetzMap_maximallyMixedTensor`: the raw Petz map for
  the maximally mixed tensor reference factors as the identity on the first
  tensor factor and the Petz map on the remaining factors.
* `Matrix.partialTraceRightPetzComplementMap_maximallyMixedTensor`: the
  complementary support-completion term has the same factorization.
* `Matrix.partialTraceRightPetzChannel_maximallyMixedTensor`: the completed
  Petz channel factors as the identity tensored with the local channel.
* `Matrix.partialTraceRightPetzChannel_maximallyMixedTensor_isKrausCPTP`: the
  completed channel is CPTP when the local reference has trace one.

## References

* Hayden, Jozsa, Petz, and Winter, arXiv:quant-ph/0304007v2,
  Theorem 3, equation (8), and the specialization following their
  relative-entropy monotonicity equation.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section PartialTrace

variable {L R : Type*} [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R]

/-- The raw Petz transpose map for the right partial trace with reference
`σ`.  It is the support formula
`X ↦ sqrt(σ) ((tr_R σ)⁻¹/² X (tr_R σ)⁻¹/² ⊗ 1_R) sqrt(σ)` from
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3, equation (8).

The source states this formula on the support of `tr_R σ`; this definition does
not extend it to a trace-preserving map on the complementary subspace. -/
noncomputable def partialTraceRightPetzMap
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    Matrix L L ℂ →ₗ[ℂ] Matrix (L × R) (L × R) ℂ :=
  singleKrausMap (hσ.isHermitian.cfc Real.sqrt) ∘ₗ
    preparationMap (1 : Matrix R R ℂ) ∘ₗ
      singleKrausMap (PosSemidef.supportInvSqrt
        (PosSemidef.partialTraceRight hσ))

/-- The raw partial-trace Petz map has the displayed support formula from
arXiv:quant-ph/0304007v2, equation (8). -/
theorem partialTraceRightPetzMap_apply
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef)
    (X : Matrix L L ℂ) :
    partialTraceRightPetzMap σ hσ X =
      hσ.isHermitian.cfc Real.sqrt *
        leftKroneckerEmbed (n := R)
          ((PosSemidef.partialTraceRight hσ).supportInvSqrt * X *
            (PosSemidef.partialTraceRight hσ).supportInvSqrt) *
        hσ.isHermitian.cfc Real.sqrt := by
  simp [partialTraceRightPetzMap, preparationMap,
    leftKroneckerEmbed_apply,
    hσ.cfc_sqrt_isHermitian.eq,
    (PosSemidef.partialTraceRight hσ).supportInvSqrt_isHermitian.eq,
    Matrix.mul_assoc]

/-- The raw partial-trace Petz map is completely positive in rectangular Kraus
form.  This is the complete-positivity part of the support formula in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3.  No global trace-preservation claim is made. -/
theorem partialTraceRightPetzMap_isKrausCP
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    IsKrausCP (partialTraceRightPetzMap σ hσ) := by
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact singleKrausMap_isKrausCP _
    · exact preparationMap_isKrausCP _ Matrix.PosSemidef.one
  · exact singleKrausMap_isKrausCP _

/-- The raw partial-trace Petz map preserves the trace on the support of the
reference marginal:
\[
  \operatorname{tr}(\mathcal R_\sigma(X))
    =\operatorname{tr}(P_{\operatorname{tr}_R\sigma}X).
\]

This is the support trace identity for the transpose channel in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3 and equation (8).  It does not assert trace preservation on the
orthogonal complement of the marginal support. -/
theorem partialTraceRightPetzMap_trace
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef)
    (X : Matrix L L ℂ) :
    Matrix.trace (partialTraceRightPetzMap σ hσ X) =
      Matrix.trace
        ((PosSemidef.partialTraceRight hσ).isHermitian.supportProj * X) := by
  let hτ := PosSemidef.partialTraceRight hσ
  let I := hτ.supportInvSqrt
  let S := hσ.isHermitian.cfc Real.sqrt
  have hS_sq : S * S = σ := hσ.cfc_sqrt_mul_self
  have hInv : I * partialTraceRight σ * I = hτ.isHermitian.supportProj :=
    hτ.supportInvSqrt_mul_self_mul_supportInvSqrt
  rw [partialTraceRightPetzMap_apply]
  change Matrix.trace (S * leftKroneckerEmbed (n := R) (I * X * I) * S) =
    Matrix.trace (hτ.isHermitian.supportProj * X)
  calc
    Matrix.trace (S * leftKroneckerEmbed (n := R) (I * X * I) * S) =
        Matrix.trace (leftKroneckerEmbed (n := R) (I * X * I) * (S * S)) := by
      simpa only [Matrix.mul_assoc] using
        (Matrix.trace_mul_cycle (leftKroneckerEmbed (n := R) (I * X * I)) S S).symm
    _ = Matrix.trace
        (leftKroneckerEmbed (n := R) (I * X * I) * σ) := by rw [hS_sq]
    _ = Matrix.trace ((I * X * I) * partialTraceRight σ) := by
      rw [trace_leftKroneckerEmbed_mul]
    _ = Matrix.trace (hτ.isHermitian.supportProj * X) := by
      calc
        Matrix.trace ((I * X * I) * partialTraceRight σ) =
            Matrix.trace ((I * partialTraceRight σ) * I * X) := by
          simpa only [Matrix.mul_assoc] using
            Matrix.trace_mul_cycle I X (I * partialTraceRight σ)
        _ = Matrix.trace (hτ.isHermitian.supportProj * X) := by rw [← hInv]

/-- The complementary measure-and-prepare term for the partial-trace Petz
map.  It measures the input on the orthogonal complement of the reference
marginal support and prepares the other marginal of the reference matrix.

This file chooses this measure-and-prepare term to complete the support
transpose formula of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3 and equation (8).  The cited equation gives
the support formula, not this particular complementary extension. -/
noncomputable def partialTraceRightPetzComplementMap
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    Matrix L L ℂ →ₗ[ℂ] Matrix (L × R) (L × R) ℂ :=
  preparationMap (partialTraceLeft σ) ∘ₗ
    singleKrausMap
      (1 - (PosSemidef.partialTraceRight hσ).isHermitian.supportProj)

/-- The complementary term has the measure-and-prepare formula used to
complete the support formula of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3 and equation (8).  The complementary term
itself is not part of the cited equation. -/
theorem partialTraceRightPetzComplementMap_apply
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef)
    (X : Matrix L L ℂ) :
    let Q := 1 - (PosSemidef.partialTraceRight hσ).isHermitian.supportProj
    partialTraceRightPetzComplementMap σ hσ X =
      (Q * X * Q) ⊗ₖ partialTraceLeft σ := by
  dsimp only
  simp [partialTraceRightPetzComplementMap, preparationMap,
    (PosSemidef.partialTraceRight hσ).isHermitian.one_sub_supportProj_isHermitian.eq]

/-- The local complementary measure-and-prepare term accompanying the support
formula of Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3,
is completely positive. -/
theorem partialTraceRightPetzComplementMap_isKrausCP
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    IsKrausCP (partialTraceRightPetzComplementMap σ hσ) := by
  apply isKrausCP_comp
  · exact singleKrausMap_isKrausCP _
  · exact preparationMap_isKrausCP _ hσ.partialTraceLeft

/-- The complementary term contributes the trace on the orthogonal complement
of the reference marginal support when the reference matrix has trace one.

This is the trace bookkeeping for the local complementary extension of the
support transpose formula in Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3. -/
theorem partialTraceRightPetzComplementMap_trace
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef)
    (hσtrace : Matrix.trace σ = 1) (X : Matrix L L ℂ) :
    let Q := 1 - (PosSemidef.partialTraceRight hσ).isHermitian.supportProj
    Matrix.trace (partialTraceRightPetzComplementMap σ hσ X) =
      Matrix.trace (Q * X) := by
  let Q := 1 - (PosSemidef.partialTraceRight hσ).isHermitian.supportProj
  have hQidem : Q * Q = Q :=
    (PosSemidef.partialTraceRight hσ).isHermitian.one_sub_supportProj_idem
  rw [partialTraceRightPetzComplementMap_apply, Matrix.trace_kronecker,
    trace_partialTraceLeft, hσtrace, mul_one]
  change Matrix.trace (Q * X * Q) = Matrix.trace (Q * X)
  calc
    Matrix.trace (Q * X * Q) = Matrix.trace ((Q * Q) * X) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle Q X Q
    _ = Matrix.trace (Q * X) := by rw [hQidem]

/-- A completion of the partial-trace Petz transpose map that is trace
preserving when the reference matrix has trace one.  It agrees with the
support formula on inputs supported on the reference marginal and sends the
complementary weight to a fixed prepared state.

This definition adds the local complementary extension to the transpose map
used in Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3 and equation (8).  The cited equation supplies only the support
formula. -/
noncomputable def partialTraceRightPetzChannel
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    Matrix L L ℂ →ₗ[ℂ] Matrix (L × R) (L × R) ℂ :=
  partialTraceRightPetzMap σ hσ + partialTraceRightPetzComplementMap σ hσ

/-- The completed partial-trace Petz map is trace-preserving and completely
positive when the reference matrix has trace one.

This is the trace-preserving property of the completed support transpose map
associated with Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3 and equation (8). -/
theorem partialTraceRightPetzChannel_isKrausCPTP
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef)
    (hσtrace : Matrix.trace σ = 1) :
    IsKrausCPTP (partialTraceRightPetzChannel σ hσ) := by
  apply isKrausCPTP_of_isKrausCP_trace_preserving
  · exact (partialTraceRightPetzMap_isKrausCP σ hσ).add
      (partialTraceRightPetzComplementMap_isKrausCP σ hσ)
  · intro X
    rw [partialTraceRightPetzChannel, LinearMap.add_apply, Matrix.trace_add,
      partialTraceRightPetzMap_trace,
      partialTraceRightPetzComplementMap_trace σ hσ hσtrace]
    let P := (PosSemidef.partialTraceRight hσ).isHermitian.supportProj
    change Matrix.trace (P * X) + Matrix.trace ((1 - P) * X) = Matrix.trace X
    calc
      Matrix.trace (P * X) + Matrix.trace ((1 - P) * X) =
          Matrix.trace (P * X + (1 - P) * X) := by rw [Matrix.trace_add]
      _ = Matrix.trace ((P + (1 - P)) * X) := by rw [Matrix.add_mul]
      _ = Matrix.trace X := by simp

/-- On an input supported on the reference marginal, the completed channel
agrees with the raw support Petz formula.

This proves that the completed map restricts to the support formula of
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3 and equation (8). -/
theorem partialTraceRightPetzChannel_apply_of_supported
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef)
    (X : Matrix L L ℂ)
    (hX :
      let P := (PosSemidef.partialTraceRight hσ).isHermitian.supportProj
      P * X * P = X) :
    partialTraceRightPetzChannel σ hσ X = partialTraceRightPetzMap σ hσ X := by
  let P := (PosSemidef.partialTraceRight hσ).isHermitian.supportProj
  let Q : Matrix L L ℂ := 1 - P
  change P * X * P = X at hX
  have hPidem : P * P = P :=
    (PosSemidef.partialTraceRight hσ).isHermitian.supportProj_idem
  have hPX : P * X = X := by
    calc
      P * X = P * (P * X * P) := by rw [hX]
      _ = (P * P) * X * P := by simp only [Matrix.mul_assoc]
      _ = P * X * P := by rw [hPidem]
      _ = X := hX
  have hXP : X * P = X := by
    calc
      X * P = (P * X * P) * P := by rw [hX]
      _ = P * X * (P * P) := by simp only [Matrix.mul_assoc]
      _ = P * X * P := by rw [hPidem]
      _ = X := hX
  have hQXQ : Q * X * Q = 0 := by
    rw [show Q = 1 - P from rfl]
    calc
      (1 - P) * X * (1 - P) = X - P * X - X * P + P * X * P := by
        noncomm_ring
      _ = 0 := by rw [hPX, hXP]; abel
  rw [partialTraceRightPetzChannel, LinearMap.add_apply,
    partialTraceRightPetzComplementMap_apply]
  change partialTraceRightPetzMap σ hσ X + (Q * X * Q) ⊗ₖ partialTraceLeft σ = _
  rw [hQXQ, zero_kronecker, add_zero]

/-- The raw partial-trace Petz map recovers its positive-semidefinite reference
matrix:
`R_σ (tr_R σ) = σ`.

This is the automatic reference-recovery identity following
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
equation (8).  It uses only the source's support formula and
does not assert trace preservation away from that support. -/
theorem partialTraceRightPetzMap_partialTraceRight
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    partialTraceRightPetzMap σ hσ (partialTraceRight σ) = σ := by
  rw [partialTraceRightPetzMap_apply]
  have hInv := PosSemidef.supportInvSqrt_mul_self_mul_supportInvSqrt
    (PosSemidef.partialTraceRight hσ)
  rw [hInv]
  set S := hσ.isHermitian.cfc Real.sqrt with hS
  set P := leftKroneckerEmbed (n := R)
    (PosSemidef.partialTraceRight hσ).isHermitian.supportProj with hP
  set Q : Matrix (L × R) (L × R) ℂ := 1 - P with hQ
  have hS_sq : S * S = σ := by
    rw [hS]
    exact hσ.cfc_sqrt_mul_self
  have hS_herm : S.IsHermitian := by
    rw [hS]
    exact hσ.cfc_sqrt_isHermitian
  have hPσ : P * σ = σ := by
    rw [hP]
    exact hσ.leftKroneckerEmbed_supportProj_mul_self
  have hPherm : P.IsHermitian := by
    rw [hP]
    change (leftKroneckerEmbed (n := R)
      (PosSemidef.partialTraceRight hσ).isHermitian.supportProj)ᴴ = _
    rw [← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose,
      (PosSemidef.partialTraceRight hσ).isHermitian.supportProj_isHermitian.eq]
  have hPidem : P * P = P := by
    rw [hP, ← map_mul,
      (PosSemidef.partialTraceRight hσ).isHermitian.supportProj_idem]
  have hQherm : Q.IsHermitian := by
    rw [hQ]
    exact Matrix.isHermitian_one.sub hPherm
  have hQidem : Q * Q = Q := by
    rw [hQ]
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPidem]; abel
  have hQσ : Q * σ = 0 := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul, hPσ, sub_self]
  have hQSQ_pos : (S * Q * S).PosSemidef := by
    have hQpos : Q.PosSemidef := by
      rw [hQherm.posSemidef_iff_eigenvalues_nonneg]
      intro i
      rcases hQherm.eigenvalues_idem_eq_zero_or_one hQidem i with hi | hi
      · simp [hi]
      · simp [hi]
    simpa [hS_herm.eq] using hQpos.mul_mul_conjTranspose_same (Sᴴ)
  have hQSQ_trace : (S * Q * S).trace = 0 := by
    calc
      (S * Q * S).trace = (S * (Q * S)).trace := by
        rw [Matrix.mul_assoc]
      _ = ((Q * S) * S).trace := Matrix.trace_mul_comm _ _
      _ = (Q * (S * S)).trace := by rw [Matrix.mul_assoc]
      _ = (Q * σ).trace := by rw [hS_sq]
      _ = 0 := by rw [hQσ, Matrix.trace_zero]
  have hQSQ : S * Q * S = 0 := hQSQ_pos.trace_eq_zero_iff.mp hQSQ_trace
  calc
    S * P * S = S * (1 - Q) * S := by rw [hQ]; congr 2; abel
    _ = S * S - S * Q * S := by noncomm_ring
    _ = σ := by rw [hQSQ, sub_zero, hS_sq]

/-- The completed partial-trace Petz channel recovers its reference matrix
from the reference marginal.

This lifts the reference-recovery identity for the support formula of
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
Theorem 3 and equation (8), to the completed map. -/
theorem partialTraceRightPetzChannel_partialTraceRight
    (σ : Matrix (L × R) (L × R) ℂ) (hσ : σ.PosSemidef) :
    partialTraceRightPetzChannel σ hσ (partialTraceRight σ) = σ := by
  rw [partialTraceRightPetzChannel_apply_of_supported]
  · exact partialTraceRightPetzMap_partialTraceRight σ hσ
  · let hτ := PosSemidef.partialTraceRight hσ
    calc
      hτ.isHermitian.supportProj * partialTraceRight σ *
          hτ.isHermitian.supportProj =
          partialTraceRight σ * hτ.isHermitian.supportProj := by
            rw [hτ.isHermitian.supportProj_mul_self]
      _ = partialTraceRight σ := hτ.isHermitian.mul_supportProj_self

end PartialTrace

section HJPWProductReferenceFactorization

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- The product reference $\rho_A\otimes\rho_{BC}$ from HJPW Theorem 3,
equation (10), reindexed from $A\times(B\times C)$ to $(A\times B)\times C$ so
that `partialTraceRight` traces out $C$.

This definition is the corrected general-first-factor reference requested in
issue #4890. -/
noncomputable def productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ) :
    Matrix ((A × B) × C) ((A × B) × C) ℂ :=
  (ρA ⊗ₖ ρBC).submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] in
/-- The product reference in HJPW Theorem 3, equation (10), is positive
semidefinite when both factors are positive semidefinite. This is part of the
product-reference stack requested in issue #4890. -/
theorem productTensorReference_posSemidef
    [Finite A] [Finite B] [Finite C]
    {ρA : Matrix A A ℂ} {ρBC : Matrix (B × C) (B × C) ℂ}
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    (productTensorReference ρA ρBC).PosSemidef := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  letI := Fintype.ofFinite C
  exact (hA.kronecker hBC).submatrix _

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq C] in
/-- The retained $AB$ marginal of the product reference from HJPW Theorem 3,
equation (10), is $\rho_A\otimes\rho_B$. This is the right-marginal identity
requested in issue #4890. -/
theorem partialTraceRight_productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ) :
    partialTraceRight (productTensorReference ρA ρBC) =
      ρA ⊗ₖ partialTraceRight ρBC := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [productTensorReference, partialTraceRight_apply,
    Matrix.kroneckerMap_apply, Finset.mul_sum]

/-- The square root of the product reference from HJPW Theorem 3, equation
(10), factors across its two positive-semidefinite factors after canonical
reassociation. This supports the corrected factorization in issue #4890. -/
theorem cfcSqrt_productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    (productTensorReference_posSemidef hA hBC).isHermitian.cfc Real.sqrt =
      (hA.isHermitian.cfc Real.sqrt ⊗ₖ hBC.isHermitian.cfc Real.sqrt).submatrix
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) := by
  rw [← (productTensorReference_posSemidef hA hBC).isHermitian.cfc_eq]
  change cfc Real.sqrt
      ((ρA ⊗ₖ ρBC).submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)) = _
  have hcfc := Matrix.cfc_submatrix_equiv (hA.kronecker hBC).isHermitian Real.sqrt
    (Equiv.prodAssoc A B C).symm
  rw [show cfc Real.sqrt
      ((ρA ⊗ₖ ρBC).submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)) =
      (cfc Real.sqrt (ρA ⊗ₖ ρBC)).submatrix
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) by
      simpa only [Equiv.symm_symm] using hcfc]
  congr 1
  have hsqrt := hA.sqrt_kronecker hBC
  rw [CFC.sqrt_eq_real_sqrt (ρA ⊗ₖ ρBC) (hA.kronecker hBC).nonneg,
    CFC.sqrt_eq_real_sqrt ρA hA.nonneg,
    CFC.sqrt_eq_real_sqrt ρBC hBC.nonneg,
    cfcₙ_eq_cfc, cfcₙ_eq_cfc, cfcₙ_eq_cfc,
    hA.isHermitian.cfc_eq, hBC.isHermitian.cfc_eq] at hsqrt
  exact hsqrt

omit [DecidableEq C] in
/-- The support inverse square root of the $AB$ marginal of the product
reference in HJPW Theorem 3, equation (10), factors across $A$ and $B$.
This is the singular-support identity needed for issue #4890. -/
theorem supportInvSqrt_partialTraceRight_productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    (PosSemidef.partialTraceRight
      (productTensorReference_posSemidef hA hBC)).supportInvSqrt =
      hA.supportInvSqrt ⊗ₖ (PosSemidef.partialTraceRight hBC).supportInvSqrt := by
  unfold PosSemidef.supportInvSqrt
  rw [← (PosSemidef.partialTraceRight
      (productTensorReference_posSemidef hA hBC)).isHermitian.cfc_eq,
    ← hA.isHermitian.cfc_eq,
    ← (PosSemidef.partialTraceRight hBC).isHermitian.cfc_eq,
    partialTraceRight_productTensorReference]
  have hfac := hA.supportInvSqrt_kronecker
    (PosSemidef.partialTraceRight hBC)
  unfold PosSemidef.supportInvSqrt at hfac
  rw [← (hA.kronecker
      (PosSemidef.partialTraceRight hBC)).isHermitian.cfc_eq,
    ← hA.isHermitian.cfc_eq,
    ← (PosSemidef.partialTraceRight hBC).isHermitian.cfc_eq] at hfac
  exact hfac

omit [DecidableEq C] in
/-- The support projector of the $AB$ marginal of the product reference in
HJPW Theorem 3, equation (10), is $P_A\otimes P_B$. This is the
right-marginal support identity requested in issue #4890. -/
theorem supportProj_partialTraceRight_productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    (PosSemidef.partialTraceRight
      (productTensorReference_posSemidef hA hBC)).isHermitian.supportProj =
      hA.isHermitian.supportProj ⊗ₖ
        (PosSemidef.partialTraceRight hBC).isHermitian.supportProj := by
  let hτ := PosSemidef.partialTraceRight
    (productTensorReference_posSemidef hA hBC)
  rw [← hτ.supportInvSqrt_mul_self_mul_supportInvSqrt,
    supportInvSqrt_partialTraceRight_productTensorReference ρA ρBC hA hBC,
    partialTraceRight_productTensorReference ρA ρBC,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hA.supportInvSqrt_mul_self_mul_supportInvSqrt,
    (PosSemidef.partialTraceRight hBC).supportInvSqrt_mul_self_mul_supportInvSqrt]

/-- The linear support-compression map $X\mapsto PXP$. For a support projector
$P=P_A$, this is the first tensor factor in the globally valid raw Petz
factorization from HJPW Theorem 3, equation (10), as corrected in issue #4890. -/
noncomputable def supportCompressionMap
    (P : Matrix A A ℂ) : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun X := P * X * P
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

/-- Evaluation of the projective support-compression map used in the corrected
HJPW equation (10) factorization from issue #4890. -/
@[simp]
theorem supportCompressionMap_apply (P X : Matrix A A ℂ) :
    supportCompressionMap P X = P * X * P := rfl

/-- **HJPW Theorem 3, equation (10), elementary-tensor form.** For an arbitrary
positive-semidefinite first factor, the globally defined raw support-Petz map
sends $A_0\otimes X$ to
$(P_AA_0P_A)\otimes\mathcal R^{\mathrm{raw}}_{\rho_{BC}}(X)$ after canonical
reassociation.

This is the corrected singular-first-factor statement of issue #4890. It does
not replace $P_AA_0P_A$ by $A_0$ unless the input is supported or $\rho_A$ is
positive definite, and it makes no claim about TNLean's generic completed
channel. -/
theorem partialTraceRightPetzMap_productTensor_kronecker
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef)
    (A₀ : Matrix A A ℂ) (X : Matrix B B ℂ) :
    equivReindexMap (Equiv.prodAssoc A B C)
        (partialTraceRightPetzMap
          (productTensorReference ρA ρBC)
          (productTensorReference_posSemidef hA hBC)
          (A₀ ⊗ₖ X)) =
      (hA.isHermitian.supportProj * A₀ * hA.isHermitian.supportProj) ⊗ₖ
        partialTraceRightPetzMap ρBC hBC X := by
  rw [partialTraceRightPetzMap_apply, partialTraceRightPetzMap_apply]
  rw [cfcSqrt_productTensorReference ρA ρBC hA hBC,
    supportInvSqrt_partialTraceRight_productTensorReference ρA ρBC hA hBC]
  change (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc A B C)) (_ * _ * _) = _
  rw [map_mul, map_mul]
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  rw [show (((hA.isHermitian.cfc Real.sqrt ⊗ₖ
        hBC.isHermitian.cfc Real.sqrt).submatrix
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)).submatrix
        (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm) =
      hA.isHermitian.cfc Real.sqrt ⊗ₖ hBC.isHermitian.cfc Real.sqrt by
    ext i j
    rfl]
  rw [show (leftKroneckerEmbed (n := C)
        ((hA.supportInvSqrt ⊗ₖ
            (PosSemidef.partialTraceRight hBC).supportInvSqrt) *
          (A₀ ⊗ₖ X) *
          (hA.supportInvSqrt ⊗ₖ
            (PosSemidef.partialTraceRight hBC).supportInvSqrt))).submatrix
        (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm =
      (hA.supportInvSqrt * A₀ * hA.supportInvSqrt) ⊗ₖ
        leftKroneckerEmbed (n := C)
          ((PosSemidef.partialTraceRight hBC).supportInvSqrt * X *
            (PosSemidef.partialTraceRight hBC).supportInvSqrt) by
    simp only [leftKroneckerEmbed_apply]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    ext ⟨a, bc⟩ ⟨a', bc'⟩
    simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      Equiv.prodAssoc_symm_apply]
    ring]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  have hfirst :
      hA.isHermitian.cfc Real.sqrt *
          (hA.supportInvSqrt * A₀ * hA.supportInvSqrt) *
          hA.isHermitian.cfc Real.sqrt =
        hA.isHermitian.supportProj * A₀ * hA.isHermitian.supportProj := by
    calc
      _ = (hA.isHermitian.cfc Real.sqrt * hA.supportInvSqrt) * A₀ *
          (hA.supportInvSqrt * hA.isHermitian.cfc Real.sqrt) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hA.cfc_sqrt_mul_supportInvSqrt,
          hA.supportInvSqrt_mul_cfc_sqrt]
        rfl
  rw [hfirst]

/-- **HJPW Theorem 3, equation (10), global raw-map factorization.** For a
possibly singular positive-semidefinite $\rho_A$, the globally defined raw map
is the local recovery map tensored with support compression on $A$:
\[
  \mathcal R^{\mathrm{raw}}_{\rho_A\otimes\rho_{BC}}
  = \mathcal C_{P_A}\otimes
    \mathcal R^{\mathrm{raw}}_{\rho_{BC}}.
\]

This is the corrected global statement of issue #4890. It deliberately does
not claim a global identity-tensored formula for singular $\rho_A$ or a
factorization of TNLean's generic completed channel. -/
theorem partialTraceRightPetzMap_productTensor
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc A B C) ∘ₗ
        partialTraceRightPetzMap
          (productTensorReference ρA ρBC)
          (productTensorReference_posSemidef hA hBC) =
      idTensorMapLM (δ := A) (partialTraceRightPetzMap ρBC hBC) ∘ₗ
        tensorMapIdLM (δ := B)
          (supportCompressionMap hA.isHermitian.supportProj) := by
  apply LinearMap.ext
  intro X
  obtain ⟨A₀, Y, hX⟩ :=
    hasOperatorSchmidtDecomposition_operatorSchmidtRank X
  rw [hX]
  simp only [LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorMapIdLM_apply, tensorMapId_kronecker,
    idTensorMapLM_apply, idTensorMap_kronecker,
    supportCompressionMap_apply]
  exact partialTraceRightPetzMap_productTensor_kronecker
    ρA ρBC hA hBC (A₀ i) (Y i)

/-- Applying support compression on the $A$ factor is the same as sandwiching
by $P_A\otimes\mathbf 1_B$. This is the supported-input condition used in the
HJPW equation (10) corollary requested in issue #4890. -/
theorem tensorMapId_supportCompressionMap
    {ρA : Matrix A A ℂ} (hA : ρA.PosSemidef)
    (X : Matrix (A × B) (A × B) ℂ) :
    tensorMapIdLM (δ := B) (supportCompressionMap hA.isHermitian.supportProj) X =
      (hA.isHermitian.supportProj ⊗ₖ (1 : Matrix B B ℂ)) * X *
        (hA.isHermitian.supportProj ⊗ₖ (1 : Matrix B B ℂ)) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [tensorMapIdLM_apply, tensorMapId_apply,
    supportCompressionMap_apply, Matrix.mul_apply,
    bipartiteSlice_apply, Matrix.kroneckerMap_apply, one_apply]
  simp_rw [Fintype.sum_prod_type]
  simp

/-- **Supported-input corollary of HJPW Theorem 3, equation (10).** If an input
on $A\otimes B$ is supported by $P_A$ on its left tensor factor, then the
support compression in the raw product-reference factorization disappears,
and the map agrees with
$\operatorname{id}_A\otimes\mathcal R^{\mathrm{raw}}_{\rho_{BC}}$.

This is the supported-input statement requested in issue #4890. It does not
assert this identity on unsupported inputs when $\rho_A$ is singular. -/
theorem partialTraceRightPetzMap_productTensor_apply_of_left_supported
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef)
    (X : Matrix (A × B) (A × B) ℂ)
    (hX : (hA.isHermitian.supportProj ⊗ₖ (1 : Matrix B B ℂ)) * X *
      (hA.isHermitian.supportProj ⊗ₖ (1 : Matrix B B ℂ)) = X) :
    equivReindexMap (Equiv.prodAssoc A B C)
        (partialTraceRightPetzMap
          (productTensorReference ρA ρBC)
          (productTensorReference_posSemidef hA hBC) X) =
      idTensorMapLM (δ := A) (partialTraceRightPetzMap ρBC hBC) X := by
  have hglobal := congrArg (fun T ↦ T X)
    (partialTraceRightPetzMap_productTensor ρA ρBC hA hBC)
  simp only [LinearMap.comp_apply] at hglobal
  rw [tensorMapId_supportCompressionMap (B := B) hA X, hX] at hglobal
  exact hglobal

/-- **Positive-definite-left corollary of HJPW Theorem 3, equation (10).** If
$\rho_A$ is positive definite, then $P_A=\mathbf 1_A$ and the global raw
product-reference Petz map is literally
$\operatorname{id}_A\otimes\mathcal R^{\mathrm{raw}}_{\rho_{BC}}$ after
canonical reassociation.

This is the full-support global corollary requested in issue #4890. It makes no
claim about the generic completed channel for singular $\rho_A$. -/
theorem partialTraceRightPetzMap_productTensor_of_posDef_left
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosDef) (hBC : ρBC.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc A B C) ∘ₗ
        partialTraceRightPetzMap
          (productTensorReference ρA ρBC)
          (productTensorReference_posSemidef hA.posSemidef hBC) =
      idTensorMapLM (δ := A) (partialTraceRightPetzMap ρBC hBC) := by
  rw [partialTraceRightPetzMap_productTensor ρA ρBC hA.posSemidef hBC]
  have hproj : hA.posSemidef.isHermitian.supportProj = 1 :=
    hA.supportProj_eq_one
  have hcompression : supportCompressionMap hA.posSemidef.isHermitian.supportProj =
      (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) := by
    apply LinearMap.ext
    intro X
    change hA.posSemidef.isHermitian.supportProj * X *
      hA.posSemidef.isHermitian.supportProj = X
    rw [hproj]
    simp
  rw [hcompression, tensorMapIdLM_id, LinearMap.comp_id]

end HJPWProductReferenceFactorization

section HJPWTensorFactorization

variable {dA : ℕ} [NeZero dA]
variable {B C : Type*} [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- The maximally mixed matrix on a nonzero `Fin dA` index. -/
noncomputable def maximallyMixedOn : Matrix (Fin dA) (Fin dA) ℂ :=
  (dA : ℂ)⁻¹ • (1 : Matrix (Fin dA) (Fin dA) ℂ)

/-- The maximally mixed matrix is positive definite. -/
theorem maximallyMixedOn_posDef : (maximallyMixedOn (dA := dA)).PosDef := by
  apply Matrix.PosDef.smul Matrix.PosDef.one
  rw [inv_pos]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA)

/-- The reference
$\sigma_{ABC}=d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$, reindexed from
$A\times(B\times C)$ to $(A\times B)\times C$ so that `partialTraceRight`
traces out $C$.

This is the maximally mixed specialization of the reference in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, equation (10). It is
not the Hayashi--Koashi--Imoto block decomposition. -/
noncomputable def maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    Matrix ((Fin dA × B) × C) ((Fin dA × B) × C) ℂ :=
  (maximallyMixedOn (dA := dA) ⊗ₖ ρ).submatrix
    (Equiv.prodAssoc (Fin dA) B C) (Equiv.prodAssoc (Fin dA) B C)

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
/-- The maximally mixed tensor reference is positive semidefinite whenever
$\rho_{BC}$ is positive semidefinite. -/
theorem maximallyMixedTensorReference_posSemidef
    [Finite B] [Finite C]
    {ρ : Matrix (B × C) (B × C) ℂ} (hρ : ρ.PosSemidef) :
    (maximallyMixedTensorReference (dA := dA) ρ).PosSemidef := by
  classical
  letI := Fintype.ofFinite B
  letI := Fintype.ofFinite C
  exact (maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker hρ
    |>.submatrix _

omit [NeZero dA] [Fintype B] [DecidableEq B] [DecidableEq C] in
/-- Tracing $C$ from the maximally mixed specialization of HJPW equation (10)
gives $d_A^{-1}\mathbf 1_A\otimes\rho_B$. -/
theorem partialTraceRight_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    partialTraceRight (maximallyMixedTensorReference (dA := dA) ρ) =
      maximallyMixedOn (dA := dA) ⊗ₖ partialTraceRight ρ := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [maximallyMixedTensorReference, maximallyMixedOn,
    partialTraceRight_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, Finset.mul_sum]

private theorem cfcSqrt_maximallyMixedOn_kronecker
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    ((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker hρ).isHermitian.cfc
        Real.sqrt =
      (Real.sqrt ((dA : ℝ)⁻¹) : ℂ) •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          hρ.isHermitian.cfc Real.sqrt) := by
  let c : ℝ := (dA : ℝ)⁻¹
  have hc : 0 ≤ c := by positivity
  have hbase : maximallyMixedOn (dA := dA) ⊗ₖ ρ =
      c • ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ ρ) := by
    ext a b
    simp [maximallyMixedOn, c, Matrix.kroneckerMap_apply,
      Matrix.smul_apply]
    ring
  have hsqrt :=
    ((Matrix.PosSemidef.one (n := Fin dA)).kronecker hρ).sqrt_smul hc
  have hleft : CFC.sqrt (maximallyMixedOn (dA := dA) ⊗ₖ ρ) =
      ((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker
        hρ).isHermitian.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt _
      ((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker hρ).nonneg,
      cfcₙ_eq_cfc,
      ((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker
        hρ).isHermitian.cfc_eq]
  have hright : CFC.sqrt
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ ρ) =
      ((Matrix.PosSemidef.one (n := Fin dA)).kronecker
        hρ).isHermitian.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt _
      ((Matrix.PosSemidef.one (n := Fin dA)).kronecker hρ).nonneg,
      cfcₙ_eq_cfc,
      ((Matrix.PosSemidef.one (n := Fin dA)).kronecker
        hρ).isHermitian.cfc_eq]
  calc
    _ = CFC.sqrt (maximallyMixedOn (dA := dA) ⊗ₖ ρ) := hleft.symm
    _ = CFC.sqrt
        (c • ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ ρ)) := by rw [← hbase]
    _ = Real.sqrt c • CFC.sqrt
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ ρ) := hsqrt
    _ = Real.sqrt c •
        ((Matrix.PosSemidef.one (n := Fin dA)).kronecker
          hρ).isHermitian.cfc Real.sqrt := by rw [hright]
    _ = Real.sqrt c • ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        hρ.isHermitian.cfc Real.sqrt) := by
      rw [← ((Matrix.PosSemidef.one (n := Fin dA)).kronecker
        hρ).isHermitian.cfc_eq,
        Matrix.cfc_one_kronecker hρ.isHermitian, hρ.isHermitian.cfc_eq]
    _ = (Real.sqrt ((dA : ℝ)⁻¹) : ℂ) •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          hρ.isHermitian.cfc Real.sqrt) := by rw [Complex.coe_smul]

/-- The square root in the maximally mixed specialization of HJPW equation
(10) factors into the dimension normalization and the square root of $\rho_{BC}$, after the
canonical product-index reassociation. -/
theorem cfcSqrt_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    (maximallyMixedTensorReference_posSemidef
      (dA := dA) hρ).isHermitian.cfc Real.sqrt =
      ((Real.sqrt ((dA : ℝ)⁻¹) : ℂ) •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          hρ.isHermitian.cfc Real.sqrt)).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C) := by
  rw [← (maximallyMixedTensorReference_posSemidef
    (dA := dA) hρ).isHermitian.cfc_eq]
  change cfc Real.sqrt
      ((maximallyMixedOn (dA := dA) ⊗ₖ ρ).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C)) = _
  have hcfc := Matrix.cfc_submatrix_equiv
    (((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker
      hρ).isHermitian) Real.sqrt (Equiv.prodAssoc (Fin dA) B C).symm
  rw [show cfc Real.sqrt
      ((maximallyMixedOn (dA := dA) ⊗ₖ ρ).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C)) =
      (cfc Real.sqrt (maximallyMixedOn (dA := dA) ⊗ₖ ρ)).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C) by
        simpa only [Equiv.symm_symm] using hcfc]
  rw [((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker
    hρ).isHermitian.cfc_eq, cfcSqrt_maximallyMixedOn_kronecker ρ hρ]

omit [Fintype C] [DecidableEq B] [DecidableEq C] in
/-- Tracing out the untouched $A\times B$ factors from the maximally mixed
specialization of HJPW equation (10) gives the $C$ marginal of $\rho_{BC}$. -/
theorem partialTraceLeft_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    partialTraceLeft (maximallyMixedTensorReference (dA := dA) ρ) =
      partialTraceLeft ρ := by
  ext c c'
  simp only [maximallyMixedTensorReference, maximallyMixedOn,
    partialTraceLeft_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, Equiv.prodAssoc_apply, smul_eq_mul,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [one_apply_eq, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hd : (dA : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne dA
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

omit [DecidableEq B] [DecidableEq C] in
/-- The maximally mixed tensor reference has the same trace as $\rho_{BC}$. -/
theorem trace_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    Matrix.trace (maximallyMixedTensorReference (dA := dA) ρ) =
      Matrix.trace ρ := by
  rw [← trace_partialTraceLeft,
    partialTraceLeft_maximallyMixedTensorReference, trace_partialTraceLeft]

omit [DecidableEq C] in
/-- For the maximally mixed specialization of HJPW equation (10), the support
inverse square root of the $AB$ marginal is $\sqrt{d_A}\,\mathbf 1_A\otimes\rho_B^{-1/2}$ on its
support. -/
theorem supportInvSqrt_partialTraceRight_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    (PosSemidef.partialTraceRight
      (maximallyMixedTensorReference_posSemidef
        (dA := dA) hρ)).supportInvSqrt =
      (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          (PosSemidef.partialTraceRight hρ).supportInvSqrt) := by
  classical
  let c : ℝ := (dA : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA))
  have hmarg :
      partialTraceRight (maximallyMixedTensorReference (dA := dA) ρ) =
        c • ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          partialTraceRight ρ) := by
    rw [partialTraceRight_maximallyMixedTensorReference]
    ext a b
    simp [maximallyMixedOn, c, Matrix.kroneckerMap_apply,
      Matrix.smul_apply]
    ring
  let hbase := (Matrix.PosSemidef.one (n := Fin dA)).kronecker
    (PosSemidef.partialTraceRight hρ)
  have hscaled := hbase.supportInvSqrt_smul hc
  unfold PosSemidef.supportInvSqrt at hscaled ⊢
  rw [← (PosSemidef.partialTraceRight
    (maximallyMixedTensorReference_posSemidef
      (dA := dA) hρ)).isHermitian.cfc_eq,
    hmarg, (hbase.smul hc.le).isHermitian.cfc_eq]
  rw [hscaled]
  congr 1
  exact Matrix.PosSemidef.supportInvSqrt_one_kronecker
    (PosSemidef.partialTraceRight hρ)

omit [DecidableEq C] in
/-- The support projector of the $AB$ marginal in the maximally mixed
specialization of HJPW equation (10) is the identity on $A$ tensored with the
support projector of $\rho_B$.

The proof uses the support-inverse sandwich
$\tau^{-1/2}\tau\tau^{-1/2}=P_{\operatorname{supp}\tau}$ together with the
specialized support-inverse factorization above. -/
theorem supportProj_partialTraceRight_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    (PosSemidef.partialTraceRight
      (maximallyMixedTensorReference_posSemidef
        (dA := dA) hρ)).isHermitian.supportProj =
      (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        (PosSemidef.partialTraceRight hρ).isHermitian.supportProj := by
  let hτ := PosSemidef.partialTraceRight
    (maximallyMixedTensorReference_posSemidef (dA := dA) hρ)
  have hsupport := hτ.supportInvSqrt_mul_self_mul_supportInvSqrt
  rw [← hsupport]
  rw [supportInvSqrt_partialTraceRight_maximallyMixedTensorReference ρ hρ,
    partialTraceRight_maximallyMixedTensorReference]
  simp only [maximallyMixedOn, Matrix.smul_mul, Matrix.mul_smul]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one,
    (PosSemidef.partialTraceRight hρ).supportInvSqrt_mul_self_mul_supportInvSqrt]
  have hc : (0 : ℝ) < (dA : ℝ)⁻¹ := inv_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA))
  have hcancelR : (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ *
      (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ * (dA : ℝ)⁻¹ = 1 := by
    calc
      _ = (Real.sqrt ((dA : ℝ)⁻¹) *
          Real.sqrt ((dA : ℝ)⁻¹))⁻¹ * (dA : ℝ)⁻¹ := by
        rw [mul_inv]
      _ = ((dA : ℝ)⁻¹)⁻¹ * (dA : ℝ)⁻¹ := by
        rw [← pow_two, Real.sq_sqrt hc.le]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hc)
  have hcancelC : (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) * (dA : ℂ)⁻¹ = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_one] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) hcancelR
  ext i j
  simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, one_apply,
    smul_eq_mul]
  by_cases hij : i.1 = j.1
  · simp only [hij, if_pos, Complex.real_smul]
    rw [mul_one, one_mul]
    change (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) *
      ((((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) *
        ((dA : ℂ)⁻¹ *
          (PosSemidef.partialTraceRight hρ).isHermitian.supportProj i.2 j.2)) = _
    calc
      _ = ((((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) * (dA : ℂ)⁻¹) *
          (PosSemidef.partialTraceRight hρ).isHermitian.supportProj i.2 j.2 := by ring
      _ = _ := by rw [hcancelC, one_mul]
  · simp [hij]

/-- **Maximally mixed specialization of HJPW equation (10), elementary-tensor
algebra.** For the reference
$\sigma_{ABC}=d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$, the raw partial-trace
Petz support formula sends every elementary tensor $A_0\otimes X_B$ to
$A_0\otimes\mathcal R_{\rho_{BC}}(X_B)$, up to the canonical reassociation
$(A\times B)\times C\simeq A\times(B\times C)$.

This is the maximally mixed specialization of the tensor-product factorization
in Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, equation (10).

**Maximally mixed specialization
(docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex):**
This theorem proves only the $d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$ case.
The general support-compressed raw identity is
`partialTraceRightPetzMap_productTensor`; its positive-definite-left corollary
recovers the literal identity-tensored formula. Neither result implies the
Koashi--Imoto/Hayashi block decomposition. -/
theorem partialTraceRightPetzMap_maximallyMixedTensor_kronecker
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef)
    (A : Matrix (Fin dA) (Fin dA) ℂ) (X : Matrix B B ℂ) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C)
        (partialTraceRightPetzMap
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ)
          (A ⊗ₖ X)) =
      A ⊗ₖ partialTraceRightPetzMap ρ hρ X := by
  rw [partialTraceRightPetzMap_apply, partialTraceRightPetzMap_apply]
  rw [cfcSqrt_maximallyMixedTensorReference ρ hρ,
    supportInvSqrt_partialTraceRight_maximallyMixedTensorReference ρ hρ]
  change (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc (Fin dA) B C))
    (_ * _ * _) = _
  rw [map_mul, map_mul]
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  rw [show ((((Real.sqrt ((dA : ℝ)⁻¹) : ℂ) •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          hρ.isHermitian.cfc Real.sqrt)).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C)).submatrix
        (Equiv.prodAssoc (Fin dA) B C).symm
        (Equiv.prodAssoc (Fin dA) B C).symm) =
      (Real.sqrt ((dA : ℝ)⁻¹) : ℂ) •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          hρ.isHermitian.cfc Real.sqrt) by ext; rfl]
  rw [show (leftKroneckerEmbed (n := C)
        ((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ •
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
              (PosSemidef.partialTraceRight hρ).supportInvSqrt) *
          (A ⊗ₖ X) *
          (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ •
            ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
              (PosSemidef.partialTraceRight hρ).supportInvSqrt))).submatrix
        (Equiv.prodAssoc (Fin dA) B C).symm
        (Equiv.prodAssoc (Fin dA) B C).symm =
      A ⊗ₖ leftKroneckerEmbed (n := C)
        ((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ •
            (PosSemidef.partialTraceRight hρ).supportInvSqrt * X *
          (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ •
            (PosSemidef.partialTraceRight hρ).supportInvSqrt) by
      simp only [leftKroneckerEmbed_apply, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_kronecker]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.one_mul, Matrix.mul_one]
      ext ⟨a, bc⟩ ⟨a', bc'⟩
      simp [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
        Matrix.smul_apply]
      ring]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  have hc : (0 : ℝ) < (dA : ℝ)⁻¹ := inv_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA))
  have hs : Real.sqrt ((dA : ℝ)⁻¹) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hc
  simp only [smul_smul]
  rw [← Complex.coe_smul, map_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  have hcancelR :
      (Real.sqrt ((dA : ℝ)⁻¹) * Real.sqrt ((dA : ℝ)⁻¹)) *
        ((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ *
          (Real.sqrt ((dA : ℝ)⁻¹))⁻¹) = 1 := by
    calc
      _ = (Real.sqrt ((dA : ℝ)⁻¹) *
          (Real.sqrt ((dA : ℝ)⁻¹))⁻¹) *
        (Real.sqrt ((dA : ℝ)⁻¹) *
          (Real.sqrt ((dA : ℝ)⁻¹))⁻¹) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hs, one_mul]
  have hcancel : ((Real.sqrt ((dA : ℝ)⁻¹) : ℂ) *
      Real.sqrt ((dA : ℝ)⁻¹)) *
      (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ *
        (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcancelR
  set Z : ℂ := (hρ.isHermitian.cfc Real.sqrt *
    leftKroneckerEmbed (n := C)
      ((PosSemidef.partialTraceRight hρ).supportInvSqrt * X *
        (PosSemidef.partialTraceRight hρ).supportInvSqrt) *
    hρ.isHermitian.cfc Real.sqrt) i.2 j.2 with hZ
  change (Real.sqrt ((dA : ℝ)⁻¹) : ℂ) *
    Real.sqrt ((dA : ℝ)⁻¹) *
    (A i.1 j.1 * ((((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ *
      (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) * Z)) = A i.1 j.1 * Z
  calc
    _ = (((Real.sqrt ((dA : ℝ)⁻¹) : ℂ) *
        Real.sqrt ((dA : ℝ)⁻¹)) *
        (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ *
          (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ)) *
        (A i.1 j.1 * Z) := by ring
    _ = A i.1 j.1 * Z := by rw [hcancel, one_mul]

/-- **Complementary-term compatibility, elementary-tensor form.** For the
maximally mixed tensor reference, TNLean's complementary measure-and-prepare
term acts as the identity on $A$ and as the local complementary term on $B$,
after canonical reassociation.

This statement concerns TNLean's support completion; it is not part of HJPW
equation (10). -/
theorem partialTraceRightPetzComplementMap_maximallyMixedTensor_kronecker
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef)
    (A : Matrix (Fin dA) (Fin dA) ℂ) (X : Matrix B B ℂ) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C)
        (partialTraceRightPetzComplementMap
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ)
          (A ⊗ₖ X)) =
      A ⊗ₖ partialTraceRightPetzComplementMap ρ hρ X := by
  rw [partialTraceRightPetzComplementMap_apply,
    partialTraceRightPetzComplementMap_apply]
  rw [supportProj_partialTraceRight_maximallyMixedTensorReference ρ hρ,
    partialTraceLeft_maximallyMixedTensorReference]
  let P := (PosSemidef.partialTraceRight hρ).isHermitian.supportProj
  have hQ : (1 : Matrix (Fin dA × B) (Fin dA × B) ℂ) -
      (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ P =
      (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ (1 - P) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    by_cases haa : a = a' <;> by_cases hbb : b = b' <;>
      simp [haa, hbb, Matrix.kroneckerMap_apply]
  rw [hQ, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  ext ⟨a, bc⟩ ⟨a', bc'⟩
  simp only [equivReindexMap, LinearEquiv.coe_toLinearMap,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodAssoc_symm_apply]
  rw [Matrix.partialTraceLeft_apply, mul_assoc]

/-- **Maximally mixed specialization of HJPW equation (10), raw Petz-map
factorization.** For
$\sigma_{ABC}=d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$, the raw partial-trace
Petz map is $\operatorname{id}_A\otimes\mathcal R_{\rho_{BC}}$, after the
canonical reassociation of product indices.

This is the maximally mixed specialization of equation (10) of
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2.

**Maximally mixed specialization
(docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex):**
This theorem proves only the $d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$ case.
The general support-compressed raw identity is
`partialTraceRightPetzMap_productTensor`; its positive-definite-left corollary
recovers the literal identity-tensored formula. Neither result implies the
Koashi--Imoto/Hayashi block decomposition. -/
theorem partialTraceRightPetzMap_maximallyMixedTensor
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C) ∘ₗ
        partialTraceRightPetzMap
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ) =
      idTensorMapLM (δ := Fin dA) (partialTraceRightPetzMap ρ hρ) := by
  apply LinearMap.ext
  intro X
  obtain ⟨A, Y, hX⟩ :=
    hasOperatorSchmidtDecomposition_operatorSchmidtRank X
  rw [hX]
  simp only [LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [idTensorMapLM_apply, idTensorMap_kronecker]
  exact partialTraceRightPetzMap_maximallyMixedTensor_kronecker
    ρ hρ (A i) (Y i)

/-- **Complementary-term compatibility.** For the maximally mixed tensor
reference, TNLean's complementary measure-and-prepare term factors as the
identity on $A$ tensored with the local complementary term on $B$, after
canonical reassociation.

This is a compatibility property of TNLean's support completion, not a claim
from HJPW equation (10). -/
theorem partialTraceRightPetzComplementMap_maximallyMixedTensor
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C) ∘ₗ
        partialTraceRightPetzComplementMap
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ) =
      idTensorMapLM (δ := Fin dA)
        (partialTraceRightPetzComplementMap ρ hρ) := by
  apply LinearMap.ext
  intro X
  obtain ⟨A, Y, hX⟩ :=
    hasOperatorSchmidtDecomposition_operatorSchmidtRank X
  rw [hX]
  simp only [LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [idTensorMapLM_apply, idTensorMap_kronecker]
  exact partialTraceRightPetzComplementMap_maximallyMixedTensor_kronecker
    ρ hρ (A i) (Y i)

/-- **Completed-channel factorization.** For the maximally mixed tensor
reference, TNLean's completed partial-trace Petz channel is the identity on
$A$ tensored with the completed local channel on $B$, after canonical
reassociation.

The raw support-map summand is the maximally mixed specialization of HJPW
equation (10). The complementary summand is TNLean's support-completion
compatibility and is not asserted by that equation. This theorem does not
invoke or assert a Koashi--Imoto decomposition. -/
theorem partialTraceRightPetzChannel_maximallyMixedTensor
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C) ∘ₗ
        partialTraceRightPetzChannel
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ) =
      idTensorMapLM (δ := Fin dA) (partialTraceRightPetzChannel ρ hρ) := by
  rw [partialTraceRightPetzChannel, LinearMap.comp_add,
    partialTraceRightPetzMap_maximallyMixedTensor,
    partialTraceRightPetzComplementMap_maximallyMixedTensor,
    partialTraceRightPetzChannel, idTensorMapLM_add]

/-- The completed Petz channel for the maximally mixed tensor reference is
trace-preserving and completely positive whenever $\rho_{BC}$ has trace one. -/
theorem partialTraceRightPetzChannel_maximallyMixedTensor_isKrausCPTP
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef)
    (hρtrace : Matrix.trace ρ = 1) :
    IsKrausCPTP
      (partialTraceRightPetzChannel
        (maximallyMixedTensorReference (dA := dA) ρ)
        (maximallyMixedTensorReference_posSemidef (dA := dA) hρ)) := by
  apply partialTraceRightPetzChannel_isKrausCPTP
  rw [trace_maximallyMixedTensorReference, hρtrace]

end HJPWTensorFactorization

end Matrix
