/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.KrausCPTP
import TNLean.Channel.MarginalSupportAbsorption
import TNLean.Channel.TensorMap
import TNLean.Algebra.OperatorSchmidt

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


section HJPWTensorFactorization

variable {dA : ℕ} [NeZero dA]
variable {B C : Type*} [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

private noncomputable def petzReindexStarAlgHom {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun M := M.submatrix e.symm e.symm
  map_one' := by simp [Matrix.submatrix_one_equiv]
  map_mul' A B := by
    rw [← Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.submatrix_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      show (r • (1 : Matrix m m ℂ)).submatrix e.symm e.symm =
          r • ((1 : Matrix m m ℂ).submatrix e.symm e.symm) from rfl,
      Matrix.submatrix_one_equiv]
  map_star' A := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose,
      Matrix.conjTranspose_submatrix]

private theorem petzCfc_submatrix_equiv {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) (e : m ≃ n) :
    cfc f (A.submatrix e.symm e.symm) =
      (cfc f A).submatrix e.symm e.symm := by
  have hcont : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hcontφ : Continuous (petzReindexStarAlgHom e) :=
    LinearMap.continuous_of_finiteDimensional
      ((petzReindexStarAlgHom e : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ))
  have hsa : IsSelfAdjoint A := hA
  have hsa' : IsSelfAdjoint (petzReindexStarAlgHom e A) := by
    change (A.submatrix e.symm e.symm).IsHermitian
    exact hA.submatrix e.symm
  simpa [petzReindexStarAlgHom] using
    (StarAlgHomClass.map_cfc (petzReindexStarAlgHom e) f A
      hcont hcontφ hsa hsa').symm

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

This is the reference used in Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, equation (10). It is not the Koashi--Imoto or
Hayashi block decomposition. -/
noncomputable def maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    Matrix ((Fin dA × B) × C) ((Fin dA × B) × C) ℂ :=
  (maximallyMixedOn (dA := dA) ⊗ₖ ρ).submatrix
    (Equiv.prodAssoc (Fin dA) B C) (Equiv.prodAssoc (Fin dA) B C)

/-- The maximally mixed tensor reference is positive semidefinite whenever
$\rho_{BC}$ is positive semidefinite. -/
omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
theorem maximallyMixedTensorReference_posSemidef
    {ρ : Matrix (B × C) (B × C) ℂ} (hρ : ρ.PosSemidef) :
    (maximallyMixedTensorReference (dA := dA) ρ).PosSemidef := by
  exact (maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker hρ
    |>.submatrix _

/-- Tracing $C$ from the HJPW equation (10) reference gives
$d_A^{-1}\mathbf 1_A\otimes\rho_B$. -/
omit [NeZero dA] [Fintype B] [DecidableEq B] [DecidableEq C] in
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

/-- The square root in the HJPW equation (10) reference factors into the
maximally mixed normalization and the square root of $\rho_{BC}$, after the
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
  have hcfc := petzCfc_submatrix_equiv
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

/-- The support inverse square root of the $AB$ marginal of the HJPW equation
(10) reference is $\sqrt{d_A}\,\mathbf 1_A\otimes\rho_B^{-1/2}$ on its
support. -/
omit [DecidableEq C] in
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

/-- **HJPW equation (10), elementary-tensor algebra.** For the reference
$\sigma_{ABC}=d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$, the raw partial-trace
Petz support formula sends every elementary tensor $A_0\otimes X_B$ to
$A_0\otimes\mathcal R_{\rho_{BC}}(X_B)$, up to the canonical reassociation
$(A\times B)\times C\simeq A\times(B\times C)$.

This is the tensor-product factorization in Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, equation (10). It is an algebraic Petz-map statement,
not the Koashi--Imoto decomposition. -/
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

/-- **HJPW equation (10), raw Petz-map factorization.** For
$\sigma_{ABC}=d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$, the raw partial-trace
Petz map is $\operatorname{id}_A\otimes\mathcal R_{\rho_{BC}}$, after the
canonical reassociation of product indices.

This is equation (10) of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2. It is not a statement of the Koashi--Imoto
or Hayashi decomposition. -/
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

end HJPWTensorFactorization

end Matrix
