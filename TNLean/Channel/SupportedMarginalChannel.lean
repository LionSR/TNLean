/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OperatorSchmidt
import TNLean.Channel.KrausCPTP
import TNLean.Channel.PartialTrace
import TNLean.Channel.TensorMap
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Channel associated with a supported bipartite marginal

This file records the linear-algebraic part of the canonical channel
reformulation of a bipartite density operator.  In an eigenbasis of a faithful
first marginal with eigenvalues `p i > 0`, the `(i,j)` operator block is divided
by `sqrt (p i * p j)`.  The resulting linear map has the same range dimension
as the original operator-Schmidt reshaping.

The finite-dimensional inequality bounding entanglement-assisted mutual
information by the logarithm of this range dimension follows from Beigi's
weighted Hilbert--Schmidt contraction and order monotonicity, together with
the order-one limit of Müller-Lennert et al.  The mathematical argument and
formalization status are recorded in
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`; the inequality
is not asserted here.

## Main definitions

* `Matrix.supportedMarginalInputScaling`: inverse-square-root scaling on the
  input matrix entries.
* `Matrix.supportedMarginalMap`: the resulting map from the supported first
  matrix algebra to the second matrix algebra.

## Main statements

* `Matrix.supportedMarginalInputScaling_surjective`: positivity of every
  marginal eigenvalue makes the scaling invertible.
* `Matrix.range_supportedMarginalMap`: the resulting map has the same range as
  the operator-Schmidt reshaping.
* `Matrix.finrank_range_supportedMarginalMap`: its linear rank is the
  operator-Schmidt rank of the bipartite operator.
* `Matrix.supportedMarginalMap_isKrausCPTP`: positivity and a faithful right
  partial trace make the supported-marginal map a quantum channel.
* `Matrix.supportedMarginalReconstruction_eq`: applying this channel to the
  canonical purification reconstructs the original bipartite operator.

## References

* C. H. Bennett, P. W. Shor, J. A. Smolin, and A. V. Thapliyal,
  arXiv:quant-ph/0106052, entanglement-assisted channel mutual information.
* S. Beigi, *Sandwiched Rényi Divergence Satisfies Data Processing
  Inequality*, J. Math. Phys. 54 (2013), 122202, Theorems 6 and 7.
* M.-D. Choi, *Completely positive linear maps on complex matrices*,
  Linear Algebra Appl. 10 (1975), 285--290.
* M. Müller-Lennert, F. Dupuis, O. Szehr, S. Fehr, and M. Tomamichel,
  *On quantum Rényi entropies: a new generalization and some properties*,
  J. Math. Phys. 54 (2013), 122203, Theorem 5.
-/

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- The inverse square root of a positive marginal eigenvalue, regarded as a
complex scalar. -/
noncomputable def marginalInvSqrt (p : α → ℝ) (i : α) : ℂ :=
  ((Real.sqrt (p i) : ℝ) : ℂ)⁻¹

omit [Fintype α] [DecidableEq α] in
@[simp]
theorem star_marginalInvSqrt (p : α → ℝ) (i : α) :
    star (marginalInvSqrt p i) = marginalInvSqrt p i := by
  simp [marginalInvSqrt]

/-- Entrywise conjugation by the inverse square roots of the first marginal
eigenvalues.

This is the inverse marginal scaling in the finite-dimensional state--channel
correspondence.  The entanglement-assisted mutual information of the resulting
channel is the quantity maximized in arXiv:quant-ph/0106052, equation (9). -/
noncomputable def supportedMarginalInputScaling (p : α → ℝ) :
    Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ where
  toFun X i j := marginalInvSqrt p i * X i j * marginalInvSqrt p j
  map_add' X Y := by
    ext i j
    simp only [Matrix.add_apply]
    ring
  map_smul' c X := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The supported-marginal map associated with a bipartite operator in an
eigenbasis of its first marginal.

For matrix units it is the block formula
`Φ(Eᵢⱼ) = ρᵢⱼ / sqrt(pᵢ pⱼ)` from the canonical purification channel
reformulation. -/
noncomputable def supportedMarginalMap
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ) :
    Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ :=
  operatorSchmidtMap ρ ∘ₗ supportedMarginalInputScaling p

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp]
theorem supportedMarginalMap_apply
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ) (X : Matrix α α ℂ) :
    supportedMarginalMap ρ p X =
      ∑ ij : α × α,
        (marginalInvSqrt p ij.1 * X ij.1 ij.2 * marginalInvSqrt p ij.2) •
          operatorBlock ρ ij.1 ij.2 := by
  rfl

omit [Fintype α] [DecidableEq α] in
/-- Strict positivity of the marginal eigenvalues makes the input scaling
surjective. -/
theorem supportedMarginalInputScaling_surjective (p : α → ℝ)
    (hp : ∀ i, 0 < p i) :
    Function.Surjective (supportedMarginalInputScaling p) := by
  intro X
  refine ⟨fun i j ↦ (Real.sqrt (p i) : ℂ) * X i j * (Real.sqrt (p j) : ℂ), ?_⟩
  ext i j
  simp only [supportedMarginalInputScaling, marginalInvSqrt, LinearMap.coe_mk,
    AddHom.coe_mk]
  have hi : (Real.sqrt (p i) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hp i))
  have hj : (Real.sqrt (p j) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hp j))
  field_simp

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- The supported-marginal map has the same range as the original reshaped
operator. -/
theorem range_supportedMarginalMap (ρ : Matrix (α × β) (α × β) ℂ)
    (p : α → ℝ) (hp : ∀ i, 0 < p i) :
    LinearMap.range (supportedMarginalMap ρ p) =
      LinearMap.range (operatorSchmidtMap ρ) := by
  rw [supportedMarginalMap, LinearMap.range_comp]
  rw [LinearMap.range_eq_top.mpr (supportedMarginalInputScaling_surjective p hp)]
  rw [Submodule.map_top]

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- The linear rank of the supported-marginal map is the operator-Schmidt rank
of the bipartite operator. -/
theorem finrank_range_supportedMarginalMap [Finite β]
    (ρ : Matrix (α × β) (α × β) ℂ)
    (p : α → ℝ) (hp : ∀ i, 0 < p i) :
    Module.finrank ℂ (LinearMap.range (supportedMarginalMap ρ p)) =
      operatorSchmidtRank ρ := by
  rw [operatorSchmidtRank, range_supportedMarginalMap ρ p hp]

omit [Fintype α] [DecidableEq α] [DecidableEq β] in
/-- The trace of an operator block is the corresponding entry of the right
partial trace. -/
@[simp]
theorem trace_operatorBlock
    (ρ : Matrix (α × β) (α × β) ℂ) (i j : α) :
    Matrix.trace (operatorBlock ρ i j) = partialTraceRight ρ i j := by
  rfl

omit [DecidableEq β] in
/-- If the first marginal is diagonal with strictly positive eigenvalues, the
supported-marginal map preserves trace. -/
theorem supportedMarginalMap_trace
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ)
    (hp : ∀ i, 0 < p i)
    (hmargin : partialTraceRight ρ = Matrix.diagonal fun i ↦ (p i : ℂ))
    (X : Matrix α α ℂ) :
    Matrix.trace (supportedMarginalMap ρ p X) = Matrix.trace X := by
  rw [supportedMarginalMap_apply, Matrix.trace_sum]
  simp_rw [Matrix.trace_smul]
  change ∑ x : α × α,
      (marginalInvSqrt p x.1 * X x.1 x.2 * marginalInvSqrt p x.2) *
        partialTraceRight ρ x.1 x.2 = Matrix.trace X
  rw [hmargin]
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, marginalInvSqrt]
  have hi : (Real.sqrt (p i) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hp i))
  have hsq : (Real.sqrt (p i) : ℂ) * (Real.sqrt (p i) : ℂ) = (p i : ℂ) := by
    norm_cast
    exact (pow_two (Real.sqrt (p i))).symm.trans (Real.sq_sqrt (le_of_lt (hp i)))
  rw [← hsq]
  field_simp

/-- Positivity of the bipartite operator gives a rectangular Kraus
representation of its supported-marginal map. -/
theorem supportedMarginalMap_isKrausCP
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ)
    (hρ : ρ.PosSemidef) :
    IsKrausCP (supportedMarginalMap ρ p) := by
  classical
  obtain ⟨r, v, hρeq⟩ := (Matrix.posSemidef_iff_eq_sum_vecMulVec).mp hρ
  refine ⟨r, fun t b i ↦ marginalInvSqrt p i * v t (i, b), ?_⟩
  intro X
  ext b c
  simp only [supportedMarginalMap_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, operatorBlock, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hρeq]
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  have hstar (t : Fin r) (i : α) (d : β) :
      star (marginalInvSqrt p i * v t (i, d)) =
        marginalInvSqrt p i * star (v t (i, d)) := by
    simp
  simp_rw [hstar]
  rw [Fintype.sum_prod_type]
  change (∑ i, ∑ j,
      marginalInvSqrt p i * X i j * marginalInvSqrt p j *
        ∑ t, v t (i, b) * star (v t (j, c))) =
    ∑ t, ∑ j, (∑ i, marginalInvSqrt p i * v t (i, b) * X i j) *
      (marginalInvSqrt p j * star (v t (j, c)))
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have sum_rotate (f : α → α → Fin r → ℂ) :
      (∑ i, ∑ j, ∑ t, f i j t) = ∑ t, ∑ j, ∑ i, f i j t := by
    calc
      (∑ i, ∑ j, ∑ t, f i j t) = ∑ i, ∑ t, ∑ j, f i j t := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ t, ∑ i, ∑ j, f i j t := by
        rw [Finset.sum_comm]
      _ = ∑ t, ∑ j, ∑ i, f i j t := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_comm]
  rw [sum_rotate]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

/-- A positive bipartite operator whose first marginal is faithful and
diagonal determines a trace-preserving completely positive map. -/
theorem supportedMarginalMap_isKrausCPTP
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ)
    (hρ : ρ.PosSemidef) (hp : ∀ i, 0 < p i)
    (hmargin : partialTraceRight ρ = Matrix.diagonal fun i ↦ (p i : ℂ)) :
    IsKrausCPTP (supportedMarginalMap ρ p) := by
  apply isKrausCPTP_of_isKrausCP_trace_preserving
  · exact supportedMarginalMap_isKrausCP ρ p hρ
  · exact supportedMarginalMap_trace ρ p hp hmargin

/-- The canonical purification vector of a diagonal marginal with eigenvalues
`p`, written in its eigenbasis. -/
noncomputable def diagonalMarginalPurification (p : α → ℝ) : α × α → ℂ :=
  fun ij ↦ if ij.1 = ij.2 then (Real.sqrt (p ij.1) : ℂ) else 0

/-- The rank-one projector onto the canonical purification of a diagonal
marginal. -/
noncomputable def diagonalMarginalPurificationProj (p : α → ℝ) :
    Matrix (α × α) (α × α) ℂ :=
  Matrix.vecMulVec (diagonalMarginalPurification p)
    (star (diagonalMarginalPurification p))

/-- Apply the supported-marginal map to the purifying half and restore the
original ordering of the two tensor factors. -/
noncomputable def supportedMarginalReconstruction
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ) :
    Matrix (α × β) (α × β) ℂ :=
  (tensorMapId (supportedMarginalMap ρ p) (diagonalMarginalPurificationProj p)).submatrix
    (fun ib ↦ (ib.2, ib.1)) (fun ib ↦ (ib.2, ib.1))

omit [Fintype β] [DecidableEq β] in
/-- The canonical purification and supported-marginal map reconstruct the
original bipartite operator when every marginal eigenvalue is positive. -/
theorem supportedMarginalReconstruction_eq
    (ρ : Matrix (α × β) (α × β) ℂ) (p : α → ℝ)
    (hp : ∀ i, 0 < p i) :
    supportedMarginalReconstruction ρ p = ρ := by
  ext ⟨i, b⟩ ⟨j, c⟩
  simp only [supportedMarginalReconstruction, Matrix.submatrix_apply,
    tensorMapId_apply]
  rw [supportedMarginalMap_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, operatorBlock,
    bipartiteSlice_apply, diagonalMarginalPurificationProj, Matrix.vecMulVec_apply,
    Pi.star_apply, diagonalMarginalPurification]
  simp only [RCLike.star_def, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [hk]) (by simp)]
  simp
  have hi : (Real.sqrt (p i) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hp i))
  have hj : (Real.sqrt (p j) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hp j))
  simp only [marginalInvSqrt]
  field_simp

end Matrix
