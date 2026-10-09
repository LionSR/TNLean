/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleBondAverage

/-!
# Exact two-block parent space for the clockwise quantum double

The image of the actual two-tensor contraction is the common fixed space
of the two product-one constraints and the coherent normalized bond average.
This derives a parent-space identification from the tensor entries. It does
not identify the full periodic Hamiltonian or assume unitary transport from
the unblocked tensor. Source: SCP10, arXiv:1001.3807v3, lines 2918–2923.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Both local product-one conditions on the full eight-spin space. -/
def quantumDoubleKPairLocalProjector : Matrix
    ((G × G × G × G) × (G × G × G × G))
    ((G × G × G × G) × (G × G × G × G)) ℂ :=
  Matrix.diagonal fun x =>
    if quantumDoubleKHolonomy x.1 = 1 ∧ quantumDoubleKHolonomy x.2 = 1 then 1 else 0

/-- The two local constraints form an orthogonal projector. -/
theorem quantumDoubleKPairLocalProjector_isStarProjection :
    IsStarProjection (quantumDoubleKPairLocalProjector (G := G)) := by
  apply (isStarProjection_iff').mpr
  constructor
  · rw [quantumDoubleKPairLocalProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    split_ifs <;> simp
  · change (quantumDoubleKPairLocalProjector (G := G))ᴴ = _
    ext x y
    simp only [quantumDoubleKPairLocalProjector, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all

/-- The actual physical coherent bond average commutes with the local constraints. -/
theorem quantumDoubleKPairLocalProjector_commute_bondAverage :
    Commute (quantumDoubleKPairLocalProjector (G := G)) quantumDoubleKBondAverage := by
  unfold quantumDoubleKBondAverage
  apply Commute.smul_right
  apply Commute.sum_right
  intro u _
  change Commute _ ((quantumDoubleKBondPermutation u)⁻¹.permMatrix ℂ)
  apply Matrix.commute_permMatrix_of_entry_invariant
  intro x y
  simp only [quantumDoubleKPairLocalProjector, Matrix.diagonal_apply,
    ((quantumDoubleKBondPermutation u)⁻¹).injective.eq_iff]
  change (if x = y then
    (if quantumDoubleKHolonomy (quantumDoubleKBondLeft u⁻¹ x.1) = 1 ∧
      quantumDoubleKHolonomy (quantumDoubleKBondRight u⁻¹ x.2) = 1 then (1 : ℂ) else 0)
    else 0) = _
  simp only [quantumDoubleKHolonomy_bondLeft, quantumDoubleKHolonomy_bondRight]

/-- The common projector of the explicit local and coherent bond constraints. -/
noncomputable def quantumDoubleKBondSupportProjector : Matrix
    ((G × G × G × G) × (G × G × G × G))
    ((G × G × G × G) × (G × G × G × G)) ℂ :=
  quantumDoubleKBondAverage * quantumDoubleKPairLocalProjector

theorem quantumDoubleKBondSupportProjector_isStarProjection :
    IsStarProjection (quantumDoubleKBondSupportProjector (G := G)) :=
  quantumDoubleKBondAverage_isStarProjection.mul
    quantumDoubleKPairLocalProjector_isStarProjection
    quantumDoubleKPairLocalProjector_commute_bondAverage.symm

/-- The product-one conditions hold on every column of the actual network. -/
theorem quantumDoubleKPairLocalProjector_contraction :
    quantumDoubleKPairLocalProjector (G := G) * quantumDoubleKBondContraction =
      quantumDoubleKBondContraction := by
  ext x b
  rw [quantumDoubleKPairLocalProjector, Matrix.diagonal_mul]
  by_cases hx : quantumDoubleKHolonomy x.1 = 1 ∧ quantumDoubleKHolonomy x.2 = 1
  · simp [hx]
  · simp only [hx, ite_false, zero_mul]
    rw [quantumDoubleKBondContraction_eq]
    symm
    apply Finset.sum_eq_zero
    intro q _
    have hne : x ≠ (quantumDoubleKSpins (b.1.1, q, b.1.2.1, b.1.2.2),
        quantumDoubleKSpins (b.2.1, b.2.2.1, b.2.2.2, q)) := by
      rintro rfl
      exact hx ⟨quantumDoubleKHolonomy_spins _, quantumDoubleKHolonomy_spins _⟩
    simp [hne]

/-- Every network column is fixed by the independently defined common projector. -/
theorem quantumDoubleKBondSupportProjector_contraction :
    quantumDoubleKBondSupportProjector (G := G) * quantumDoubleKBondContraction =
      quantumDoubleKBondContraction := by
  rw [quantumDoubleKBondSupportProjector, Matrix.mul_assoc,
    quantumDoubleKPairLocalProjector_contraction, quantumDoubleKBondAverage_contraction]

/-- Six boundary colors reconstruct any product-one pair, with shared color one. -/
def quantumDoubleKBondBoundaryColors
    (x : (G × G × G × G) × (G × G × G × G)) : (G × G × G) × (G × G × G) :=
  ((x.1.1, x.1.2.1⁻¹, (x.1.2.1 * x.1.2.2.1)⁻¹),
    (x.2.1 * x.2.2.1 * x.2.2.2.1, x.2.2.1 * x.2.2.2.1, x.2.2.2.1))

omit [Fintype G] [DecidableEq G] in
/-- The boundary reconstruction uses the true nonabelian multiplication order. -/
theorem quantumDoubleKBondBoundaryColors_spins
    (x : (G × G × G × G) × (G × G × G × G))
    (hx : quantumDoubleKHolonomy x.1 = 1 ∧ quantumDoubleKHolonomy x.2 = 1) :
    let b := quantumDoubleKBondBoundaryColors x
    (quantumDoubleKSpins (b.1.1, 1, b.1.2.1, b.1.2.2),
      quantumDoubleKSpins (b.2.1, b.2.2.1, b.2.2.2, 1)) = x := by
  rcases x with ⟨⟨a, b, c, d⟩, ⟨e, f, g, h⟩⟩
  have hd : (a * b * c)⁻¹ = d := inv_eq_of_mul_eq_one_right hx.1
  have hh : (e * f * g)⁻¹ = h := inv_eq_of_mul_eq_one_right hx.2
  simp only [quantumDoubleKBondBoundaryColors, quantumDoubleKSpins, inv_one,
    inv_inv, mul_one, one_mul]
  rw [← hd, ← hh]
  congr 2 <;> group

/-- An allowed basis ket, coherently averaged over the bond, is an explicit
boundary column of the real contraction divided by the group order. -/
theorem quantumDoubleKBondAverage_single_eq_contraction
    (x : (G × G × G × G) × (G × G × G × G))
    (hx : quantumDoubleKHolonomy x.1 = 1 ∧ quantumDoubleKHolonomy x.2 = 1) :
    quantumDoubleKBondAverage *ᵥ Pi.single x 1 =
      (Fintype.card G : ℂ)⁻¹ •
        (fun y => quantumDoubleKBondContraction y (quantumDoubleKBondBoundaryColors x)) := by
  rw [quantumDoubleKBondAverage, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp_rw [quantumDoubleKBondMatrix_single]
  congr 1
  funext y
  rw [Finset.sum_apply, quantumDoubleKBondContraction_eq]
  apply Finset.sum_congr rfl
  intro q _
  have he := congrArg (quantumDoubleKBondAction q)
    (quantumDoubleKBondBoundaryColors_spins x hx)
  rw [quantumDoubleKBondAction, ← quantumDoubleKSpins_bondLeft,
    ← quantumDoubleKSpins_bondRight, mul_one] at he
  simp only [Pi.single_apply, he]

/-- Exact two-block parent identification on the entire eight-spin space.
The reverse inclusion is supplied by explicit boundary colors, not an assumed
conjugacy or a definition of the desired ground space. -/
theorem range_quantumDoubleKBondContraction :
    LinearMap.range (Matrix.mulVecLin (quantumDoubleKBondContraction (G := G))) =
      LinearMap.range (Matrix.mulVecLin (quantumDoubleKBondSupportProjector (G := G))) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    refine ⟨quantumDoubleKBondContraction *ᵥ v, ?_⟩
    change quantumDoubleKBondSupportProjector *ᵥ (quantumDoubleKBondContraction *ᵥ v) = _
    rw [Matrix.mulVec_mulVec, quantumDoubleKBondSupportProjector_contraction]
    rfl
  · rintro _ ⟨v, rfl⟩
    rw [← (Pi.basisFun ℂ ((G × G × G × G) × (G × G × G × G))).sum_repr v]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro x _
    apply Submodule.smul_mem
    simp only [Pi.basisFun_apply, Matrix.mulVecBilin_apply]
    rw [quantumDoubleKBondSupportProjector, ← Matrix.mulVec_mulVec]
    rw [quantumDoubleKPairLocalProjector, Matrix.diagonal_mulVec_single]
    by_cases hx : quantumDoubleKHolonomy x.1 = 1 ∧ quantumDoubleKHolonomy x.2 = 1
    · simp only [hx.1, hx.2, and_self, ite_true, one_mul]
      rw [quantumDoubleKBondAverage_single_eq_contraction x hx]
      refine ⟨(Fintype.card G : ℂ)⁻¹ • Pi.single (quantumDoubleKBondBoundaryColors x) 1, ?_⟩
      ext y
      simp [Matrix.col, Matrix.transpose_apply]
    · simp [hx]

/-- Membership in the actual two-block parent space is precisely local
product-one support and equal weight under each coherent physical bond action. -/
theorem mem_range_quantumDoubleKBondContraction_iff
    (v : ((G × G × G × G) × (G × G × G × G)) → ℂ) :
    v ∈ LinearMap.range (Matrix.mulVecLin (quantumDoubleKBondContraction (G := G))) ↔
      quantumDoubleKPairLocalProjector *ᵥ v = v ∧
        ∀ u x, v (quantumDoubleKBondAction u x) = v x := by
  rw [range_quantumDoubleKBondContraction]
  have hA : quantumDoubleKBondAverage (G := G) * quantumDoubleKBondAverage =
      quantumDoubleKBondAverage := quantumDoubleKBondAverage_isStarProjection.isIdempotentElem.eq
  have hB : quantumDoubleKPairLocalProjector (G := G) * quantumDoubleKPairLocalProjector =
      quantumDoubleKPairLocalProjector :=
    quantumDoubleKPairLocalProjector_isStarProjection.isIdempotentElem.eq
  have hAB := quantumDoubleKPairLocalProjector_commute_bondAverage (G := G)
  rw [← quantumDoubleKBondAverage_mulVec_eq_self_iff]
  constructor
  · rintro ⟨w, hw⟩
    change quantumDoubleKBondSupportProjector *ᵥ w = v at hw
    rw [← hw]
    constructor
    · rw [Matrix.mulVec_mulVec, quantumDoubleKBondSupportProjector,
        ← Matrix.mul_assoc, hAB.eq, Matrix.mul_assoc, hB]
    · rw [Matrix.mulVec_mulVec, quantumDoubleKBondSupportProjector,
        ← Matrix.mul_assoc, hA]
  · rintro ⟨hlocal, havg⟩
    refine ⟨v, ?_⟩
    change quantumDoubleKBondSupportProjector *ᵥ v = v
    rw [quantumDoubleKBondSupportProjector, ← Matrix.mulVec_mulVec, hlocal, havg]

end TNLean.PEPS
