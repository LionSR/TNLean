/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDouble

/-!
# The clockwise quantum-double tensor and its local parent term

SCP10, arXiv:1001.3807v3, equation (7.10), source lines 2904–2923, uses
`K(p,q,r,s) = |pq⁻¹, qr⁻¹, rs⁻¹, sp⁻¹⟩`. This file retains that exact
nonabelian order, identifies its physical image, and proves that the first
of the three stated Hamiltonian terms is the complementary diagonal
orthogonal projector. The physical alphabet is the full `G⁴`, not only
its product-one subset. No unblocked-to-blocked unitary is asserted.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G]

/-- The four clockwise physical spins in SCP10 equation (7.10). -/
def quantumDoubleKSpins (c : G × G × G × G) : G × G × G × G :=
  (c.1 * c.2.1⁻¹, c.2.1 * c.2.2.1⁻¹, c.2.2.1 * c.2.2.2⁻¹, c.2.2.2 * c.1⁻¹)

/-- The ordered clockwise holonomy of one blocked tensor. -/
def quantumDoubleKHolonomy (x : G × G × G × G) : G :=
  x.1 * x.2.1 * x.2.2.1 * x.2.2.2

@[simp]
theorem quantumDoubleKHolonomy_spins (c : G × G × G × G) :
    quantumDoubleKHolonomy (quantumDoubleKSpins c) = 1 := by
  simp [quantumDoubleKHolonomy, quantumDoubleKSpins, mul_assoc]

/-- Explicit physical basis relabelling from the review's dual convention
into the clockwise convention of SCP10; this is not the blocking of `T`. -/
def quantumDoubleDualToK : Equiv.Perm (G × G × G × G) where
  toFun x := (x.2.1⁻¹, x.2.2.1, x.2.2.2, x.1⁻¹)
  invFun x := (x.2.2.2⁻¹, x.1⁻¹, x.2.1, x.2.2.1)
  left_inv x := by rcases x with ⟨a, b, c, d⟩; simp
  right_inv x := by rcases x with ⟨a, b, c, d⟩; simp

@[simp]
theorem quantumDoubleDualToK_spins (c : G × G × G × G) :
    quantumDoubleDualToK (quantumDoubleDualSpins c) = quantumDoubleKSpins c := by
  rcases c with ⟨p, q, r, s⟩
  simp [quantumDoubleDualToK, quantumDoubleDualSpins, quantumDoubleKSpins]

/-- A product-one spin tuple has this explicit coloring with first color one. -/
def quantumDoubleKColors (x : G × G × G × G) : G × G × G × G :=
  (1, x.1⁻¹, (x.1 * x.2.1)⁻¹, (x.1 * x.2.1 * x.2.2.1)⁻¹)

theorem quantumDoubleKSpins_colors {x : G × G × G × G}
    (hx : quantumDoubleKHolonomy x = 1) :
    quantumDoubleKSpins (quantumDoubleKColors x) = x := by
  rcases x with ⟨a, b, c, d⟩
  have hd : (a * b * c)⁻¹ = d := by
    apply inv_eq_of_mul_eq_one_right
    exact hx
  simp only [quantumDoubleKSpins, quantumDoubleKColors, inv_inv, one_mul, inv_one, mul_one]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ hd)) <;> group

/-- Exactly the product-one spin configurations occur in the clockwise tensor. -/
theorem quantumDoubleKSpins_range :
    Set.range (quantumDoubleKSpins (G := G)) = {x | quantumDoubleKHolonomy x = 1} := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact quantumDoubleKHolonomy_spins c
  · intro hx
    exact ⟨quantumDoubleKColors x, quantumDoubleKSpins_colors hx⟩

variable (G) [DecidableEq G]

/-- The actual unnormalized blocked tensor of SCP10 equation (7.10). -/
def quantumDoubleKTensor (p q r s : G) (x : G × G × G × G) : ℂ :=
  if x = quantumDoubleKSpins (p, q, r, s) then 1 else 0

variable {G}

theorem quantumDoubleKTensor_eq_dual (p q r s : G) (x : G × G × G × G) :
    quantumDoubleKTensor G p q r s x =
      quantumDoubleDualTensor G p q r s (quantumDoubleDualToK.symm x) := by
  unfold quantumDoubleKTensor quantumDoubleDualTensor
  simp only [Equiv.symm_apply_eq, quantumDoubleDualToK_spins]

variable [Fintype G]

/-- The source's local product-one projector on the entire four-spin space. -/
def quantumDoubleKLocalProjector : Matrix (G × G × G × G) (G × G × G × G) ℂ :=
  Matrix.diagonal fun x => if quantumDoubleKHolonomy x = 1 then 1 else 0

/-- The first physical Hamiltonian term in SCP10, source lines 2918–2920. -/
def quantumDoubleKLocalTerm : Matrix (G × G × G × G) (G × G × G × G) ℂ :=
  1 - quantumDoubleKLocalProjector

/-- The local constraint is an orthogonal projector, including off-support spins. -/
theorem quantumDoubleKLocalProjector_isStarProjection :
    IsStarProjection (quantumDoubleKLocalProjector (G := G)) := by
  apply (isStarProjection_iff').mpr
  constructor
  · rw [quantumDoubleKLocalProjector, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    split_ifs <;> simp
  · change (quantumDoubleKLocalProjector (G := G))ᴴ = _
    ext x y
    simp only [quantumDoubleKLocalProjector, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all

/-- The local Hamiltonian term is the complementary orthogonal projector. -/
theorem quantumDoubleKLocalTerm_isStarProjection :
    IsStarProjection (quantumDoubleKLocalTerm (G := G)) :=
  quantumDoubleKLocalProjector_isStarProjection.one_sub

@[simp]
theorem quantumDoubleKLocalProjector_mulVec (v : (G × G × G × G) → ℂ)
    (x : G × G × G × G) :
    (quantumDoubleKLocalProjector *ᵥ v) x =
      if quantumDoubleKHolonomy x = 1 then v x else 0 := by
  simp [quantumDoubleKLocalProjector, Matrix.mulVec_diagonal]

theorem siteMap_quantumDoubleKTensor_apply (v : (G × G × G × G) → ℂ)
    (x : G × G × G × G) :
    siteMap (quantumDoubleKTensor G) v x =
      ∑ c : G × G × G × G, if x = quantumDoubleKSpins c then v c else 0 := by
  rw [siteMap_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [quantumDoubleKTensor]

/-- The first physical term annihilates the actual blocked tensor, with no
restriction on the virtual vector. -/
theorem quantumDoubleKLocalProjector_siteMap (v : (G × G × G × G) → ℂ) :
    quantumDoubleKLocalProjector *ᵥ siteMap (quantumDoubleKTensor G) v =
      siteMap (quantumDoubleKTensor G) v := by
  funext x
  rw [quantumDoubleKLocalProjector_mulVec]
  split_ifs with hx
  · rfl
  · rw [siteMap_quantumDoubleKTensor_apply]
    symm
    apply Finset.sum_eq_zero
    intro c _
    have hxc : x ≠ quantumDoubleKSpins c := by
      rintro rfl
      exact hx (quantumDoubleKHolonomy_spins c)
    simp [hxc]

/-- Every allowed computational basis vector is the image of an explicit
virtual basis vector. Thus the local parent identification is substantive. -/
theorem siteMap_quantumDoubleKTensor_single (c : G × G × G × G) :
    siteMap (quantumDoubleKTensor G) (Pi.single c 1) =
      Pi.single (quantumDoubleKSpins c) 1 := by
  funext x
  rw [siteMap_quantumDoubleKTensor_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hbc
    simp [hbc]
  · simp

/-- The image of the actual blocked tensor is exactly the range of the
physical product-one projector. This is the local parent-space identification. -/
theorem range_siteMap_quantumDoubleKTensor :
    LinearMap.range (siteMap (quantumDoubleKTensor G)) =
      LinearMap.range (Matrix.mulVecLin (quantumDoubleKLocalProjector (G := G))) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨_, quantumDoubleKLocalProjector_siteMap v⟩
  · rintro _ ⟨v, rfl⟩
    rw [← (Pi.basisFun ℂ (G × G × G × G)).sum_repr v]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro x _
    apply Submodule.smul_mem
    by_cases hx : quantumDoubleKHolonomy x = 1
    · refine ⟨Pi.single (quantumDoubleKColors x) 1, ?_⟩
      rw [siteMap_quantumDoubleKTensor_single, quantumDoubleKSpins_colors hx]
      ext y
      simp only [Pi.basisFun_apply, Matrix.mulVecBilin_apply,
        quantumDoubleKLocalProjector_mulVec, left_eq_ite_iff]
      intro hy
      have hxy : y ≠ x := by rintro rfl; exact hy hx
      simp [hxy]
    · have hz : Matrix.mulVecLin (quantumDoubleKLocalProjector (G := G))
          (Pi.basisFun ℂ (G × G × G × G) x) = 0 := by
        ext y
        simp only [Pi.basisFun_apply, Matrix.mulVecBilin_apply,
          quantumDoubleKLocalProjector_mulVec, Pi.zero_apply, ite_eq_right_iff]
        intro hy
        have hxy : y ≠ x := by rintro rfl; exact hx hy
        simp [hxy]
      rw [hz]
      exact Submodule.zero_mem _

/-- The zero-energy space of the actual physical local term is exactly the
image of K, on the full ambient four-spin space. -/
theorem range_siteMap_quantumDoubleKTensor_eq_ker_localTerm :
    LinearMap.range (siteMap (quantumDoubleKTensor G)) =
      LinearMap.ker (Matrix.mulVecLin (quantumDoubleKLocalTerm (G := G))) := by
  rw [range_siteMap_quantumDoubleKTensor]
  have hp := (quantumDoubleKLocalProjector_isStarProjection (G := G)).isIdempotentElem.eq
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    change (1 - quantumDoubleKLocalProjector) *ᵥ (quantumDoubleKLocalProjector *ᵥ w) = 0
    rw [Matrix.mulVec_mulVec, sub_mul, one_mul, hp, sub_self, Matrix.zero_mulVec]
  · intro hv
    change (1 - quantumDoubleKLocalProjector) *ᵥ v = 0 at hv
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact ⟨v, hv.symm⟩

end TNLean.PEPS
