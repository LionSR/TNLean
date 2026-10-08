/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleLocalConstraint
import TNLean.Algebra.RepresentationTensorProduct
import TNLean.Algebra.FiniteGroupUnitaryAverage
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.Algebra.PermutationMatrixCommutation

/-!
# The coherent physical bond action of the blocked quantum double

SCP10, arXiv:1001.3807v3, source lines 2918–2923: the bond term acts on
four physical spins in two neighboring blocked tensors. For an east-west
bond `q`, the shared color changes by `q ↦ u q`. Its physical action is
`(a,b,c,d;e,f,g,h) ↦ (a u⁻¹,u b,c,d;e,f,g u⁻¹,u h)`.
The normalized average is an orthogonal projector on the full eight-spin
space. It fixes the actual two-tensor contraction.

**Local fix (normalization):** The factor `|G|⁻¹`, missing from the displayed
source sum, is necessary for projector normalization. Documented in
`docs/paper-gaps/scp10_quantum_double_local_hamiltonian.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G]

/-- The four-spin action on the left block of an east-west bond. -/
def quantumDoubleKBondLeft (u : G) (x : G × G × G × G) : G × G × G × G :=
  (x.1 * u⁻¹, u * x.2.1, x.2.2.1, x.2.2.2)

/-- The four-spin action on the right block of an east-west bond. -/
def quantumDoubleKBondRight (u : G) (x : G × G × G × G) : G × G × G × G :=
  (x.1, x.2.1, x.2.2.1 * u⁻¹, u * x.2.2.2)

/-- One color change, acting coherently on the four spins bordering the bond.
The other four physical spins are unchanged. -/
def quantumDoubleKBondAction (u : G)
    (x : (G × G × G × G) × (G × G × G × G)) :
    (G × G × G × G) × (G × G × G × G) :=
  (quantumDoubleKBondLeft u x.1, quantumDoubleKBondRight u x.2)

@[simp]
theorem quantumDoubleKBondAction_one
    (x : (G × G × G × G) × (G × G × G × G)) :
    quantumDoubleKBondAction 1 x = x := by
  simp [quantumDoubleKBondAction, quantumDoubleKBondLeft, quantumDoubleKBondRight]

theorem quantumDoubleKBondAction_mul (u v : G)
    (x : (G × G × G × G) × (G × G × G × G)) :
    quantumDoubleKBondAction (u * v) x =
      quantumDoubleKBondAction u (quantumDoubleKBondAction v x) := by
  simp [quantumDoubleKBondAction, quantumDoubleKBondLeft, quantumDoubleKBondRight,
    mul_inv_rev, mul_assoc]

/-- The physical bond action as a genuine group representation by permutations. -/
def quantumDoubleKBondPermutation : G →* Equiv.Perm
    ((G × G × G × G) × (G × G × G × G)) where
  toFun u :=
    { toFun := quantumDoubleKBondAction u
      invFun := quantumDoubleKBondAction u⁻¹
      left_inv x := by rw [← quantumDoubleKBondAction_mul, inv_mul_cancel]; simp
      right_inv x := by rw [← quantumDoubleKBondAction_mul, mul_inv_cancel]; simp }
  map_one' := by apply Equiv.ext; intro x; exact quantumDoubleKBondAction_one x
  map_mul' u v := by apply Equiv.ext; intro x; exact quantumDoubleKBondAction_mul u v x

@[simp]
theorem quantumDoubleKHolonomy_bondLeft (u : G) (x : G × G × G × G) :
    quantumDoubleKHolonomy (quantumDoubleKBondLeft u x) = quantumDoubleKHolonomy x := by
  simp [quantumDoubleKHolonomy, quantumDoubleKBondLeft, mul_assoc]

@[simp]
theorem quantumDoubleKHolonomy_bondRight (u : G) (x : G × G × G × G) :
    quantumDoubleKHolonomy (quantumDoubleKBondRight u x) = quantumDoubleKHolonomy x := by
  simp [quantumDoubleKHolonomy, quantumDoubleKBondRight, mul_assoc]

/-- Exact left-block tensor intertwining, in nonabelian order. -/
theorem quantumDoubleKSpins_bondLeft (u p q r s : G) :
    quantumDoubleKSpins (p, u * q, r, s) =
      quantumDoubleKBondLeft u (quantumDoubleKSpins (p, q, r, s)) := by
  simp [quantumDoubleKSpins, quantumDoubleKBondLeft, mul_inv_rev, mul_assoc]

/-- Exact right-block tensor intertwining for the same shared color. -/
theorem quantumDoubleKSpins_bondRight (u p q r s : G) :
    quantumDoubleKSpins (p, q, r, u * s) =
      quantumDoubleKBondRight u (quantumDoubleKSpins (p, q, r, s)) := by
  simp [quantumDoubleKSpins, quantumDoubleKBondRight, mul_inv_rev, mul_assoc]

variable [Fintype G] [DecidableEq G]

/-- The physical permutation matrix sends the ket at `x` to the ket at the
coherently transformed spin tuple. -/
def quantumDoubleKBondMatrix (u : G) : Matrix
    ((G × G × G × G) × (G × G × G × G))
    ((G × G × G × G) × (G × G × G × G)) ℂ :=
  Matrix.permMatrixHom (quantumDoubleKBondPermutation u)

/-- The source's coherent bond average with the necessary normalization. -/
noncomputable def quantumDoubleKBondAverage : Matrix
    ((G × G × G × G) × (G × G × G × G))
    ((G × G × G × G) × (G × G × G × G)) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ u : G, quantumDoubleKBondMatrix u

/-- The third physical Hamiltonian term in SCP10. -/
noncomputable def quantumDoubleKBondTerm : Matrix
    ((G × G × G × G) × (G × G × G × G))
    ((G × G × G × G) × (G × G × G × G)) ℂ :=
  1 - quantumDoubleKBondAverage

/-- The normalized physical bond average is an orthogonal projector. -/
theorem quantumDoubleKBondAverage_isStarProjection :
    IsStarProjection (quantumDoubleKBondAverage (G := G)) := by
  let ρ : G →* Matrix.unitaryGroup
      ((G × G × G × G) × (G × G × G × G)) ℂ :=
    { toFun u := ⟨quantumDoubleKBondMatrix u,
        (quantumDoubleKBondPermutation u)⁻¹.permMatrix_mem_unitaryGroup⟩
      map_one' := Subtype.ext (by
        change Matrix.permMatrixHom (quantumDoubleKBondPermutation 1) = 1
        rw [map_one, map_one])
      map_mul' u v := Subtype.ext (by
        change Matrix.permMatrixHom (quantumDoubleKBondPermutation (u * v)) = _
        rw [map_mul, map_mul]; rfl) }
  exact TNLean.Algebra.isStarProjection_inv_card_smul_sum ρ

/-- The actual Hamiltonian term is the complementary orthogonal projector. -/
theorem quantumDoubleKBondTerm_isStarProjection :
    IsStarProjection (quantumDoubleKBondTerm (G := G)) :=
  quantumDoubleKBondAverage_isStarProjection.one_sub

theorem quantumDoubleKBondMatrix_mulVec (u : G)
    (v : ((G × G × G × G) × (G × G × G × G)) → ℂ) :
    quantumDoubleKBondMatrix u *ᵥ v = fun x => v (quantumDoubleKBondAction u⁻¹ x) := by
  change (quantumDoubleKBondPermutation u)⁻¹.permMatrix ℂ *ᵥ v = _
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- Equal weight means invariance under every coherent physical color change,
and is exactly the fixed-space condition for the normalized average. -/
theorem quantumDoubleKBondAverage_mulVec_eq_self_iff
    (v : ((G × G × G × G) × (G × G × G × G)) → ℂ) :
    quantumDoubleKBondAverage *ᵥ v = v ↔
      ∀ u x, v (quantumDoubleKBondAction u x) = v x := by
  let _ : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let ρ := (Matrix.permMatrixHom (R := ℂ)).comp (quantumDoubleKBondPermutation (G := G))
  let σ : Representation ℂ G (((G × G × G × G) × (G × G × G × G)) → ℂ) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ
  have havg : σ.averageMap v = quantumDoubleKBondAverage *ᵥ v := by
    rw [Representation.averageMap_apply_eq_sum]
    change (⅟(Fintype.card G : ℂ)) • ∑ u, quantumDoubleKBondMatrix u *ᵥ v = _
    rw [invOf_eq_inv, quantumDoubleKBondAverage, Matrix.smul_mulVec, Matrix.sum_mulVec]
  rw [← havg]
  constructor
  · intro h u x
    have hf := σ.averageMap_invariant v u⁻¹
    rw [h] at hf
    change quantumDoubleKBondMatrix u⁻¹ *ᵥ v = v at hf
    rw [quantumDoubleKBondMatrix_mulVec, inv_inv] at hf
    exact congrFun hf x
  · intro h
    apply σ.averageMap_id
    intro u
    change quantumDoubleKBondMatrix u *ᵥ v = v
    rw [quantumDoubleKBondMatrix_mulVec]
    exact funext (h u⁻¹)

/-- The matrix implements the stated physical ket action, fixing all
matrix-versus-pullback inverse conventions. -/
theorem quantumDoubleKBondMatrix_single (u : G)
    (x : (G × G × G × G) × (G × G × G × G)) :
    quantumDoubleKBondMatrix u *ᵥ Pi.single x 1 =
      Pi.single (quantumDoubleKBondAction u x) 1 := by
  rw [quantumDoubleKBondMatrix_mulVec]
  funext y
  have he : quantumDoubleKBondAction u⁻¹ y = x ↔ y = quantumDoubleKBondAction u x :=
    (quantumDoubleKBondPermutation u).symm_apply_eq
  simp only [Pi.single_apply, he]


/-- The actual two-block contraction over the common east-west color. The
six open colors are `(p,r,s;t,v,w)`. -/
def quantumDoubleKBondContraction : Matrix
    ((G × G × G × G) × (G × G × G × G)) ((G × G × G) × (G × G × G)) ℂ :=
  fun x b => ∑ q : G,
    quantumDoubleKTensor G b.1.1 q b.1.2.1 b.1.2.2 x.1 *
      quantumDoubleKTensor G b.2.1 b.2.2.1 b.2.2.2 q x.2

/-- The contraction coefficient is the sum of the basis kets obtained by
varying exactly the common bond, rather than a stipulated invariant state. -/
theorem quantumDoubleKBondContraction_eq (b : (G × G × G) × (G × G × G))
    (x : (G × G × G × G) × (G × G × G × G)) :
    quantumDoubleKBondContraction x b = ∑ q : G,
      if x = (quantumDoubleKSpins (b.1.1, q, b.1.2.1, b.1.2.2),
          quantumDoubleKSpins (b.2.1, b.2.2.1, b.2.2.2, q)) then 1 else 0 := by
  unfold quantumDoubleKBondContraction quantumDoubleKTensor
  apply Finset.sum_congr rfl
  intro q _
  simp only [Prod.ext_iff]
  split_ifs <;> simp_all

/-- Changing the shared color really induces the coherent four-spin action. -/
theorem quantumDoubleKBondContraction_invariant (u : G)
    (b : (G × G × G) × (G × G × G))
    (x : (G × G × G × G) × (G × G × G × G)) :
    quantumDoubleKBondContraction (quantumDoubleKBondAction u x) b =
      quantumDoubleKBondContraction x b := by
  rw [quantumDoubleKBondContraction_eq, quantumDoubleKBondContraction_eq]
  rw [← Equiv.sum_comp (Equiv.mulLeft u) (fun q : G =>
    if quantumDoubleKBondAction u x =
      (quantumDoubleKSpins (b.1.1, q, b.1.2.1, b.1.2.2),
        quantumDoubleKSpins (b.2.1, b.2.2.1, b.2.2.2, q)) then (1 : ℂ) else 0)]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Equiv.coe_mulLeft, quantumDoubleKSpins_bondLeft, quantumDoubleKSpins_bondRight]
  change (if (quantumDoubleKBondPermutation u) x =
    (quantumDoubleKBondPermutation u)
      (quantumDoubleKSpins (b.1.1, q, b.1.2.1, b.1.2.2),
        quantumDoubleKSpins (b.2.1, b.2.2.1, b.2.2.2, q)) then (1 : ℂ) else 0) = _
  simp only [(quantumDoubleKBondPermutation u).injective.eq_iff]

/-- The normalized physical bond projector fixes every open-boundary column
of the actual two-block network. -/
theorem quantumDoubleKBondAverage_contraction :
    quantumDoubleKBondAverage (G := G) * quantumDoubleKBondContraction =
      quantumDoubleKBondContraction := by
  have hfix (u : G) : quantumDoubleKBondMatrix u * quantumDoubleKBondContraction =
      quantumDoubleKBondContraction := by
    ext x b
    change (quantumDoubleKBondMatrix u *ᵥ (fun y => quantumDoubleKBondContraction y b)) x = _
    rw [quantumDoubleKBondMatrix_mulVec]
    exact quantumDoubleKBondContraction_invariant u⁻¹ b x
  rw [quantumDoubleKBondAverage, Matrix.smul_mul, Matrix.sum_mul]
  simp only [hfix, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hc, one_smul]

end TNLean.PEPS
