/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Matrix-unit registers in products of operator tensors

For a matrix `Z` indexed by a register and a second space, its register blocks
reconstruct `Z` as `∑ a,b, E_ab ⊗ Z_ab`. Consequently the intermediate register
in a stacked operator-tensor letter can be contracted exactly, leaving the
outer matrix unit as a separate factor. The result holds for all letters and
arbitrary matrices over a commutative semiring.

Source: `Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, section 0,
and `Model.half` and `twisted_fusion_lhs` in
`Notes/OpenProblemsTN/checks/round45_p6_ising_twist.py`. The identities are stated
here independently of the construction record. They provide the register
contraction needed before the fusion of the reduced Ising letters; the full
boundary-fusion scope is recorded in
`docs/paper-gaps/tnlean_ising_three_object_twist_scope.tex`.
-/

open scoped Matrix Kronecker BigOperators

namespace Matrix

/-- Reconstruct a matrix from its register blocks by tensoring each block with
its matrix unit. This is the register identity used in the construction record
`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, section 0. -/
theorem sum_single_kronecker_submatrix
    {R r k : Type*} [CommSemiring R] [Fintype r] [DecidableEq r]
    (Z : Matrix (r × k) (r × k) R) :
    (∑ a : r, ∑ b : r, Matrix.single a b (1 : R) ⊗ₖ
      Z.submatrix (fun i => (a, i)) (fun j => (b, j))) = Z := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [Matrix.sum_apply, Matrix.single_apply, Matrix.submatrix_apply, ite_and]

end Matrix

namespace MPOTensor

/-- Reassociate the two bond spaces so that the outer register is the last
factor: `((v,a),(i,b)) ↦ ((v,(a,i)),b)`. This is the factor order used for the
full stacked boundary tensor in the construction record
`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, section 0. -/
def registerFusionEquiv (V r k : Type*) :
    ((V × r) × (k × r)) ≃ ((V × (r × k)) × r) where
  toFun := fun ((v, a), (i, b)) => ((v, (a, i)), b)
  invFun := fun ((v, (a, i)), b) => ((v, a), (i, b))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The exact contraction of the intermediate matrix-unit register in a
stacked operator-tensor letter. Every horizontal and register label is summed;
the result retains the outer matrix unit as its last factor.

This is the general register contraction underlying section 0 of
`Notes/OpenProblemsTN/checks/asym_ising_action_data.md` and the reduced letter
`twisted_fusion_lhs` in `checks/round45_p6_ising_twist.py`. -/
theorem registerFusion_contraction
    {R H V r k : Type*} [CommSemiring R] [Fintype H] [Fintype r] [DecidableEq r]
    (X : H → Matrix V V R) (Z : H → Matrix (r × k) (r × k) R) (c d : r) :
    (∑ h : H, ∑ a : r, ∑ b : r,
      (X h ⊗ₖ Matrix.single a b (1 : R)) ⊗ₖ
        ((Z h).submatrix (fun i => (a, i)) (fun j => (b, j)) ⊗ₖ
          Matrix.single c d (1 : R))).submatrix
      (registerFusionEquiv V r k).symm (registerFusionEquiv V r k).symm =
    (∑ h, X h ⊗ₖ Z h) ⊗ₖ Matrix.single c d (1 : R) := by
  ext ⟨⟨v, ⟨a, i⟩⟩, c'⟩ ⟨⟨w, ⟨b, j⟩⟩, d'⟩
  simp only [Matrix.submatrix_apply, registerFusionEquiv, Equiv.coe_fn_symm_mk, Matrix.sum_apply,
    Matrix.kronecker_apply]
  simp [Matrix.single_apply, ite_and]

end MPOTensor
