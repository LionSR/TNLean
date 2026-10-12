/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionTrees

/-!
# Coordinates of the two action trees

The four analysis and synthesis maps are evaluated on the common incoming
bond `((xa, xb), xx)`. Their Kronecker identity strands remove one finite
summation, and the sequential tree's bond associator places both trees in
these same coordinates.

The formulas hold for arbitrary fusion and action maps. They introduce no
injectivity, biorthogonality, or coherence assumptions, and they include
empty intermediate bond spaces. They are the coordinate contractions needed
to compare the auxiliary fusion trees with the source action trees.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
  `eq:F_symbol2`, and `1Fsymbol`, lines 491--552.
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)

/-- Fusion followed by action: the synthesis entry contracts only the
intermediate operator bond. Source: GLM23 `rawrels`, left tree. -/
theorem fusionThenActionSynthesis_apply
    (a b c : Fin r) (x y : Fin s) (mu : Fin (N a b c)) (k : Fin (M c x y))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (z : Fin (D y)) :
    fusionThenActionSynthesis WF WA a b x ⟨⟨c, mu⟩, y, k⟩
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) z =
      ∑ v : Fin (χ c),
        WF a b c mu (finProdFinEquiv (xa, xb)) v *
          WA c x y k (finProdFinEquiv (v, xx)) z := by
  classical
  rw [fusionThenActionSynthesis, Matrix.mul_apply,
    ← Equiv.sum_comp (finProdFinEquiv :
      Fin (χ c) × Fin (D x) ≃ Fin (χ c * D x)), Fintype.sum_prod_type]
  simp [kronId, Matrix.one_apply, mul_ite, ite_mul]

/-- Two successive actions: the analysis entry in the common incoming
coordinates contracts only the intermediate state bond.
Source: GLM23 `rawrels`, right tree. -/
theorem sequentialActionAnalysis_apply
    (a b : Fin r) (x y t : Fin s) (i : Fin (M a t y)) (j : Fin (M b x t))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (z : Fin (D y)) :
    sequentialActionAnalysis VA a b x ⟨⟨t, j⟩, y, i⟩ z
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) =
      ∑ v : Fin (D t),
        VA a t y i z (finProdFinEquiv (xa, v)) *
          VA b x t j v (finProdFinEquiv (xb, xx)) := by
  classical
  rw [sequentialActionAnalysis, mulTensorAssocInvMatrix,
    PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_apply, Equiv.symm_symm, id_eq,
    mulTensorAssocEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.refl_apply, Equiv.prodAssoc_apply, Prod.map_apply, Equiv.symm_apply_apply]
  rw [Matrix.mul_apply,
    ← Equiv.sum_comp (finProdFinEquiv :
      Fin (χ a) × Fin (D t) ≃ Fin (χ a * D t)), Fintype.sum_prod_type]
  simp [idKron, Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_irrel]

/-- Fusion followed by action: the analysis entry is the reversed
contraction of the two analysis maps. Source: GLM23 `rawrels`, left tree. -/
theorem fusionThenActionAnalysis_apply
    (a b c : Fin r) (x y : Fin s) (mu : Fin (N a b c)) (k : Fin (M c x y))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (z : Fin (D y)) :
    fusionThenActionAnalysis VF VA a b x ⟨⟨c, mu⟩, y, k⟩ z
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) =
      ∑ v : Fin (χ c),
        VA c x y k z (finProdFinEquiv (v, xx)) *
          VF a b c mu v (finProdFinEquiv (xa, xb)) := by
  classical
  rw [fusionThenActionAnalysis, Matrix.mul_apply,
    ← Equiv.sum_comp (finProdFinEquiv :
      Fin (χ c) × Fin (D x) ≃ Fin (χ c * D x)), Fintype.sum_prod_type]
  simp [kronId, Matrix.one_apply, mul_ite]

/-- Two successive actions: the synthesis entry in the common incoming
coordinates contracts only the intermediate state bond.
Source: GLM23 `rawrels`, right tree. -/
theorem sequentialActionSynthesis_apply
    (a b : Fin r) (x y t : Fin s) (i : Fin (M a t y)) (j : Fin (M b x t))
    (xa : Fin (χ a)) (xb : Fin (χ b)) (xx : Fin (D x)) (z : Fin (D y)) :
    sequentialActionSynthesis WA a b x ⟨⟨t, j⟩, y, i⟩
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) z =
      ∑ v : Fin (D t),
        WA b x t j (finProdFinEquiv (xb, xx)) v *
          WA a t y i (finProdFinEquiv (xa, v)) z := by
  classical
  rw [sequentialActionSynthesis, mulTensorAssocMatrix,
    PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.submatrix_apply, id_eq,
    mulTensorAssocEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.refl_apply, Equiv.prodAssoc_apply, Prod.map_apply, Equiv.symm_apply_apply]
  rw [Matrix.mul_apply,
    ← Equiv.sum_comp (finProdFinEquiv :
      Fin (χ a) × Fin (D t) ≃ Fin (χ a * D t)), Fintype.sum_prod_type]
  simp [idKron, Matrix.one_apply, ite_mul, Finset.sum_ite_irrel]

end MPOTensor
