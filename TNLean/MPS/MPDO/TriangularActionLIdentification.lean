/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularBoundaryDecomposition
import TNLean.MPS.MPDO.BoundaryZipper
import TNLean.MPS.MPDO.BoundaryActionTreeEntries
import TNLean.MPS.MPDO.BoundaryActionLMatrix
import TNLean.MPS.MPDO.CompleteZipperFusionTrace

/-!
# The auxiliary fusion comparison is the actual action L matrix

This is an algebraic identification of constructed matrices, not a premise
of coherence. Whenever the triangular fusion/action matrices form a complete
zipper family, its forward comparison on two operator labels and one state
label is exactly the normalized-trace L matrix of the original action trees.
The physical alphabet and letters may already have been commonly blocked;
only the unchanged virtual analysis and synthesis maps enter the proof.

The row order of the auxiliary comparison is `(z,j,i)`, whereas the action
L matrix uses `(z,i,j)`. Its column order is `(c,mu,k)`, whereas L uses
`(c,k,mu)`. Neither reordering reverses the comparison: both sides are the
sequential analysis followed by fusion-then-action synthesis.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3,
`eq:F_symbol2` and `1Fsymbol`, lines 517--552.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {p r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}
  {T : ∀ q : Fin r ⊕ Fin s, MPOTensor p (triangularBondDim χ D q)}
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
  (hD : ∀ q, 0 < triangularBondDim χ D q)
  (hT : ∀ q, Kraus.IsInjective (T q).toMPSTensor)
  (hVW : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin r ⊕ Fin s) × Fin (triangularFusionMultiplicity N M a b c) ↦
        (T q.1).toMPSTensor)
      (fun q ↦ triangularFusionAnalysis VF VA a b q.1 q.2)
      (fun q ↦ triangularFusionSynthesis WF WA a b q.1 q.2))
  (K : Matrix ((c : Fin r ⊕ Fin s) ×
    (Fin (triangularBondDim χ D c) × Fin (triangularBondDim χ D c)))
      (Fin p × Fin p) ℂ)
  (hK : ∀ (c d : Fin r ⊕ Fin s)
    (x y : Fin (triangularBondDim χ D c)) (x' y' : Fin (triangularBondDim χ D d)),
    (∑ i : Fin p, ∑ k : Fin p, K ⟨c, x, y⟩ (i, k) * T d i k x' y') =
      if he : c = d then
        if _ : he ▸ x = x' then if _ : he ▸ y = y' then 1 else 0 else 0
      else 0)

local notation "F" => CompleteZipperFusionFamily.ofBiorthogonal hD hT
  (triangularFusionAnalysis VF VA) (triangularFusionSynthesis WF WA) hVW K hK

/-- The auxiliary forward F comparison is literally the original action L
matrix, with the source multiplicity orders restored. This assertion is
independent of the physical blocking used to obtain the complete family. -/
theorem triangular_printedFMatrix_eq_actionLMatrix
    (a b c : Fin r) (x y z : Fin s)
    (i : Fin (M a z y)) (j : Fin (M b x z))
    (k : Fin (M c x y)) (mu : Fin (N a b c)) :
    (F).printedFMatrix (.inl a) (.inl b) (.inr x) (.inr y)
        ⟨.inr z, j, i⟩ ⟨.inl c, mu, k⟩ =
      actionLMatrix WF VA WA a b x y ⟨z, i, j⟩ ⟨c, k, mu⟩ := by
  classical
  rw [(F).printedFMatrix_eq_inv_dim_mul_trace]
  change (D y : ℂ)⁻¹ * Matrix.trace _ = (D y : ℂ)⁻¹ * Matrix.trace
    (sequentialActionAnalysis VA a b x ⟨⟨z, j⟩, y, i⟩ *
      fusionThenActionSynthesis WF WA a b x ⟨⟨c, mu⟩, y, k⟩)
  congr 1
  congr 1
  ext u v
  simp only [Matrix.mul_apply]
  refine Fintype.sum_equiv
    ((Equiv.prodCongr (finProdFinEquiv : Fin (χ a) × Fin (χ b) ≃ Fin (χ a * χ b))
      (Equiv.refl (Fin (D x)))).trans finProdFinEquiv) _ _ ?_
  rintro ⟨⟨xa, xb⟩, xx⟩
  change
    (∑ t : Fin (D z),
      VA a z y i u (finProdFinEquiv (xa, t)) *
        VA b x z j t (finProdFinEquiv (xb, xx))) *
      (∑ t : Fin (χ c),
        WF a b c mu (finProdFinEquiv (xa, xb)) t *
          WA c x y k (finProdFinEquiv (t, xx)) v) =
    sequentialActionAnalysis VA a b x ⟨⟨z, j⟩, y, i⟩ u
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) *
      fusionThenActionSynthesis WF WA a b x ⟨⟨c, mu⟩, y, k⟩
        (finProdFinEquiv (finProdFinEquiv (xa, xb), xx)) v
  rw [sequentialActionAnalysis_apply, fusionThenActionSynthesis_apply]

end MPOTensor
