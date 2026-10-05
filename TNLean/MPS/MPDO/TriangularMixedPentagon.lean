/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularActionLIdentification
import TNLean.MPS.MPDO.BoundaryFusionFMatrix
import TNLean.MPS.MPDO.CompleteZipperFusionMixedEntries

/-!
# Mixed pentagon of the actual fusion and action coefficients

The auxiliary operator-only inverse comparison is the original fusion F
contraction. Combined with the proved auxiliary P=L identification, its
ordinary fourfold coherence gives the coupled pentagon of the actual maps.
No mixed-pentagon, module-category, unit, or duality field is assumed.

The constructor hypotheses in this intermediate module concern the exact
auxiliary family at a suitable physical blocking. The source wrapper derives
that family from the original separated injective operator and state blocks.

**Local fix (multiplicity indices):** The fusion entry has row `(d,eta,chi)`
and column `(f,mu,nu)`. GLM23 reverses both multiplicity pairs in the printed
coupled pentagon. See `docs/paper-gaps/glm23_multiplicity_l_indices.tex`.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `coupledpent`,
lines 554--562, and `Fsymbolsdef`.
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

/-- The operator-only inverse comparison in the auxiliary family is the
actual source-oriented fusion coefficient of the original V/W maps. -/
theorem triangular_inversePrintedFMatrix_eq_fusionFMatrix
    (a b c d e f : Fin r)
    (mu : Fin (N a b e)) (nu : Fin (N e c d))
    (lambda : Fin (N b c f)) (sigma : Fin (N a f d)) :
    (F).inversePrintedFMatrix (.inl a) (.inl b) (.inl c) (.inl d)
        ⟨.inl e, mu, nu⟩ ⟨.inl f, lambda, sigma⟩ =
      fusionFMatrix VF WF a b c d ⟨e, mu, nu⟩ ⟨f, lambda, sigma⟩ := by
  rw [(F).inversePrintedFMatrix_eq_inv_dim_mul_trace]
  rfl

/-- The actual normalized-trace fusion/action coefficients obey the typed
GLM23 mixed pentagon. Both sides are derived from exact fourfold tree
comparison; every intermediate index runs over its actual multiplicity
space, which may be empty. Source: GLM23 `coupledpent`, with the corrected
fusion index order recorded above. -/
theorem triangular_actionLMatrix_mixed_pentagon
    (a b c e f : Fin r) (x y z t : Fin s)
    (i : Fin (M a z y)) (j : Fin (M b t z)) (k : Fin (M c x t))
    (m : Fin (M e x y)) (mu : Fin (N b c f)) (nu : Fin (N a f e)) :
    (∑ d : Fin r, ∑ n : Fin (M d t y),
      ∑ eta : Fin (N a b d), ∑ chi : Fin (N d c e),
        actionLMatrix WF VA WA a b t y ⟨z, i, j⟩ ⟨d, n, eta⟩ *
          actionLMatrix WF VA WA d c x y ⟨t, n, k⟩ ⟨e, m, chi⟩ *
          fusionFMatrix VF WF a b c e ⟨d, eta, chi⟩ ⟨f, mu, nu⟩) =
      ∑ l : Fin (M f x z),
        actionLMatrix WF VA WA b c x z ⟨t, j, k⟩ ⟨f, l, mu⟩ *
          actionLMatrix WF VA WA a f x y ⟨z, i, l⟩ ⟨e, m, nu⟩ := by
  classical
  have h := (F).printedFMatrix_mixed_pentagon
    (.inl a) (.inl b) (.inl c) (.inr x) (.inr y)
    (.inl f) (.inl e) (.inr t) (.inr z) mu nu m k j i
  simpa only [Fintype.sum_sum_type, triangularFusionMultiplicity,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    triangular_printedFMatrix_eq_actionLMatrix,
    triangular_inversePrintedFMatrix_eq_fusionFMatrix] using h

end MPOTensor
