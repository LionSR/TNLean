/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularMixedPentagon
import TNLean.MPS.MPDO.TriangularBoundaryBlocked

/-!
# Source-derived multiplicity mixed pentagon

The exact unblocked fusion and action matrices satisfy the coupled pentagon.
Common positive blocking is used only to obtain the simultaneous inverse of
an auxiliary triangular operator family; it does not change any coefficient.
The final theorem derives those exact maps from arbitrary-boundary operator
closedness and operator/state compatibility, together with individually
injective, positive-dimensional, scalar-gauge-separated blocks.

No simultaneous word span, ambient support completeness, semisimple module
structure, unit, duality, or coherence equation is added to the source inputs.
The F coefficient is the actual analysis-oriented fusion contraction and L
is the actual sequential-analysis/fusion-synthesis contraction.

**Local fix (multiplicity indices):** The F factor uses upper `(d,eta,chi)`
and lower `(f,mu,nu)`, correcting both reversed pairs in the source display.
See `docs/paper-gaps/glm23_multiplicity_l_indices.tex`.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `algcond`,
`eq:compatible`, `Fsymbolsdef`, `eq:F_symbol2`, `coupledpent`, and Appendix A.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- Exact source fusion/action maps satisfy the actual coupled pentagon.
Individual injectivity and scalar-gauge separation derive the common
blocking needed in its proof; the conclusion uses the unblocked maps. -/
theorem actionLMatrix_mixed_pentagon
    (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor)
    (hInjA : ∀ x, Kraus.IsInjective (A x))
    (hχ : ∀ a, 0 < χ a) (hD : ∀ x, 0 < D x)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (hneA : MPSTensor.BlocksNotGaugePhaseEquiv A)
    (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
    (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
    (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
    (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (a b c e f : Fin r) (x y z t : Fin s)
    (i : Fin (M a z y)) (j : Fin (M b t z)) (k : Fin (M c x t))
    (m : Fin (M e x y)) (mu : Fin (N b c f)) (nu : Fin (N a f e)) :
    (∑ v : Fin r, ∑ n : Fin (M v t y),
      ∑ eta : Fin (N a b v), ∑ chi : Fin (N v c e),
        actionLMatrix WF VA WA a b t y ⟨z, i, j⟩ ⟨v, n, eta⟩ *
          actionLMatrix WF VA WA v c x y ⟨t, n, k⟩ ⟨e, m, chi⟩ *
          fusionFMatrix VF WF a b c e ⟨v, eta, chi⟩ ⟨f, mu, nu⟩) =
      ∑ l : Fin (M f x z),
        actionLMatrix WF VA WA b c x z ⟨t, j, k⟩ ⟨f, l, mu⟩ *
          actionLMatrix WF VA WA a f x y ⟨z, i, l⟩ ⟨e, m, nu⟩ := by
  classical
  obtain ⟨L, hL, hInj, K, hK⟩ :=
    exists_triangular_blockTensor_leftInverse O A hInjO hInjA hχ hD hneO hneA
  have hDim : ∀ q, 0 < triangularBondDim χ D q := by
    intro q
    cases q with
    | inl a => exact hχ a
    | inr x => exact hD x
  exact triangular_actionLMatrix_mixed_pentagon VF WF VA WA hDim hInj
    (fun a b ↦ (isBiorthogonalDecomposition_triangularTensor VF WF VA WA O A hF hA
      a b).blockMPO_fintype hL) K hK a b c e f x y z t i j k m mu nu

/-- Arbitrary-boundary closedness and compatibility construct exact fusion
and action maps whose actual normalized-trace coefficients satisfy GLM23's
typed coupled pentagon. There is no coherence or joint-span hypothesis. -/
theorem IsBoundaryCompatible.exists_exact_mixed_pentagon
    {T : MPOTensor d (∑ a : Fin r, χ a)}
    {B : MPSTensor d (∑ x : Fin s, D x)}
    (hClosed : IsBoundaryClosed T) (hCompatible : IsBoundaryCompatible T B)
    (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
    (hT : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun a ↦ (O a).toMPSTensor))
    (hB : B = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) A)
    (hInjO : ∀ a, Kraus.IsInjective (O a).toMPSTensor)
    (hInjA : ∀ x, Kraus.IsInjective (A x))
    (hχ : ∀ a, 0 < χ a) (hD : ∀ x, 0 < D x)
    (hneO : MPSTensor.BlocksNotGaugePhaseEquiv (fun a ↦ (O a).toMPSTensor))
    (hneA : MPSTensor.BlocksNotGaugePhaseEquiv A) :
    ∃ (N : Fin r → Fin r → Fin r → ℕ) (M : Fin r → Fin s → Fin s → ℕ)
      (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
      (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
      (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
      (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ),
      (∀ a b, MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2)) ∧
      (∀ a x, MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2)) ∧
      ∀ (a b c e f : Fin r) (x y z t : Fin s)
        (i : Fin (M a z y)) (j : Fin (M b t z)) (k : Fin (M c x t))
        (m : Fin (M e x y)) (mu : Fin (N b c f)) (nu : Fin (N a f e)),
        (∑ v : Fin r, ∑ n : Fin (M v t y),
          ∑ eta : Fin (N a b v), ∑ chi : Fin (N v c e),
            actionLMatrix WF VA WA a b t y ⟨z, i, j⟩ ⟨v, n, eta⟩ *
              actionLMatrix WF VA WA v c x y ⟨t, n, k⟩ ⟨e, m, chi⟩ *
              fusionFMatrix VF WF a b c e ⟨v, eta, chi⟩ ⟨f, mu, nu⟩) =
          ∑ l : Fin (M f x z),
            actionLMatrix WF VA WA b c x z ⟨t, j, k⟩ ⟨f, l, mu⟩ *
              actionLMatrix WF VA WA a f x y ⟨z, i, l⟩ ⟨e, m, nu⟩ := by
  classical
  choose N VF WF hF using fun a b ↦
    hClosed.exists_blockFusionDecomposition_of_isInjective O hT hInjO hχ hneO a b
  choose M VA WA hA using fun a x ↦
    hCompatible.exists_blockActionDecomposition_of_isInjective
      O A hT hB hInjA hD hneA a x
  exact ⟨N, M, VF, WF, VA, WA, hF, hA,
    actionLMatrix_mixed_pentagon O A hInjO hInjA hχ hD hneO hneA
      VF WF VA WA hF hA⟩

end MPOTensor
