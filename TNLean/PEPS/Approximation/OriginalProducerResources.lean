/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateCircuitResources

/-!
# Original monomial counts and coefficient-sum majorants

Every produced occurrence keeps the original monomial count. Increasing an
upper bound for the coefficient sum preserves the same bound on the number
of pair effects. These elementary comparisons supply the actual expansion
bounds used in distributed compression.

Source: polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`,
lines 143–149 and 199–208, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect.OriginalCircuit

variable {P : Type}

/-- Every actual produced gate occurrence retains its original monomial-list bound.
The producer preserves the original occurrences; no bounds on private memories enter.
Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 143–149 and 199–208. -/
theorem monomialCount_produce_le {a b : Layout P} (w : OriginalCircuit a b) {K : ℕ} :
    w.IsMonomialBounded K → ∀ g : w.produce.gateLocations,
      w.produce.monomialCount g ≤ K := by
  induction w with
  | id => intro _ g; exact nomatch g
  | comp w v ihw ihv =>
      intro hK g
      cases g with
      | inl g => exact ihw hK.1 g
      | inr g => exact ihv hK.2 g
  | privateMap => intro _ g; exact nomatch g
  | nonprivateGate =>
      intro hK g
      simpa only [produce, EffectCircuit.monomialCount, IsMonomialBounded] using hK
  | swap => intro _ g; exact nomatch g
  | frame r w ih => intro hK g; exact ih hK g

/-- Increasing the coefficient-sum bound preserves the original effect-count bound.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 143–149 and 199–208. -/
theorem isExpansionBounded_mono (r : ℕ) (S S' : ℝ) (hSS : S ≤ S') :
    {a b : Layout P} → (w : OriginalCircuit a b) →
      w.IsExpansionBounded r S → w.IsExpansionBounded r S'
  | _, _, .id _, _ => True.intro
  | _, _, .comp w v, h =>
      ⟨isExpansionBounded_mono r S S' hSS w h.1,
        isExpansionBounded_mono r S S' hSS v h.2⟩
  | _, _, .privateMap .., _ => True.intro
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ _ _ _ _, h =>
      ⟨h.1, h.2.trans hSS⟩
  | _, _, .swap .., _ => True.intro
  | _, _, .frame _ w, h => isExpansionBounded_mono r S S' hSS w h

end TNLean.PEPS.PairEffect.OriginalCircuit
