/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicEntropyCover
import TNLean.PEPS.AreaLaw.Geometry.RectangleShellWeightedCover
import TNLean.PEPS.AreaLaw.WeakRectangleShellSafety

/-!
# Entropy of a weak-rectangle shell from a safe-box estimate

A pointwise safe-box estimate and the parent's safe-box clearance bound
the entropy of its actual physical shell. The weighted partition and
the safety of all selected squares are derived from the rectangle.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, proof of Proposition 9.5,
08-scanner.tex, lines 717–729,
at openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
This is a conditional shell estimate, not the one-step entropy improvement
or Proposition 9.5 itself.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- The actual shell entropy under a pointwise estimate on safe rectangles.
Source: proof of Proposition 9.5, 08-scanner.tex, lines 717–729.
The explicit scalar budget supplies the selected squares' clearance. -/
theorem IntRect.regionalEntropy_shell_le_of_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (Q : IntRect) (hsafe : IsSafe Λ A D₀ Q)
    (j L K : ℕ) (hj : j ≤ L) (hL : L ≤ Q.size)
    (hlo : 2 ^ K ≤ L) (hhi : L < 2 ^ (K + 1))
    (hbudget : D₀ * L + L ≤ D₀ * Q.size)
    (e C : ℝ) (he : 0 < e) (hC : 0 ≤ C)
    (hbox : ∀ Q' : IntRect, IsSafe Λ A D₀ Q' →
      regionalEntropy Λ q Ω (rectRegion A Q') ≤ C * (Q'.size : ℝ) ^ (1 + e)) :
    regionalEntropy Λ q Ω
      (A.filter fun x ↦ x.1 ∈ (Q.dilate j).toFinset \ Q.toFinset) ≤
      C * (24 + 64 / ((2 : ℝ) ^ e - 1)) * (Q.size : ℝ) * (L : ℝ) ^ e := by
  have hsafeCells : ∀ c ∈ Geometry.cappedDyadicPartition
      ((Q.dilate j).toFinset \ Q.toFinset) K,
      IsSafe Λ A D₀ (Geometry.latticeDyadicRect c.1 c.2) := by
    intro c hc
    exact hsafe.isSafe_cappedDyadicPartition_shell j L K c.1 c.2 hj hlo hbudget hc
  have hcover := Geometry.regionalEntropy_filter_le_weighted_cover
    Λ q D₀ Ω hΩ A ((Q.dilate j).toFinset \ Q.toFinset) K e C hsafeCells hbox
  have hweighted := mul_le_mul_of_nonneg_left
    (Q.sum_rpow_cappedDyadicPartition_shell_le j L K hj hL hlo hhi e he) hC
  exact hcover.trans (by simpa only [mul_assoc] using hweighted)

end TNLean.PEPS.AreaLaw
