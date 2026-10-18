/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Log
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicEntropyCover
import TNLean.PEPS.AreaLaw.Geometry.TemplateCoreCover
import TNLean.PEPS.AreaLaw.Geometry.TemplateShellCover
import TNLean.PEPS.AreaLaw.Geometry.TemplateSafeRectangles
import TNLean.PEPS.AreaLaw.Geometry.TemplateEntropy

/-!
# Template entropy from a safe-box estimate

The actual dyadic partition induces disjoint native rectangle regions whose union
is the physical filtered region. Subadditivity, the pointwise safe-box input,
and the proved weighted coverings bound the core and shells. The existing
partial-row theorem then bounds arbitrary prefixes. The input is an estimate
for every safe rectangle, not for the desired template regions.

These results use natural clearance. The final theorem additionally assumes
box estimates at every exponent in `(0, 1)`. The corresponding statement
at one fixed positive exponent and real clearance is proved by
`template_entropy_bounds_of_real_safe_box` in `TemplateBoxEntropyReal`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4, `08-scanner.tex`, lines 574–590 and 641–667,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
This conditional entropy component does not assert the full lemma or derive
an arbitrary exponent from the initial existential safe-box exponent.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Core entropy from a uniform estimate on every safe native rectangle.
The weighted count and safety are derived from the actual template. -/
theorem Template.regionalEntropy_core_le_of_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (K : ℕ) (hlo : 2 ^ K ≤ s₀) (hhi : s₀ < 2 ^ (K + 1))
    (e C : ℝ) (he : 0 < e) (hCbox : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    regionalEntropy Λ q Ω (A.filter fun x ↦ x.1 ∈ T.points) ≤
      C * (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e := by
  have h := regionalEntropy_filter_le_weighted_cover Λ q D₀ Ω hΩ A T.points K e C
    (fun c hc ↦ hsep.isSafe_cappedDyadicPartition_core hD K c.1 c.2 hlo hc) hbox
  have hw := mul_le_mul_of_nonneg_left
    (T.sum_rpow_cappedDyadicPartition_core_le hC K hlo hhi e he) hCbox
  exact h.trans (by simpa only [mul_assoc] using hw)

/-- Shell entropy from the same safe-box estimate, including the empty shell. -/
theorem Template.regionalEntropy_shell_le_of_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j L K : ℕ) (hj : j ≤ L) (hL : L ≤ s₀)
    (hlo : 2 ^ K ≤ L) (hhi : L < 2 ^ (K + 1))
    (e C : ℝ) (he : 0 < e) (hCbox : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    regionalEntropy Λ q Ω
      (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points) ≤
      C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e := by
  have h := regionalEntropy_filter_le_weighted_cover Λ q D₀ Ω hΩ A
    (ambientDilation T.points j \ T.points) K e C
    (fun c hc ↦ hsep.isSafe_cappedDyadicPartition_shell hD j K c.1 c.2
      (hj.trans hL) (hlo.trans hL) hc) hbox
  have hw := mul_le_mul_of_nonneg_left
    (T.sum_rpow_cappedDyadicPartition_shell_le hC j L K hj hL hlo hhi e he) hCbox
  exact h.trans (by simpa only [mul_assoc] using hw)

/-- A partial final row adds at most `n log q` to the shell entropy estimate.
This includes arbitrary subsets of that row; no row-order hypothesis is added. -/
theorem Template.regionalEntropy_prefix_le_of_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (hq : 1 ≤ q)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ))
    {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j L K : ℕ) (hj : 1 ≤ j) (hjL : j ≤ L) (hL : L ≤ s₀)
    (hlo : 2 ^ K ≤ L) (hhi : L < 2 ^ (K + 1))
    (Y : Finset (ℤ × ℤ))
    (hY : Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1))
    (e C : ℝ) (he : 0 < e) (hCbox : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    regionalEntropy Λ q Ω
      (A.filter fun x ↦ x.1 ∈ (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
      C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e + n * Real.log q := by
  have hs := Template.regionalEntropy_shell_le_of_safe_box Λ q D₀ Ω hΩ A T hC hsep hD
    (j - 1) L K (by omega) hL hlo hhi e C he hCbox hbox
  have hp := template_partial_row_entropy_le Λ q hq Ω hΩ T hC A j hj
    (hjL.trans hL) Y hY
  have hu := (abs_le.mp hp).2
  linarith

/-- A safe-box estimate explicitly quantified over every source exponent supplies
one nonnegative constant, uniform over all actual templates, for the core,
full shells and partial-row prefixes. The geometric factors remain explicit.
This is conditional on that safe-box input; it does not produce it from the
existence of a single initial exponent. -/
theorem exists_template_entropy_bounds_of_arbitrary_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (hq : 1 ≤ q) (hD : 1 ≤ D₀)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ))
    (hbox : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : IntRect, IsSafe Λ A D₀ Q →
        regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + ε))
    (e : ℝ) (he : 0 < e) (he₁ : e < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
      24 ≤ Ctpl → T.IsSeparated D₀ (boundaryEndpoints Λ A) →
      (regionalEntropy Λ q Ω (A.filter fun x ↦ x.1 ∈ T.points) ≤
        C * (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e) ∧
      (∀ j L : ℕ, 1 ≤ L → j ≤ L → L ≤ s₀ →
        regionalEntropy Λ q Ω
          (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points) ≤
          C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e) ∧
      (∀ j L : ℕ, 1 ≤ j → j ≤ L → L ≤ s₀ →
        ∀ Y : Finset (ℤ × ℤ),
          Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1) →
          regionalEntropy Λ q Ω
            (A.filter fun x ↦ x.1 ∈ (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
            C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e + n * Real.log q) := by
  obtain ⟨C, hCbox, hb⟩ := hbox e he he₁
  refine ⟨C, hCbox, ?_⟩
  intro Ctpl n s₀ T hC hsep
  refine ⟨?_, ?_, ?_⟩
  · exact Template.regionalEntropy_core_le_of_safe_box Λ q D₀ Ω hΩ A T hC hsep hD
      (Nat.log 2 s₀) (Nat.pow_log_le_self 2 (Nat.ne_of_gt T.s₀_pos))
      (Nat.lt_pow_succ_log_self (by decide) s₀) e C he hCbox hb
  · intro j L hLpos hj hL
    exact Template.regionalEntropy_shell_le_of_safe_box Λ q D₀ Ω hΩ A T hC hsep hD
      j L (Nat.log 2 L) hj hL (Nat.pow_log_le_self 2 (by omega))
      (Nat.lt_pow_succ_log_self (by decide) L) e C he hCbox hb
  · intro j L hj hjL hL Y hY
    exact Template.regionalEntropy_prefix_le_of_safe_box Λ q D₀ hq Ω hΩ A T hC hsep hD
      j L (Nat.log 2 L) hj hjL hL (Nat.pow_log_le_self 2 (by omega))
      (Nat.lt_pow_succ_log_self (by decide) L) Y hY e C he hCbox hb

end TNLean.PEPS.AreaLaw.Geometry
