/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Log
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicEntropyCover
import TNLean.PEPS.AreaLaw.Geometry.TemplateCoreCover
import TNLean.PEPS.AreaLaw.Geometry.TemplateShellCover
import TNLean.PEPS.AreaLaw.Geometry.TemplateEntropy

/-!
# Template entropy from a box estimate at real clearance

A pointwise rectangle entropy estimate at one fixed positive exponent bounds
an actual template core, its complete shells and its partial-row prefixes.
The clearance is real, and the constants are uniform over the templates.
The sufficient assumptions are a normalized pure state and the pointwise box
estimate; the Hamiltonian hypotheses enter only in obtaining that estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4 (`scanner:templates`), `08-scanner.tex`,
lines 574–590 and 641–667; the standing real safety parameter is specified
in `02-initial.tex`, lines 223–228. Revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The core, shell and prefix entropy estimates of Lemma 9.4 for real
clearance and one fixed exponent. The pointwise box hypothesis is required
only at that exponent. Replacing its constant by `max C 0` requires no sign
assumption on the supplied constant. The estimate holds for every positive exponent and
clearance at least one, hence in particular for the source range `0 < e < 1`
and its standing clearance `D₀ > 2R+10`.
Source: `scanner:templates`, `08-scanner.tex`, lines 574–590 and 641–667. -/
theorem template_entropy_bounds_of_real_safe_box
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ))
    (D₀ e C : ℝ) (hD : 1 ≤ D₀) (he : 0 < e)
    (hbox : ∀ Q : IntRect,
      (∀ x ∈ Q.toFinset, ∀ z ∈ boundaryEndpoints Λ A,
        D₀ * (Q.size : ℝ) < (supDist x z : ℝ)) →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
      24 ≤ Ctpl → T.IsSeparated D₀ (boundaryEndpoints Λ A) →
      (regionalEntropy Λ q Ω (A.filter fun x ↦ x.1 ∈ T.points) ≤
        max C 0 * (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e) ∧
      (∀ j L : ℕ, 1 ≤ L → j ≤ L → L ≤ s₀ →
        regionalEntropy Λ q Ω
          (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points) ≤
          max C 0 * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e) ∧
      (∀ j L : ℕ, 1 ≤ j → j ≤ L → L ≤ s₀ →
        ∀ Y : Finset (ℤ × ℤ),
          Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1) →
          regionalEntropy Λ q Ω
            (A.filter fun x ↦ x.1 ∈ (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
            max C 0 * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e + n * Real.log q) := by
  classical
  intro Ctpl n s₀ T hC hsep
  have hcover (S : Finset (ℤ × ℤ)) (j K : ℕ) (hj : j ≤ s₀)
      (hcap : 2 ^ K ≤ s₀) (hS : S ⊆ ambientDilation T.points j) :
      regionalEntropy Λ q Ω (A.filter fun x ↦ x.1 ∈ S) ≤
        max C 0 * (cappedDyadicPartition S K).sum
          (fun c ↦ ((2 : ℝ) ^ c.1) ^ (1 + e)) := by
    refine regionalEntropy_filter_le_weighted_cover_of_forall Λ q Ω hΩ A S K e
      (max C 0) fun c hc ↦ ?_
    obtain ⟨hk, hsub, _⟩ := (mem_cappedDyadicPartition S K c.1 c.2).mp hc
    have hsize : (latticeDyadicRect c.1 c.2).size ≤ s₀ := by
      simpa only [size_latticeDyadicRect] using
        (Nat.pow_le_pow_right (by decide) hk).trans hcap
    have hclear : ∀ x ∈ (latticeDyadicRect c.1 c.2).toFinset,
        ∀ z ∈ boundaryEndpoints Λ A,
          D₀ * ((latticeDyadicRect c.1 c.2).size : ℝ) < (supDist x z : ℝ) := by
      intro x hx z hz
      simpa only [cast_supDist] using
        hsep.side_lt_dist_of_mem_ambientDilation hD hj hsize
          (hS (hsub (by simpa only [toFinset_latticeDyadicRect] using hx))) hz
    exact (hbox (latticeDyadicRect c.1 c.2) hclear).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hshell (j L : ℕ) (hLpos : 1 ≤ L) (hj : j ≤ L) (hL : L ≤ s₀) :
      regionalEntropy Λ q Ω
        (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points) ≤
        max C 0 * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e := by
    refine (hcover (ambientDilation T.points j \ T.points) j (Nat.log 2 L)
      (hj.trans hL) ((Nat.pow_log_le_self 2 (by omega)).trans hL) Finset.sdiff_subset).trans ?_
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (T.sum_rpow_cappedDyadicPartition_shell_le hC j L (Nat.log 2 L) hj hL
        (Nat.pow_log_le_self 2 (by omega))
        (Nat.lt_pow_succ_log_self (by decide) L) e he) (le_max_right C 0)
  refine ⟨?_, hshell, ?_⟩
  · refine (hcover T.points 0 (Nat.log 2 s₀) (Nat.zero_le _)
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt T.s₀_pos)) (by simp)).trans ?_
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (T.sum_rpow_cappedDyadicPartition_core_le hC (Nat.log 2 s₀)
        (Nat.pow_log_le_self 2 (Nat.ne_of_gt T.s₀_pos))
        (Nat.lt_pow_succ_log_self (by decide) s₀) e he) (le_max_right C 0)
  · intro j L hj hjL hL Y hY
    have hs := hshell (j - 1) L (hj.trans hjL) (by omega) hL
    have hp := template_partial_row_entropy_le Λ q hq Ω hΩ T hC A j hj
      (hjL.trans hL) Y hY
    linarith only [hs, (abs_le.mp hp).2]

end TNLean.PEPS.AreaLaw.Geometry
