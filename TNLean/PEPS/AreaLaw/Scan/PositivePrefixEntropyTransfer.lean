/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixComparison
import TNLean.PEPS.AreaLaw.Scan.Budgets
import TNLean.PEPS.AreaLaw.TwoFamilies
import TNLean.PEPS.AreaLaw.RegionalEntropyContinuity

/-!
# Entropy transfer on positive-depth prefixes

An entropy bound for the original vector on every whole-row positive-depth
prefix transfers to the same supplied truncated vector. The compact-region
cardinality bound and the actual quantitative truncation estimate give one
threshold before the domain, vectors, depth function and prefixes.

The original entropy bound is an explicit hypothesis, as in the scanner
proposition. No Hamiltonian, truncated vector or comparison family is chosen
here. The depth identification and geometric size estimate are supplied by
their separate geometric applications.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `08-scanner.tex`, `scanner:entropy-input`, lines 353--357,
and its continuity argument, lines 399--404; `01-preliminaries.tex`,
Lemma 2.1, lines 33--46; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit threshold `truncationEntropyThreshold q g Cvol` transfers the original
entropy bound to every positive-depth prefix in the same truncated vector. The actual global
trace distance retains the normalized gap coefficient, and the dimension
bound concerns only the compact region. The threshold is independent of
the entropy coefficient and exponent as well as the supplied finite system.
Source: `08-scanner.tex`, lines 353--357 and 399--404, at the manuscript
revision stated in the module documentation. -/
theorem regionalEntropy_positiveDepthPrefix_le_of_truncationEntropyThreshold_le
    (q : ℕ) (hq : 1 ≤ q) (g Cvol : ℝ) (hg : 0 < g) {n : ℕ}
    (hthr : truncationEntropyThreshold q g Cvol ≤ n) :
    ∀ (Λ : Finset (ℤ × ℤ)) (Ω Ωt : StateSpace Λ q),
    ‖Ω‖ = 1 → ‖Ωt‖ = 1 →
    ∀ (A : Finset (Site Λ)) (depth : Site Λ → ℤ) (L : ℕ),
    ((depthPrefix A depth (L : ℤ)).card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
    Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
        (Matrix.vecMulVec Ω (star Ω)) ≤
      Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
    ∀ Ce e : ℝ,
    (∀ j : ℕ, j ≤ L →
      regionalEntropy Λ q Ω (positiveDepthPrefix A depth (j : ℤ)) ≤
        Ce * ((n : ℝ) * (L : ℝ) ^ e + n)) →
    ∀ j : ℕ, j ≤ L →
      regionalEntropy Λ q Ωt (positiveDepthPrefix A depth (j : ℤ)) ≤
        Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ) := by
  classical
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hcost := continuityCost_le_of_fixed_coefficient_of_threshold_le
    (Real.sqrt (2 / g)) (max 4 Cvol) (Real.log q)
    (Real.sqrt_nonneg _) (le_trans (by norm_num) (le_max_left _ _))
    (Real.log_nonneg hq') hthr
  intro Λ Ω Ωt hΩ hΩt A depth L hcard hdist Ce e hentropy j hj
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  set R := positiveDepthPrefix A depth (j : ℤ) with hR
  -- Entropy continuity in the regional dimension.
  have hcont := abs_regionalEntropy_sub_le_sqrt_traceDistance Λ q Ωt Ω hΩt hΩ R
  set t := Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
      (Matrix.vecMulVec Ω (star Ω)) with ht
  -- The region is contained in the full prefix, so its volume is controlled.
  have hsub : R ⊆ depthPrefix A depth (L : ℤ) := by
    rw [hR]
    intro x hx
    simp only [positiveDepthPrefix, Finset.mem_filter] at hx
    simp only [depthPrefix, Finset.mem_filter]
    exact ⟨hx.1, hx.2.2.trans (by exact_mod_cast hj)⟩
  have hcardle : (R.card : ℝ) ≤ (max 4 Cvol) * (n : ℝ) ^ 2 := by
    have hcard1 : (R.card : ℝ) ≤ ((depthPrefix A depth (L : ℤ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    refine hcard1.trans (hcard.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right 4 Cvol) (by positivity)
  -- The actual trace distance stays below the threshold of the continuity estimate.
  have hhalf : Real.sqrt ((n : ℝ) ^ (-1000 : ℝ)) = (n : ℝ) ^ (-500 : ℝ) := by
    have h1 : (n : ℝ) ^ (-1000 : ℝ) = ((n : ℝ) ^ (-500 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (-500 : ℝ)) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      norm_num
    rw [h1, Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have htbound : t ≤ Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by
    refine hdist.trans ?_
    have hmin : min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) ≤ (n : ℝ) ^ (-1000 : ℝ) := min_le_left _ _
    have h2g : (0 : ℝ) ≤ 2 / g := div_nonneg (by norm_num) hg.le
    have hle : 2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g ≤ 2 * (n : ℝ) ^ (-1000 : ℝ) / g := by
      rw [show 2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g
            = (2 / g) * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) by ring,
        show 2 * (n : ℝ) ^ (-1000 : ℝ) / g = (2 / g) * (n : ℝ) ^ (-1000 : ℝ) by ring]
      exact mul_le_mul_of_nonneg_left hmin h2g
    calc Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g)
        ≤ Real.sqrt (2 * (n : ℝ) ^ (-1000 : ℝ) / g) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (2 / g) * (n : ℝ) ^ (-500 : ℝ) := by
          rw [show 2 * (n : ℝ) ^ (-1000 : ℝ) / g = (2 / g) * (n : ℝ) ^ (-1000 : ℝ) by ring,
            Real.sqrt_mul h2g, hhalf]
  -- The continuity cost on this region is at most `n^{-247}`.
  have hBcost : 4 * Real.sqrt t * (1 + (R.card : ℝ) * Real.log q) ≤ (n : ℝ) ^ (-247 : ℝ) := by
    refine le_trans ?_ (hcost t htbound)
    have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    have h4C : (4 : ℝ) ≤ max 4 Cvol := le_max_left 4 Cvol
    have hC0 : (0 : ℝ) ≤ max 4 Cvol := le_trans (by norm_num) h4C
    have hfacpos : (0 : ℝ) ≤ 1 + (R.card : ℝ) * Real.log q := by
      have := mul_nonneg (Nat.cast_nonneg R.card) hlq; linarith
    have hfac1 : 1 + (R.card : ℝ) * Real.log q ≤
        1 + (max 4 Cvol) * (n : ℝ) ^ 2 * Real.log q := by
      have := mul_le_mul_of_nonneg_right hcardle hlq; linarith
    calc 4 * Real.sqrt t * (1 + (R.card : ℝ) * Real.log q)
        ≤ (max 4 Cvol) * Real.sqrt t * (1 + (R.card : ℝ) * Real.log q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4C hst) hfacpos
      _ ≤ (max 4 Cvol) * Real.sqrt t * (1 + (max 4 Cvol) * (n : ℝ) ^ 2 * Real.log q) :=
          mul_le_mul_of_nonneg_left hfac1 (mul_nonneg hC0 hst)
  -- Combine with the continuity difference and the original prefix bound.
  have heΩ := hentropy j hj
  rw [← hR] at heΩ
  have hupper : regionalEntropy Λ q Ωt R ≤
      regionalEntropy Λ q Ω R + 4 * Real.sqrt t * (1 + (R.card : ℝ) * Real.log q) := by
    have habs := le_abs_self (regionalEntropy Λ q Ωt R - regionalEntropy Λ q Ω R)
    linarith [hcont, habs]
  linarith [heΩ, hupper, hBcost]

/-- A single large-scale threshold transfers the original entropy bound to
every positive-depth prefix in the same truncated vector. The actual global
trace distance retains the normalized gap coefficient, and the dimension
bound concerns only the compact region. The threshold is independent of
the entropy coefficient and exponent as well as the supplied finite system.
Source: `08-scanner.tex`, lines 353--357 and 399--404, at the manuscript
revision stated in the module documentation. -/
theorem eventually_regionalEntropy_positiveDepthPrefix_le
    (q : ℕ) (hq : 1 ≤ q) (g Cvol : ℝ) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (Λ : Finset (ℤ × ℤ)) (Ω Ωt : StateSpace Λ q),
      ‖Ω‖ = 1 → ‖Ωt‖ = 1 →
      ∀ (A : Finset (Site Λ)) (depth : Site Λ → ℤ) (L : ℕ),
      ((depthPrefix A depth (L : ℤ)).card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
      Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
          (Matrix.vecMulVec Ω (star Ω)) ≤
        Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
      ∀ Ce e : ℝ,
      (∀ j : ℕ, j ≤ L →
        regionalEntropy Λ q Ω (positiveDepthPrefix A depth (j : ℤ)) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ e + n)) →
      ∀ j : ℕ, j ≤ L →
        regionalEntropy Λ q Ωt (positiveDepthPrefix A depth (j : ℤ)) ≤
          Ce * ((n : ℝ) * (L : ℝ) ^ e + n) + (n : ℝ) ^ (-247 : ℝ) :=
  eventually_atTop.2 ⟨_, fun _ =>
    regionalEntropy_positiveDepthPrefix_le_of_truncationEntropyThreshold_le q hq g Cvol hg⟩

end TNLean.PEPS.AreaLaw.Scan
