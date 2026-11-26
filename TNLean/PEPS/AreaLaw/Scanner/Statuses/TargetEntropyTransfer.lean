/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Collar.Scales.Budgets
import QICLean.ManyBody.Entropy.MutualInformationPerturbation

/-!
# Target entropy transfer for the same quantitative truncation

The regional continuity bound and the actual target-window trace distance
give a uniform `n^(-247)` entropy discrepancy on every region of controlled
quadratic volume. Both vectors and the region are supplied. The threshold
precedes all finite physical data and every later entropy bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 399–404; Lemma 2.1 in `01-preliminaries.tex`, lines 33–46,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.abs_regionEntropy_sub_le_sqrt_traceDistance_card`: regional entropy
  continuity on a finite lattice.
-/

section RegionalEntropyContinuity

/-!
## Regional entropy continuity on a finite lattice

For two normalized vectors on the same finite lattice, the entropy change
on a fixed region is bounded by the global trace distance and the number of
sites in that region. The dimension factor is `1 + |A| log q`.

The statement makes no geometric or Hamiltonian assumption and includes
empty regions and local dimension one. Both vectors are supplied; the
argument makes no further choice of state.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, Lemma 2.1 (`01-preliminaries.tex`, lines 33–46), as used in
`08-scanner.tex`, lines 399–404, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The Lean proof follows the argument of Lemma 2.1 rather than transcribing its text.
-/

namespace TNLean.PEPS.AreaLaw

/-- Regional entropy continuity with the dimension of the actual region.
Source: Lemma 2.1, `01-preliminaries.tex`, lines 33–46, and its application
in `08-scanner.tex`, lines 399–404. -/
theorem abs_regionEntropy_sub_le_sqrt_traceDistance_card
    (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω Φ : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1) (hΦ : ‖Φ‖ = 1)
    (A : Finset ↥Λ) :
    |ManyBody.regionEntropy Ω A - ManyBody.regionEntropy Φ A| ≤
      4 * Real.sqrt (Matrix.traceDistance
        (Matrix.vecMulVec Ω (star Ω)) (Matrix.vecMulVec Φ (star Φ))) *
        (1 + (A.card : ℝ) * Real.log q) := by
  have h := ManyBody.abs_regionEntropy_sub_le_sqrt_traceDistance
    (fun _ : ↥Λ ↦ Fin q) Ω Φ hΩ hΦ A
  have hdim :
      (Fintype.card (ManyBody.RegionConfig (fun _ : ↥Λ ↦ Fin q) A) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr
      (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one
        (ManyBody.trace_regionState_eq_one hΩ (D := A))))).ne'
  rw [Real.log_mul (Real.exp_ne_zero 1) hdim] at h
  simpa [Nat.cast_pow, Real.log_pow] using h

end TNLean.PEPS.AreaLaw

end RegionalEntropyContinuity

section TargetEntropyTransfer

open Filter

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- The same actual trace-distance estimate controls the target entropy, uniformly over all
regions of the supplied quadratic volume bound, at every `n` from the explicit threshold
`truncationEntropyThreshold q g Cvol` on. Source: `08-scanner.tex`, lines 399–404. -/
theorem abs_regionEntropy_sub_le_of_truncationEntropyThreshold_le
    (q : ℕ) (hq : 1 ≤ q) (g Cvol : ℝ) (hg : 0 < g) {n : ℕ}
    (hthr : truncationEntropyThreshold q g Cvol ≤ n) :
    ∀ (Λ : Finset (ℤ × ℤ)) (Ω Ωt : EuclideanSpace ℂ (↥Λ → Fin q)),
    ‖Ω‖ = 1 → ‖Ωt‖ = 1 → ∀ X : Finset ↥Λ,
    (X.card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
    Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
        (Matrix.vecMulVec Ω (star Ω)) ≤
      Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
    |ManyBody.regionEntropy Ωt X - ManyBody.regionEntropy Ω X| ≤
      (n : ℝ) ^ (-247 : ℝ) := by
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hcost := continuityCost_le_of_fixed_coefficient_of_threshold_le
    (Real.sqrt (2 / g)) (max 4 Cvol) (Real.log q)
    (Real.sqrt_nonneg _) (le_trans (by norm_num) (le_max_left _ _)) hlq hthr
  intro Λ Ω Ωt hΩ hΩt X hcard hdist
  set t := Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
    (Matrix.vecMulVec Ω (star Ω)) with ht
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
  have hcard' : (X.card : ℝ) ≤ (max 4 Cvol) * (n : ℝ) ^ 2 :=
    hcard.trans (mul_le_mul_of_nonneg_right (le_max_right 4 Cvol) (sq_nonneg _))
  have hcont := abs_regionEntropy_sub_le_sqrt_traceDistance_card Λ q Ωt Ω hΩt hΩ X
  refine hcont.trans ?_
  calc
    4 * Real.sqrt t * (1 + (X.card : ℝ) * Real.log q) ≤
        (max 4 Cvol) * Real.sqrt t *
          (1 + (max 4 Cvol) * (n : ℝ) ^ 2 * Real.log q) := by
      gcongr
      exact le_max_left 4 Cvol
    _ ≤ (n : ℝ) ^ (-247 : ℝ) := hcost t htbound

/-- The same actual trace-distance estimate controls the target entropy,
uniformly over all regions of the supplied quadratic volume bound.
Source: `08-scanner.tex`, lines 399–404. -/
theorem eventually_abs_regionEntropy_sub_le_of_truncation
    (q : ℕ) (hq : 1 ≤ q) (g Cvol : ℝ) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (Λ : Finset (ℤ × ℤ)) (Ω Ωt : EuclideanSpace ℂ (↥Λ → Fin q)),
      ‖Ω‖ = 1 → ‖Ωt‖ = 1 → ∀ X : Finset ↥Λ,
      (X.card : ℝ) ≤ Cvol * (n : ℝ) ^ 2 →
      Matrix.traceDistance (Matrix.vecMulVec Ωt (star Ωt))
          (Matrix.vecMulVec Ω (star Ω)) ≤
        Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) →
      |ManyBody.regionEntropy Ωt X - ManyBody.regionEntropy Ω X| ≤
        (n : ℝ) ^ (-247 : ℝ) :=
  eventually_atTop.2
    ⟨_, fun _ => abs_regionEntropy_sub_le_of_truncationEntropyThreshold_le q hq g Cvol hg⟩

end TNLean.PEPS.AreaLaw.Scan

end

end TargetEntropyTransfer
