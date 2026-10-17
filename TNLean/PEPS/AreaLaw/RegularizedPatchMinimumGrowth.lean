/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimizerDerivative
import TNLean.PEPS.AreaLaw.RegularizedPatchActualRegulatorTrace
import TNLean.PEPS.AreaLaw.RegularizedPatchMinimumContinuity
import TNLean.PEPS.AreaLaw.RegularizedPatchLogMinimum
import QICLean.Analysis.MinimumEnvelope

/-!
# Growth of the original patch minimum from its regulator bound

The logarithm of the original minimum is continuous. At each radius, one
attained minimizing tuple supplies a contacting branch whose derivative is
bounded by the regulator traces. A one-sided comparison then bounds the growth
without choosing a continuous or differentiable family of minimizing tuples.

The regulator trace bound is an explicit premise of this auxiliary theorem.
A physical application must derive it for the same minimizing outputs from the
original-state entropy and the Hamiltonian gap. This theorem alone is not the
physical patch-approximation theorem.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 421–481,
`eq:patch-minimum-growth`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {n : V → ℕ} {m : ℕ}

/-- The source growth estimate follows once the quarter-regulator estimate
holds for every original minimizer on the interval. This is an auxiliary
implication with an explicit regulator premise.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 453–481. -/
theorem log_regularizedPatchMinimum_exp_neg_le_of_regulator_trace
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (hΩ : ‖Ω‖ = 1) {Rstart R : ℝ} (hstart : 0 ≤ Rstart) (hR : Rstart ≤ R)
    (hreg : ∀ r ∈ Ico Rstart R,
      ∀ x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions,
      IsMinOn (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a (Real.exp (-r)) Ω)
        (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x →
      ∀ j : Fin m,
        (Real.exp (-r) •
          (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a (Real.exp (-r)) Ω x (regions j) *
            (x j + Real.exp (-r) • 1)⁻¹)).trace.re ≤ 1 / 4) :
    Real.log (regularizedPatchMinimum (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω) ≤
      (∑ j, a j) / 2 * (Rstart + R / 4) := by
  let κ : ℝ := ∑ j, a j
  let f := fun r x ↦ Real.log
    (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a (Real.exp (-r)) Ω x)
  let g := fun r ↦ Real.log
    (regularizedPatchMinimum (Out := fun v ↦ Fin (n v)) regions a (Real.exp (-r)) Ω)
  have ha0 (j : Fin m) : 0 ≤ a j := (ha j).le
  have hg : Continuous g :=
    continuous_log_regularizedPatchMinimum_exp_neg (Out := fun v ↦ Fin (n v)) regions a ha0 Ω hΩ
  have hle : ∀ r ∈ Icc Rstart R,
      ∀ x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions, g r ≤ f r x := by
    intro r _hr x hx
    exact (isLeast_log_regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a ha0
      (Real.exp_pos (-r)) Ω hΩ).2 (mem_image_of_mem _ hx)
  have hcontact : ∀ r ∈ Ico Rstart R,
      ∃ x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions,
      ∃ d : ℝ, f r x = g r ∧
        HasDerivWithinAt (fun z ↦ f z x) d (Ici r) r ∧ d ≤ κ / 8 := by
    intro r hr
    obtain ⟨x, hx, hmin⟩ :=
      exists_isMinOn_regularizedPatchObjective (Out := fun v ↦ Fin (n v))
        regions a (Real.exp_pos (-r)) Ω hΩ
    have hder := hasDerivAt_log_regularizedPatchObjective_exp_neg_of_isMinOn
      regions hnested a ha Ω hΩ x hx r hmin
    refine ⟨x, hx, _, congrArg Real.log
      (regularizedPatchObjective_eq_minimum (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-r)) Ω hx hmin),
      hder.hasDerivWithinAt, ?_⟩
    have hterm (j : Fin m) :
        (Matrix.trace
          (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a (Real.exp (-r)) Ω x (regions j) *
            (Real.exp (-r) • (x j + Real.exp (-r) • 1) ^ (-1 : ℝ)))).re ≤ 1 / 4 := by
      rw [← CFC.inverse_eq_rpow_neg_one
        ((hx j).1.add_smul_one_posDef (Real.exp_pos (-r))).isStrictlyPositive,
        ← Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_smul]
      exact hreg r hr x hx hmin j
    calc
      _ ≤ ∑ j : Fin m, (a j / 2) * (1 / 4) :=
        Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hterm j) (div_nonneg (ha0 j) (by norm_num))
      _ = κ / 8 := by
        rw [← Finset.sum_mul, ← Finset.sum_div]
        ring
  have hgrowth := lower_envelope_le_affine_of_hasDerivWithinAt
    hg.continuousOn hle hcontact (r := R) ⟨hR, le_rfl⟩
  have hinit : g Rstart ≤ Rstart * κ / 2 := by
    have hn := (regularizedPatchMinimum_exp_bounds (Out := fun v ↦ Fin (n v))
      regions a ha0 hstart Ω hΩ).2
    have hl := Real.log_le_log
      (regularizedPatchMinimum_pos (Out := fun v ↦ Fin (n v))
        regions a ha0 (Real.exp_pos (-Rstart)) Ω hΩ) hn
    simpa only [Real.log_exp] using hl
  have hκ : 0 ≤ κ := Finset.sum_nonneg (fun j _ ↦ ha0 j)
  change g R ≤ κ / 2 * (Rstart + R / 4)
  nlinarith [mul_nonneg hκ hstart]

/-- The original-marginal entropy and full trace-norm distance estimates imply
the source growth bound for the same actual minimum. These two estimates are
explicit premises of this auxiliary implication; a physical application must
derive them from the original area law and Hamiltonian gap.
Source: polynomial-PEPS manuscript, `03-patches.tex`, lines 362–481. -/
theorem log_regularizedPatchMinimum_exp_neg_le_of_entropy_distance
    (regions : Fin m → Finset V) (hnested : Monotone regions)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Fin (n v.1)))
    (hΩ : ‖Ω‖ = 1) {C u R : ℝ} (hC : 0 < C) (hu : 0 ≤ u)
    (hR : (16 * C + Real.log 8) * (1 + u) ≤ R)
    (hS : ∀ j : Fin m, _root_.vonNeumannEntropy
      (Entropy.regionState (regions j) (dependentGlobalConfigIsometry Ω))
      (Entropy.regionState_posSemidef (regions j)
        (dependentGlobalConfigIsometry Ω)).isHermitian ≤ C * (1 + u))
    (hd : ∀ r ∈ Ico ((16 * C + Real.log 8) * (1 + u)) R,
      ∀ x ∈ regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions,
      IsMinOn (regularizedPatchObjective (Out := fun v ↦ Fin (n v)) regions a (Real.exp (-r)) Ω)
        (regularizedPatchDomain (Out := fun v ↦ Fin (n v)) regions) x →
      ∀ j : Fin m, (CFC.abs
        (normalizedRegularizedPatchMarginal (Out := fun v ↦ Fin (n v))
            regions a (Real.exp (-r)) Ω x (regions j) -
          Entropy.regionState (regions j) (dependentGlobalConfigIsometry Ω))).trace.re ≤
        1 / 16) :
    Real.log (regularizedPatchMinimum (Out := fun v ↦ Fin (n v))
        regions a (Real.exp (-R)) Ω) ≤
      (∑ j, a j) / 2 * ((16 * C + Real.log 8) * (1 + u) + R / 4) := by
  have hstart : 0 ≤ (16 * C + Real.log 8) * (1 + u) :=
    mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hC.le)
      (Real.log_nonneg (by norm_num))) (by linarith)
  apply log_regularizedPatchMinimum_exp_neg_le_of_regulator_trace
    regions hnested a ha Ω hΩ hstart hR
  intro r hr x hx hmin j
  exact trace_regularizedPatchRegulator_le_quarter_of_isMinOn
    regions hnested a ha Ω hΩ hC hu hr.1 x hx hmin j (hS j) (hd r hr x hx hmin j)

end TNLean.PEPS
