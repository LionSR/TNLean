/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Resolvent of a semigroup generator (Wolf Eqs. 7.6–7.9)

This file introduces the resolvent notation for semigroup generators, proves the
Neumann-series identity in the norm-small regime, and records the Euler
approximation statement as a formal predicate.
-/

open scoped Matrix Topology
open Matrix

noncomputable section

variable {D : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

abbrev GeneratorCLM (D : ℕ) :=
  Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ

/-- Resolvent of a semigroup generator, specialized to the CLM algebra.
(Wolf Eq. 7.6.) -/
noncomputable def generatorResolvent (L : GeneratorCLM D) (z : ℂ) : GeneratorCLM D :=
  resolvent L z

set_option maxHeartbeats 1200000 in
-- The CLM-instance normalization in the geometric-series proof needs extra heartbeats.
theorem inverse_one_sub_smul_generator_eq_tsum
    (L : GeneratorCLM D) {z : ℂ} (hz : ‖L‖ < ‖z‖) :
    Ring.inverse (1 - z⁻¹ • L) = ∑' n : ℕ, (z⁻¹ • L) ^ n := by
  have hz0 : z ≠ 0 := by
    intro h0
    have : ‖z‖ = 0 := by simp [h0]
    have hz' : ‖L‖ < 0 := by simpa [this] using hz
    exact (not_lt_of_ge (norm_nonneg L)) hz'
  have hnorm : ‖(z⁻¹ • L : GeneratorCLM D)‖ < 1 := by
    rw [norm_smul, norm_inv]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hdiv : ‖L‖ / ‖z‖ < 1 := (div_lt_one hzpos).2 hz
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  exact (geom_series_eq_inverse (z⁻¹ • L : GeneratorCLM D) hnorm).symm

/-- Formal statement of Wolf Eq. (7.9): Euler approximation of the semigroup
from resolvent samples. -/
def eulerApproximation
    (L : GeneratorCLM D)
    (T : ℝ → GeneratorCLM D) : Prop :=
  ∀ t : ℝ, 0 < t →
    Filter.Tendsto (fun n : ℕ => (((n : ℂ) / t) • generatorResolvent L ((n : ℂ) / t)) ^ n)
      Filter.atTop (𝓝 (T t))
