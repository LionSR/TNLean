/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The minimizing phase in the polynomial-PEPS error

The target error of the polynomial-PEPS theorem is printed as a minimum over a
global phase. The distance `θ ↦ ‖u - e^{iθ} v‖` is continuous and `2π`-periodic,
so it attains its minimum, and an error bound for some phase is the same as an
error bound for the infimum over all phases.

## Main results

* `exists_phase_isMinOn`: the phase distance attains its minimum.
* `exists_phase_le_iff_iInf_le`: a bound at some phase is a bound on the infimum.
* `hasPEPSApproximation_iff_iInf`: the minimum-phase form of `HasPEPSApproximation`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 1.1 and `eq:target-error`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Complex

namespace TNLean.PEPS.Approximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The distance from `u` to the phase rotations of `v` attains its minimum.
Source: polynomial-PEPS `eq:target-error`, where the minimum over phases is printed. -/
theorem exists_phase_isMinOn (u v : E) :
    ∃ θ₀ : ℝ, ∀ θ : ℝ,
      ‖u - exp ((θ₀ : ℂ) * I) • v‖ ≤ ‖u - exp ((θ : ℂ) * I) • v‖ := by
  set f : ℝ → ℝ := fun θ ↦ ‖u - exp ((θ : ℂ) * I) • v‖
  have hf : Continuous f := by fun_prop
  have hp : Function.Periodic f (2 * Real.pi) := fun θ ↦ by
    simp only [f]
    have h := exp_mul_I_periodic (θ : ℂ)
    simp only at h
    push_cast
    rw [h]
  obtain ⟨m, ⟨θ₀, rfl⟩, hm⟩ :=
    (Function.Periodic.compact_of_continuous hp Real.two_pi_pos.ne' hf).exists_isLeast
      (Set.range_nonempty f)
  exact ⟨θ₀, fun θ ↦ hm ⟨θ, rfl⟩⟩

/-- An error bound at some phase is an error bound on the infimum over phases.
Source: polynomial-PEPS `eq:target-error`. -/
theorem exists_phase_le_iff_iInf_le (u v : E) (ε : ℝ) :
    (∃ θ : ℝ, ‖u - exp ((θ : ℂ) * I) • v‖ ≤ ε) ↔
      ⨅ θ : ℝ, ‖u - exp ((θ : ℂ) * I) • v‖ ≤ ε := by
  have hbdd : BddBelow (Set.range fun θ : ℝ ↦ ‖u - exp ((θ : ℂ) * I) • v‖) :=
    ⟨0, by rintro _ ⟨θ, rfl⟩; exact norm_nonneg _⟩
  constructor
  · rintro ⟨θ, hθ⟩
    exact (ciInf_le hbdd θ).trans hθ
  · intro h
    obtain ⟨θ₀, hθ₀⟩ := exists_phase_isMinOn u v
    exact ⟨θ₀, (le_ciInf hθ₀).trans h⟩

/-- `HasPEPSApproximation` with the error measured as the minimum over global phases,
as printed in the source. Source: polynomial-PEPS Theorem 1.1 and `eq:target-error`. -/
theorem hasPEPSApproximation_iff_iInf (C c : ℝ) (L q : ℕ) (Ω : StateSpace L q) :
    HasPEPSApproximation C c L q Ω ↔
      ∃ A : Tensor (squareLatticeGraph L L) q,
        (∀ e, 0 < A.bondDim e) ∧
        (∀ e, (A.bondDim e : ℝ) ≤ C * (L : ℝ) ^ c) ∧
        pepsVector A ≠ 0 ∧
        ⨅ θ : ℝ, ‖((‖pepsVector A‖⁻¹ : ℝ) : ℂ) • pepsVector A -
          exp ((θ : ℂ) * I) • Ω‖ ≤ (L : ℝ)⁻¹ := by
  simp only [HasPEPSApproximation, exists_phase_le_iff_iInf_le]

end TNLean.PEPS.Approximation
