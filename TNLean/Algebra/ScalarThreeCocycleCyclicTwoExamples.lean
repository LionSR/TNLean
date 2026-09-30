/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicTwo
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Complex.Basic

/-!
# Explicit scalar three-cocycles on Z₂

The representatives ωₚ(a,b,c) = (-1)^(pabc), for p = 0,1, are normalized,
unit-modulus scalar three-cocycles with distinct gauge classes. Here a,b,c are
bits, written multiplicatively as elements of `Multiplicative (ZMod 2)`.
Only the triple of nonidentity elements can have a value other than one.
No MPU realization or physical anomaly realization is asserted.

## References

* `Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/rfp_symmetry_bridge.tex`,
  equation `bridge:z2` and the following normalized-gauge calculation.
* arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex`, lines 1676--1778,
  equation `3cocycleeq` and the fusion-tensor coboundary convention.
-/

namespace TNLean.Algebra.ScalarThreeCochain

local notation "s₂" => (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))

/-- The representative ωₚ(a,b,c) = (-1)^(pabc), with bit parameter p. -/
def cyclicTwoCocycle (p : Fin 2) : ScalarThreeCochain (Multiplicative (ZMod 2)) :=
  fun a b c => if a = s₂ ∧ b = s₂ ∧ c = s₂ then (-1) ^ p.val else 1

/-- The value of ωₚ on the generator triple is (-1)^p. -/
@[simp]
theorem cyclicTwoCocycle_generator (p : Fin 2) :
    cyclicTwoCocycle p s₂ s₂ s₂ = (-1) ^ p.val := by
  simp [cyclicTwoCocycle]

/-- The parameter zero gives the constant cocycle one. -/
@[simp]
theorem cyclicTwoCocycle_zero : cyclicTwoCocycle 0 = fun _ _ _ => 1 := by
  funext a b c
  simp [cyclicTwoCocycle]

/-- Each representative is normalized in all three arguments. -/
theorem cyclicTwoCocycle_isNormalized (p : Fin 2) :
    IsNormalized (cyclicTwoCocycle p) := by
  have h : (1 : Multiplicative (ZMod 2)) ≠ s₂ := by decide
  exact ⟨fun _ _ => by simp [cyclicTwoCocycle, h],
    fun _ _ => by simp [cyclicTwoCocycle, h],
    fun _ _ => by simp [cyclicTwoCocycle, h]⟩

private lemma bit_cases (g : Multiplicative (ZMod 2)) : g = 1 ∨ g = s₂ := by
  revert g
  decide

/-- The representatives satisfy the scalar three-cocycle equation. -/
theorem cyclicTwoCocycle_isCocycle (p : Fin 2) : IsCocycle (cyclicTwoCocycle p) := by
  have hs : s₂ * s₂ = 1 := by decide
  have hn : (1 : Multiplicative (ZMod 2)) ≠ s₂ := by decide
  intro a b c d
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
      rcases bit_cases c with rfl | rfl <;>
        rcases bit_cases d with rfl | rfl <;>
          fin_cases p <;> simp [cyclicTwoCocycle, hs, hn]

/-- All values of the representatives are phases. -/
theorem cyclicTwoCocycle_norm (p : Fin 2) (a b c : Multiplicative (ZMod 2)) :
    ‖(cyclicTwoCocycle p a b c : ℂ)‖ = 1 := by
  unfold cyclicTwoCocycle
  split_ifs <;> simp

/-- The inversion scalar is precisely the sign (-1)^p. -/
@[simp]
theorem cyclicTwoCocycle_sigma_generator (p : Fin 2) :
    sigma (cyclicTwoCocycle p) s₂ = (-1) ^ p.val := by
  have hs : s₂⁻¹ = s₂ := by decide
  simp [sigma, hs]

/-- The sign-minus representative has nontrivial scalar gauge class, even when
arbitrary (not necessarily normalized) scalar two-cochains are allowed. -/
theorem cyclicTwoCocycle_one_not_isTrivialGaugeClass :
    ¬ IsTrivialGaugeClass (cyclicTwoCocycle 1) := by
  rw [isTrivialGaugeClass_iff_sigma_generator_eq_one (cyclicTwoCocycle_isNormalized 1)]
  simp

/-- The two explicit representatives are cohomologous exactly when their
parameters agree. The gauge two-cochain is not required to be normalized. -/
theorem cyclicTwoCocycle_cohomologousTo_iff (p q : Fin 2) :
    CohomologousTo (cyclicTwoCocycle p) (cyclicTwoCocycle q) ↔ p = q := by
  constructor
  · intro h
    fin_cases p <;> fin_cases q
    · rfl
    · exact False.elim (cyclicTwoCocycle_one_not_isTrivialGaugeClass
        (by
          change CohomologousTo (cyclicTwoCocycle 0) (cyclicTwoCocycle 1) at h
          simpa only [IsTrivialGaugeClass, cyclicTwoCocycle_zero] using h.symm))
    · exact False.elim (cyclicTwoCocycle_one_not_isTrivialGaugeClass
        (by
          change CohomologousTo (cyclicTwoCocycle 1) (cyclicTwoCocycle 0) at h
          simpa only [IsTrivialGaugeClass, cyclicTwoCocycle_zero] using h))
    · rfl
  · rintro rfl
    exact CohomologousTo.refl _

/-- A normalized fusion gauge leaves the generator-triple sign unchanged. -/
theorem cyclicTwoCocycle_fusionGauge_generator (p : Fin 2)
    {β : ScalarCocycle (Multiplicative (ZMod 2))} (hβ : β.IsNormalized) :
    fusionGauge β (cyclicTwoCocycle p) s₂ s₂ s₂ = (-1) ^ p.val := by
  have hs : s₂ * s₂ = 1 := by decide
  simp [fusionGauge, coboundary, hs, hβ.1, hβ.2]

end TNLean.Algebra.ScalarThreeCochain
