/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycle

/-!
# Scalar L-symbols

This file isolates the scalar L-symbol relations in arXiv:2502.20257,
equations `eq:Lsymbgauge`, `eq:omega_and_Ls`, and `eq:triv_Ls`. It does not
assert the existence of action tensors, impose transitivity or finiteness, or
attach these scalars to a matrix product unitary.

## Main definitions

* `LSymbol`: scalar L-symbols for a group action.
* `ActionTensorGauge`: scalar gauge choices for action tensors.
* `LSymbol.IsCompatible`: compatibility with a scalar 3-cochain.
* `LSymbol.gauge`: the joint fusion-tensor and action-tensor gauge action.
* `LSymbol.IsNormalized`: triviality when either group argument is the identity.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X]

/-- Scalar L-symbols `Lˣ_{g,h}` for a group `G` acting on a type `X`. -/
abbrev LSymbol (G X : Type*) := X → G → G → Units ℂ

/-- Scalar action-tensor gauges `γ_{g,x}`. -/
abbrev ActionTensorGauge (G X : Type*) := G → X → Units ℂ

namespace ActionTensorGauge

/-- An action-tensor gauge is normalized when `γ_{1,x} = 1` for every `x`. -/
def IsNormalized (γ : ActionTensorGauge G X) : Prop :=
  ∀ x, γ 1 x = 1

end ActionTensorGauge

namespace LSymbol

/-- Compatibility of L-symbols with a scalar 3-cochain:

`Lˣ_{g,hk} Lˣ_{h,k} = ω(g,h,k) L^{k • x}_{g,h} Lˣ_{gh,k}`.

This is arXiv:2502.20257, `eq:omega_and_Ls`. -/
def IsCompatible (L : LSymbol G X) (ω : ScalarThreeCochain G) : Prop :=
  ∀ x g h k,
    L x g (h * k) * L x h k =
      ω g h k * L (k • x) g h * L x (g * h) k

/-- The joint fusion-tensor and action-tensor scalar gauge action:

`Lˣ_{g,h} ↦ γ_{gh,x} β_{g,h} / (γ_{g,h • x} γ_{h,x}) Lˣ_{g,h}`.

This is arXiv:2502.20257, `eq:Lsymbgauge`. -/
def gauge (β : ScalarCocycle G) (γ : ActionTensorGauge G X) (L : LSymbol G X) :
    LSymbol G X :=
  fun x g h =>
    ((γ (g * h) x * β g h) / (γ g (h • x) * γ h x)) * L x g h

/-- Joint scalar gauges preserve compatibility, with the 3-cochain changed by
the corresponding fusion gauge. -/
theorem IsCompatible.gauge {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (β : ScalarCocycle G) (γ : ActionTensorGauge G X) :
    IsCompatible (gauge β γ L) (ScalarThreeCochain.fusionGauge β ω) := by
  intro x g h k
  simp only [gauge, ScalarThreeCochain.fusionGauge, ScalarThreeCochain.coboundary]
  rw [hL]
  apply Units.ext
  push_cast
  simp only [map_mul, map_div, smul_smul]
  field_simp

/-- L-symbols are normalized when `Lˣ_{g,1} = Lˣ_{1,g} = 1`. This is the
standing convention in arXiv:2502.20257, `eq:triv_Ls`. -/
def IsNormalized (L : LSymbol G X) : Prop :=
  (∀ x g, L x g 1 = 1) ∧ (∀ x g, L x 1 g = 1)

/-- The exact right identity-axis formula for a joint scalar gauge. -/
theorem gauge_apply_right_one (β : ScalarCocycle G) (γ : ActionTensorGauge G X)
    (L : LSymbol G X) (x : X) (g : G) :
    gauge β γ L x g 1 = (β g 1 / γ 1 x) * L x g 1 := by
  simp [gauge, mul_comm]

/-- The exact left identity-axis formula for a joint scalar gauge. -/
theorem gauge_apply_left_one (β : ScalarCocycle G) (γ : ActionTensorGauge G X)
    (L : LSymbol G X) (x : X) (g : G) :
    gauge β γ L x 1 g = (β 1 g / γ 1 (g • x)) * L x 1 g := by
  simp [gauge, mul_comm]

/-- Exact characterization of when a joint scalar gauge is normalized. -/
theorem isNormalized_gauge_iff (β : ScalarCocycle G) (γ : ActionTensorGauge G X)
    (L : LSymbol G X) :
    IsNormalized (gauge β γ L) ↔
      (∀ x g, β g 1 * L x g 1 = γ 1 x) ∧
        (∀ x g, β 1 g * L x 1 g = γ 1 (g • x)) := by
  simp only [IsNormalized, gauge_apply_right_one, gauge_apply_left_one]
  constructor
  · rintro ⟨hright, hleft⟩
    refine ⟨fun x g => ?_, fun x g => ?_⟩
    · exact (div_mul_eq_one_iff_eq (γ 1 x)).mp (hright x g)
    · exact (div_mul_eq_one_iff_eq (γ 1 (g • x))).mp (hleft x g)
  · rintro ⟨hright, hleft⟩
    refine ⟨fun x g => ?_, fun x g => ?_⟩
    · exact (div_mul_eq_one_iff_eq (γ 1 x)).mpr (hright x g)
    · exact (div_mul_eq_one_iff_eq (γ 1 (g • x))).mpr (hleft x g)

/-- Normalized fusion and action gauges preserve normalized L-symbols. -/
theorem IsNormalized.gauge {L : LSymbol G X} (hL : IsNormalized L)
    {β : ScalarCocycle G} (hβ : β.IsNormalized) {γ : ActionTensorGauge G X}
    (hγ : γ.IsNormalized) : IsNormalized (gauge β γ L) := by
  apply (isNormalized_gauge_iff β γ L).2
  exact ⟨fun x g => by simp [hβ.2, hL.1, hγ],
    fun x g => by simp [hβ.1, hL.2, hγ]⟩

end LSymbol

end TNLean.Algebra
