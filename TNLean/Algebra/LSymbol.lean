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

## Main results

* `LSymbol.IsCompatible.gauge`: joint gauges transport compatibility along the fusion gauge.
* `LSymbol.IsCompatible.mul`, `LSymbol.IsCompatible.inv`, `LSymbol.IsCompatible.mul_inv_one`:
  compatibility is multiplicative.
* `LSymbol.gauge_one_mul`, `LSymbol.IsCompatible.gauge_one`: action-tensor gauges with trivial
  fusion gauge.
* `LSymbol.IsCompatible.apply_right_one`, `LSymbol.IsCompatible.apply_left_one`: the values
  with one identity argument.
* `LSymbol.IsCompatible.isNormalized_gauge`: an action-tensor gauge normalizes compatible
  L-symbols.
* `LSymbol.IsCompatible.apply_involution`: the diagonal relation for an involution.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X]

/-- Scalar L-symbols `Lˣ_{g,h}` for a group `G` acting on a type `X`.

These are the scalars produced by the compatibility of matrix product unitary
fusion with the action on a matrix product state, arXiv:2502.20257, `eq:defL`,
lines 1875--1913. Only the scalars are formalized here; no fusion or action
tensor is constructed. -/
abbrev LSymbol (G X : Type*) := X → G → G → Units ℂ

/-- Scalar action-tensor gauges `γ_{g,x}`, written `γˣ_g` in the source.

This is the scalar gauge freedom of the action tensors, arXiv:2502.20257,
`eq:scalar_act_ten`, lines 1871--1873. -/
abbrev ActionTensorGauge (G X : Type*) := G → X → Units ℂ

namespace ActionTensorGauge

/-- An action-tensor gauge is normalized when `γ_{1,x} = 1` for every `x`.

This is not a labelled equation of arXiv:2502.20257: it is the scalar shadow
of the standing convention at lines 1936--1937 that any fusion or action
tensor involving the identity element is trivial. -/
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

`Lˣ_{g,h} ↦ γˣ_{gh} β_{g,h} / (γ^{h • x}_g γˣ_h) Lˣ_{g,h}`.

This is arXiv:2502.20257, `eq:Lsymbgauge`. -/
def gauge (β : ScalarCocycle G) (γ : ActionTensorGauge G X) (L : LSymbol G X) :
    LSymbol G X :=
  fun x g h =>
    ((γ (g * h) x * β g h) / (γ g (h • x) * γ h x)) * L x g h

/-- The identity fusion and action gauges leave an L-symbol unchanged. -/
@[simp]
theorem gauge_one (L : LSymbol G X) :
    gauge (fun _ _ ↦ 1) (fun _ _ ↦ 1) L = L := by
  funext x g h
  simp [gauge]

/-- Successive joint scalar gauges multiply both cochains pointwise. -/
theorem gauge_comp (β₁ β₂ : ScalarCocycle G)
    (γ₁ γ₂ : ActionTensorGauge G X) (L : LSymbol G X) :
    gauge β₂ γ₂ (gauge β₁ γ₁ L) = gauge (β₁ * β₂) (γ₁ * γ₂) L := by
  funext x g h
  simp only [gauge, Pi.mul_apply]
  (apply Units.ext; push_cast; field_simp)

/-- Joint scalar gauges preserve compatibility, with the 3-cochain changed by
the corresponding fusion gauge. -/
theorem IsCompatible.gauge {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (β : ScalarCocycle G) (γ : ActionTensorGauge G X) :
    IsCompatible (gauge β γ L) (ScalarThreeCochain.fusionGauge β ω) := by
  intro x g h k
  simp only [LSymbol.gauge, ScalarThreeCochain.fusionGauge,
    ScalarThreeCochain.coboundary]
  apply Units.ext
  push_cast
  simp only [smul_smul]
  have hL' := congrArg Units.val (hL x g h k)
  push_cast at hL'
  field_simp
  simp only [mul_assoc]
  calc
    _ = (γ (g * (h * k)) x : ℂ) *
        ((L x g (h * k) : ℂ) * (L x h k : ℂ)) := by ring
    _ = (γ (g * (h * k)) x : ℂ) *
        ((ω g h k : ℂ) * (L (k • x) g h : ℂ) * (L x (g * h) k : ℂ)) := by
      rw [hL']
    _ = _ := by ring

/-- Compatibility is multiplicative: pointwise products of compatible L-symbols are compatible
with the pointwise product of the three-cochains. -/
theorem IsCompatible.mul {L₁ L₂ : LSymbol G X} {ω₁ ω₂ : ScalarThreeCochain G}
    (h₁ : IsCompatible L₁ ω₁) (h₂ : IsCompatible L₂ ω₂) :
    IsCompatible (L₁ * L₂) (ω₁ * ω₂) := by
  intro x g h k
  simp only [Pi.mul_apply]
  calc
    _ = (L₁ x g (h * k) * L₁ x h k) * (L₂ x g (h * k) * L₂ x h k) := by ac_rfl
    _ = (ω₁ g h k * L₁ (k • x) g h * L₁ x (g * h) k) *
        (ω₂ g h k * L₂ (k • x) g h * L₂ x (g * h) k) := by rw [h₁, h₂]
    _ = _ := by ac_rfl

/-- The pointwise inverse of a compatible L-symbol is compatible with the inverse
three-cochain. -/
theorem IsCompatible.inv {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) : IsCompatible L⁻¹ ω⁻¹ := by
  intro x g h k
  simp only [Pi.inv_apply]
  rw [← mul_inv, hL x g h k, mul_inv, mul_inv]

/-- The ratio of two L-symbols compatible with the same three-cochain is compatible with the
trivial three-cochain. -/
theorem IsCompatible.mul_inv_one {L L₀ : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (hL₀ : IsCompatible L₀ ω) :
    IsCompatible (L * L₀⁻¹) (fun _ _ _ ↦ 1) := by
  have h := hL.mul hL₀.inv
  rw [mul_inv_cancel] at h
  exact h

/-- An action-tensor gauge with trivial fusion gauge commutes with multiplication by a fixed
L-symbol. -/
theorem gauge_one_mul (γ : ActionTensorGauge G X) (L₁ L₂ : LSymbol G X) :
    gauge (fun _ _ ↦ 1) γ (L₁ * L₂) = L₁ * gauge (fun _ _ ↦ 1) γ L₂ := by
  funext x g h
  simp only [gauge, Pi.mul_apply]
  ac_rfl

/-- An action-tensor gauge with trivial fusion gauge preserves compatibility with the same
three-cochain. -/
theorem IsCompatible.gauge_one {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (γ : ActionTensorGauge G X) :
    IsCompatible (LSymbol.gauge (fun _ _ ↦ 1) γ L) ω := by
  simpa only [ScalarThreeCochain.fusionGauge_one] using hL.gauge (fun _ _ ↦ 1) γ

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
    · simpa only [div_mul_eq_mul_div, div_eq_one] using hright x g
    · simpa only [div_mul_eq_mul_div, div_eq_one] using hleft x g
  · rintro ⟨hright, hleft⟩
    refine ⟨fun x g => ?_, fun x g => ?_⟩
    · simpa only [div_mul_eq_mul_div, div_eq_one] using hright x g
    · simpa only [div_mul_eq_mul_div, div_eq_one] using hleft x g

/-- Normalized fusion and action gauges preserve normalized L-symbols. -/
theorem IsNormalized.gauge {L : LSymbol G X} (hL : IsNormalized L)
    {β : ScalarCocycle G} (hβ : β.IsNormalized) {γ : ActionTensorGauge G X}
    (hγ : γ.IsNormalized) : IsNormalized (gauge β γ L) := by
  apply (isNormalized_gauge_iff β γ L).2
  exact ⟨fun x g => by simp [hβ.2, hL.1, hγ x],
    fun x g => by simp [hβ.1, hL.2, hγ (g • x)]⟩

/-- Compatibility at `(g,1,1)` gives
`Lˣ_{g,1} = Lˣ_{1,1} / ω(g,1,1)`.
This is arXiv:2502.20257, `eq:aux1`. -/
theorem IsCompatible.apply_right_one {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hL : IsCompatible L ω) (x : X) (g : G) :
    L x g 1 = L x 1 1 / ω g 1 1 := by
  have h := hL x g 1 1
  simp only [mul_one, one_smul] at h
  calc
    L x g 1 = (ω g 1 1 * L x g 1 * L x g 1) /
        (ω g 1 1 * L x g 1) := by simp [div_eq_mul_inv]
    _ = (L x g 1 * L x 1 1) / (ω g 1 1 * L x g 1) := by rw [← h]
    _ = L x 1 1 / ω g 1 1 := by
      (apply Units.ext; push_cast; field_simp)

/-- Compatibility at `(1,1,g)` gives
`Lˣ_{1,g} = ω(1,1,g) L^{g • x}_{1,1}`.
This is arXiv:2502.20257, `eq:aux2`. -/
theorem IsCompatible.apply_left_one {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hL : IsCompatible L ω) (x : X) (g : G) :
    L x 1 g = ω 1 1 g * L (g • x) 1 1 := by
  have h := hL x 1 1 g
  simp only [one_mul] at h
  apply (mul_right_cancel (b := L x 1 g))
  simpa [mul_assoc] using h

/-- The action-tensor gauge `γ_{g,x} = Lˣ_{1,1}`, with trivial fusion gauge, turns
compatible L-symbols `L` for a normalized three-cochain into `L'` with
`L'ˣ_{g,1} = L'ˣ_{1,g} = 1`, as asserted in arXiv:2203.12563, lines 716–728, and
restated for the `ℤ₂` examples at lines 1830–1839. -/
theorem IsCompatible.isNormalized_gauge {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (hω : ω.IsNormalized) :
    IsNormalized (LSymbol.gauge (fun _ _ ↦ 1) (fun _ x ↦ L x 1 1) L) := by
  apply (isNormalized_gauge_iff _ _ _).2
  exact ⟨fun x g ↦ by simpa [hω.2.2] using hL.apply_right_one x g,
    fun x g ↦ by simpa [hω.1] using hL.apply_left_one x g⟩

/-- For an involution `g` and normalized compatible L-symbols,
`Lˣ_{g,g} = ω(g,g,g) L^{g • x}_{g,g}`. This gives the sign relations of
arXiv:2203.12563, lines 1830–1839 and 1886. -/
theorem IsCompatible.apply_involution {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (hn : IsNormalized L) (x : X) {g : G}
    (hg : g * g = 1) : L x g g = ω g g g * L (g • x) g g := by
  simpa only [hg, hn.1, hn.2, one_mul, mul_one] using hL x g g g

end LSymbol

end TNLean.Algebra
