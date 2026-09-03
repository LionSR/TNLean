/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.LSymbolBlockIndependence

/-!
# Restricted scalar gauges

This file isolates the tensor-independent part of the standing gauge convention
in arXiv:2502.20257, lines 2050--2054. The fusion scalar `β` is one on both
identity axes and on every inverse pair `(g, g⁻¹)`, while the action scalar `γ`
is one at the identity. These conditions are closed under pointwise identity,
multiplication, and inversion.

No fusion tensor, action tensor, dagger gauge, or representation-level gauge is
constructed here.

## Main definitions

* `ScalarCocycle.IsInverseNormalized`: the restricted condition on `β`.
* `RestrictedFusionGauge`: an inverse-normalized fusion gauge.
* `RestrictedScalarGauge`: a bundled restricted choice `(β, γ)`.
-/

namespace TNLean.Algebra

variable {G X : Type*} [Group G] [MulAction G X]

namespace ScalarCocycle

/-- A fusion scalar `β` satisfies the restricted standing convention when it is
normalized and `β(g,g⁻¹) = 1` for every `g`. This is arXiv:2502.20257, lines
2050--2053. -/
def IsInverseNormalized (β : ScalarCocycle G) : Prop :=
  β.IsNormalized ∧ ∀ g, β g g⁻¹ = 1

/-- The identity fusion scalar is inverse-normalized. -/
@[simp]
theorem isInverseNormalized_one : IsInverseNormalized (1 : ScalarCocycle G) := by
  exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun _ => rfl⟩

/-- Pointwise multiplication preserves the restricted fusion convention. -/
theorem IsInverseNormalized.mul {β₁ β₂ : ScalarCocycle G}
    (hβ₁ : β₁.IsInverseNormalized) (hβ₂ : β₂.IsInverseNormalized) :
    (β₁ * β₂).IsInverseNormalized := by
  refine ⟨⟨fun g => by simp [hβ₁.1.1 g, hβ₂.1.1 g],
    fun g => by simp [hβ₁.1.2 g, hβ₂.1.2 g]⟩, fun g => ?_⟩
  simp [hβ₁.2 g, hβ₂.2 g]

/-- Pointwise inversion preserves the restricted fusion convention. -/
theorem IsInverseNormalized.inv {β : ScalarCocycle G}
    (hβ : β.IsInverseNormalized) : β⁻¹.IsInverseNormalized := by
  refine ⟨⟨fun g => by simp [hβ.1.1 g], fun g => by simp [hβ.1.2 g]⟩, fun g => ?_⟩
  simp [hβ.2 g]

end ScalarCocycle

/-- An inverse-normalized fusion scalar `β` satisfying the standing convention
of arXiv:2502.20257, lines 2050--2053. -/
structure RestrictedFusionGauge (G : Type*) [Group G] where
  /-- The scalar fusion gauge `β`. -/
  beta : ScalarCocycle G
  /-- Normalization on the identity axes and inverse pairs. -/
  isInverseNormalized : beta.IsInverseNormalized

namespace RestrictedFusionGauge

/-- The identity restricted fusion gauge. -/
def one : RestrictedFusionGauge G where
  beta := 1
  isInverseNormalized := ScalarCocycle.isInverseNormalized_one

/-- Pointwise multiplication of restricted fusion gauges. -/
def mul (β₁ β₂ : RestrictedFusionGauge G) : RestrictedFusionGauge G where
  beta := β₁.beta * β₂.beta
  isInverseNormalized := β₁.isInverseNormalized.mul β₂.isInverseNormalized

/-- Pointwise inversion of a restricted fusion gauge. -/
def inv (β : RestrictedFusionGauge G) : RestrictedFusionGauge G where
  beta := β.beta⁻¹
  isInverseNormalized := β.isInverseNormalized.inv

/-- The identity restricted fusion gauge acts trivially on scalar 3-cochains. -/
@[simp]
theorem fusionGauge_one (ω : ScalarThreeCochain G) :
    ScalarThreeCochain.fusionGauge (one (G := G)).beta ω = ω :=
  ScalarThreeCochain.fusionGauge_one ω

/-- A restricted fusion gauge preserves normalization of scalar 3-cochains. -/
theorem isNormalized_fusionGauge (β : RestrictedFusionGauge G)
    {ω : ScalarThreeCochain G} (hω : ω.IsNormalized) :
    (ScalarThreeCochain.fusionGauge β.beta ω).IsNormalized :=
  hω.fusionGauge β.isInverseNormalized.1

/-- A restricted fusion gauge preserves the scalar 3-cocycle equation. -/
theorem isCocycle_fusionGauge (β : RestrictedFusionGauge G)
    {ω : ScalarThreeCochain G} (hω : ω.IsCocycle) :
    (ScalarThreeCochain.fusionGauge β.beta ω).IsCocycle :=
  hω.fusionGauge β.beta

/-- Successive restricted fusion gauges compose according to
`ScalarThreeCochain.fusionGauge_comp`. -/
theorem fusionGauge_mul (β₁ β₂ : RestrictedFusionGauge G)
    (ω : ScalarThreeCochain G) :
    ScalarThreeCochain.fusionGauge β₂.beta
        (ScalarThreeCochain.fusionGauge β₁.beta ω) =
      ScalarThreeCochain.fusionGauge (mul β₁ β₂).beta ω :=
  ScalarThreeCochain.fusionGauge_comp β₁.beta β₂.beta ω

/-- Applying a restricted fusion gauge and then its pointwise inverse is the
identity action. -/
@[simp]
theorem fusionGauge_inv (β : RestrictedFusionGauge G) (ω : ScalarThreeCochain G) :
    ScalarThreeCochain.fusionGauge (inv β).beta
        (ScalarThreeCochain.fusionGauge β.beta ω) = ω := by
  rw [ScalarThreeCochain.fusionGauge_comp]
  change ScalarThreeCochain.fusionGauge (β.beta * β.beta⁻¹) ω = ω
  rw [mul_inv_cancel]
  exact ScalarThreeCochain.fusionGauge_one ω

end RestrictedFusionGauge

namespace ActionTensorGauge

omit [MulAction G X] in
/-- The identity action scalar is normalized. -/
@[simp]
theorem isNormalized_one : IsNormalized (1 : ActionTensorGauge G X) :=
  fun _ => rfl

omit [MulAction G X] in
/-- Pointwise multiplication preserves normalized action scalars. -/
theorem IsNormalized.mul {γ₁ γ₂ : ActionTensorGauge G X}
    (hγ₁ : γ₁.IsNormalized) (hγ₂ : γ₂.IsNormalized) : (γ₁ * γ₂).IsNormalized :=
  fun x => by simp [hγ₁ x, hγ₂ x]

omit [MulAction G X] in
/-- Pointwise inversion preserves normalized action scalars. -/
theorem IsNormalized.inv {γ : ActionTensorGauge G X}
    (hγ : γ.IsNormalized) : γ⁻¹.IsNormalized :=
  fun x => by simp [hγ x]

end ActionTensorGauge

/-- A restricted scalar gauge bundles an inverse-normalized fusion scalar `β`
with a normalized action scalar `γ`, as in arXiv:2502.20257, lines 2050--2054. -/
structure RestrictedScalarGauge (G X : Type*) [Group G] where
  /-- The restricted fusion gauge. -/
  fusion : RestrictedFusionGauge G
  /-- The scalar action gauge `γ`. -/
  gamma : ActionTensorGauge G X
  /-- Normalization of `γ` at the identity. -/
  gamma_isNormalized : gamma.IsNormalized

namespace RestrictedScalarGauge

/-- The identity restricted scalar gauge. -/
def one : RestrictedScalarGauge G X where
  fusion := RestrictedFusionGauge.one
  gamma := 1
  gamma_isNormalized := ActionTensorGauge.isNormalized_one

/-- Pointwise multiplication of restricted scalar gauges. -/
def mul (κ₁ κ₂ : RestrictedScalarGauge G X) : RestrictedScalarGauge G X where
  fusion := RestrictedFusionGauge.mul κ₁.fusion κ₂.fusion
  gamma := κ₁.gamma * κ₂.gamma
  gamma_isNormalized := κ₁.gamma_isNormalized.mul κ₂.gamma_isNormalized

/-- Pointwise inversion of a restricted scalar gauge. -/
def inv (κ : RestrictedScalarGauge G X) : RestrictedScalarGauge G X where
  fusion := RestrictedFusionGauge.inv κ.fusion
  gamma := κ.gamma⁻¹
  gamma_isNormalized := κ.gamma_isNormalized.inv

/-- The identity restricted scalar gauge acts trivially on L-symbols. -/
@[simp]
theorem gauge_one (L : LSymbol G X) :
    LSymbol.gauge (one (G := G) (X := X)).fusion.beta
      (one (G := G) (X := X)).gamma L = L :=
  LSymbol.gauge_one L

/-- Restricted scalar gauges preserve normalized L-symbols. -/
theorem isNormalized_gauge (κ : RestrictedScalarGauge G X) {L : LSymbol G X}
    (hL : L.IsNormalized) :
    (LSymbol.gauge κ.fusion.beta κ.gamma L).IsNormalized := by
  apply (LSymbol.isNormalized_gauge_iff κ.fusion.beta κ.gamma L).2
  exact ⟨fun x g => by
      simp [κ.fusion.isInverseNormalized.1.2 g, hL.1 x g, κ.gamma_isNormalized x],
    fun x g => by
      simp [κ.fusion.isInverseNormalized.1.1 g, hL.2 x g,
        κ.gamma_isNormalized (g • x)]⟩

/-- Restricted scalar gauges preserve compatibility while acting on the
corresponding scalar 3-cochain by the fusion gauge. -/
theorem isCompatible_gauge (κ : RestrictedScalarGauge G X) {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hL : L.IsCompatible ω) :
    (LSymbol.gauge κ.fusion.beta κ.gamma L).IsCompatible
      (ScalarThreeCochain.fusionGauge κ.fusion.beta ω) :=
  hL.gauge κ.fusion.beta κ.gamma

/-- Successive restricted scalar gauges compose according to
`LSymbol.gauge_comp`. -/
theorem gauge_mul (κ₁ κ₂ : RestrictedScalarGauge G X) (L : LSymbol G X) :
    LSymbol.gauge κ₂.fusion.beta κ₂.gamma
        (LSymbol.gauge κ₁.fusion.beta κ₁.gamma L) =
      LSymbol.gauge (mul κ₁ κ₂).fusion.beta (mul κ₁ κ₂).gamma L :=
  LSymbol.gauge_comp κ₁.fusion.beta κ₂.fusion.beta κ₁.gamma κ₂.gamma L

/-- Applying a restricted scalar gauge and then its pointwise inverse is the
identity action on L-symbols. -/
@[simp]
theorem gauge_inv (κ : RestrictedScalarGauge G X) (L : LSymbol G X) :
    LSymbol.gauge (inv κ).fusion.beta (inv κ).gamma
        (LSymbol.gauge κ.fusion.beta κ.gamma L) = L := by
  rw [LSymbol.gauge_comp]
  change LSymbol.gauge (κ.fusion.beta * κ.fusion.beta⁻¹)
    (κ.gamma * κ.gamma⁻¹) L = L
  rw [mul_inv_cancel, mul_inv_cancel]
  exact LSymbol.gauge_one L

end RestrictedScalarGauge

end TNLean.Algebra
