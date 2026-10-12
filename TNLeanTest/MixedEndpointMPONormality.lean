/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointMPONormality

/-!
# Mixed endpoint MPO normality regressions

The three-site conclusion concerns the actual mixed constructor and retains
arbitrary positive multiplicity. The core requires neither an endpoint MPS
nor action reconstruction, completeness, L-symbols, or F-symbols.
-/

-- These regressions intentionally inspect kernel-dependency reports.
set_option linter.hashCommand false

open scoped Matrix
open MPSTensor MPSTensor.MPOSymmetry

namespace MixedEndpointMPONormalityTest

variable {D₀ D₁ χ₀ χ₁ m : ℕ}
  (T₀ : MPOTensor (D₀ * D₀) χ₀) (T₁ : MPOTensor (D₁ * D₁) χ₁)
  (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
  (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
  (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
  (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
  (hD₀ : 0 < D₀) (hD₁ : 0 < D₁) (hm : 0 < m)
  (hT₀ : Kraus.IsInjective T₀.toMPSTensor)
  (hT₁ : Kraus.IsInjective T₁.toMPSTensor)
  (hret₀ : ∀ μ, V₀ μ * W₀ μ = 1)
  (hret₁ : ∀ μ, V₁ μ * W₁ μ = 1)
  (horth₀ : ∀ μ ν, μ ≠ ν → V₀ μ * W₀ ν = 0)
  (horth₁ : ∀ μ ν, μ ≠ ν → V₁ μ * W₁ ν = 0)

example : Kraus.IsNBlkInjective
    (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁).toMPSTensor 3 :=
  isNBlkInjective_mixedEndpointMPO_three T₀ T₁ V₀ V₁ W₀ W₁
    hD₀ hD₁ hm hT₀ hT₁ hret₀ hret₁ horth₀ horth₁

example : Kraus.IsNormal (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁).toMPSTensor :=
  isNormal_mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁
    hD₀ hD₁ hm hT₀ hT₁ hret₀ hret₁ horth₀ horth₁

example (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hχ₀ : 0 < χ₀) (hA₀ : Kraus.IsInjective A₀)
    (h₀ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₀ A₀)
      (fun _ : Fin m => A₀) V₀ W₀)
    (h₁ : IsBiorthogonalDecomposition (MPOTensor.actTensor T₁ A₁)
      (fun _ : Fin m => A₁) V₁ W₁) :
    Kraus.IsNBlkInjective (mixedEndpointMPO T₀ T₁ V₀ V₁ W₀ W₁).toMPSTensor 3 :=
  isNBlkInjective_mixedEndpointMPO_three_of_exact_action T₀ T₁ A₀ A₁ V₀ V₁ W₀ W₁
    hD₀ hD₁ hχ₀ hT₀ hT₁ hA₀ h₀ h₁

/--
info: 'MPSTensor.MPOSymmetry.isNBlkInjective_mixedEndpointMPO_three'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.isNBlkInjective_mixedEndpointMPO_three

/--
info: 'MPSTensor.MPOSymmetry.isNormal_mixedEndpointMPO'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.isNormal_mixedEndpointMPO

/--
info: 'MPSTensor.MPOSymmetry.multiplicity_pos_of_injective_endpoint_action'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.multiplicity_pos_of_injective_endpoint_action

/--
info: 'MPSTensor.MPOSymmetry.isNBlkInjective_mixedEndpointMPO_three_of_exact_action'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.isNBlkInjective_mixedEndpointMPO_three_of_exact_action

end MixedEndpointMPONormalityTest
