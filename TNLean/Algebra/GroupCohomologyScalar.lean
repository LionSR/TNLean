/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleGroupCohomology

/-!
# Scalar values of inhomogeneous three-cochains

The coefficient representation is the trivial integral representation on the
additive form of complex units. These evaluations recover multiplicative values
from Mathlib's cochains and cocycles, as used by the gates of arXiv:2203.12563,
lines 2060–2068, and the cyclic examples of arXiv:2405.00439, line 2040.
No new cochain or cocycle type is introduced.
-/

noncomputable section

open CategoryTheory
open scoped TNLean.Algebra.ScalarCohomology

namespace groupCohomology

open TNLean.Algebra

variable {G : Type} [Group G]

/-- The multiplicative value of an inhomogeneous three-cochain of complex units. -/
def scalarCochainValue₃ (f : (Fin 3 → G) → Rep.ofMulDistribMulAction G ℂˣ)
    (a b c : G) : ℂˣ :=
  ((scalarRepresentationEquiv G).symm (f ![a, b, c])).toMul

/-- The multiplicative value of a certified three-cocycle of complex units. -/
def scalarCocycleValue₃ (x : cocycles (Rep.ofMulDistribMulAction G ℂˣ) 3)
    (a b c : G) : ℂˣ :=
  scalarCochainValue₃ (iCocycles (Rep.ofMulDistribMulAction G ℂˣ) 3 x) a b c

@[simp]
theorem scalarCochainValue₃_iCocycles
    (x : cocycles (Rep.ofMulDistribMulAction G ℂˣ) 3) (a b c : G) :
    scalarCochainValue₃ (iCocycles (Rep.ofMulDistribMulAction G ℂˣ) 3 x) a b c =
      scalarCocycleValue₃ x a b c := rfl

/-- The cochain underlying a certified three-cocycle has zero differential. -/
theorem d_iCocycles₃ (x : cocycles (Rep.ofMulDistribMulAction G ℂˣ) 3) :
    inhomogeneousCochains.d (Rep.ofMulDistribMulAction G ℂˣ) 3
      (iCocycles (Rep.ofMulDistribMulAction G ℂˣ) 3 x) = 0 := by
  rw [← inhomogeneousCochains.d_def]
  exact ConcreteCategory.congr_hom
    ((inhomogeneousCochains (Rep.ofMulDistribMulAction G ℂˣ)).iCycles_d 3 4) x

@[simp]
theorem scalarCochainValue₃_zero (a b c : G) :
    scalarCochainValue₃ (0 : (Fin 3 → G) → Rep.ofMulDistribMulAction G ℂˣ) a b c = 1 := by
  simp [scalarCochainValue₃]

/-- Closed inhomogeneous three-cochains satisfy the multiplicative cocycle equation. -/
theorem scalarCochainValue₃_cocycle
    {f : (Fin 3 → G) → Rep.ofMulDistribMulAction G ℂˣ}
    (hf : inhomogeneousCochains.d (Rep.ofMulDistribMulAction G ℂˣ) 3 f = 0)
    (a b c d : G) :
    scalarCochainValue₃ f (a * b) c d * scalarCochainValue₃ f a b (c * d) =
      scalarCochainValue₃ f a b c * scalarCochainValue₃ f a (b * c) d *
        scalarCochainValue₃ f b c d := by
  exact ((ScalarThreeCochain.isCocycle_iff_d_eq_zero
    (ScalarThreeCochain.ofInhomogeneousCochain f)).2 (by
      simpa only [ScalarThreeCochain.toInhomogeneousCochain_ofInhomogeneousCochain]
        using hf)) a b c d

@[simp]
theorem scalarCocycleValue₃_zero :
    scalarCocycleValue₃ (0 : cocycles (Rep.ofMulDistribMulAction G ℂˣ) 3) =
      fun _ _ _ ↦ 1 := by
  funext a b c
  simp [scalarCocycleValue₃]

@[simp]
theorem scalarCocycleValue₃_neg (x : cocycles (Rep.ofMulDistribMulAction G ℂˣ) 3) :
    scalarCocycleValue₃ (-x) = (scalarCocycleValue₃ x)⁻¹ := by
  funext a b c
  simp [scalarCocycleValue₃, scalarCochainValue₃]

/-- A certified scalar three-cocycle is determined by its multiplicative values. -/
theorem scalarCocycleValue₃_injective :
    Function.Injective (scalarCocycleValue₃ (G := G)) := by
  intro x y h
  apply (ModuleCat.mono_iff_injective (iCocycles (Rep.ofMulDistribMulAction G ℂˣ) 3)).1
    inferInstance
  funext p
  apply (scalarRepresentationEquiv G).symm.injective
  apply Additive.toMul.injective
  have hp : ![p 0, p 1, p 2] = p := by
    funext i
    fin_cases i <;> rfl
  simpa only [scalarCocycleValue₃, scalarCochainValue₃, hp] using
    congrFun (congrFun (congrFun h (p 0)) (p 1)) (p 2)

@[simp]
theorem scalarCocycleValue₃_toCocycles
    (ω : {ω : ScalarThreeCochain G // ScalarThreeCochain.IsCocycle ω}) :
    scalarCocycleValue₃ (ScalarThreeCochain.toCocycles ω) = ω.1 := by
  funext a b c
  simp [scalarCocycleValue₃, scalarCochainValue₃,
    ScalarThreeCochain.iCocycles_toCocycles, ScalarThreeCochain.toInhomogeneousCochain]

end groupCohomology
