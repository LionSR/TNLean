/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.NestedCylinderOrthogonalization

/-!
# Degenerate nested-cylinder families

These examples retain empty families, zero inside spaces, empty physical regions,
and empty complementary coordinate alphabets in the orthogonalization statements.
-/

open scoped BigOperators Matrix
open TNLean.PEPS

namespace TNLeanTest.NestedCylinderOrthogonalization

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]

example (R : Fin 0 → Finset V)
    (S : (j : Fin 0) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    coordinateRangeProjector (⨆ i, dependentRegionCylinder (R i) (S i)) = 0 := by
  have hR : Monotone R := fun i => Fin.elim0 i
  simpa using nestedCylinderInnovation_projector_sum R hR S

example (R : Fin 0 → Finset V)
    (S : (j : Fin 0) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ))
    (U : Finset V) :
    ∃ T : Submodule ℂ (((w : {w : V // w ∈ U}) → Out w.1) → ℂ),
      coordinateRangeProjector (⨆ i, dependentRegionCylinder (R i) (S i)) =
        dependentRegionOperatorLift U (coordinateRangeProjector T) :=
  nestedCylinder_projector_supported R S U (fun i => Fin.elim0 i)

example {n : ℕ} (R : Fin n → Finset V) (hR : Monotone R) (j : Fin n) :
    nestedCylinderInnovation (Out := Out) R hR (fun _ => ⊥) j = ⊥ :=
  nestedCylinderInnovation_eq_bot_of_le R hR (fun _ => ⊥) j bot_le

example {n : ℕ} (R : Fin n → Finset V) (hR : Monotone R)
    (S : (j : Fin n) → Submodule ℂ (((w : {w : V // w ∈ R j}) → Out w.1) → ℂ)) :
    (⨆ i : {i : Fin n // i.1 < 0},
      dependentRegionCylinder (R i.1) (nestedCylinderInnovation R hR S i.1)) = ⊥ := by
  simp

example : Module.finrank ℂ
    (⊤ : Submodule ℂ (((w : {w : Fin 1 // w ∈ (∅ : Finset (Fin 1))}) → Fin 2) → ℂ)) = 1 := by
  simp

example : dependentRegionCylinder (Out := fun _ : Fin 1 => Fin 2) ∅ ⊤ = ⊤ := by
  ext x
  simp


omit [∀ v, Fintype (Out v)] in
private theorem subregionLift_self (R : Finset V)
    (K : Matrix ((w : {w : V // w ∈ R}) → Out w.1)
      ((w : {w : V // w ∈ R}) → Out w.1) ℂ) :
    dependentSubregionOperatorLift R R (fun _ h => h) K = K := by
  classical
  ext α β
  have h : ∀ v, ∀ hv : v ∈ R, v ∉ R → α ⟨v, hv⟩ = β ⟨v, hv⟩ :=
    fun _ hv hn => (hn hv).elim
  change (if ∀ v, ∀ hv : v ∈ R, v ∉ R → α ⟨v, hv⟩ = β ⟨v, hv⟩ then
    K (fun w => α ⟨w.1, w.2⟩) (fun w => β ⟨w.1, w.2⟩) else 0) = K α β
  rw [ite_eq_left h]

/-- Repeating the same clipped region and inside space contributes no second innovation. -/
example (R : Finset V)
    (S : Submodule ℂ (((w : {w : V // w ∈ R}) → Out w.1) → ℂ)) :
    nestedCylinderInnovation (fun _ : Fin 2 => R) monotone_const (fun _ => S) 1 = ⊥ := by
  let : Nonempty {i : Fin 2 // i < 1} := ⟨⟨0, by decide⟩⟩
  apply nestedCylinderInnovation_eq_bot_of_le
  simp [nestedCylinderEarlierInside, subregionLift_self, range_coordinateRangeProjector]

/-- A nonzero inside space can have a zero cylinder when the exterior configuration type
is empty. -/
example :
    (⊤ : Submodule ℂ (((w : {w : Fin 1 // w ∈ (∅ : Finset (Fin 1))}) → Fin 0) → ℂ)) ≠ ⊥ ∧
      dependentRegionCylinder (Out := fun _ : Fin 1 => Fin 0) ∅ ⊤ = ⊥ := by
  constructor
  · exact top_ne_bot
  · let _ : IsEmpty ((w : {w : Fin 1 // w ∈ Finset.univ}) → Fin 0) :=
      ⟨fun x => Fin.elim0 (x ⟨0, Finset.mem_univ 0⟩)⟩
    exact Subsingleton.elim _ _

example :
    coordinateRangeProjector
        (dependentRegionCylinder (Out := fun _ : Fin 1 => Fin 0) ∅ ⊤) =
      dependentRegionOperatorLift (Out := fun _ : Fin 1 => Fin 0) ∅ (coordinateRangeProjector
        (⊤ : Submodule ℂ (((w : {w : Fin 1 // w ∈ (∅ : Finset (Fin 1))}) → Fin 0) → ℂ))) :=
  coordinateRangeProjector_dependentRegionCylinder ∅ ⊤

end TNLeanTest.NestedCylinderOrthogonalization
