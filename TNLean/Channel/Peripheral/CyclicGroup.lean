/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.CyclicGroupKraus
import TNLean.Channel.Peripheral.ClosureFixedPoint

/-!
# Transfer-map forms of peripheral cyclicity

These statements express finite-Kraus peripheral multiplication and cyclicity
for the equal MPS transfer map.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace MPSTensor

variable {d D : ℕ}

/-- Peripheral eigenvalues are closed under multiplication for irreducible
unital MPS transfer maps with a positive-definite adjoint fixed point. -/
theorem peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := d) (D := D) K)) :
    ∀ μ ν : ℂ,
      μ ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) →
      ν ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) →
        μ * ν ∈ peripheralEigenvalues (MPSTensor.transferMap (d := d) (D := D) K) := by
  have hIrr' : IsIrreducibleMap (Kraus.mapLM K) :=
    Kraus.isIrreducibleMap_mapLM_of_transferMap K hIrr
  simpa only [Kraus.mapLM_eq_transferMap] using
    (Kraus.peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint
      K h_unital ρ hρ hfix hIrr')

/-- The peripheral eigenvalues of an irreducible unital MPS transfer map with a
positive-definite adjoint fixed point form a cyclic group of roots of unity. -/
theorem peripheralEigenvalues_eq_range_primitiveRoot [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (MPSTensor.transferMap (d := d) (D := D) K)) :
    let E := MPSTensor.transferMap (d := d) (D := D) K
    let hfin := peripheralEigenvalues_finite (f := E)
    let m := hfin.toFinset.card
    0 < m ∧
    ∃ (γ : ℂ), IsPrimitiveRoot γ m ∧
      peripheralEigenvalues E = Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
  have hIrr' : IsIrreducibleMap (Kraus.mapLM K) :=
    Kraus.isIrreducibleMap_mapLM_of_transferMap K hIrr
  rw [← Kraus.mapLM_eq_transferMap K]
  exact Kraus.peripheralEigenvalues_eq_range_primitiveRoot
    K h_unital ρ hρ hfix hIrr'

end MPSTensor
