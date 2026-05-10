/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.BlockingInfrastructure

/-!
# Physical reindexing along alphabet equivalences

This file proves that changing physical letters by a bijection preserves the
basic tensor properties used by blocking and canonical-form arguments.

## Main statements

* `reindexPhysical_cast_dim` — physical reindexing commutes with bond-dimension casts.
* `transferMap_reindexPhysical_equiv` — the transfer map is unchanged by a physical
  alphabet bijection.
* `leftCanonical_reindexPhysical_equiv` and
  `isPrimitive_transferMap_reindexPhysical_equiv` — left-canonical normalization and
  transfer-map primitivity are preserved.
* `hasInvariantProj_reindexPhysical_equiv`, `isIrreducibleTensor_reindexPhysical_equiv`,
  and `isInjective_reindexPhysical_equiv` — invariant projections, irreducibility, and
  one-site injectivity are preserved.
* `gaugePhaseEquiv_reindexPhysical_equiv` — gauge-phase equivalence is preserved
  when both tensors are reindexed by the same physical alphabet bijection.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Physical reindexing commutes with bond-dimension casts. -/
theorem reindexPhysical_cast_dim {d₁ d₂ D₁ D₂ : ℕ} (e : Fin d₁ ≃ Fin d₂)
    (h : D₁ = D₂) (A : MPSTensor d₂ D₁) :
    reindexPhysical e (cast (congr_arg (MPSTensor d₂) h) A) =
      cast (congr_arg (MPSTensor d₁) h) (reindexPhysical e A) := by
  subst h
  rfl

/-- Reindexing by a physical-index equivalence does not change the transfer map. -/
theorem transferMap_reindexPhysical_equiv {d₁ d₂ D : ℕ} (e : Fin d₁ ≃ Fin d₂)
    (A : MPSTensor d₂ D) :
    transferMap (d := d₁) (D := D) (reindexPhysical e A) =
      transferMap (d := d₂) (D := D) A := by
  ext X i j
  simp only [transferMap_apply, reindexPhysical]
  have hsum :
      (∑ x : Fin d₁, A (e x) * X * (A (e x))ᴴ) =
        ∑ x : Fin d₂, A x * X * (A x)ᴴ :=
    Fintype.sum_equiv e
      (fun x : Fin d₁ => A (e x) * X * (A (e x))ᴴ)
      (fun x : Fin d₂ => A x * X * (A x)ᴴ)
      (fun _ => rfl)
  exact congr_fun (congr_fun hsum i) j

/-- Reindexing by a physical-index equivalence preserves left-canonical normalization. -/
theorem leftCanonical_reindexPhysical_equiv {d₁ d₂ D : ℕ} (e : Fin d₁ ≃ Fin d₂)
    (A : MPSTensor d₂ D) :
    (∑ i : Fin d₁,
        (reindexPhysical e A i)ᴴ * reindexPhysical e A i = 1) ↔
      (∑ i : Fin d₂, (A i)ᴴ * A i = 1) := by
  simp only [reindexPhysical]
  have hsum :
      (∑ i : Fin d₁, (A (e i))ᴴ * A (e i)) =
        ∑ i : Fin d₂, (A i)ᴴ * A i :=
    Fintype.sum_equiv e
      (fun i : Fin d₁ => (A (e i))ᴴ * A (e i))
      (fun i : Fin d₂ => (A i)ᴴ * A i)
      (fun _ => rfl)
  rw [hsum]

/-- Reindexing by a physical-index equivalence preserves transfer-map primitivity. -/
theorem isPrimitive_transferMap_reindexPhysical_equiv {d₁ d₂ D : ℕ}
    (e : Fin d₁ ≃ Fin d₂) (A : MPSTensor d₂ D) :
    _root_.IsPrimitive
        (transferMap (d := d₁) (D := D) (reindexPhysical e A)) ↔
      _root_.IsPrimitive (transferMap (d := d₂) (D := D) A) := by
  rw [transferMap_reindexPhysical_equiv e A]

/-- Reindexing by a physical-index equivalence preserves invariant projections. -/
theorem hasInvariantProj_reindexPhysical_equiv {d₁ d₂ D : ℕ} (e : Fin d₁ ≃ Fin d₂)
    (A : MPSTensor d₂ D) :
    HasInvariantProj (reindexPhysical e A) ↔ HasInvariantProj A := by
  constructor
  · rintro ⟨P, hPproj, hP0, hP1, hLower⟩
    refine ⟨P, hPproj, hP0, hP1, ?_⟩
    intro i
    simpa [reindexPhysical] using hLower (e.symm i)
  · rintro ⟨P, hPproj, hP0, hP1, hLower⟩
    refine ⟨P, hPproj, hP0, hP1, ?_⟩
    intro i
    exact hLower (e i)

/-- Reindexing by a physical-index equivalence preserves tensor irreducibility. -/
theorem isIrreducibleTensor_reindexPhysical_equiv {d₁ d₂ D : ℕ}
    (e : Fin d₁ ≃ Fin d₂) (A : MPSTensor d₂ D) :
    IsIrreducibleTensor (reindexPhysical e A) ↔ IsIrreducibleTensor A := by
  rw [IsIrreducibleTensor, IsIrreducibleTensor, hasInvariantProj_reindexPhysical_equiv e A]

/-- Reindexing by a physical-index equivalence preserves algebraic injectivity. -/
theorem isInjective_reindexPhysical_equiv {d₁ d₂ D : ℕ} (e : Fin d₁ ≃ Fin d₂)
    (A : MPSTensor d₂ D) :
    IsInjective (reindexPhysical e A) ↔ IsInjective A := by
  have hRange : Set.range (reindexPhysical e A) = Set.range A := by
    ext X
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp [reindexPhysical]⟩
  simp [IsInjective, hRange]

/-- Reindexing both tensors by a physical-index equivalence preserves gauge-phase equivalence. -/
theorem gaugePhaseEquiv_reindexPhysical_equiv {d₁ d₂ D : ℕ}
    (e : Fin d₁ ≃ Fin d₂) (A B : MPSTensor d₂ D) :
    GaugePhaseEquiv (reindexPhysical e A) (reindexPhysical e B) ↔
      GaugePhaseEquiv A B := by
  constructor
  · rintro ⟨X, ζ, hζ, hXB⟩
    refine ⟨X, ζ, hζ, ?_⟩
    intro i
    simpa [reindexPhysical] using hXB (e.symm i)
  · rintro ⟨X, ζ, hζ, hXB⟩
    refine ⟨X, ζ, hζ, ?_⟩
    intro i
    simpa [reindexPhysical] using hXB (e i)

end MPSTensor
