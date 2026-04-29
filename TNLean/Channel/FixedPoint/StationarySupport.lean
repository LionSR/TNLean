/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Irreducible.Ergodicity
import TNLean.Channel.Irreducible.Basic
import TNLean.MPS.Core.OrthogonalProjectionInvariance
import TNLean.MPS.Irreducible.FixedPointProjection

/-!
# Stationary support for irreducible channels

This file collects the quantum-channel support-projection results for
stationary states, in the spirit of Wolf §6.4 (Lemmas 6.4--6.5 and
Propositions 6.9--6.11).

## Main declarations

* `support_proj_fixed`: if `ρ` is a PSD fixed point of a channel `E`, then its
  support projection `P` satisfies
  `P * E (P * X * P) * P = E (P * X * P)` for all `X`.
* `stationarySupport`: support projection of the unique density-matrix fixed
  point of an irreducible channel.
* `stationarySupport_eq_one`: for an irreducible channel, the stationary support
  is full (`= 1`).
* TODO (Wolf Prop. 6.9): upgrade to the non-vacuous equivalence between
  irreducibility and full support of stationary states.
* TODO (Wolf Prop. 6.10): formalize minimality of stationary support without an
  irreducibility hypothesis.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace Channel

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Lemma 6.4 (support projection of a fixed PSD point is invariant under the
corner action). -/
theorem support_proj_fixed
    {E : Mat →ₗ[ℂ] Mat} (hE : IsChannel E) {ρ : Mat}
    (hρ_psd : ρ.PosSemidef) (hρ_fix : E ρ = ρ) :
    ∀ X : Mat,
      MPSTensor.supportProj (D := D) ρ hρ_psd *
        E (MPSTensor.supportProj (D := D) ρ hρ_psd * X *
          MPSTensor.supportProj (D := D) ρ hρ_psd) *
        MPSTensor.supportProj (D := D) ρ hρ_psd =
      E (MPSTensor.supportProj (D := D) ρ hρ_psd * X *
        MPSTensor.supportProj (D := D) ρ hρ_psd) := by
  obtain ⟨r, K, hK⟩ := hE.cp
  have hE_eq_transfer : E = MPSTensor.transferMap (d := r) (D := D) K := by
    ext1 X
    simp only [MPSTensor.transferMap_apply]
    exact hK X
  have hρ_fix' : MPSTensor.transferMap (d := r) (D := D) K ρ = ρ := by
    simpa [hE_eq_transfer] using hρ_fix
  let P : Mat := MPSTensor.supportProj (D := D) ρ hρ_psd
  have hP_data :
      IsOrthogonalProjection P ∧
        (∀ i : Fin r, (1 - P) * K i * P = 0) := by
    simpa [P] using
      (MPSTensor.lowerZero_of_posSemidef_fixedPoint
        (d := r) (D := D) K ρ hρ_psd hρ_fix')
  intro X
  rw [hE_eq_transfer]
  simpa [P] using MPSTensor.lowerZero_implies_invariance K P hP_data.1 hP_data.2 X

/-- Chosen stationary state of an irreducible channel. -/
noncomputable def stationaryState
    (E : Mat →ₗ[ℂ] Mat) (hE : IsChannel E)
    (hIrr : IsIrreducibleMap E) (hD : 0 < D) : Mat :=
  Classical.choose (IsChannel.exists_unique_density_fixedPoint_of_irreducible
    (E := E) hE hIrr hD)

lemma stationaryState_spec
    {E : Mat →ₗ[ℂ] Mat} (hE : IsChannel E)
    (hIrr : IsIrreducibleMap E) (hD : 0 < D) :
    stationaryState E hE hIrr hD ∈ densityMatrices D ∧
      (stationaryState E hE hIrr hD).PosDef ∧
      E (stationaryState E hE hIrr hD) = stationaryState E hE hIrr hD := by
  have hspec :
      stationaryState E hE hIrr hD ∈ densityMatrices D ∧
        (stationaryState E hE hIrr hD).PosDef ∧
        E (stationaryState E hE hIrr hD) = stationaryState E hE hIrr hD ∧
        ∀ τ : Mat,
          τ ∈ densityMatrices D →
            E τ = τ → τ = stationaryState E hE hIrr hD := by
    simpa [stationaryState] using
      (Classical.choose_spec
        (IsChannel.exists_unique_density_fixedPoint_of_irreducible
          (E := E) hE hIrr hD))
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩

/-- Support projection of the unique fixed-point density matrix of an irreducible
channel. -/
noncomputable def stationarySupport
    (E : Mat →ₗ[ℂ] Mat) (hE : IsChannel E)
    (hIrr : IsIrreducibleMap E) (hD : 0 < D) : Mat :=
  MPSTensor.supportProj (D := D)
    (stationaryState E hE hIrr hD)
    (stationaryState_spec (E := E) hE hIrr hD).1.1

lemma stationarySupport_isOrthogonalProjection
    {E : Mat →ₗ[ℂ] Mat} (hE : IsChannel E)
    (hIrr : IsIrreducibleMap E) (hD : 0 < D) :
    IsOrthogonalProjection (stationarySupport E hE hIrr hD) := by
  simpa [stationarySupport] using
    (MPSTensor.isOrthogonalProjection_supportProj (D := D)
      (ρ := stationaryState E hE hIrr hD)
      (hρ := (stationaryState_spec (E := E) hE hIrr hD).1.1))

lemma stationarySupport_invariant
    {E : Mat →ₗ[ℂ] Mat} (hE : IsChannel E)
    (hIrr : IsIrreducibleMap E) (hD : 0 < D) :
    ∀ X : Mat,
      stationarySupport E hE hIrr hD *
        E (stationarySupport E hE hIrr hD * X * stationarySupport E hE hIrr hD) *
        stationarySupport E hE hIrr hD =
      E (stationarySupport E hE hIrr hD * X * stationarySupport E hE hIrr hD) := by
  simpa [stationarySupport] using
    (support_proj_fixed (D := D) (E := E) hE
      (hρ_psd := (stationaryState_spec (E := E) hE hIrr hD).1.1)
      (hρ_fix := (stationaryState_spec (E := E) hE hIrr hD).2.2))

private lemma stationaryState_ne_zero
    {E : Mat →ₗ[ℂ] Mat} (hE : IsChannel E)
    (hIrr : IsIrreducibleMap E) (hD : 0 < D) :
    stationaryState E hE hIrr hD ≠ 0 := by
  intro hzero
  have htr : Matrix.trace (stationaryState E hE hIrr hD) = 1 :=
    (stationaryState_spec (E := E) hE hIrr hD).1.2
  have : Matrix.trace (stationaryState E hE hIrr hD) = 0 := by
    simp [hzero]
  have h10 : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = Matrix.trace (stationaryState E hE hIrr hD) := htr.symm
      _ = 0 := this
  exact one_ne_zero h10

/-- Prop. 6.9: for an irreducible channel, the stationary support is full. -/
theorem stationarySupport_eq_one
    {E : Mat →ₗ[ℂ] Mat} (hE : IsChannel E)
    (hIrr : IsIrreducibleMap E) (hD : 0 < D) :
    stationarySupport E hE hIrr hD = 1 := by
  let P := stationarySupport E hE hIrr hD
  have hP_proj : IsOrthogonalProjection P :=
    stationarySupport_isOrthogonalProjection (E := E) hE hIrr hD
  have hP_inv : ∀ X : Mat, P * E (P * X * P) * P = E (P * X * P) := by
    simpa [P] using stationarySupport_invariant (E := E) hE hIrr hD
  have hP_zero_or_one : P = 0 ∨ P = 1 := hIrr P hP_proj hP_inv
  rcases hP_zero_or_one with hP0 | hP1
  · exfalso
    have hρ_psd : (stationaryState E hE hIrr hD).PosSemidef :=
      (stationaryState_spec (E := E) hE hIrr hD).1.1
    have hρ_ne : stationaryState E hE hIrr hD ≠ 0 :=
      stationaryState_ne_zero (E := E) hE hIrr hD
    have hP_ne : P ≠ 0 := by
      simpa [P, stationarySupport] using
        (MPSTensor.supportProj_ne_zero_of_ne_zero
          (ρ := stationaryState E hE hIrr hD) hρ_psd hρ_ne)
    exact hP_ne hP0
  · simpa [P] using hP1

/-
TODO (Wolf Props. 6.9–6.10):
The original declarations `irreducible_iff_support_full` and
`stationary_support_minimal` were removed because their previous formulations
were vacuous/trivial. They should be replaced by:
* a non-vacuous Prop. 6.9 equivalence (irreducibility ↔ full support of
  stationary states), and
* Prop. 6.10 minimality of stationary support without assuming irreducibility.
-/

end Channel
