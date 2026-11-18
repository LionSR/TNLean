/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Placement

/-!
# Placement through a containing region

For regions `R ⊆ U` of a system of sites, a matrix `K` on the configurations of `R` extends to
a matrix on the configurations of `U` by the identity on the sites of `U` outside `R`. Placing
that matrix on `U` is placing `K` on `R`: placement through an intermediate region is placement.

## Main definitions

* `ManyBody.subregionPlace`: the extension `K ⊗ 1_{U ∖ R}` of a matrix on `R` to `U`.

## Main results

* `ManyBody.place_subregionPlace`: `place U (subregionPlace hRU K) = place R K`.
* `ManyBody.exists_place_eq_place_of_subset`: an operator placed on `R` is placed on every
  region containing `R`.

## Implementation notes

The statements use only the configurations and placement of QICLean's `ManyBody` layer; they
are recorded as candidates for QICLean.
-/

open Matrix

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, DecidableEq (X v)]

/-- The extension of a matrix on the configurations of `R` to the configurations of a region
`U ⊇ R`, by the identity on the sites of `U` outside `R`. -/
noncomputable def subregionPlace {R U : Finset V} (hRU : R ⊆ U)
    (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) :
    Matrix (RegionConfig X U) (RegionConfig X U) ℂ := by
  classical
  exact fun α β ↦
    if ∀ v, ∀ hv : v ∈ U, v ∉ R → α ⟨v, hv⟩ = β ⟨v, hv⟩ then
      K (fun w ↦ α ⟨w.1, hRU w.2⟩) (fun w ↦ β ⟨w.1, hRU w.2⟩)
    else 0

/-- Placing the extension of `K` to a containing region `U` is placing `K` on `R`. -/
theorem place_subregionPlace {R U : Finset V} (hRU : R ⊆ U)
    (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) :
    place U (subregionPlace hRU K) = place R K := by
  classical
  ext σ τ
  simp only [place_apply, subregionPlace]
  by_cases hR : ∀ v ∉ R, σ v = τ v
  · have hU : ∀ v ∉ U, σ v = τ v := fun v hv ↦ hR v fun h ↦ hv (hRU h)
    rw [ite_eq_left hU, ite_eq_left (fun v _ hv ↦ hR v hv), ite_eq_left hR]
  · rw [ite_eq_right hR]
    by_cases hU : ∀ v ∉ U, σ v = τ v
    · have hUR : ¬ ∀ v, ∀ _ : v ∈ U, v ∉ R → σ v = τ v := by
        intro h
        apply hR
        intro v hv
        by_cases hvU : v ∈ U
        · exact h v hvU hv
        · exact hU v hvU
      rw [ite_eq_left hU, ite_eq_right hUR]
    · rw [ite_eq_right hU]

/-- An operator placed on `R` is placed on every region containing `R`. -/
theorem exists_place_eq_place_of_subset {R U : Finset V} (hRU : R ⊆ U)
    (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) :
    ∃ L : Matrix (RegionConfig X U) (RegionConfig X U) ℂ, place R K = place U L :=
  ⟨subregionPlace hRU K, (place_subregionPlace hRU K).symm⟩

end ManyBody
