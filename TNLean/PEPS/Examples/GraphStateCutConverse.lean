/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.GraphStateCutRegion

/-! # A rank obstruction from coincident inside endpoints -/

open scoped BigOperators
namespace TNLean.PEPS.GraphStateCut
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Finset V)

abbrev Occupied := Set.range (inside G R)

noncomputable def internalFactor (s : RegionPhysicalConfig (d := 2) R) : ℂ :=
  ∏ i : Internal G R, hadamardEntry (s ⟨_,i.2.1⟩) (s ⟨_,i.2.2⟩)

theorem internalFactor_ne_zero (s : RegionPhysicalConfig (d := 2) R) : internalFactor G R s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp [hadamardEntry, Complex.invSqrtTwo]

/-- Only one physical bit per occupied inside endpoint enters the boundary-leg product. -/
noncomputable def boundaryPart :
    (RegionBoundaryConfig (graphStatePEPS G) R → ℂ) →ₗ[ℂ] ((Occupied G R → Fin 2) → ℂ) :=
  Fintype.linearCombination ℂ fun u t => ∏ e : Crossing G R,
    graphStateLeg G (inside G R e).1 e.1 (u e) (t ⟨_,e,rfl⟩)

theorem map_factor (z : RegionBoundaryConfig (graphStatePEPS G) R → ℂ)
    (s : RegionPhysicalConfig (d := 2) R) :
    openRegionMap (graphStatePEPS G) R z s =
      internalFactor G R s * boundaryPart G R z (fun v => s v.1) := by
  classical
  let spin (v : V) := if h : v ∈ R then s ⟨v,h⟩ else 0
  have hs (v : R) : spin v.1 = s v := by simp [spin, v.2]
  have he (u : RegionBoundaryConfig (graphStatePEPS G) R) :=
    (matrix_entry G R spin u).trans (entry_factor G _ _ _ _ _ _)
  simp only [hs] at he
  rw [openRegionMap_apply]
  simp only [boundaryPart, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  change z u * (cutMatrix G R s u) = _
  rw [show cutMatrix G R s u = _ from he u]
  unfold internalFactor
  have h1 (i : Internal G R) : spin i.1.1.1 = s ⟨_,i.2.1⟩ := hs ⟨_,i.2.1⟩
  have h2 (i : Internal G R) : spin i.1.1.2 = s ⟨_,i.2.2⟩ := hs ⟨_,i.2.2⟩
  simp_rw [h1, h2]
  ring

theorem injective_iff : Function.Injective (openRegionMap (graphStatePEPS G) R) ↔
    Function.Injective (inside G R) := by
  classical
  refine ⟨fun h => ?_, openRegionMap_injective G R⟩
  have hb : Function.Injective (boundaryPart G R) := by
    intro x y eq
    apply h
    funext s
    rw [map_factor, map_factor, eq]
  have dim := LinearMap.finrank_le_finrank_of_injective hb
  change Module.finrank ℂ (((Crossing G R → Fin 2)) → ℂ) ≤
    Module.finrank ℂ ((Occupied G R → Fin 2) → ℂ) at dim
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin] at dim
  by_contra hn
  let f := Set.rangeFactorization (inside G R)
  have hf : ¬ Function.Injective f := fun hi => hn fun _ _ eq => hi (Subtype.ext eq)
  have lt := Fintype.card_lt_of_surjective_not_injective f Set.rangeFactorization_surjective hf
  exact (not_lt_of_ge dim) (Nat.pow_lt_pow_right (by decide : 1 < 2) lt)

namespace BrickWall

private instance : Fact (1 < 6) := ⟨by decide⟩
private instance : Fact (1 < 4) := ⟨by decide⟩

/-- The two-by-two coordinate rectangle at the origin of the six-by-four torus. -/
def rectangle : Finset (TorusVertex 6 4) := {(0,0), (0,1), (1,0), (1,1)}

/-- At (1,0), the rightward and downward bonds both leave this rectangle. -/
theorem rectangle_not_injective :
    ¬ Function.Injective (openRegionMap (honeycombClusterPEPS 6 4) rectangle) := by
  intro h
  let east : Crossing (honeycombGraph 6 4) rectangle :=
    ⟨⟨((1,0), (2,0)), by decide⟩, by decide⟩
  let south : Crossing (honeycombGraph 6 4) rectangle :=
    ⟨⟨((1,0), (1,3)), by decide⟩, by decide⟩
  have he : inside _ rectangle east = inside _ rectangle south := by decide
  have hn : east ≠ south := by decide
  exact hn ((injective_iff _ rectangle).1 h he)

end BrickWall
end TNLean.PEPS.GraphStateCut
