/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.GraphStateCutConverse

/-! # Exact dimension of the graph-state open-region image -/

open scoped BigOperators
namespace TNLean.PEPS.GraphStateCut
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (R : Finset V)

private noncomputable def row (t : Occupied G R → Fin 2) (u : Crossing G R → Fin 2) : ℂ :=
  ∏ e, graphStateLeg G (inside G R e).1 e.1 (u e) (t ⟨_,e,rfl⟩)

open scoped Classical in
theorem boundary_row_orthogonal (t s : Occupied G R → Fin 2) :
    ∑ u, row G R t u * star (row G R s u) = if t = s then 1 else 0 := by
  classical
  have leg (e : Crossing G R) (a b : Fin 2) :
      ∑ j : Fin 2, graphStateLeg G (inside G R e).1 e.1 j a *
        star (graphStateLeg G (inside G R e).1 e.1 j b) = if a = b then 1 else 0 := by
    unfold graphStateLeg
    split <;> fin_cases a <;> fin_cases b <;>
      norm_num [Fin.sum_univ_two, hadamardEntry, Complex.invSqrtTwo_mul_self]
  unfold row
  simp only [show ∀ z : ℂ, star z = (starRingEnd ℂ) z by intro z; rfl, map_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (e : Crossing G R) (j : Fin 2) =>
    graphStateLeg G (inside G R e).1 e.1 j (t ⟨_,e,rfl⟩) *
      (starRingEnd ℂ) (graphStateLeg G (inside G R e).1 e.1 j (s ⟨_,e,rfl⟩)))]
  simp_rw [← show ∀ z : ℂ, star z = (starRingEnd ℂ) z by intro z; rfl, leg]
  by_cases h : t = s
  · simp [h]
  · obtain ⟨⟨_,e,rfl⟩,hne⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right hne)).trans (ite_eq_right h).symm

theorem boundaryPart_surjective : Function.Surjective (boundaryPart G R) := by
  classical
  intro y
  refine ⟨fun u => ∑ s, y s * star (row G R s u), ?_⟩
  funext t
  simp only [boundaryPart, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s, y s * (∑ u, row G R t u * star (row G R s u)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      change _ * row G R t u = _
      ring
    _ = _ := by simp_rw [boundary_row_orthogonal]; simp

private noncomputable def physicalPart :
    ((Occupied G R → Fin 2) → ℂ) →ₗ[ℂ] (RegionPhysicalConfig (d := 2) R → ℂ) where
  toFun y s := internalFactor G R s * y (fun v => s v.1)
  map_add' _ _ := by ext; simp [mul_add]
  map_smul' _ _ := by ext; simp [mul_left_comm]

open scoped Classical in
theorem finrank_range_openRegionMap :
    Module.finrank ℂ (LinearMap.range (openRegionMap (graphStatePEPS G) R)) =
      2 ^ Fintype.card (Occupied G R) := by
  classical
  have inj : Function.Injective (physicalPart G R) := by
    intro f g eq
    funext t
    let s (v : R) := if h : v ∈ Set.range (inside G R) then t ⟨v,h⟩ else 0
    have read : (fun v : Occupied G R => s v.1) = t := by
      funext v
      exact dite_eq_left v.2
    have he := congrFun eq s
    change internalFactor G R s * f _ = internalFactor G R s * g _ at he
    rw [read] at he
    exact mul_left_cancel₀ (internalFactor_ne_zero G R s) he
  have factor : openRegionMap (graphStatePEPS G) R = (physicalPart G R).comp (boundaryPart G R) :=
    LinearMap.ext fun z => funext (map_factor G R z)
  rw [factor, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _
    (boundaryPart_surjective G R)), LinearMap.finrank_range_of_inj inj]
  simp

end TNLean.PEPS.GraphStateCut
