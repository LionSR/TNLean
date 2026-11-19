/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.HoneycombPlaquetteInjectivity

/-! # Edgewise graph-state contraction for a cut

Rows are written in split coordinates: one spin per crossing leg and one spin per
remaining site. Identifying these coordinates and the edgewise product with an
open-region coefficient matrix is a separate incidence reindexing.
-/

open scoped BigOperators
open ManyBody (Edge)

namespace TNLean.PEPS.GraphStateCut

variable {V I B J : Type*} [LinearOrder V] (G : SimpleGraph V)
variable [Fintype I] [Fintype B] [Fintype J]
variable [DecidableEq I] [DecidableEq B] [DecidableEq J]
variable (inner : I → Edge G) (outer : B → Edge G) (site : B → V)

/-- Contract both endpoint legs of every internal bond, keeping the cut legs free. -/
noncomputable def entry (s : V → Fin 2) (x u : B → Fin 2) : ℂ :=
  ∑ η : I → Fin 2,
    (∏ i, graphStateLeg G (inner i).1.1 (inner i) (η i) (s (inner i).1.1) *
      graphStateLeg G (inner i).1.2 (inner i) (η i) (s (inner i).1.2)) *
    ∏ i, graphStateLeg G (site i) (outer i) (u i) (x i)

omit [DecidableEq B] in
theorem entry_factor (s : V → Fin 2) (x u : B → Fin 2) :
    entry G inner outer site s x u =
      (∏ i, hadamardEntry (s (inner i).1.1) (s (inner i).1.2)) *
      ∏ i, graphStateLeg G (site i) (outer i) (u i) (x i) := by
  classical
  unfold entry
  rw [← Finset.sum_mul, ← Fintype.prod_sum (fun (i : I) (b : Fin 2) =>
    graphStateLeg G (inner i).1.1 (inner i) b (s (inner i).1.1) *
      graphStateLeg G (inner i).1.2 (inner i) b (s (inner i).1.2))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [graphStateLeg, (inner i).2.1.ne]

private theorem legGram (v : V) (e : Edge G) (u w : Fin 2) :
    ∑ t : Fin 2, star (graphStateLeg G v e u t) * graphStateLeg G v e w t =
      if u = w then 1 else 0 := by
  unfold graphStateLeg
  split
  · exact hadamardEntry_columnGram u w
  · fin_cases u <;> fin_cases w <;> norm_num [Fin.sum_univ_two]

private theorem signGram (u v : Fin 2) :
    star (hadamardEntry u v) * hadamardEntry u v = (2 : ℂ)⁻¹ := by
  fin_cases u <;> fin_cases v <;> norm_num [hadamardEntry, Complex.invSqrtTwo_mul_self]

/-- Each free interior spin doubles the diagonal Gram entry, and each contracted
edge contributes a factor of one half. Internal spins may depend on the full row. -/
theorem columnGram
    (spin : (J → Fin 2) → (B → Fin 2) → V → Fin 2) (u v : B → Fin 2) :
    ∑ y : J → Fin 2, ∑ x : B → Fin 2,
      star (entry G inner outer site (spin y x) x u) *
        entry G inner outer site (spin y x) x v =
      (2 : ℂ) ^ Fintype.card J * (2 : ℂ)⁻¹ ^ Fintype.card I *
        (if u = v then 1 else 0) := by
  classical
  simp only [entry_factor, map_mul,
    show ∀ z : ℂ, star z = (starRingEnd ℂ) z by intro z; rfl, map_prod]
  conv_lhs =>
    enter [2, y, 2, x]
    rw [show ∀ a b c d : ℂ, (a * b) * (c * d) = (a * c) * (b * d) by intros; ring]
  simp only [← Finset.prod_mul_distrib,
    ← show ∀ z : ℂ, star z = (starRingEnd ℂ) z by intro z; rfl, signGram,
    Finset.prod_const, Finset.card_univ]
  simp_rw [← Finset.mul_sum, ← Fintype.prod_sum (fun i t =>
    star (graphStateLeg G (site i) (outer i) (u i) t) *
      graphStateLeg G (site i) (outer i) (v i) t), legGram]
  by_cases h : u = v
  · simp [h, nsmul_eq_mul, mul_comm]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (i := i) (f := fun j => if u j = v j then (1 : ℂ) else 0)
      (Finset.mem_univ i) (ite_eq_right hi)]
    simp [h]

end TNLean.PEPS.GraphStateCut
