/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Products of commuting matrix projections

A finite list product of commuting star projections is a star projection.
Its fixed vectors are precisely the vectors fixed by every listed factor.
The list may be empty or contain repeated indices.

This is new implementation for the SCP10 restoration, not recovered source.
-/

open scoped Matrix

namespace Matrix

variable {ι J : Type*} [Fintype ι] [DecidableEq ι]
variable (P : J → Matrix ι ι ℂ) (hP : ∀ j, IsStarProjection (P j))
variable (hcomm : ∀ j k, Commute (P j) (P k))

private theorem commute_list_prod (j : J) (l : List J) :
    Commute (P j) (l.map P).prod := by
  apply Commute.list_prod_right
  intro A hA
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hA
  exact hcomm j k

/-- A list product of pairwise commuting star projections is a star projection. -/
theorem isStarProjection_list_prod (l : List J) :
    IsStarProjection (l.map P).prod := by
  induction l with
  | nil => simpa using (IsStarProjection.one : IsStarProjection (1 : Matrix ι ι ℂ))
  | cons j l ih =>
    simpa only [List.map_cons, List.prod_cons] using
      (hP j).mul ih (commute_list_prod P hcomm j l)

private theorem mul_list_prod_of_mem (l : List J) (j : J) (hj : j ∈ l) :
    P j * (l.map P).prod = (l.map P).prod := by
  induction l with
  | nil => simp at hj
  | cons k l ih =>
    simp only [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [← mul_assoc, (hP j).isIdempotentElem.eq]
    · rw [← mul_assoc, (hcomm j k).eq, mul_assoc, ih hj]

/-- The fixed space of a commuting projection product is the intersection of
the fixed spaces of its listed factors, including empty lists and repetitions. -/
theorem list_prod_mulVec_eq_self_iff (l : List J) (v : ι → ℂ) :
    (l.map P).prod *ᵥ v = v ↔ ∀ j ∈ l, P j *ᵥ v = v := by
  constructor
  · intro hv j hj
    calc
      P j *ᵥ v = P j *ᵥ ((l.map P).prod *ᵥ v) := congrArg (P j *ᵥ ·) hv.symm
      _ = (l.map P).prod *ᵥ v := by
        rw [mulVec_mulVec, mul_list_prod_of_mem P hP hcomm l j hj]
      _ = v := hv
  · intro hv
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, ← mulVec_mulVec]
      rw [ih (fun k hk => hv k (List.mem_cons_of_mem j hk))]
      exact hv j (List.mem_cons_self j l)

end Matrix
