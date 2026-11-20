/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Teleportation.ZeroSubspace

/-!
# Infinite control and zero regions

A shift at site zero can depend on every other natural-number site. The vector
supported on the all-zero configuration is nonzero and has zero labels on all
natural-number sites. These statements concern configurations and vectors as
functions; they assert no infinite-dimensional matrix or norm theorem.
-/

open QuantumCircuit

namespace ConfigurationSetScopeRegression

open Classical in
noncomputable def tailControl (x : ℕ → Fin 2) : Fin 2 :=
  if ∀ n, n ≠ 0 → x n = 0 then 0 else 1

theorem tailControl_update (x : ℕ → Fin 2) (c : Fin 2) :
    tailControl (Function.update x 0 c) = tailControl x := by
  classical
  have h : (∀ n, n ≠ 0 → Function.update x 0 c n = 0) ↔
      ∀ n, n ≠ 0 → x n = 0 := by
    constructor <;> intro h n hn <;> simpa [Function.update_of_ne hn] using h n hn
  simp only [tailControl, h]

example : IsLocalPerm (Set.univ : Set ℕ) (shiftPerm 0 tailControl tailControl_update) := by
  apply isLocalPerm_shiftPerm (Set.mem_univ 0)
  intro x y h
  exact congrArg tailControl (funext fun n => h n (Set.mem_univ n))

-- Every positive site can change the shifted value at zero.
example (n : ℕ) (hn : n ≠ 0) :
    shiftPerm 0 tailControl tailControl_update (fun _ => 0) 0 ≠
      shiftPerm 0 tailControl tailControl_update (Function.update (fun _ => 0) n 1) 0 := by
  have h : ¬∀ k, k ≠ 0 → Function.update (fun _ => (0 : Fin 2)) n 1 k = 0 := by
    intro h
    have := h n hn
    simp at this
  simp [shiftPerm_apply, tailControl, h, Ne.symm hn]

open Classical in
noncomputable def vacuum (x : ℕ → Fin 2) : ℂ :=
  if x = fun _ => 0 then 1 else 0

example : vacuum ∈ zeroOnSubmodule (Set.univ : Set ℕ) := by
  intro x hx i _
  by_cases h : x = fun _ => 0
  · simp [h]
  · simp [vacuum, h] at hx

example : vacuum ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 0)
  simp [vacuum] at this

-- Finite matrix support still uses the unique canonical owner.
example {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (σ : Equiv.Perm (ι → Fin d)) (h : IsLocalPerm (S : Set ι) σ) :
    σ.permMatrix ℂ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S :=
  h.permMatrix_mem_supportedOperators

end ConfigurationSetScopeRegression
