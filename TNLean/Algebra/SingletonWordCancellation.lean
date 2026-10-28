/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Cancellation of a singleton sample label

Sum an ordered product over all assignments from a finite set of sample labels
to a finite alphabet. If one label occurs exactly once, and its factor has sum
zero over the alphabet, the whole sum vanishes. The factors need not commute,
and they may depend on their positions in the word.

This is a supporting result for the finite even-moment approach to the sampled
projection in LVV, arXiv:1307.5143v1, Section 2.3.1. It proves no matrix moment
bound or concentration inequality. The ground-energy dependence of the source
sampler is discussed in `docs/paper-gaps/lvv13_sampling_ground_energy.tex`.
-/

open Finset Function

namespace Fintype

open Classical in
/-- Summing an ordered noncommutative word over independent uniform sample assignments
gives zero if a sample label occurs once and its factor is centered. The factors may
depend on their positions. This is the finite singleton-cancellation step in an
otherwise unproved moment argument for LVV, arXiv:1307.5143v1, Section 2.3.1. -/
theorem sum_ordered_word_eq_zero_of_singleton {α β R : Type*}
    [Fintype α] [Fintype β] [Semiring R] {m : ℕ}
    (s : Fin m → β) (t : Fin m)
    (hs : ∀ k, s k = s t → k = t) (Φ : Fin m → α → R)
    (hΦ : ∑ a, Φ t a = 0) :
    ∑ σ : β → α, (List.ofFn fun k ↦ Φ k (σ (s k))).prod = 0 := by
  classical
  let e := Equiv.funSplitAt (s t) α
  rw [← e.symm.sum_comp (fun σ ↦ (List.ofFn fun k ↦ Φ k (σ (s k))).prod)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro θ _
  let v (k : Fin m) : R :=
    if hk : k = t then 0 else Φ k (θ ⟨s k, fun heq ↦ hk (hs k heq)⟩)
  have heval (a : α) :
      (fun k ↦ Φ k (e.symm (a, θ) (s k))) = Function.update v t (Φ t a) := by
    funext k
    by_cases hk : k = t
    · subst k
      simp [e, Equiv.funSplitAt_symm_apply]
    · have hsk : s k ≠ s t := fun h ↦ hk (hs k h)
      simp [e, Equiv.funSplitAt_symm_apply, v, hk, hsk]
  simp_rw [heval]
  let F := MultilinearMap.mkPiAlgebraFin ℕ m R
  change ∑ a, F (Function.update v t (Φ t a)) = 0
  rw [← F.map_update_sum, hΦ]
  exact F.map_update_zero v t

end Fintype
