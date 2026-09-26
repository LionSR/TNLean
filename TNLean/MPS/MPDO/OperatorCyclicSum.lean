/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.MPDO.Defs

/-!
# Entries of a periodic operator as a sum over bond configurations

The entry of the periodic operator of a matrix product operator tensor at the output and input
configurations `(s, t)` is the sum over closed bond configurations `g` of the products
`∏_n M^{s_n t_n}_{g_n g_{n+1}}` around the chain. When every bond configuration except one
meets a vanishing factor, the entry is the single product along the surviving configuration.
This is the way the periodic operators of monomial tensors, such as the CZX matrix product
unitaries, are computed.

## Main results

* `MPOTensor.mpo_apply_eq_sum_cyclic`: the entry as a sum over closed bond configurations.
* `MPOTensor.mpo_apply_eq_prod_of_forced_bond`: the entry as the product along the unique
  bond configuration that is not forced to vanish.
* `MPOTensor.mpo_apply_of_forced_right_bond`, `MPOTensor.mpo_apply_of_forced_left_bond`: for a
  monomial tensor whose output is a function of the input and one of whose bonds is a function
  of the physical indices, the entry is a product of phases along the forced bonds when the
  output configuration is the sitewise image of the input configuration, and zero otherwise.
-/

open scoped BigOperators

namespace MPOTensor

variable {d D N : ℕ} [NeZero N]

/-- The entry of the periodic operator at `(s, t)` is the sum over closed bond configurations
of the products of the tensor entries around the chain. -/
theorem mpo_apply_eq_sum_cyclic (M : MPOTensor d D) (s t : Fin N → Fin d) :
    mpo M N s t = ∑ g : Fin N → Fin D, ∏ n : Fin N, M (s n) (t n) (g n) (g (n + 1)) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  have h := MPSTensor.trace_evalWord_eq_sum_cyclic M.toMPSTensor
    (fun n ↦ finProdFinEquiv (s n, t n))
  rw [MPSTensor.evalWord_ofFn_eq_prod] at h
  simpa only [toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat] using h

/-- **A periodic entry along a forced bond configuration.** If every closed bond configuration
other than `g₀` meets a vanishing tensor entry, then the entry of the periodic operator at
`(s, t)` is the product of the tensor entries along `g₀`. -/
theorem mpo_apply_eq_prod_of_forced_bond (M : MPOTensor d D) (s t : Fin N → Fin d)
    (g₀ : Fin N → Fin D) (h : ∀ g, g ≠ g₀ → ∃ n, M (s n) (t n) (g n) (g (n + 1)) = 0) :
    mpo M N s t = ∏ n : Fin N, M (s n) (t n) (g₀ n) (g₀ (n + 1)) := by
  rw [mpo_apply_eq_sum_cyclic, Fintype.sum_eq_single g₀]
  intro g hg
  obtain ⟨n, hn⟩ := h g hg
  exact Finset.prod_eq_zero (Finset.mem_univ n) hn

/-- **The periodic operator of a monomial tensor with a forced outgoing bond.** Suppose that the
entry `M^{ij}_{lr}` vanishes unless the output is `i = π j` and the outgoing bond is
`r = β i j`, and then equals `φ i j l`. Then the entry of the periodic operator at `(s, t)`
vanishes unless `s = π ∘ t`, and then it is the product over the edges `(n, n + 1)` of the phase
of site `n + 1` evaluated at the bond forced by site `n`. -/
theorem mpo_apply_of_forced_right_bond {M : MPOTensor d D} {π : Fin d → Fin d}
    {β : Fin d → Fin d → Fin D} {φ : Fin d → Fin d → Fin D → ℂ}
    (hM : ∀ i j l r, M i j l r = if i = π j ∧ r = β i j then φ i j l else 0)
    (s t : Fin N → Fin d) :
    mpo M N s t = if s = (fun n ↦ π (t n)) then
      ∏ n : Fin N, φ (s (n + 1)) (t (n + 1)) (β (s n) (t n)) else 0 := by
  rw [mpo_apply_eq_prod_of_forced_bond M s t (fun n ↦ β (s (n - 1)) (t (n - 1))) fun g hg ↦ ?_]
  · split_ifs with hst
    · refine (Fintype.prod_equiv (Equiv.addRight 1) _ _ fun n ↦ ?_).symm
      rw [Equiv.coe_addRight, hM, ite_eq_left ⟨congrFun hst _, by simp⟩, add_sub_cancel_right]
    · obtain ⟨n, hn⟩ := Function.ne_iff.mp hst
      exact Finset.prod_eq_zero (Finset.mem_univ n) (by rw [hM, ite_eq_right fun h ↦ hn h.1])
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    refine ⟨n - 1, ?_⟩
    rw [hM, ite_eq_right fun h ↦ hn ?_]
    simpa using h.2

/-- **The periodic operator of a monomial tensor with a forced incoming bond.** Suppose that the
entry `M^{ij}_{lr}` vanishes unless the output is `i = π j` and the incoming bond is
`l = β i j`, and then equals `φ i j r`. Then the entry of the periodic operator at `(s, t)`
vanishes unless `s = π ∘ t`, and then it is the product over the sites `n` of the phase of site
`n` evaluated at the bond forced by site `n + 1`. -/
theorem mpo_apply_of_forced_left_bond {M : MPOTensor d D} {π : Fin d → Fin d}
    {β : Fin d → Fin d → Fin D} {φ : Fin d → Fin d → Fin D → ℂ}
    (hM : ∀ i j l r, M i j l r = if i = π j ∧ l = β i j then φ i j r else 0)
    (s t : Fin N → Fin d) :
    mpo M N s t = if s = (fun n ↦ π (t n)) then
      ∏ n : Fin N, φ (s n) (t n) (β (s (n + 1)) (t (n + 1))) else 0 := by
  rw [mpo_apply_eq_prod_of_forced_bond M s t (fun n ↦ β (s n) (t n)) fun g hg ↦ ?_]
  · split_ifs with hst
    · exact Finset.prod_congr rfl fun n _ ↦ by rw [hM, ite_eq_left ⟨congrFun hst n, rfl⟩]
    · obtain ⟨n, hn⟩ := Function.ne_iff.mp hst
      exact Finset.prod_eq_zero (Finset.mem_univ n) (by rw [hM, ite_eq_right fun h ↦ hn h.1])
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    exact ⟨n, by rw [hM, ite_eq_right fun h ↦ hn h.2]⟩

end MPOTensor
