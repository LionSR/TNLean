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

end MPOTensor
