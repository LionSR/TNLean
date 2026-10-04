/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import Mathlib.Data.ZMod.Basic

/-!
# Cyclic site permutations and window exchange

The successor permutation, its cyclic-group coordinates, and the exchange of
entries of a window are finite index geometry. They are independent of the
Knabe, spectator-transport, and singlet-Hamiltonian developments that use them.

## References

See `TNLean.MPS.ParentHamiltonian.CyclicWindow` for the cyclic window convention.
-/

namespace MPSTensor

/-- Addition in \(\mathbb Z/N\mathbb Z\) is cyclic forward motion on the
corresponding finite site. -/
theorem finEquiv_symm_add_eq_cyclicForwardSite {N : ℕ} [NeZero N]
    (s : ZMod N) (q : ℕ) :
    (ZMod.finEquiv N).symm (s + q) =
      cyclicForwardSite ((ZMod.finEquiv N).symm s) q := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N =>
      apply Fin.ext
      change (s.val + (q : ZMod (N + 1)).val) % (N + 1) =
        (s.val + q) % (N + 1)
      rw [ZMod.val_natCast, Nat.add_mod_mod]

/-- The successor permutation of the sites of a periodic chain. -/
noncomputable def cyclicSuccessorEquiv (N : ℕ) [NeZero N] : Equiv.Perm (Fin N) :=
  (ZMod.finEquiv N).toEquiv |>.trans (Equiv.addRight (1 : ZMod N))
    |>.trans (ZMod.finEquiv N).symm.toEquiv

/-- The successor permutation agrees with motion by one cyclic site. -/
theorem cyclicSuccessorEquiv_apply {N : ℕ} [NeZero N] (i : Fin N) :
    cyclicSuccessorEquiv N i = cyclicForwardSite i 1 := by
  change (ZMod.finEquiv N).symm (ZMod.finEquiv N i + 1) = _
  simpa only [Nat.cast_one, RingEquiv.symm_apply_apply] using
    finEquiv_symm_add_eq_cyclicForwardSite (ZMod.finEquiv N i) 1

/-- The successor on a ring of at least two sites has no fixed point. -/
theorem cyclicSuccessorEquiv_ne {N : ℕ} [NeZero N] (hN : 2 ≤ N) (i : Fin N) :
    cyclicSuccessorEquiv N i ≠ i := by
  let : Fact (1 < N) := ⟨by omega⟩
  intro hi
  change (ZMod.finEquiv N).symm (ZMod.finEquiv N i + 1) = i at hi
  have h := congrArg (ZMod.finEquiv N) hi
  simp only [RingEquiv.apply_symm_apply, add_eq_left] at h
  exact one_ne_zero h

/-- The cyclic successor is addition by one in the group of sites. -/
theorem finEquiv_cyclicSuccessorEquiv {N : ℕ} [NeZero N] (i : Fin N) :
    ZMod.finEquiv N (cyclicSuccessorEquiv N i) = ZMod.finEquiv N i + 1 := by
  change ZMod.finEquiv N ((ZMod.finEquiv N).symm (ZMod.finEquiv N i + 1)) = _
  exact (ZMod.finEquiv N).apply_symm_apply _

/-- The cyclic predecessor is subtraction by one in the group of sites. -/
theorem finEquiv_cyclicSuccessorEquiv_symm {N : ℕ} [NeZero N] (i : Fin N) :
    ZMod.finEquiv N ((cyclicSuccessorEquiv N).symm i) = ZMod.finEquiv N i - 1 := by
  apply (eq_sub_iff_add_eq).2
  simpa only [Equiv.apply_symm_apply] using
    (finEquiv_cyclicSuccessorEquiv ((cyclicSuccessorEquiv N).symm i)).symm

/-- Exchanging two entries of an extracted window exchanges the corresponding
sites when the window is inserted back into the chain. -/
theorem cyclicCfg_extractWindow_comp_swap_of_le {d N L : ℕ}
    (hN : 0 < N) (hLN : L ≤ N) (i : Fin N) (σ : Cfg d N) (a b : Fin L) :
    cyclicCfg hN L i (extractWindow L i σ ∘ Equiv.swap a b) σ =
      σ ∘ Equiv.swap (cyclicForwardSite i a.val) (cyclicForwardSite i b.val) := by
  rw [Equiv.comp_swap_eq_update, Equiv.comp_swap_eq_update, ← update_cyclicCfg hN hLN,
    ← update_cyclicCfg hN hLN, cyclicCfg_extractWindow hN hLN]
  rfl

end MPSTensor
