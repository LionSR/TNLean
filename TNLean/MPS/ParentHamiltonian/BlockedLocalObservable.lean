/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedInteractionWindow

/-!
# Original local observables in blocked interval coordinates

Every observable on a nonempty original interval is the image under blocking
of an observable on a nonempty blocked interval. Enlarge the original support
to an aligned interval, adjoin identities, and invert the configuration
reindexing. Negative starts are included. No tensor, state, or translation
invariance is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, site regrouping at lines
825--836 and the local observable convention in Section 3.
-/

open SpinChain MPSTensor
namespace SpinChain
variable {d L : ℕ} [NeZero d] [NeZero L]
/-- An arbitrary positive-length original interval observable is the
blocked image of a positive-length interval observable. Its blocked support
may be larger than necessary. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 825--836 and Section 3. -/
theorem exists_blocked_quasiLocalIntervalObservable
    (a : ℤ) {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hk : 0 < k) :
    ∃ (b : ℤ) (N : ℕ), 0 < N ∧
      ∃ Y : Matrix (Cfg (blockPhysDim d L) N) (Cfg (blockPhysDim d L) N) ℂ,
        quasiLocalBlocking d L (quasiLocalIntervalObservable (blockPhysDim d L) b N Y) =
          quasiLocalIntervalObservable d a k X := by
  let c := (a % (L : ℤ)).toNat
  have hc : (c : ℤ) = a % (L : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast NeZero.ne L))
  refine ⟨a / (L : ℤ), c + k, by omega,
    (Matrix.reindexLinearEquiv ℂ ℂ (blockedConfigEquiv d (c + k) L)
      (blockedConfigEquiv d (c + k) L)).symm
      (chainWindowOperator ((c + k) * L) c X), ?_⟩
  rw [quasiLocalBlocking_quasiLocalIntervalObservable]
  change quasiLocalIntervalObservable d ((a / (L : ℤ)) * L) ((c + k) * L)
    ((Matrix.reindexLinearEquiv ℂ ℂ (blockedConfigEquiv d (c + k) L)
      (blockedConfigEquiv d (c + k) L))
      ((Matrix.reindexLinearEquiv ℂ ℂ (blockedConfigEquiv d (c + k) L)
        (blockedConfigEquiv d (c + k) L)).symm
          (chainWindowOperator ((c + k) * L) c X))) = _
  rw [LinearEquiv.apply_symm_apply,
    quasiLocalIntervalObservable_chainWindowOperator _ _ _ X hk
      (Nat.le_mul_of_pos_right (c + k) (NeZero.pos L))]
  simp only [hc, Int.ediv_mul_add_emod]

end SpinChain
