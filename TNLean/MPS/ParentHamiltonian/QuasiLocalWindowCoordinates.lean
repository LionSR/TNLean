/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IntervalObservableCoordinates
import TNLean.MPS.ParentHamiltonian.BulkObservableAlgebra
import TNLean.QCA.QuasiLocalInterval

/-!
# Quasi-local coordinates of a finite observable window

Identity extensions and nonwrapping finite-chain windows represent the same
quasi-local observable. These are shared interval-coordinate identities for
parent-Hamiltonian commutators and actual MPU circuit windows.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, local observable
convention; CPSV17, arXiv:1703.09188, Appendix, lines 2292--2306.
-/

open MPSTensor
open scoped Matrix

namespace SpinChain

variable {d : ℕ} [NeZero d]

/-- Identity extensions of an interval observable have the same quasi-local
image, including empty intervals. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 3, the local observable convention. -/
theorem quasiLocalIntervalObservable_bulkObservable (a : ℤ) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (ℓ r : ℕ) :
    quasiLocalIntervalObservable d (a - (ℓ : ℤ)) ((ℓ + k) + r)
      (bulkObservable X ℓ r) = quasiLocalIntervalObservable d a k X := by
  have h := congrArg (quasiLocalIntervalObservable d (a - (ℓ : ℤ)) ((ℓ + k) + r))
    (intervalCoordinates_localInclusion_eq_bulkObservable d a k ℓ r
      ((intervalCoordinates d a k).symm X))
  simpa only [quasiLocalIntervalObservable_apply, StarAlgEquiv.apply_symm_apply,
    StarAlgEquiv.symm_apply_apply, quasiLocalObservable_localInclusion] using h.symm

/-- A nonwrapping finite-chain window has its ordinary translated interval
image in the quasi-local algebra. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 3. -/
theorem quasiLocalIntervalObservable_chainWindowOperator (a : ℤ) (N b : ℕ) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hk : 0 < k) (hb : b + k ≤ N) :
    quasiLocalIntervalObservable d a N (chainWindowOperator N b X) =
      quasiLocalIntervalObservable d (a + (b : ℤ)) k X := by
  have h := quasiLocalIntervalObservable_bulkObservable (a + (b : ℤ)) X b (N - (b + k))
  rw [bulkObservable_eq_chainWindowOperator hk, Nat.add_sub_of_le hb,
    add_sub_cancel_right] at h
  exact h

end SpinChain
