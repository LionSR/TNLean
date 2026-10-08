/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IntervalObservableCoordinates
import TNLean.MPS.ParentHamiltonian.BulkObservableCommutator
import TNLean.QCA.QuasiLocalInterval

/-!
# Fixed support of finite-volume commutator energies

The quasi-local inclusion of an interior observable is independent of the
free physical intervals around it. For a finite-range interaction, its
commutator energy is supported on the fixed interval obtained by adjoining
one interaction margin on each side. Consequently its quasi-local image is
literally constant once the finite volume contains those margins.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3 and lines 2649--2675.
These are locality identities for arbitrary finite matrices; they do not
require a tensor, a state, or a spectral-gap assumption.
-/

open Filter MPSTensor
open scoped Matrix Topology

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

/-- The finite-volume commutator energy has a fixed quasi-local support once
both interaction margins are present. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem quasiLocalIntervalObservable_bulkObservable_commutator (a : ℤ) {R k ℓ r : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hk : 0 < k) (hℓ : R - 1 ≤ ℓ) (hr : R - 1 ≤ r) :
    quasiLocalIntervalObservable d (a - (ℓ : ℤ)) ((ℓ + k) + r)
      ((bulkObservable X ℓ r)ᴴ *
        (openInteractionMatrix h ((ℓ + k) + r) * bulkObservable X ℓ r -
          bulkObservable X ℓ r * openInteractionMatrix h ((ℓ + k) + r))) =
      quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X) := by
  rw [bulkObservable_adjoint_mul_openInteractionMatrix_commutator h X hR hk hℓ hr]
  rw [quasiLocalIntervalObservable_chainWindowOperator _ _ _ _ (by omega) (by omega)]
  congr 2
  omega

/-- Along expanding free intervals, the quasi-local commutator energy is
eventually equal to one fixed local observable. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem eventually_quasiLocalIntervalObservable_bulkObservable_commutator_eq
    (a : ℤ) {R k : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    ∀ᶠ n in f,
      quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
        ((bulkObservable X (ℓ n) (r n))ᴴ *
          (openInteractionMatrix h ((ℓ n + k) + r n) * bulkObservable X (ℓ n) (r n) -
            bulkObservable X (ℓ n) (r n) * openInteractionMatrix h ((ℓ n + k) + r n))) =
        quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
          ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X) := by
  filter_upwards [hℓ.eventually (eventually_ge_atTop (R - 1)),
    hr.eventually (eventually_ge_atTop (R - 1))] with n hln hrn
  exact quasiLocalIntervalObservable_bulkObservable_commutator a h X hR hk hln hrn

/-- The literal finite-volume commutator energies converge in the quasi-local
algebra to their fixed local representative. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem tendsto_quasiLocalIntervalObservable_bulkObservable_commutator
    (a : ℤ) {R k : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hR : 0 < R) (hk : 0 < k)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n ↦
      quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
        ((bulkObservable X (ℓ n) (r n))ᴴ *
          (openInteractionMatrix h ((ℓ n + k) + r n) * bulkObservable X (ℓ n) (r n) -
            bulkObservable X (ℓ n) (r n) * openInteractionMatrix h ((ℓ n + k) + r n)))) f
      (nhds (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X))) := by
  exact tendsto_const_nhds.congr'
    (Filter.EventuallyEq.symm
      (eventually_quasiLocalIntervalObservable_bulkObservable_commutator_eq a h X hR hk hℓ hr))

/-- Evaluation of the literal commutator energy converges to evaluation of
its fixed local representative. Because the quasi-local observable is
eventually constant, continuity or positivity of the functional is not needed.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem tendsto_apply_quasiLocalIntervalObservable_bulkObservable_commutator
    (ω : QuasiLocalAlgebra d → ℂ) (a : ℤ) {R k : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hk : 0 < k)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n ↦ ω
      (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
        ((bulkObservable X (ℓ n) (r n))ᴴ *
          (openInteractionMatrix h ((ℓ n + k) + r n) * bulkObservable X (ℓ n) (r n) -
            bulkObservable X (ℓ n) (r n) * openInteractionMatrix h ((ℓ n + k) + r n))))) f
      (nhds (ω (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)))) := by
  exact tendsto_const_nhds.congr'
    (Filter.EventuallyEq.fun_comp (Filter.EventuallyEq.symm
      (eventually_quasiLocalIntervalObservable_bulkObservable_commutator_eq a h X hR hk hℓ hr)) ω)

/-- The literal quasi-local product \(X^*[H_N,X]\) is the fixed local
commutator observable once the finite volume contains both interaction
margins. Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem quasiLocalIntervalObservable_commutator_locality (a : ℤ) {R k ℓ r : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hk : 0 < k) (hℓ : R - 1 ≤ ℓ) (hr : R - 1 ≤ r) :
    star (quasiLocalIntervalObservable d a k X) *
        (quasiLocalIntervalObservable d (a - (ℓ : ℤ)) ((ℓ + k) + r)
            (openInteractionMatrix h ((ℓ + k) + r)) *
          quasiLocalIntervalObservable d a k X -
          quasiLocalIntervalObservable d a k X *
            quasiLocalIntervalObservable d (a - (ℓ : ℤ)) ((ℓ + k) + r)
              (openInteractionMatrix h ((ℓ + k) + r))) =
      quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X) := by
  simpa only [← Matrix.star_eq_conjTranspose, map_mul, map_sub, map_star,
    quasiLocalIntervalObservable_bulkObservable] using
      quasiLocalIntervalObservable_bulkObservable_commutator a h X hR hk hℓ hr

/-- Evaluation of the literal finite-volume quasi-local commutator energy
converges to evaluation of the fixed local commutator observable. This holds
for every functional, since the energy observable is eventually constant.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem tendsto_apply_quasiLocalIntervalObservable_commutator
    (ω : QuasiLocalAlgebra d → ℂ) (a : ℤ) {R k : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hR : 0 < R) (hk : 0 < k)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n ↦ ω (star (quasiLocalIntervalObservable d a k X) *
      (quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
          (openInteractionMatrix h ((ℓ n + k) + r n)) *
        quasiLocalIntervalObservable d a k X -
        quasiLocalIntervalObservable d a k X *
          quasiLocalIntervalObservable d (a - (ℓ n : ℤ)) ((ℓ n + k) + r n)
            (openInteractionMatrix h ((ℓ n + k) + r n))))) f
      (nhds (ω (quasiLocalIntervalObservable d (a - ((R - 1 : ℕ) : ℤ))
        ((R - 1 + k) + (R - 1)) (localCommutatorObservable h X)))) := by
  simpa only [← Matrix.star_eq_conjTranspose, map_mul, map_sub, map_star,
    quasiLocalIntervalObservable_bulkObservable] using
      tendsto_apply_quasiLocalIntervalObservable_bulkObservable_commutator ω a h X hR hk hℓ hr

end SpinChain
