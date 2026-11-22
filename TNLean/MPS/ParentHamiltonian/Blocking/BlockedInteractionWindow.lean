/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalState.QuasiLocalCommutatorLocality
import TNLean.QCA.BlockingIntervalCoordinates
import Mathlib.Analysis.Matrix.Order

/-!
# Nonwrapping interaction windows under physical blocking

Placing an arbitrary operator on consecutive blocked sites and then decoding
the configurations gives the same matrix as decoding the local operator
first and placing it on the corresponding original sites. The window start
and length are multiplied by the block length. This follows from the exact
interval observable identities and injectivity of the interval inclusion.

Consequently, the blocked open interaction sum becomes a sum over aligned
original windows. For a positive interaction, these aligned terms are bounded
by the sum over all original starts, with coefficient one. Volumes shorter
than the interaction range are included.

The window and blocking identities assume positive physical dimension and
positive block length. The positive-term counting bound requires only the
latter. No tensor, normalization, state, or spectral-gap data enter these
operator identities.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, equation (3.12),
and site regrouping at lines 825--836; CPGSV17, arXiv:1703.09188,
Appendix, lines 2308 and 2313--2320. The aligned-window upper bound is a
derived positive-term counting statement.

## Original local observables in blocked interval coordinates

Every observable on a nonempty original interval is the image under blocking
of an observable on a nonempty blocked interval. Enlarge the original support
to an aligned interval, adjoin identities, and invert the configuration
reindexing. Negative starts are included. No tensor, state, or translation
invariance is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, site regrouping at lines
825--836 and the local observable convention in Section 3.
-/

section

open SpinChain
open scoped ComplexOrder MatrixOrder
open Kraus (blockPhysDim)
open ManyBody (placeAlong chainWindow)

namespace MPSTensor

variable {d L : ℕ} [NeZero d] [NeZero L]

/-- Physical blocking commutes with placement on a window that does not wrap
around the chain: a window starting at blocked site \(b\) starts at original
site \(bL\). This is an operator identity, requiring no tensor or state data.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3 and lines 825--836;
CPGSV17, arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
theorem placeAlong_chainWindow_blocking_reindex {K N b : ℕ}
    (h : Matrix (Cfg (blockPhysDim d L) K) (Cfg (blockPhysDim d L) K) ℂ)
    (hb : b + K ≤ N) :
    Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
        (placeAlong (X := fun _ ↦ Fin (blockPhysDim d L)) (chainWindow b hb) h) =
      placeAlong (X := fun _ ↦ Fin d)
        (chainWindow (b * L) (by simpa only [Nat.add_mul] using Nat.mul_le_mul_right L hb))
        (Matrix.reindex (blockedConfigEquiv d K L) (blockedConfigEquiv d K L) h) := by
  have hbL : b * L + K * L ≤ N * L := by
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right L hb
  apply (intervalCoordinates d ((0 : ℤ) * L) (N * L)).symm.injective
  apply quasiLocalObservable_injective d (finiteChainRegion ((0 : ℤ) * L) (N * L))
  change quasiLocalIntervalObservable d ((0 : ℤ) * L) (N * L)
    (Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
      (placeAlong (X := fun _ ↦ Fin (blockPhysDim d L)) (chainWindow b hb) h)) =
    quasiLocalIntervalObservable d ((0 : ℤ) * L) (N * L)
      (placeAlong (X := fun _ ↦ Fin d) (chainWindow (b * L) hbL)
        (Matrix.reindex (blockedConfigEquiv d K L) (blockedConfigEquiv d K L) h))
  rw [← quasiLocalBlocking_quasiLocalIntervalObservable]
  rw [quasiLocalIntervalObservable_placeAlong_chainWindow 0 N b h hb,
    quasiLocalBlocking_quasiLocalIntervalObservable]
  rw [quasiLocalIntervalObservable_placeAlong_chainWindow _ _ _ _ hbL]
  simp only [zero_add, zero_mul, Nat.cast_mul]

/-- The reindexed open interaction sum on a blocked chain is the sum of
original-chain windows whose starts are multiples of the block length; every
start in the summation range gives a window of the chain. This includes
volumes shorter than the interaction range, when both sums vanish. Source:
Nachtergaele, arXiv:cond-mat/9410110, equation (3.12), under the site
regrouping at lines 825--836. -/
theorem openInteractionMatrix_blocking_reindex {K : ℕ}
    (h : Matrix (Cfg (blockPhysDim d L) K) (Cfg (blockPhysDim d L) K) ℂ) (N : ℕ) :
    Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
        (openInteractionMatrix h N) =
      ∑ i ∈ Finset.range (N + 1 - K),
        if hi : i * L + K * L ≤ N * L then
          placeAlong (X := fun _ ↦ Fin d) (chainWindow (i * L) hi)
            (Matrix.reindex (blockedConfigEquiv d K L) (blockedConfigEquiv d K L) h)
        else 0 := by
  change (Matrix.reindexLinearEquiv ℂ ℂ (blockedConfigEquiv d N L)
    (blockedConfigEquiv d N L)) (openInteractionMatrix h N) = _
  rw [openInteractionMatrix, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i + K ≤ N := by
    have hi'' := Finset.mem_range.mp hi
    omega
  have hiL : i * L + K * L ≤ N * L := by
    simpa only [Nat.add_mul] using Nat.mul_le_mul_right L hi'
  simp only [dite_eq_left hi', dite_eq_left hiL]
  exact placeAlong_chainWindow_blocking_reindex h hi'

omit [NeZero d] in
/-- For a positive interaction, summing only windows aligned with the block
partition is bounded by the open sum over all windows, with coefficient one.
This holds at every volume and needs no positive physical-dimension hypothesis.
Source: a positive-term counting consequence of Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem sum_aligned_placeAlong_chainWindow_le_openInteractionMatrix {K : ℕ}
    (h : Matrix (Cfg d (K * L)) (Cfg d (K * L)) ℂ)
    (hh : h.PosSemidef) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1 - K),
      if hi : i * L + K * L ≤ N * L then
        placeAlong (X := fun _ ↦ Fin d) (chainWindow (i * L) hi) h else 0) ≤
      openInteractionMatrix h (N * L) := by
  have hsub : (Finset.range (N + 1 - K)).image (fun i => i * L) ⊆
      Finset.range (N * L + 1 - K * L) := by
    rintro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hb : i + K ≤ N := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hscaled : i * L + K * L ≤ N * L := by
      simpa only [Nat.add_mul] using Nat.mul_le_mul_right L hb
    exact Finset.mem_range.mpr (by omega)
  have hsum : (∑ j ∈ (Finset.range (N + 1 - K)).image (fun i => i * L),
      if hj : j + K * L ≤ N * L then
        placeAlong (X := fun _ ↦ Fin d) (chainWindow j hj) h else 0) =
      ∑ i ∈ Finset.range (N + 1 - K),
        if hi : i * L + K * L ≤ N * L then
          placeAlong (X := fun _ ↦ Fin d) (chainWindow (i * L) hi) h else 0 :=
    Finset.sum_image (fun i _ j _ hij => mul_left_injective₀ (NeZero.ne L) hij)
  rw [← hsum, openInteractionMatrix]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro j _ _
  by_cases hj : j + K * L ≤ N * L
  · simp only [dite_eq_left hj]
    exact Matrix.nonneg_iff_posSemidef.mpr (ManyBody.posSemidef_placeAlong _ hh)
  · simp only [dite_eq_right hj, le_refl]

end MPSTensor

end

section

open SpinChain MPSTensor
open Kraus (blockPhysDim)
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
  have hcL : c + k ≤ (c + k) * L := Nat.le_mul_of_pos_right (c + k) (NeZero.pos L)
  refine ⟨a / (L : ℤ), c + k, by omega,
    (Matrix.reindexLinearEquiv ℂ ℂ (blockedConfigEquiv d (c + k) L)
      (blockedConfigEquiv d (c + k) L)).symm
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow c hcL) X), ?_⟩
  rw [quasiLocalBlocking_quasiLocalIntervalObservable]
  change quasiLocalIntervalObservable d ((a / (L : ℤ)) * L) ((c + k) * L)
    ((Matrix.reindexLinearEquiv ℂ ℂ (blockedConfigEquiv d (c + k) L)
      (blockedConfigEquiv d (c + k) L))
      ((Matrix.reindexLinearEquiv ℂ ℂ (blockedConfigEquiv d (c + k) L)
        (blockedConfigEquiv d (c + k) L)).symm
          (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow c hcL) X))) = _
  rw [LinearEquiv.apply_symm_apply, quasiLocalIntervalObservable_placeAlong_chainWindow _ _ _ X hcL]
  simp only [hc, Int.ediv_mul_add_emod]

end SpinChain

end
