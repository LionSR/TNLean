/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.QuasiLocalCommutatorLocality
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

The window and blocking identities assume positive physical dimension,
positive block length, and positive window length. The positive-term counting
bound requires only the latter two assumptions. No tensor, normalization,
state, or spectral-gap data enter these operator identities.

Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3, equation (3.12),
and site regrouping at lines 825--836; CPGSV17, arXiv:1703.09188,
Appendix, lines 2308 and 2313--2320. The aligned-window upper bound is a
derived positive-term counting statement.
-/

open SpinChain
open scoped ComplexOrder MatrixOrder

namespace MPSTensor

variable {d L : ℕ} [NeZero d] [NeZero L]

/-- Physical blocking commutes with placement on a nonwrapping window:
a window starting at blocked site `b` starts at original site `b * L`.
This is an operator identity, requiring no tensor or state data.
Source: Nachtergaele, arXiv:cond-mat/9410110, Section 3 and lines 825--836;
CPGSV17, arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
theorem chainWindowOperator_blocking_reindex {K N b : ℕ}
    (h : Matrix (Cfg (blockPhysDim d L) K) (Cfg (blockPhysDim d L) K) ℂ)
    (hK : 0 < K) (hb : b + K ≤ N) :
    Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
        (chainWindowOperator N b h) =
      chainWindowOperator (N * L) (b * L)
        (Matrix.reindex (blockedConfigEquiv d K L) (blockedConfigEquiv d K L) h) := by
  apply (intervalCoordinates d ((0 : ℤ) * L) (N * L)).symm.injective
  apply quasiLocalObservable_injective d (intervalRegion ((0 : ℤ) * L) (N * L))
  change quasiLocalIntervalObservable d ((0 : ℤ) * L) (N * L)
    (Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
      (chainWindowOperator N b h)) =
    quasiLocalIntervalObservable d ((0 : ℤ) * L) (N * L)
      (chainWindowOperator (N * L) (b * L)
        (Matrix.reindex (blockedConfigEquiv d K L) (blockedConfigEquiv d K L) h))
  rw [← quasiLocalBlocking_quasiLocalIntervalObservable]
  rw [quasiLocalIntervalObservable_chainWindowOperator 0 N b h hK hb,
    quasiLocalBlocking_quasiLocalIntervalObservable]
  rw [quasiLocalIntervalObservable_chainWindowOperator _ _ _ _
    (Nat.mul_pos hK (NeZero.pos L))
    (by simpa only [Nat.add_mul] using Nat.mul_le_mul_right L hb)]
  simp only [zero_add, zero_mul, Nat.cast_mul]

/-- The reindexed open interaction sum on a blocked chain is the sum of
original-chain windows whose starts are multiples of the block length.
This includes volumes shorter than the interaction range, when both sums
vanish. Source: Nachtergaele, arXiv:cond-mat/9410110,
equation (3.12), under the site regrouping at lines 825--836. -/
theorem openInteractionMatrix_blocking_reindex {K : ℕ}
    (h : Matrix (Cfg (blockPhysDim d L) K) (Cfg (blockPhysDim d L) K) ℂ)
    (hK : 0 < K) (N : ℕ) :
    Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
        (openInteractionMatrix h N) =
      ∑ i ∈ Finset.range (N + 1 - K), chainWindowOperator (N * L) (i * L)
        (Matrix.reindex (blockedConfigEquiv d K L) (blockedConfigEquiv d K L) h) := by
  change (Matrix.reindexLinearEquiv ℂ ℂ (blockedConfigEquiv d N L)
    (blockedConfigEquiv d N L)) (openInteractionMatrix h N) = _
  rw [openInteractionMatrix, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact chainWindowOperator_blocking_reindex h hK (by
    have hi' := Finset.mem_range.mp hi
    omega)

omit [NeZero d] in
/-- For a positive interaction, summing only windows aligned with the block
partition is bounded by the open sum over all windows, with coefficient one.
This holds at every volume and needs no positive physical-dimension hypothesis.
Source: a positive-term counting consequence of Nachtergaele,
arXiv:cond-mat/9410110, equation (3.12). -/
theorem sum_aligned_chainWindowOperator_le_openInteractionMatrix {K : ℕ}
    (h : Matrix (Cfg d (K * L)) (Cfg d (K * L)) ℂ)
    (hh : h.PosSemidef) (hK : 0 < K) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1 - K), chainWindowOperator (N * L) (i * L) h) ≤
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
      chainWindowOperator (N * L) j h) =
      ∑ i ∈ Finset.range (N + 1 - K), chainWindowOperator (N * L) (i * L) h := by
    exact Finset.sum_image (fun i _ j _ hij => mul_left_injective₀ (NeZero.ne L) hij)
  rw [← hsum, openInteractionMatrix]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro j hj _hj
  have hKL : 0 < K * L := Nat.mul_pos hK (NeZero.pos L)
  have hb : j + K * L ≤ N * L := by
    have hj' := Finset.mem_range.mp hj
    omega
  rw [Matrix.nonneg_iff_posSemidef,
    chainWindowOperator_eq_embedLocalOperatorAlgHom (by omega) hb]
  exact Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg (chainWindowStarAlgHom (d := d) (K * L) (N * L) j
      (by omega) hb) hh.nonneg)

end MPSTensor
