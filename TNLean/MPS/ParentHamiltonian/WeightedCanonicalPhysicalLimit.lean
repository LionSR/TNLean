/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.PGVWC07CanonicalForm
import TNLean.MPS.Symmetry.PeriodicMPSNormLowerBound

/-!
# Disappearance of subleading weighted canonical blocks

For a weighted TI canonical tensor, each unital block has periodic state
norm bounded by its bond dimension. The exact weighted decomposition
therefore bounds the physical remainder after retaining the unit-weight
blocks by a finite sum of geometric sequences. This remainder tends to
zero without any spectral or convergence assumption.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorems 4 and 6, lines 742–759
and 970–993. This is the physical contribution estimate for the weighted
canonical half-chain limit; it does not identify a unique dominant block
from Condition C2 or replace finite-ring normalization by one.
-/

open Filter
open scoped Matrix BigOperators Topology

namespace MPSTensor.PGVWC07CanonicalFormData

variable {d D : ℕ} {A : MPSTensor d D} (h : PGVWC07CanonicalFormData A)

/-- The actual physical contribution of subunit canonical weights has a
finite geometric bound. No irreducibility, peripheral simplicity, or
assumed decay estimate is needed. Source: PGVWC07, Theorems 4 and 6,
lines 742–759 and 970–993. -/
theorem norm_mpvState_sub_unitWeight_sum_le (N : ℕ) :
    ‖mpvState A N - ∑ k ∈ Finset.univ.filter (fun k => h.weight k = 1),
      mpvState (h.blocks k) N‖ ≤
    ∑ k ∈ Finset.univ.filter (fun k => h.weight k < 1),
      h.weight k ^ N * (h.dim k : ℝ) := by
  classical
  have hState := mpvState_eq_sum_of_decomp A h.blocks
    (fun k => (h.weight k : ℂ) ^ N) (h.mpv_eq_sum (N := N))
  have hSplit : mpvState A N -
      ∑ k ∈ Finset.univ.filter (fun k => h.weight k = 1), mpvState (h.blocks k) N =
      ∑ k ∈ Finset.univ.filter (fun k => h.weight k < 1),
        (h.weight k : ℂ) ^ N • mpvState (h.blocks k) N := by
    rw [hState]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : h.weight k = 1
    · simp [hk]
    · have hklt : h.weight k < 1 := lt_of_le_of_ne (h.weight_le_one k) hk
      simp only [hk, hklt, ite_true, ite_false, sub_zero]
  rw [hSplit]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (h.weight_pos k).le]
  exact mul_le_mul_of_nonneg_left
    (norm_mpvState_le_bondDimension_of_unital (h.blocks k) (h.unital k) N)
    (pow_nonneg (h.weight_pos k).le N)

/-- All strictly subunit canonical weights disappear in actual periodic
state norm. The retained state is the sum of the unit-weight block vectors,
without an assumption that this sum consists of only one block. Source:
PGVWC07, Theorems 4 and 6, lines 742–759 and 970–993. -/
theorem tendsto_norm_mpvState_sub_unitWeight_sum :
    Tendsto (fun N => ‖mpvState A N -
      ∑ k ∈ Finset.univ.filter (fun k => h.weight k = 1), mpvState (h.blocks k) N‖)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  have hSum : Tendsto (fun N =>
      ∑ k ∈ Finset.univ.filter (fun k => h.weight k < 1),
        h.weight k ^ N * (h.dim k : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul, Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ.filter (fun k => h.weight k < 1))
        (fun k hk =>
          (tendsto_pow_atTop_nhds_zero_of_lt_one (h.weight_pos k).le
            (Finset.mem_filter.mp hk).2).mul_const (h.dim k : ℝ))
  exact squeeze_zero (fun _ => norm_nonneg _) (h.norm_mpvState_sub_unitWeight_sum_le) hSum

end MPSTensor.PGVWC07CanonicalFormData
