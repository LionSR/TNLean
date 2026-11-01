/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ArbitraryInteractionBlockDegeneracy
import TNLean.MPS.ParentHamiltonian.PGVWC07CutRank

/-!
# Arbitrary positive interactions annihilate every separated canonical block

The canonical data and C1 derive the complementary simultaneous span at the
source length. The interaction can be any positive local operator. No local
annihilation equation, parent-projector identity or extra simultaneous-span
premise is supplied.

**Scope restriction (separated canonical blocks):** the source's statement
that the weighted block states are pairwise different is replaced by
inequivalence under a gauge and a phase. This is the existing distinctness
restriction of `PGVWC07CanonicalFormData.wordTupleSpanTop_of_ge`, made explicit
here as well. See
`docs/paper-gaps/pgvwc07_direct_sum_input.tex`.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 11 (`2blocks.1`),
lines 1407–1422 and its standing hypotheses at lines 1314–1330 of
`Papers/quant-ph_0608197/MPSarchive.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

/-- At the source volume bound, any positive periodic interaction annihilating
the original canonical vector annihilates every block vector.
The simultaneous span and all individual local annihilation equations are
derived. Source: PGVWC07, Theorem 11 (`2blocks.1`), lines 1407–1422;
standing block hypotheses at lines 1314–1330. -/
theorem PGVWC07CanonicalFormData.periodicInteractionHamiltonianES_blocks_eq_zero
    (data : PGVWC07CanonicalFormData A)
    (hr : 2 ≤ data.r)
    (hDistinct : BlocksNotGaugePhaseEquiv (d := d) data.blocks)
    {L₀ L N : ℕ} (hL₀ : 0 < L₀)
    (hC1 : ∀ j, Kraus.IsNBlkInjective (data.blocks j) L₀)
    (hN : 3 * (data.r - 1) * (L₀ + 1) + L ≤ N)
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hzero : periodicInteractionHamiltonianES h N (mpvState A N) = 0) :
    ∀ j, periodicInteractionHamiltonianES h N (mpvState (data.blocks j) N) = 0 := by
  classical
  have hpred : 1 ≤ data.r - 1 := by omega
  have hL₀Bound : L₀ ≤ 3 * (data.r - 1) * (L₀ + 1) := by
    have hm : L₀ + 1 ≤ (data.r - 1) * (L₀ + 1) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (L₀ + 1) hpred
    nlinarith
  have hSpan : WordTupleSpanTop data.blocks (N - L) :=
    data.wordTupleSpanTop_of_ge hL₀ hC1 hDistinct (by omega)
  have hsum : mpvState A N =
      ∑ j, (data.weight j : ℂ) ^ N • mpvState (data.blocks j) N := by
    apply PiLp.ext
    intro σ
    simpa only [mpvState_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul] using data.mpv_eq_sum σ
  rw [hsum] at hzero
  exact periodicInteractionHamiltonianES_mpvState_eq_zero_of_wordTupleSpanTop
    data.blocks (fun j => (data.weight j : ℂ) ^ N)
    (fun j => pow_ne_zero N (by exact_mod_cast (data.weight_pos j).ne'))
    h hh (by omega) hSpan hzero

/-- The number of separated canonical blocks bounds the ground-space dimension
of every positive local interaction annihilating the original periodic state,
at the source volume bound. Source: PGVWC07, Theorem 11, `2blocks.1`,
lines 1407–1416. -/
theorem PGVWC07CanonicalFormData.blockCount_le_finrank_ker_periodicInteractionHamiltonianES
    (data : PGVWC07CanonicalFormData A)
    (hr : 2 ≤ data.r)
    (hDistinct : BlocksNotGaugePhaseEquiv (d := d) data.blocks)
    {L₀ L N : ℕ} (hL₀ : 0 < L₀)
    (hC1 : ∀ j, Kraus.IsNBlkInjective (data.blocks j) L₀)
    (hN : 3 * (data.r - 1) * (L₀ + 1) + L ≤ N)
    (h : MPVSpace d L →ₗ[ℂ] MPVSpace d L) (hh : h.IsPositive)
    (hzero : periodicInteractionHamiltonianES h N (mpvState A N) = 0) :
    data.r ≤ Module.finrank ℂ (LinearMap.ker (periodicInteractionHamiltonianES h N)) := by
  classical
  let : ∀ j, NeZero (data.dim j) := fun j => ⟨(data.dim_pos j).ne'⟩
  have hpred : 1 ≤ data.r - 1 := by omega
  have hL₀Bound : L₀ ≤ 3 * (data.r - 1) * (L₀ + 1) := by
    have hm : L₀ + 1 ≤ (data.r - 1) * (L₀ + 1) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (L₀ + 1) hpred
    nlinarith
  have hSpan : WordTupleSpanTop data.blocks N :=
    data.wordTupleSpanTop_of_ge hL₀ hC1 hDistinct (by omega)
  have hIndependent := linearIndependent_mpvState_of_wordTupleSpanTop data.blocks hSpan
  have hblocks := data.periodicInteractionHamiltonianES_blocks_eq_zero
    hr hDistinct hL₀ hC1 hN h hh hzero
  let K := LinearMap.ker (periodicInteractionHamiltonianES h N)
  let states : Fin data.r → K := fun j => ⟨mpvState (data.blocks j) N, hblocks j⟩
  have hIndependentK : LinearIndependent ℂ states :=
    LinearIndependent.of_comp K.subtype hIndependent
  simpa only [Fintype.card_fin] using hIndependentK.fintype_card_le_finrank

end MPSTensor
