/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.Case1

/-!
# Periodic overlap dichotomy: Case 2

This module contains the equal-period, no-sector-match case of Appendix A of
arXiv:1708.00029: after blocking by the common period, absence of a sector match
forces the overlap to tend to $0$.

## Main declarations

* `sectorBlocked_isNormal_of_isPeriodic`
* `exists_sector_match_of_gaugePhaseEquiv`
* `periodicOverlap_tendsto_zero_of_no_sector_match`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ## Case 2: Same period, no sector match → orthogonal (Appendix A, second case) -/

/-- Case-2 normality lemma for the compressed blocked sector tensors.

The intended mathematical content is Lemma 2.4: after blocking by the period,
each cyclic sector is a normal tensor. The statement uses the compressed sector
tensor on the corner bond space, as produced by
`exists_cyclic_sector_decomp_after_blocking_of_isPeriodic`.

The nontriviality hypothesis `dim u ≠ 0` excludes the degenerate
zero-dimensional "missing sector" case. With the current definitions, an
`MPSTensor _ 0` may satisfy block-injectivity/normality vacuously, so this
assumption is used to focus on genuine nonempty sectors.

The `hBlocks_mpv` hypothesis ties the compressed block decomposition back to
the original blocked tensor, and `hCyclic` ensures the block indexing
follows the cyclic orbit structure of the transfer map's peripheral
spectrum (see `IsCyclicSectorDecomp`).

The orbit-lift / corner-irreducibility input is now supplied unconditionally by
`SelfOverlap.primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`. The
remaining gaps in this file lie further along, in the sector-match and
mixed-overlap arguments. -/
lemma sectorBlocked_isNormal_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    (hCyclic : IsCyclicSectorDecomp A blocks)
    (u : Fin m) (hNonzero : dim u ≠ 0) :
    IsNormal (blocks u) := by
  haveI : NeZero (dim u) := ⟨hNonzero⟩
  obtain ⟨hPrim, hIrr⟩ :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hCyclic u hNonzero
  exact isNormal_of_tp_primitive_irreducible (blocks u) (hBlocks_lc u) hPrim hIrr

/-- Gauge-phase equivalence is preserved by physical blocking.

If `B i = ζ · X A i X⁻¹`, then every blocked letter is a word of length `L`,
so `blockTensor B L` is related to `blockTensor A L` by the same gauge and
phase `ζ ^ L`. -/
private theorem gaugePhaseEquiv_blockTensor
    (A B : MPSTensor d D) (L : ℕ)
    (hGPE : GaugePhaseEquiv A B) :
    GaugePhaseEquiv (blockTensor (d := d) (D := D) A L)
      (blockTensor (d := d) (D := D) B L) := by
  rcases hGPE with ⟨X, ζ, hζ, hX⟩
  refine ⟨X, ζ ^ L, pow_ne_zero L hζ, ?_⟩
  intro i
  let C : MPSTensor d D := fun j =>
    (X : Matrix (Fin D) (Fin D) ℂ) * A j *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hB : B = fun j => ζ • C j := by
    funext j
    simpa [C] using hX j
  have hGauge :
      evalWord C (wordOfBlock d L i) =
        (X : Matrix (Fin D) (Fin D) ℂ) *
          evalWord A (wordOfBlock d L i) *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [C] using
      (evalWord_gauge (A := A) (B := C) X (by intro j; rfl)
        (wordOfBlock d L i))
  calc
    blockTensor (d := d) (D := D) B L i
        = evalWord B (wordOfBlock d L i) := rfl
    _ = evalWord (fun j => ζ • C j) (wordOfBlock d L i) := by simp [hB]
    _ = (ζ ^ (wordOfBlock d L i).length) •
          evalWord C (wordOfBlock d L i) := by
          simpa using
            (evalWord_smul (ζ := ζ) (A := C) (wordOfBlock d L i))
    _ = (ζ ^ L) •
          ((X : Matrix (Fin D) (Fin D) ℂ) *
            blockTensor (d := d) (D := D) A L i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
          simp [hGauge, blockTensor]

/-- Missing mixed-overlap statement after blocking.

If two blocked tensors are globally gauge-phase equivalent and both are decomposed
into cyclic compressed sectors, then some sector of the `A` decomposition has a
non-decaying overlap with some sector of the `B` decomposition.

This is the analytic core of the Wedderburn uniqueness step needed below.  The
intended proof expands the total blocked overlap using `hA_mpv` and `hB_mpv` as a
finite double sum of sector overlaps.  Global gauge-phase equivalence keeps the
total blocked overlap nonzero asymptotically (after the usual unit-modulus
normalization of the global phase), so not every mixed sector overlap can tend
to zero. -/
private lemma exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) B m)) :
    ∃ u v : Fin m,
      ¬ Tendsto
        (fun N => mpvOverlap (d := blockPhysDim d m)
          (blocksA u) (blocksB v) N)
        atTop (nhds (0 : ℂ)) := by
  rcases hGPE_block with ⟨X, ζ, hζ_ne, hX⟩
  set T := blockTensor (d := d) (D := D) A m
  set U := blockTensor (d := d) (D := D) B m
  -- GPE gives mpv relations
  have hTU_rel : ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)), mpv U σ = ζ ^ N * mpv T σ :=
    mpv_eq_pow_mul_of_gaugePhase T U X ζ hX
  -- Step A: blocked self-overlap is same as original overlap
  -- Use the same approach as mpvOverlap_blockTensor_self_eq
  have h_TT_eq (N : ℕ) : mpvOverlap T T N = mpvOverlap (d := d) A A (N * m) := by
    dsimp [T]
    rw [← trace_mixedTransferMap_pow_eq_mpvOverlap
      (A := blockTensor (d := d) (D := D) A m)
      (B := blockTensor (d := d) (D := D) A m) N]
    rw [← trace_mixedTransferMap_pow_eq_mpvOverlap (A := A) (B := A) (N * m)]
    simp [mixedTransferMap_self, transferMap_blockTensor, pow_mul, mul_comm]
  have h_UU_eq (N : ℕ) : mpvOverlap U U N = mpvOverlap (d := d) B B (N * m) := by
    dsimp [U]
    rw [← trace_mixedTransferMap_pow_eq_mpvOverlap
      (A := blockTensor (d := d) (D := D) B m)
      (B := blockTensor (d := d) (D := D) B m) N]
    rw [← trace_mixedTransferMap_pow_eq_mpvOverlap (A := B) (B := B) (N * m)]
    simp [mixedTransferMap_self, transferMap_blockTensor, pow_mul, mul_comm]
  -- Step B: the subsequence limits exist via periodicSelfOverlap_tendsto
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hA_subseq : Tendsto (fun k : ℕ => mpvOverlap (d := d) A A (m * k)) atTop (nhds (m : ℂ)) :=
    periodicSelfOverlap_tendsto A hA
  have hB_subseq : Tendsto (fun k : ℕ => mpvOverlap (d := d) B B (m * k)) atTop (nhds (m : ℂ)) :=
    periodicSelfOverlap_tendsto B hB
  -- Then deduce T T (m*k) → m (and U U similarly)
  have h_mul_atTop : Tendsto (fun k : ℕ => m * k) atTop atTop := by
    refine tendsto_atTop_atTop.mpr (fun C => ⟨C, fun k hk => ?_⟩)
    have h1m : 1 ≤ m := Nat.succ_le_of_lt hm_pos
    have hk_le : k ≤ m * k := calc
      k = 1 * k := by simp
      _ ≤ m * k := Nat.mul_le_mul_right k h1m
    exact le_trans hk hk_le
  have h_TT_mul : Tendsto (fun k : ℕ => mpvOverlap T T (m * k)) atTop (nhds (m : ℂ)) := by
    have eq : (fun k : ℕ => mpvOverlap T T (m * k)) =
        (fun n : ℕ => mpvOverlap (d := d) A A (m * n)) ∘ (fun k : ℕ => m * k) := by
      ext k
      simp [h_TT_eq (m * k), mul_comm, mul_assoc]
    rw [eq]
    exact hA_subseq.comp h_mul_atTop
  have h_UU_mul : Tendsto (fun k : ℕ => mpvOverlap U U (m * k)) atTop (nhds (m : ℂ)) := by
    have eq : (fun k : ℕ => mpvOverlap U U (m * k)) =
        (fun n : ℕ => mpvOverlap (d := d) B B (m * n)) ∘ (fun k : ℕ => m * k) := by
      ext k
      simp [h_UU_eq (m * k), mul_comm, mul_assoc]
    rw [eq]
    exact hB_subseq.comp h_mul_atTop
  -- Step C: from GPE compute mpvOverlap UU in terms of TT
  have h_UU_formula (N : ℕ) : mpvOverlap U U N =
      ((star ζ * ζ : ℂ) ^ N) * mpvOverlap T T N := by
    calc
      mpvOverlap U U N = ∑ σ : Fin N → Fin (blockPhysDim d m), mpv U σ * star (mpv U σ) := rfl
      _ = ∑ σ : Fin N → Fin (blockPhysDim d m),
          (ζ ^ N * mpv T σ) * star (ζ ^ N * mpv T σ) := by
        simp_rw [hTU_rel N]
      _ = ∑ σ : Fin N → Fin (blockPhysDim d m),
          (ζ ^ N * mpv T σ) * ((star ζ) ^ N * star (mpv T σ)) := by simp
      _ = ∑ σ : Fin N → Fin (blockPhysDim d m),
          ((star ζ * ζ : ℂ) ^ N) * (mpv T σ * star (mpv T σ)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring
      _ = ((star ζ * ζ : ℂ) ^ N) * mpvOverlap T T N := by
        simp [mpvOverlap, Finset.mul_sum]
  -- Step D: deduce ‖ζ‖ = 1
  have hm_ne_zero_ℂ : (m : ℂ) ≠ 0 := by exact_mod_cast hm_pos.ne'
  have h_norm_zeta_eq_one : ‖ζ‖ = 1 := by
    -- First show lim (star ζ * ζ)^(m*k) = 1 in ℂ using h_UU_formula + limits
    have h_denom_ne : ∀ᶠ k in atTop, mpvOverlap T T (m * k) ≠ 0 :=
      h_TT_mul.eventually_ne hm_ne_zero_ℂ
    have h_div : Tendsto (fun k : ℕ => mpvOverlap U U (m * k) / mpvOverlap T T (m * k))
        atTop (nhds ((m : ℂ) / (m : ℂ))) :=
      h_UU_mul.div h_TT_mul h_denom_ne
    have hm_div_hm : (m : ℂ) / (m : ℂ) = (1 : ℂ) := by
      field_simp [hm_ne_zero_ℂ]
    have h_limit_ratio : Tendsto (fun k : ℕ => (star ζ * ζ : ℂ) ^ (m * k)) atTop (nhds (1 : ℂ)) := by
      have h_eventually_eq : ∀ᶠ k in atTop,
          (fun k : ℕ => mpvOverlap U U (m * k) / mpvOverlap T T (m * k)) k =
          (fun k : ℕ => (star ζ * ζ : ℂ) ^ (m * k)) k := by
        filter_upwards [h_denom_ne] with k hk
        rw [h_UU_formula (m * k)]
        field_simp [hk]
      simpa [hm_div_hm] using h_div.congr h_eventually_eq
    -- Now extract ℝ limit: |ζ|² = star ζ * ζ ≥ 0 is real.
    -- (|ζ|²)^(m*k) → 1 in ℂ, take real part → 1 in ℝ.
    have h_re_nonneg : 0 ≤ (star ζ * ζ : ℂ).re := by
      simpa [Complex.re_ofReal, Complex.normSq_eq_conj_mul_self] using Complex.normSq_nonneg ζ
    set s : ℝ := ((star ζ * ζ : ℂ).re : ℝ) ^ m with hs_def
    have hs_nonneg : 0 ≤ s := pow_nonneg h_re_nonneg m
    -- (star ζ * ζ).re ^ (m * k) → 1 in ℝ
    have h_real_limit : Tendsto (fun k : ℕ => ((star ζ * ζ : ℂ).re : ℝ) ^ (m * k)) atTop (nhds (1 : ℝ)) := by
      have h_re_one : Complex.re (1 : ℂ) = (1 : ℝ) := by simp
      have h_re_pow (k : ℕ) : Complex.re ((star ζ * ζ : ℂ) ^ (m * k)) = ((star ζ * ζ : ℂ).re : ℝ) ^ (m * k) := by
        simp
      simpa [h_re_one, h_re_pow] using (Complex.continuous_re.tendsto (1 : ℂ)).comp h_limit_ratio
    -- s^k → 1
    have hs_limit : Tendsto (fun k : ℕ => s ^ k) atTop (nhds (1 : ℝ)) := by
      simpa [hs_def, pow_mul] using h_real_limit
    -- For s ≥ 0: s^k → 1 implies s = 1.
    by_cases hs_lt_one : s < 1
    · have hzero : Tendsto (fun k : ℕ => s ^ k) atTop (nhds (0 : ℝ)) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hs_nonneg hs_lt_one
      have h01 : (0 : ℝ) ≠ 1 := by norm_num
      exact h01 (tendsto_nhds_unique hzero hs_limit)
    · by_cases hs_gt_one : 1 < s
      · have hlt2 : ∀ᶠ k in atTop, s ^ k < 2 :=
          hs_limit.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
        rcases ((Filter.tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt hs_gt_one) 2).and hlt2).exists
          with ⟨k, hk_ge, hk_lt⟩
        linarith
      · -- s ≥ 1 and s ≤ 1, so s = 1
        have hs_eq_one : s = 1 := by linarith
        -- Then (|ζ|²)^m = 1 → |ζ|² = 1 → |ζ| = 1
        have h_normSq_eq_one : Complex.normSq ζ = 1 := by
          have : (Complex.normSq ζ : ℝ) ^ m = 1 := by
            have : (star ζ * ζ : ℂ).re = Complex.normSq ζ := by
              simp [Complex.normSq_eq_conj_mul_self]
            simpa [hs_def, this] using hs_eq_one
          have h_nonneg_normSq : 0 ≤ Complex.normSq ζ := Complex.normSq_nonneg ζ
          have h_one_pow : ((1 : ℝ) ^ m : ℝ) = 1 := by simp
          nlinarith
        nlinarith [Complex.normSq_eq_norm_mul_self ζ, h_normSq_eq_one]
  -- Step E: ‖ζ‖ = 1 means the mixed overlap does NOT tend to 0
  have h_TU_not_zero : ¬ Tendsto (fun N : ℕ => mpvOverlap T U N) atTop (nhds (0 : ℂ)) := by
    intro hzero
    have h_TU_formula (N : ℕ) : mpvOverlap T U N = (star ζ) ^ N * mpvOverlap T T N := by
      calc
        mpvOverlap T U N = ∑ σ : Fin N → Fin (blockPhysDim d m), mpv T σ * star (mpv U σ) := rfl
        _ = ∑ σ : Fin N → Fin (blockPhysDim d m),
            mpv T σ * star (ζ ^ N * mpv T σ) := by simp_rw [hTU_rel N]
        _ = ∑ σ : Fin N → Fin (blockPhysDim d m),
            mpv T σ * ((star ζ) ^ N * star (mpv T σ)) := by simp
        _ = (star ζ) ^ N * mpvOverlap T T N := by
          simp [mpvOverlap, Finset.mul_sum]
    -- Take absolute values
    have h_TT_norm_not_zero : ¬ Tendsto (fun N : ℕ => ‖mpvOverlap T T N‖) atTop (nhds (0 : ℝ)) := by
      intro h
      have h_sub : Tendsto (fun k : ℕ => ‖mpvOverlap T T (m * k)‖) atTop (nhds (0 : ℝ)) :=
        h.comp h_mul_atTop
      have h_norm_sub : Tendsto (fun k : ℕ => ‖mpvOverlap T T (m * k)‖) atTop (nhds (‖(m : ℂ)‖)) :=
        (continuous_norm.tendsto _).comp h_TT_mul
      have hm_norm_pos : (0 : ℝ) < ‖(m : ℂ)‖ := by
        simpa using hm_pos
      have : (0 : ℝ) = ‖(m : ℂ)‖ := tendsto_nhds_unique h_sub h_norm_sub
      linarith
    have h_abs_formula (N : ℕ) : ‖mpvOverlap T U N‖ = ‖mpvOverlap T T N‖ := by
      rw [h_TU_formula N, norm_mul, norm_pow, h_norm_zeta_eq_one, one_pow, one_mul]
    have h_abs_zero : Tendsto (fun N : ℕ => ‖mpvOverlap T U N‖) atTop (nhds (0 : ℝ)) :=
      (continuous_norm.tendsto (0 : ℂ)).comp hzero
    exact h_TT_norm_not_zero (by simpa [h_abs_formula] using h_abs_zero)
  -- Step F: Expand blocked overlap as double sum
  have h_expand (N : ℕ) : mpvOverlap T U N =
      ∑ u : Fin m, ∑ v : Fin m, mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := by
    have hA_mpv_decomp (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)) :
        mpv T σ = ∑ u : Fin m, mpv (blocksA u) σ := by
      rw [hA_mpv N σ, mpv_toTensorFromBlocks_eq_sum (fun _ => (1 : ℂ)) blocksA σ]
      simp
    have hB_mpv_decomp (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)) :
        mpv U σ = ∑ v : Fin m, mpv (blocksB v) σ := by
      rw [hB_mpv N σ, mpv_toTensorFromBlocks_eq_sum (fun _ => (1 : ℂ)) blocksB σ]
      simp
    simp only [mpvOverlap, hA_mpv_decomp, hB_mpv_decomp, star_sum]
    simp [Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
  -- Step G: Contradiction if all sector pairs → 0
  by_cases h_all_zero : ∀ u v : Fin m,
      Tendsto (fun N : ℕ => mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N) atTop (nhds (0 : ℂ))
  · -- Then the finite sum → 0, contradicting h_TU_not_zero
    have h_sum_zero : Tendsto (fun N : ℕ => ∑ u : Fin m, ∑ v : Fin m,
        mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N) atTop (nhds (0 : ℂ)) := by
      refine tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun u _ =>
        tendsto_finset_sum (Finset.univ : Finset (Fin m)) fun v _ => h_all_zero u v
    have h_TU_zero : Tendsto (fun N : ℕ => mpvOverlap T U N) atTop (nhds (0 : ℂ)) := by
      simpa [h_expand] using h_sum_zero
    exact h_TU_not_zero h_TU_zero
  · -- Not all pairs tend to zero, so ∃ u,v with non-decaying overlap
    push_neg at h_all_zero
    exact h_all_zero

/-- Missing compressed-sector uniqueness statement after blocking.

Once global gauge-phase equivalence has been transported to the blocked
tensors, the cyclic sector decompositions of the two blocked tensors should be
unique up to relabeling of nonzero Wedderburn/cyclic sectors. This statement is
the precise remaining statement needed for `exists_sector_match_of_gaugePhaseEquiv`:
it extracts one nonzero compressed sector of `A` and a gauge-phase-equivalent
compressed sector of `B`. -/
private lemma exists_sector_match_of_blockedGaugePhaseEquiv_cyclicDecomp
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) B m)) :
    ∃ (u v : Fin m) (hdim : dimA u = dimB v),
      dimA u ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v) := by
  obtain ⟨u, v, hNondecay⟩ :=
    exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp
      A B hA hB blocksA blocksB hA_blocks_lc hB_blocks_lc
      hA_mpv hB_mpv hA_cyclic hB_cyclic hNondegA hNondegB hGPE_block
  haveI : NeZero (dimA u) := ⟨hNondegA u⟩
  haveI : NeZero (dimB v) := ⟨hNondegB v⟩
  have hA_irr : IsIrreducibleTensor (blocksA u) :=
    (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      A hA blocksA hA_blocks_lc hA_mpv hA_cyclic u (hNondegA u)).2
  have hB_irr : IsIrreducibleTensor (blocksB v) :=
    (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      B hB blocksB hB_blocks_lc hB_mpv hB_cyclic v (hNondegB v)).2
  have hdim : dimA u = dimB v := by
    by_contra hne
    exact hNondecay
      (mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
        (blocksA u) (blocksB v) hA_irr hB_irr
        (hA_blocks_lc u) (hB_blocks_lc v) hne)
  refine ⟨u, v, hdim, hNondegA u, ?_⟩
  by_contra hNot
  exact hNondecay
    (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      hdim (blocksA u) (blocksB v) hA_irr hB_irr
      (hA_blocks_lc u) (hB_blocks_lc v) hNot)

/-- A global gauge-phase equivalence between two periodic tensors forces at
least one compatible nonzero pair of compressed cyclic sectors to be
gauge-phase equivalent.

This is the structural step used by the no-sector-match case: the cyclic
sector decomposition is unique up to relabeling, and a global gauge-phase
equivalence carries a nonzero sector of `A` to a sector of `B`. The hypothesis
`hNondegA` supplies the nonzero-sector condition for the returned `A` sector, while
`hNondegB` provides the typeclass needed to apply the mixed-sector overlap dichotomy.
Both come from the periodic sector decomposition constructed by
`exists_cyclic_sector_decomp_after_blocking_of_isPeriodic`.
The current interface does not yet expose that uniqueness theorem in this
compressed-sector form, so the missing step is isolated here as the only missing
ingredient. -/
lemma exists_sector_match_of_gaugePhaseEquiv
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hGPE : GaugePhaseEquiv A B) :
    ∃ (u v : Fin m) (hdim : dimA u = dimB v),
      dimA u ≠ 0 ∧
      GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v) := by
  exact exists_sector_match_of_blockedGaugePhaseEquiv_cyclicDecomp
    A B hA hB blocksA blocksB hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv
    hA_cyclic hB_cyclic hNondegA hNondegB
    (gaugePhaseEquiv_blockTensor A B m hGPE)

/-- If no nonzero compressed sector pair matches, then the original periodic
tensors cannot be globally gauge-phase equivalent. -/
lemma not_gaugePhaseEquiv_of_no_sector_match
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hNoMatch : ∀ u v (hdim : dimA u = dimB v),
      dimA u ≠ 0 →
      ¬ GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v)) :
    ¬ GaugePhaseEquiv A B := by
  intro hGPE
  obtain ⟨u, v, hdim, hNondeg, hMatch⟩ :=
    exists_sector_match_of_gaugePhaseEquiv
      A B hA hB blocksA blocksB hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv
      hA_cyclic hB_cyclic hNondegA hNondegB hGPE
  exact hNoMatch u v hdim hNondeg hMatch

/-- Same-period / no-match statement using compressed sector tensors.

If two periodic tensors have the same period `m` but no compressed sector
pair matches (up to dimension cast and gauge-phase equivalence), their
overlap decays to zero.

The `hNoMatch` hypothesis quantifies over nondegenerate dimension
equalities: for each sector pair `(u, v)` with `dimA u ≠ 0` and any
proof that `dimA u = dimB v`, the compressed blocks are not gauge-phase
equivalent. The nondegeneracy guard `dimA u ≠ 0` is essential: when
`dimA u = 0`, `GaugePhaseEquiv` may hold vacuously for
`MPSTensor _ 0`, and without this guard `hNoMatch` would be
unsatisfiable whenever a zero-dimensional sector pair exists. With
this guard and the separate nondegeneracy hypotheses
`hNondegA : ∀ u, dimA u ≠ 0` and `hNondegB : ∀ v, dimB v ≠ 0`
coming from the periodic sector decompositions, `hNoMatch` is exactly
the negation of `hSomeMatch` in `periodicOverlap_gaugeEquiv_of_sector_match`,
making the two conditions complementary for the dichotomy proof.  The
`hNondegB` hypothesis is also needed by the mixed-sector overlap dichotomy
used to extract a sector match from global gauge-phase equivalence.

This is the "first case" of the same-period argument in Appendix A:
block by `m`, decompose into normal sectors, and observe that all
cross-sector overlaps decay by the normal-tensor overlap dichotomy. -/
theorem periodicOverlap_tendsto_zero_of_no_sector_match
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksA k i)ᴴ * blocksA k i = 1)
    (hB_blocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocksB k i)ᴴ * blocksB k i = 1)
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hA_cyclic : IsCyclicSectorDecomp A blocksA)
    (hB_cyclic : IsCyclicSectorDecomp B blocksB)
    (hNondegA : ∀ u, dimA u ≠ 0)
    (hNondegB : ∀ v, dimB v ≠ 0)
    (hNoMatch : ∀ u v (hdim : dimA u = dimB v),
      dimA u ≠ 0 →
      ¬ GaugePhaseEquiv
        (cast (congr_arg
          (MPSTensor (blockPhysDim d m)) hdim)
          (blocksA u))
        (blocksB v)) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0) := by
  -- PROOF STRUCTURE: see lemma
  -- `not_gaugePhaseEquiv_of_no_sector_match` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `exists_sector_match_of_gaugePhaseEquiv`.
  sorry


end MPSTensor
