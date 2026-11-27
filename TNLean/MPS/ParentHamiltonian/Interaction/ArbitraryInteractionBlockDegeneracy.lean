/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonianBasic
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.CyclicWindowOpenHamiltonian
import TNLean.MPS.Tensor.Overlap
import QICLean.Spectral.Gap.WeightedPositiveKernel
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockGroundSpaceMapContinuity
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BoundaryMatrix.PGVWC07CutRank

/-!
# Periodic MPS vectors in cyclic active-block coordinates

Expose a consecutive active block and its ordered complement. The actual
periodic vector becomes the boundary map of the active tensor evaluated on
the complementary word. This is the tensor-coordinate identity used in
PGVWC07, arXiv:quant-ph/0608197, Theorem 11 (`2blocks.1`), proof lines
1418–1422 of `Papers/quant-ph_0608197/MPSarchive.tex`.

## Block ground states for an arbitrary local interaction

The interaction is an arbitrary linear operator, rather than the canonical
parent projector. A simultaneous span on the complementary sites separates
the weighted block vectors after the interaction acts. Positivity
then passes from a periodic Hamiltonian equation to its individual local
terms, giving the blockwise Hamiltonian equations.

This is the linear argument of PGVWC07, arXiv:quant-ph/0608197, Theorem 11
(`2blocks.1`), lines 1407–1422 of
`Papers/quant-ph_0608197/MPSarchive.tex`. The simultaneous span is explicit
in the general statement; the source-length specialization is separate.

## Arbitrary positive interactions annihilate every separated canonical block

The canonical data and C1 derive the complementary simultaneous span at the
source length. The interaction can be any positive local operator. No local
annihilation equation, parent-projector identity or extra simultaneous-span
premise is supplied.

**Local fix (projective distinctness of the blocks):** the source assumes that
the weighted block states are pairwise different (lines 1329–1330); its proof of
the direct-sum lemma (lines 1373–1377) needs them pairwise nonproportional, and
that is the reading adopted. Gauge-phase-equivalent blocks give proportional
states at every length, and inequivalent blocks give linearly independent states
at the source length, so the explicit premise `BlocksNotGaugePhaseEquiv` is the
source's hypothesis in length-independent form. The canonical form of Theorem 4
carries no distinctness, so the premise is stated here rather than in
`PGVWC07CanonicalFormData`. Documented in
`docs/paper-gaps/pgvwc07_direct_sum_input.tex`.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 11 (`2blocks.1`),
lines 1407–1422 and its standing hypotheses at lines 1314–1330 of
`Papers/quant-ph_0608197/MPSarchive.tex`.
-/

open MPTensor

section

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D N L : ℕ}

/-- Joining the two cyclic blocks factors the closed-word amplitude.
Source: PGVWC07, Theorem 11, `2blocks.1`, proof lines 1418–1422. -/
theorem mpv_cyclicActiveBlockConfigEquiv_symm
    (A : MPSTensor d D) (hLN : L ≤ N) (i : Fin N)
    (σ : Cfg d L) (τ : Cfg d (N - L)) :
    mpv A ((cyclicActiveBlockConfigEquiv d L hLN i).symm (σ, τ)) =
      groundSpaceMap A L (Kraus.evalWord A (List.ofFn τ)) σ := by
  let ω := (cyclicActiveBlockConfigEquiv d L hLN i).symm (σ, τ)
  have hrot : (List.ofFn ω).rotate i.val = List.ofFn σ ++ List.ofFn τ := by
    apply List.ext_getElem
    · simp only [List.length_rotate, List.length_append, List.length_ofFn]
      omega
    · intro k hk₁ hk₂
      have hkN : k < N := by simpa only [List.length_rotate, List.length_ofFn] using hk₁
      simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
      by_cases hkL : k < L
      · rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hkL),
          List.getElem_ofFn]
        simpa only [ω, cyclicForwardSite, Nat.add_comm] using
          cyclicActiveBlockConfigEquiv_symm_apply_window hLN i σ τ ⟨k, hkL⟩
      · rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega),
          List.getElem_ofFn]
        have hk : k - L < N - L := by omega
        simpa only [ω, cyclicForwardSite, List.length_ofFn,
          show L + (k - L) = k by omega, Nat.add_comm] using
          cyclicActiveBlockConfigEquiv_symm_apply_spectator hLN i σ τ ⟨k - L, hk⟩
  change Matrix.trace (Kraus.evalWord A (List.ofFn ω)) =
    Matrix.trace (Kraus.evalWord A (List.ofFn σ) * Kraus.evalWord A (List.ofFn τ))
  rw [← Kraus.evalWord_append, ← hrot,
    List.rotate_eq_drop_append_take (by simp only [List.length_ofFn]; exact i.isLt.le),
    Kraus.evalWord_append]
  conv_lhs => rw [← List.take_append_drop i.val (List.ofFn ω), Kraus.evalWord_append]
  exact Matrix.trace_mul_comm _ _

/-- The cyclic active-block coordinates of the periodic Hilbert vector
are the active boundary map with the complementary word as boundary matrix.
Source: PGVWC07, Theorem 11, `2blocks.1`, proof lines 1418–1422. -/
theorem cyclicActiveBlock_mpvState_apply
    (A : MPSTensor d D) (hLN : L ≤ N) (i : Fin N)
    (σ : Cfg d L) (τ : Cfg d (N - L)) :
    cyclicActiveBlockConfigLinearIsometryEquiv d L hLN i (mpvState A N) (σ, τ) =
      groundSpaceMap A L (Kraus.evalWord A (List.ofFn τ)) σ := by
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply, mpvState_apply,
    mpv_cyclicActiveBlockConfigEquiv_symm]

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d r N L : ℕ} {dim : Fin r → ℕ}

/-- A simultaneous word span makes the periodic block vectors linearly
independent when every virtual block is nonempty. This gives the degeneracy
conclusion in PGVWC07, Theorem 11, `2blocks.1`, lines 1407–1416. -/
theorem linearIndependent_mpvState_of_wordTupleSpanTop
    [∀ j, NeZero (dim j)] (A : (j : Fin r) → MPSTensor d (dim j))
    (hSpan : WordTupleSpanTop A N) :
    LinearIndependent ℂ (fun j => mpvState (A j) N) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hMatrices := block_matrices_eq_zero_of_wordTupleSpanTop_trace A hSpan
    (fun k => c k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) (by
      intro w
      have hw := congrArg (fun v : MPVSpace (Fin d) N => v w) hc
      simpa only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        mpvState_apply, mpv_eq, coeff_eq, Matrix.smul_mul, Matrix.one_mul,
        Matrix.trace_smul, smul_eq_mul, PiLp.zero_apply] using hw)
  have hj := congrFun (congrFun (hMatrices j) (0 : Fin (dim j))) (0 : Fin (dim j))
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Matrix.zero_apply] using hj

/-- Complementary word spanning turns local annihilation of a weighted block sum by a term of the
translates of a local matrix on the ring into annihilation of every virtual boundary in each
weighted block. Source: PGVWC07, Theorem 11, `2blocks.1`, proof lines 1418–1422; SPWC10,
arXiv:0909.5347, Theorem 5 proof, lines 869–880. -/
theorem weighted_boundary_eq_zero_of_toEuclideanLin_translationInvariant_term_eq_zero
    (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (h : Matrix (Cfg d L) (Cfg d L) ℂ)
    (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L)) (i : Fin N)
    (hzero : haveI : NeZero N := NeZero.of_pos i.pos;
      Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant N h).term i)
      (∑ j, c j • mpvState (A j) N) = 0) :
    ∀ j (X : Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
      c j • Matrix.toEuclideanLin h ((WithLp.linearEquiv 2 ℂ (NSiteSpace (Fin d) L)).symm
        (groundSpaceMap (A j) L X)) = 0 := by
  have : NeZero N := NeZero.of_pos i.pos
  classical
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d L hLN i
  let e := (WithLp.linearEquiv 2 ℂ (NSiteSpace (Fin d) L)).symm
  let T : ((j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) →ₗ[ℂ]
      MPVSpace (Fin d) L :=
    LinearMap.lsum ℂ (fun j => Matrix (Fin (dim j)) (Fin (dim j)) ℂ) ℂ
      (fun j => c j • (Matrix.toEuclideanLin h).comp (e.toLinearMap.comp (groundSpaceMap (A j) L)))
  have hT : T = 0 := by
    apply LinearMap.ext_on_range (v := wordTuple A (N - L)) (hv := hSpan)
    intro τ
    have hfiber : ContinuousLinearMap.rightFiber
        (U (∑ j, c j • mpvState (A j) N)) τ =
        ∑ j, c j • e (groundSpaceMap (A j) L (Kraus.evalWord (A j) (List.ofFn τ))) := by
      apply PiLp.ext
      intro σ
      simp only [ContinuousLinearMap.rightFiber, PiLp.toLp_apply,
        map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        cyclicActiveBlock_mpvState_apply, U]
      rfl
    have hUzero := congrArg U hzero
    have hRight : ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - L))
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin h))
        (U (∑ j, c j • mpvState (A j) N)) = 0 := by
      simpa only [U, cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply, map_zero]
        using hUzero
    have hτ := congrArg (fun v => ContinuousLinearMap.rightFiber v τ) hRight
    have hzeroFiber : ContinuousLinearMap.rightFiber
        (0 : EuclideanSpace ℂ (Cfg d L × Cfg d (N - L))) τ = 0 := by
      apply PiLp.ext
      intro σ
      rfl
    rw [ContinuousLinearMap.rightFiber_rightFiberwiseMap, hfiber, hzeroFiber] at hτ
    simpa only [T, LinearMap.lsum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      wordTuple, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.zero_apply,
      map_sum, map_smul, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
      using hτ
  intro j X
  have hsingle := LinearMap.lsum_piSingle ℂ
    (fun j => Matrix (Fin (dim j)) (Fin (dim j)) ℂ) ℂ
    (fun j => c j • (Matrix.toEuclideanLin h).comp (e.toLinearMap.comp (groundSpaceMap (A j) L)))
    j X
  have heq := LinearMap.congr_fun hT (Pi.single j X)
  simpa only [T, hsingle, LinearMap.zero_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe] using heq

/-- A term of the translates of a local matrix on the ring killing a weighted sum of periodic
blocks kills each weighted summand, provided complementary words span the block matrix algebra.
No parent-interaction or positivity assumption is used at this local step.
Source: PGVWC07, Theorem 11, `2blocks.1`, proof lines 1418–1422. -/
theorem toEuclideanLin_translationInvariant_term_smul_mpvState_eq_zero_of_wordTupleSpanTop
    (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (h : Matrix (Cfg d L) (Cfg d L) ℂ)
    (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L)) (i : Fin N)
    (hzero : haveI : NeZero N := NeZero.of_pos i.pos;
      Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant N h).term i)
      (∑ j, c j • mpvState (A j) N) = 0) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    ∀ j, Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant N h).term i)
      (c j • mpvState (A j) N) = 0 := by
  have : NeZero N := NeZero.of_pos i.pos
  classical
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d L hLN i
  let e := (WithLp.linearEquiv 2 ℂ (NSiteSpace (Fin d) L)).symm
  have hEach := weighted_boundary_eq_zero_of_toEuclideanLin_translationInvariant_term_eq_zero
    A c h hLN hSpan i hzero
  intro j
  apply U.injective
  rw [map_zero, cyclicActiveBlock_toEuclideanLin_translationInvariant_term_apply]
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  have hfiber : ContinuousLinearMap.rightFiber (U (c j • mpvState (A j) N)) τ =
      c j • e (groundSpaceMap (A j) L (Kraus.evalWord (A j) (List.ofFn τ))) := by
    apply PiLp.ext
    intro σ'
    simp only [ContinuousLinearMap.rightFiber, PiLp.toLp_apply,
      map_smul, PiLp.smul_apply, U, cyclicActiveBlock_mpvState_apply]
    rfl
  rw [ContinuousLinearMap.rightFiberwiseMap_apply_apply, hfiber]
  simpa only [map_smul, PiLp.smul_apply, PiLp.zero_apply,
    LinearMap.coe_toContinuousLinearMap'] using
    congrArg (fun v => v σ) (hEach j (Kraus.evalWord (A j) (List.ofFn τ)))

/-- Every block vector is a zero-energy state of the Hamiltonian of the translates on the ring of
an arbitrary positive semidefinite local matrix whenever their sum with nonzero coefficients has
zero energy and the complementary word tuples span. Positivity supplies the individual local
annihilation equations rather than adding them as hypotheses.
Source: PGVWC07, Theorem 11, `2blocks.1`, lines 1407–1422. -/
theorem toEuclideanLin_hamiltonian_translationInvariant_mpvState_eq_zero_of_wordTupleSpanTop
    [NeZero N] (A : (j : Fin r) → MPSTensor d (dim j)) (c : Fin r → ℂ)
    (hc : ∀ j, c j ≠ 0)
    (h : Matrix (Cfg d L) (Cfg d L) ℂ) (hh : h.PosSemidef)
    (hLN : L ≤ N) (hSpan : WordTupleSpanTop A (N - L))
    (hzero : Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian
      (∑ j, c j • mpvState (A j) N) = 0) :
    ∀ j, Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian
      (mpvState (A j) N) = 0 := by
  have hpos (i : Fin N) :
      ((ManyBody.Interaction.translationInvariant N h).term i).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (ManyBody.Interaction.translationInvariant_term_nonneg
      (Matrix.nonneg_iff_posSemidef.mpr hh) i)
  have hterms : ∀ i : Fin N,
      Matrix.toEuclideanLin ((ManyBody.Interaction.translationInvariant N h).term i)
        (∑ j, c j • mpvState (A j) N) = 0 := by
    rw [Matrix.toLpLin_apply, WithLp.toLp_eq_zero] at hzero
    intro i
    rw [Matrix.toLpLin_apply, WithLp.toLp_eq_zero]
    exact (ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff hpos).mp hzero i
  intro j
  rw [ManyBody.Interaction.hamiltonian, map_sum, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hblock :=
    toEuclideanLin_translationInvariant_term_smul_mpvState_eq_zero_of_wordTupleSpanTop
      A c h hLN hSpan i (hterms i) j
  rw [map_smul] at hblock
  exact (smul_eq_zero.mp hblock).resolve_left (hc j)

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

/-- At the source volume bound, the Hamiltonian of the translates on the ring of any positive
semidefinite local matrix annihilating the original canonical vector annihilates every block
vector. The simultaneous span and all individual local annihilation equations are derived.
Source: PGVWC07, Theorem 11 (`2blocks.1`), lines 1407–1422; standing block hypotheses at
lines 1314–1330. -/
theorem PGVWC07CanonicalFormData.toEuclideanLin_hamiltonian_translationInvariant_blocks_eq_zero
    (data : PGVWC07CanonicalFormData A)
    (hr : 2 ≤ data.r)
    (hDistinct : BlocksNotGaugePhaseEquiv data.blocks)
    {L₀ L N : ℕ} (hL₀ : 0 < L₀)
    (hC1 : ∀ j, Kraus.IsNBlkInjective (data.blocks j) L₀)
    (hN : 3 * (data.r - 1) * (L₀ + 1) + L ≤ N)
    (h : Matrix (Cfg d L) (Cfg d L) ℂ) (hh : h.PosSemidef)
    (hzero : haveI : NeZero N := ⟨by
      have := Nat.mul_pos (Nat.mul_pos three_pos (Nat.sub_pos_of_lt hr)) (Nat.add_one_pos L₀)
      omega⟩;
      Matrix.toEuclideanLin
      (ManyBody.Interaction.translationInvariant N h).hamiltonian
        (mpvState A N) = 0) :
    haveI : NeZero N := ⟨by
      have := Nat.mul_pos (Nat.mul_pos three_pos (Nat.sub_pos_of_lt hr)) (Nat.add_one_pos L₀)
      omega⟩;
    ∀ j, Matrix.toEuclideanLin
      (ManyBody.Interaction.translationInvariant N h).hamiltonian
        (mpvState (data.blocks j) N) = 0 := by
  have : NeZero N := ⟨by
    have := Nat.mul_pos (Nat.mul_pos three_pos (Nat.sub_pos_of_lt hr)) (Nat.add_one_pos L₀)
    omega⟩
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
  exact toEuclideanLin_hamiltonian_translationInvariant_mpvState_eq_zero_of_wordTupleSpanTop
    data.blocks (fun j => (data.weight j : ℂ) ^ N)
    (fun j => pow_ne_zero N (by exact_mod_cast (data.weight_pos j).ne'))
    h hh (by omega) hSpan hzero

/-- The number of separated canonical blocks bounds the ground-space dimension of the
Hamiltonian of the translates on the ring of every positive semidefinite local matrix
annihilating the original periodic state, at the source volume bound. Source: PGVWC07,
Theorem 11, `2blocks.1`, lines 1407–1416. -/
theorem PGVWC07CanonicalFormData.blockCount_le_finrank_ker_hamiltonian_translationInvariant
    (data : PGVWC07CanonicalFormData A)
    (hr : 2 ≤ data.r)
    (hDistinct : BlocksNotGaugePhaseEquiv data.blocks)
    {L₀ L N : ℕ} (hL₀ : 0 < L₀)
    (hC1 : ∀ j, Kraus.IsNBlkInjective (data.blocks j) L₀)
    (hN : 3 * (data.r - 1) * (L₀ + 1) + L ≤ N)
    (h : Matrix (Cfg d L) (Cfg d L) ℂ) (hh : h.PosSemidef)
    (hzero : haveI : NeZero N := ⟨by
      have := Nat.mul_pos (Nat.mul_pos three_pos (Nat.sub_pos_of_lt hr)) (Nat.add_one_pos L₀)
      omega⟩;
      Matrix.toEuclideanLin
      (ManyBody.Interaction.translationInvariant N h).hamiltonian
        (mpvState A N) = 0) :
    haveI : NeZero N := ⟨by
      have := Nat.mul_pos (Nat.mul_pos three_pos (Nat.sub_pos_of_lt hr)) (Nat.add_one_pos L₀)
      omega⟩;
    data.r ≤ Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
      (ManyBody.Interaction.translationInvariant N h).hamiltonian)) := by
  have : NeZero N := ⟨by
    have := Nat.mul_pos (Nat.mul_pos three_pos (Nat.sub_pos_of_lt hr)) (Nat.add_one_pos L₀)
    omega⟩
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
  have hblocks := data.toEuclideanLin_hamiltonian_translationInvariant_blocks_eq_zero
    hr hDistinct hL₀ hC1 hN h hh hzero
  let K := LinearMap.ker (Matrix.toEuclideanLin
    (ManyBody.Interaction.translationInvariant N h).hamiltonian)
  let states : Fin data.r → K := fun j => ⟨mpvState (data.blocks j) N, hblocks j⟩
  have hIndependentK : LinearIndependent ℂ states :=
    LinearIndependent.of_comp K.subtype hIndependent
  simpa only [Fintype.card_fin] using hIndependentK.fintype_card_le_finrank

end MPSTensor

end
