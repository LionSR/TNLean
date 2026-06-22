/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.Case1
import TNLean.MPS.SharedInfra.BlockAssembly
import TNLean.MPS.SharedInfra.GaugePhase

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

The intended mathematical content is arXiv:1708.00029, lemma lem:bdcf,
lines 377--384: after blocking by the period, each cyclic sector is a normal
tensor. The statement uses the compressed sector tensor on the corner bond
space, as produced by `exists_cyclic_sector_decomp_after_blocking_of_isPeriodic`.

The nontriviality hypothesis `dim u ≠ 0` excludes the degenerate
zero-dimensional "missing sector" case. An `MPSTensor _ 0` may satisfy
block-injectivity/normality vacuously, so this assumption focuses the statement
on genuine nonempty sectors.

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

/-- A periodic tensor has nonzero blocked self-overlap limit after blocking by
its period; the limit is the period itself. This restates
`periodicSelfOverlap_tendsto` for the blocked tensor. -/
private theorem blockTensor_selfOverlap_tendsto_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A) :
    Tendsto
      (fun N => mpvOverlap (d := blockPhysDim d m)
        (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) A m) N)
      atTop (nhds (m : ℂ)) := by
  have hSelf : Tendsto (fun N => mpvOverlap A A (m * N)) atTop (nhds (m : ℂ)) :=
    periodicSelfOverlap_tendsto A hP
  refine hSelf.congr' ?_
  filter_upwards with N
  rw [mpvOverlap_blockTensor_self_eq]
  simp [Nat.mul_comm]

/-- A gauge-phase equivalence between the period-blocked tensors of two
periodic tensors gives a mixed blocked overlap which does not tend to zero.

The proof uses the nonzero blocked self-overlap limits from Appendix A,
lines 908-914 of arXiv:1708.00029, to show that the gauge factor has unit
modulus. -/
private theorem gaugePhase_blockTensor_overlap_not_tendsto_zero_of_periodic
    [NeZero D] (A B : MPSTensor d D) {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) B m)) :
    ¬ Tendsto
      (fun N => mpvOverlap (d := blockPhysDim d m)
        (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) B m) N)
      atTop (nhds (0 : ℂ)) := by
  classical
  intro hZero
  obtain ⟨X, ζ, _hζ, hX⟩ := hGPE_block
  let Ablk := blockTensor (d := d) (D := D) A m
  let Bblk := blockTensor (d := d) (D := D) B m
  have hA_self : Tendsto (fun N => mpvOverlap (d := blockPhysDim d m) Ablk Ablk N)
      atTop (nhds (m : ℂ)) := by
    simpa [Ablk] using blockTensor_selfOverlap_tendsto_of_isPeriodic A hA
  have hB_self : Tendsto (fun N => mpvOverlap (d := blockPhysDim d m) Bblk Bblk N)
      atTop (nhds (m : ℂ)) := by
    simpa [Bblk] using blockTensor_selfOverlap_tendsto_of_isPeriodic B hB
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
      mpv Bblk σ = ζ ^ N * mpv Ablk σ :=
    mpv_eq_pow_mul_of_gaugePhase Ablk Bblk X ζ hX
  have hm_norm_ne : ‖(m : ℂ)‖ ≠ 0 := by
    simpa using (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℂ) ≠ 0)
  have hζnorm : ‖ζ‖ = 1 := by
    exact norm_eq_one_of_selfOverlap_scale_at_nonzero_limit
      (A := Ablk) (B := Bblk) (ζ := ζ) hm_norm_ne
      hA_self.norm hB_self.norm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := Ablk) (B := Bblk) (ζ := ζ) hmpv)
  have hCrossNormEq : ∀ N,
      ‖mpvOverlap (d := blockPhysDim d m) Ablk Bblk N‖ =
        ‖mpvOverlap (d := blockPhysDim d m) Ablk Ablk N‖ := by
    intro N
    rw [mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul (A := Ablk) (B := Bblk)
      (ζ := ζ) hmpv N]
    simp [norm_pow, hζnorm]
  have hCrossNormZero : Tendsto
      (fun N => ‖mpvOverlap (d := blockPhysDim d m) Ablk Bblk N‖)
      atTop (nhds (0 : ℝ)) := by
    simpa using hZero.norm
  have hA_self_norm_zero : Tendsto
      (fun N => ‖mpvOverlap (d := blockPhysDim d m) Ablk Ablk N‖)
      atTop (nhds (0 : ℝ)) :=
    hCrossNormZero.congr hCrossNormEq
  have hLimit : (0 : ℝ) = ‖(m : ℂ)‖ :=
    tendsto_nhds_unique hA_self_norm_zero hA_self.norm
  have hm_pos : 0 < ‖(m : ℂ)‖ :=
    (norm_nonneg _).lt_of_ne (Ne.symm hm_norm_ne)
  exact (ne_of_gt hm_pos) hLimit.symm

/-- Mixed-overlap extraction after blocking.

If two blocked tensors are globally gauge-phase equivalent and both are decomposed
into cyclic compressed sectors, then some sector of the `A` decomposition has a
non-decaying overlap with some sector of the `B` decomposition.

This is the contrapositive extraction behind the same-period case in
arXiv:1708.00029, Appendix A, lines 952-960. The proof expands the total
blocked overlap, using the two block decompositions, as a finite double sum of
sector overlaps. Global gauge-phase equivalence keeps the total blocked overlap
from tending to zero, so not every mixed sector overlap can tend to zero. -/
private lemma exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp
    [NeZero D] (A B : MPSTensor d D)
    {m : ℕ} [NeZero m]
    (hA : IsPeriodic m A) (hB : IsPeriodic m B)
    {dimA dimB : Fin m → ℕ}
    (blocksA :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimA k))
    (blocksB :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dimB k))
    (hA_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksA))
    (hB_mpv :
      SameMPV₂ (blockTensor B m)
        (toTensorFromBlocks (μ := fun _ => 1) blocksB))
    (hGPE_block :
      GaugePhaseEquiv (blockTensor (d := d) (D := D) A m)
        (blockTensor (d := d) (D := D) B m)) :
    ∃ u v : Fin m,
      ¬ Tendsto
        (fun N => mpvOverlap (d := blockPhysDim d m)
          (blocksA u) (blocksB v) N)
        atTop (nhds (0 : ℂ)) := by
  classical
  by_contra hNone
  simp only [not_exists, not_not] at hNone
  have hOverlap_eq : ∀ N,
      mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (D := D) A m)
          (blockTensor (d := d) (D := D) B m) N =
        ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N := by
    intro N
    exact mpvOverlap_eq_sum_of_sameMPV₂_toTensorFromBlocks_one
      (blockTensor (d := d) (D := D) A m)
      (blockTensor (d := d) (D := D) B m)
      blocksA blocksB hA_mpv hB_mpv N
  have hInnerZero : ∀ u : Fin m,
      Tendsto
        (fun N => ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N)
        atTop (nhds (0 : ℂ)) := by
    intro u
    have := tendsto_finsetSum (s := Finset.univ) fun v _ => hNone u v
    simpa using this
  have hSumZero :
      Tendsto
        (fun N => ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocksA u) (blocksB v) N)
        atTop (nhds (0 : ℂ)) := by
    have := tendsto_finsetSum (s := Finset.univ) fun u _ => hInnerZero u
    simpa using this
  have hGlobalZero :
      Tendsto
        (fun N => mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (D := D) A m)
          (blockTensor (d := d) (D := D) B m) N)
        atTop (nhds (0 : ℂ)) :=
    hSumZero.congr fun N => (hOverlap_eq N).symm
  exact
    (gaugePhase_blockTensor_overlap_not_tendsto_zero_of_periodic
      A B hA hB hGPE_block) hGlobalZero

/-- Compressed-sector uniqueness statement after blocking.

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
      A B hA hB blocksA blocksB hA_mpv hB_mpv hGPE_block
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
equivalence carries a nonzero sector of `A` to a sector of `B`. The
nondegeneracy assumptions ensure that the returned `A` sector has nonzero
virtual dimension and that the corresponding `B` sector has positive bond
dimension. Both assumptions come from the periodic sector decomposition. -/
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

The no-match condition quantifies over nondegenerate dimension equalities:
for each sector pair `(u, v)` with `dimA u ≠ 0` and any proof that
`dimA u = dimB v`, the compressed blocks are not gauge-phase equivalent.
The nondegeneracy guard `dimA u ≠ 0` is essential: when `dimA u = 0`,
gauge-phase equivalence may hold vacuously for `MPSTensor _ 0`, and without
this guard the no-match condition would be unsatisfiable whenever a
zero-dimensional sector pair exists. With this guard and the separate
assumption that every sector in both decompositions has nonzero virtual
dimension, the no-match and sector-match conditions are complementary for
the dichotomy proof. Positive virtual dimension on the `B` sectors is also
needed by the mixed-sector overlap dichotomy used to extract a sector match
from global gauge-phase equivalence.

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
  have h_notGPE : ¬ GaugePhaseEquiv A B :=
    not_gaugePhaseEquiv_of_no_sector_match A B hA hB blocksA blocksB
      hA_blocks_lc hB_blocks_lc hA_mpv hB_mpv hA_cyclic hB_cyclic
      hNondegA hNondegB hNoMatch
  exact mpvOverlap_tendsto_zero_of_irreducible_TP A B
    hA.irreducible hB.irreducible hA.leftCanonical hB.leftCanonical h_notGPE


end MPSTensor
