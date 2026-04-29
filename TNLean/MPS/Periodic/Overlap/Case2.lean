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
  -- Missing step: expand the globally non-decaying blocked overlap as a
  -- finite sum of mixed sector overlaps and use finite-sum convergence.
  sorry

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
`hNondegA` supplies the nonzero-sector identification for the returned `A` sector, while
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
  -- PROOF STRUCTURE: see lemma
  -- `exists_sector_match_of_blockedGaugePhaseEquiv_cyclicDecomp` for the
  -- planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp`
  -- and `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`.
  sorry

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
  -- PROOF STRUCTURE: see lemma
  -- `exists_sector_match_of_gaugePhaseEquiv` for the planned proof route.
  -- Currently sorry-backed pending discharge of
  -- `exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp`
  -- and `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`.
  sorry

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
