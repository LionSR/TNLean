/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Spectral.SpectralGapNT

open scoped Matrix BigOperators
open Filter

/-!
# Phase-class BNT sector data

This file builds BNT sector decompositions by quotienting a family of primitive
irreducible blocks by MPV phase equivalence.  It proves the representative
overlap data and transports finite-length MPV span identities through the chosen
phase classes.
-/

namespace MPSTensor

variable {d : ℕ}

/-! ### Eventual independence from separated overlap data -/

/-- **Eventual BNT linear independence for an already separated normal family.**

For TP primitive irreducible blocks that are pairwise not gauge-phase equivalent,
self-overlaps tend to `1` and cross-overlaps tend to `0`.  Hence their MPV states
are eventually linearly independent.  This supplies the missing linear-independence
step after a future one-sided BNT construction has chosen separated representatives
and absorbed all repeated gauge phases into sector weights. -/
theorem exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) blocks) :
    ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun k : Fin r => mpvState (d := d) (blocks k) N) := by
  apply exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal blocks
  · intro k
    exact overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (blocks k) (hIrr k) (hTP k) (hPrim k)
  · intro j k hjk
    exact cross_overlap_tendsto_zero_of_separated_normalCFBNT_data blocks
      (HasIrreducibleBlocks.ofForall hIrr)
      (IsLeftCanonicalBlockFamily.ofForall hTP)
      hBlocks j k hjk

/-- **Separated-family BNT sector construction.**

If the given TP primitive irreducible blocks are already pairwise separated by
non-gauge-phase-equivalence, the one-sector-per-block sector decomposition is a genuine BNT
sector decomposition: it represents the original weighted block sum and satisfies
`HasBNTSectorData` by the overlap-derived eventual linear independence above.

This theorem does not identify gauge-phase-equivalent blocks.  Instead it
identifies the exact remaining task for the full one-sided construction: first
choose separated representatives and absorb the corresponding phases into sector
weights, then apply this constructor. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) blocks) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P := by
  refine ⟨trivialSectorDecomp μ blocks hμne,
    sameMPV₂_trivialSectorDecomp μ blocks hμne, ?_⟩
  simpa [trivialSectorDecomp] using
    exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
      blocks hTP hIrr hPrim hBlocks

/-- The concrete sector decomposition obtained from representatives of MPV phase classes. -/
private noncomputable def collapsedBntSectorDecomp
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0) : SectorDecomposition d :=
  let classes := mpvPhaseClassData blocks
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose
  let hζ_ne : ∀ j q, ζFn j q ≠ 0 :=
    fun j q => (classes.enum_phase j q).choose_spec.1
  let sectors : SectorWeightData classes.g := {
    copies := classes.copies
    copies_pos := classes.copies_pos
    weight := fun j q => ζFn j q * μ (classes.enum j q)
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j q) (hμne (classes.enum j q))
  }
  {
    basisCount := classes.g
    basisDim := fun j => dim (classes.repr j)
    basis := fun j => blocks (classes.repr j)
    sectors := sectors
  }

private theorem collapsedBntSectorDecomp_sameMPV₂
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0) :
    SameMPV₂ (collapsedBntSectorDecomp (d := d) μ blocks hμne).toTensor
      (toTensorFromBlocks (d := d) (μ := μ) blocks) := by
  classical
  let classes := mpvPhaseClassData blocks
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose
  have hζ_mpv : ∀ j q (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks (classes.enum j q)) σ = (ζFn j q) ^ N * mpv (blocks (classes.repr j)) σ :=
    fun j q N σ => (classes.enum_phase j q).choose_spec.2 N σ
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  intro N σ
  calc mpv P.toTensor σ
      = ∑ j : Fin P.basisCount,
          ∑ q : Fin (P.copies j), (P.weight j q) ^ N * mpv (P.basis j) σ :=
          P.mpv_toTensor_eq_sum_sectors σ
    _ = ∑ j : Fin classes.g,
          ∑ q : Fin (classes.copies j),
            (ζFn j q * μ (classes.enum j q)) ^ N *
              mpv (blocks (classes.repr j)) σ := by
            rfl
    _ = ∑ j : Fin classes.g,
          ∑ q : Fin (classes.copies j),
            (μ (classes.enum j q)) ^ N * mpv (blocks (classes.enum j q)) σ := by
            refine Finset.sum_congr rfl (fun j _ =>
              Finset.sum_congr rfl (fun q _ => ?_))
            rw [mul_pow, hζ_mpv j q N σ]
            ring
    _ = ∑ k : Fin r, (μ k) ^ N * mpv (blocks k) σ :=
          classes.regroup (fun k => (μ k) ^ N * mpv (blocks k) σ)
    _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
            symm
            simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ

private theorem collapsedBntSectorDecomp_hasBNT
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    HasBNTSectorData (d := d) (collapsedBntSectorDecomp (d := d) μ blocks hμne) := by
  classical
  let classes := mpvPhaseClassData blocks
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ
        (fun j : Fin classes.g => mpvState (d := d) (blocks (classes.repr j)) N) :=
    exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
      (fun j : Fin classes.g => blocks (classes.repr j))
      (fun j => hTP (classes.repr j))
      (fun j => hIrr (classes.repr j))
      (fun j => hPrim (classes.repr j))
      classes.blocks_not_equiv
  simpa [P, collapsedBntSectorDecomp] using hLI

/-- **Unconditional one-sided BNT sector construction for primitive irreducible blocks.**

Starting from arbitrary trace-preserving primitive irreducible blocks with
nonzero weights, quotient the block indices by MPV phase equivalence.  One
representative is chosen for each class; for every original block in the class,
the associated phase is multiplied into its sector weight.  Gauge-phase-equivalent
blocks land in the same MPV phase class, so the chosen representatives satisfy
`BlocksNotGaugePhaseEquiv`.  The separated-family BNT independence theorem then
proves `HasBNTSectorData` for the constructed sector decomposition. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P := by
  refine ⟨collapsedBntSectorDecomp (d := d) μ blocks hμne, ?_, ?_⟩
  · exact collapsedBntSectorDecomp_sameMPV₂ (d := d) μ blocks hμne
  · exact collapsedBntSectorDecomp_hasBNT (d := d) μ blocks hTP hIrr hPrim hμne

/-- **Phase-class BNT sector construction with one-sided overlap data.**

Starting from trace-preserving primitive irreducible blocks with nonzero weights,
quotient the block indices by MPV phase equivalence. The constructed sector
decomposition represents the original weighted block sum, satisfies the BNT
linear-independence condition, and its chosen basis blocks carry the
single-family overlap-orthogonality data needed for the primitive
overlap-rigidity route.

The theorem also proves that if the original blocks are one-site injective,
then the chosen basis blocks are injective. It does not claim the remaining
two-family hypothesis: equality of the finite-length MPV spans between two
independently constructed bases is a separate task. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P ∧
      SectorBasisOverlapOrthoHypotheses P ∧
      ((∀ k, IsInjective (blocks k)) → ∀ j, IsInjective (P.basis j)) := by
  classical
  let classes := mpvPhaseClassData blocks
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hSame : SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) :=
    collapsedBntSectorDecomp_sameMPV₂ (d := d) μ blocks hμne
  have hBNT : HasBNTSectorData (d := d) P :=
    collapsedBntSectorDecomp_hasBNT (d := d) μ blocks hTP hIrr hPrim hμne
  refine ⟨P, hSame, hBNT, ?_, ?_⟩
  · refine {
      dim_pos := ?_
      normalized := ?_
      self_overlap := ?_
      off_overlap := ?_
    }
    · intro j
      simpa [P, collapsedBntSectorDecomp] using NeZero.pos (dim (classes.repr j))
    · intro j
      simpa [P, collapsedBntSectorDecomp] using hTP (classes.repr j)
    · intro j
      simpa [P, collapsedBntSectorDecomp] using
        overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
        (blocks (classes.repr j)) (hIrr (classes.repr j))
        (hTP (classes.repr j)) (hPrim (classes.repr j))
    · intro i j hij
      simpa [P, collapsedBntSectorDecomp] using
        cross_overlap_tendsto_zero_of_separated_normalCFBNT_data
        (fun j : Fin classes.g => blocks (classes.repr j))
        (HasIrreducibleBlocks.ofForall (fun j => hIrr (classes.repr j)))
        (IsLeftCanonicalBlockFamily.ofForall (fun j => hTP (classes.repr j)))
        classes.blocks_not_equiv i j hij
  · intro hInj j
    simpa [P, collapsedBntSectorDecomp] using hInj (classes.repr j)

/-- Concrete one-sided data for the construction using representatives of MPV phase-equivalence
classes, including the finite-length representative-span identity.

This private auxiliary lemma gives the common conclusions used by the public one-sided
overlap-data theorems. -/
private theorem bntSectorDecomp_overlapData_basisSpan_aux
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hInj : ∀ k, IsInjective (blocks k))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P ∧
      (∀ j : Fin P.basisCount, 0 < P.basisDim j) ∧
      (∀ j : Fin P.basisCount, IsInjective (P.basis j)) ∧
      (∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1) ∧
      (∀ j : Fin P.basisCount,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
          Filter.atTop (nhds (1 : ℂ))) ∧
      (∀ i j : Fin P.basisCount, i ≠ j →
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
          Filter.atTop (nhds 0)) ∧
      (∀ N,
        Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
          mpvState (d := d) (P.basis j) N)) =
        Submodule.span ℂ (Set.range (fun k : Fin r =>
          mpvState (d := d) (blocks k) N))) := by
  classical
  let classes := mpvPhaseClassData blocks
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hSame : SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) :=
    collapsedBntSectorDecomp_sameMPV₂ (d := d) μ blocks hμne
  have hBNT : HasBNTSectorData (d := d) P :=
    collapsedBntSectorDecomp_hasBNT (d := d) μ blocks hTP hIrr hPrim hμne
  refine ⟨P, hSame, hBNT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [P, collapsedBntSectorDecomp] using NeZero.pos (dim (classes.repr j))
  · intro j
    simpa [P, collapsedBntSectorDecomp] using hInj (classes.repr j)
  · intro j
    simpa [P, collapsedBntSectorDecomp] using hTP (classes.repr j)
  · intro j
    simpa [P, collapsedBntSectorDecomp] using
      overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (blocks (classes.repr j)) (hIrr (classes.repr j)) (hTP (classes.repr j))
      (hPrim (classes.repr j))
  · intro i j hij
    simpa [P, collapsedBntSectorDecomp] using
      cross_overlap_tendsto_zero_of_separated_normalCFBNT_data
      (fun j : Fin classes.g => blocks (classes.repr j))
      (HasIrreducibleBlocks.ofForall (fun j => hIrr (classes.repr j)))
      (IsLeftCanonicalBlockFamily.ofForall (fun j => hTP (classes.repr j)))
      classes.blocks_not_equiv i j hij
  · intro N
    simpa [P, collapsedBntSectorDecomp] using classes.representative_mpv_span_eq (d := d) N

/-- **Phase-class BNT sector construction with primitive overlap data.**

This strengthens `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` by exposing the
properties of the chosen representative basis blocks that are needed by the overlap-rigidity
layer. The extra `hInj` hypothesis is intentional: the one-sided BNT constructor assumes
irreducibility, primitivity, and trace preservation, while
`SectorBasisOverlapSpanHypotheses` consumes length-1 MPS-injectivity.

The finite-span comparison between two independently constructed sector bases is not part of
this one-sided theorem; it depends on comparing the two sides. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hInj : ∀ k, IsInjective (blocks k))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P ∧
      (∀ j : Fin P.basisCount, 0 < P.basisDim j) ∧
      (∀ j : Fin P.basisCount, IsInjective (P.basis j)) ∧
      (∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1) ∧
      (∀ j : Fin P.basisCount,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
          Filter.atTop (nhds (1 : ℂ))) ∧
      (∀ i j : Fin P.basisCount, i ≠ j →
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
          Filter.atTop (nhds 0)) := by
  obtain ⟨P, hSame, hBNT, hPos, hBasisInj, hBasisTP, hSelfOverlap, hCrossOverlap, _hSpan⟩ :=
    bntSectorDecomp_overlapData_basisSpan_aux
      (d := d) μ blocks hTP hIrr hPrim hInj hμne
  exact ⟨P, hSame, hBNT, hPos, hBasisInj, hBasisTP, hSelfOverlap, hCrossOverlap⟩

/-- **Phase-class BNT sector construction with overlap data and the quotient span identity.**

This strengthens `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData` by
also exposing the finite-length span invariant of the phase-class representative
construction: at every length, the chosen MPV phase-class representatives span the same
MPV subspace as the original block
family.  This removes the quotient/enumeration identities from later two-sided span
comparisons; the remaining comparison is the genuine equality of the two original nonzero-block
spans. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData_and_basisSpan
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hInj : ∀ k, IsInjective (blocks k))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P ∧
      (∀ j : Fin P.basisCount, 0 < P.basisDim j) ∧
      (∀ j : Fin P.basisCount, IsInjective (P.basis j)) ∧
      (∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1) ∧
      (∀ j : Fin P.basisCount,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
          Filter.atTop (nhds (1 : ℂ))) ∧
      (∀ i j : Fin P.basisCount, i ≠ j →
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
          Filter.atTop (nhds 0)) ∧
      (∀ N,
        Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
          mpvState (d := d) (P.basis j) N)) =
        Submodule.span ℂ (Set.range (fun k : Fin r =>
          mpvState (d := d) (blocks k) N))) := by
  exact bntSectorDecomp_overlapData_basisSpan_aux
    (d := d) μ blocks hTP hIrr hPrim hInj hμne

/-- **Two-sided overlap-span data from nonzero-weight block span equality.**

Apply the construction using representatives of MPV phase-equivalence classes on both
nonzero-weight block families. The one-sided quotient span identity above transports a
finite-length span equality for the original blocks to the two independently chosen sector bases.
Thus the theorem proves `SectorBasisOverlapSpanHypotheses` without assuming that
relation directly.

The remaining paper-level task, not proved here, is to derive the displayed block-span
equality from the global `SameMPV₂` and structural reduction data. -/
theorem exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hTPA : ∀ k, ∑ i : Fin d, (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin d, (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dimB k) (blocksB k)))
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (hBlockSpan : ∀ N,
      Submodule.span ℂ (Set.range (fun k : Fin rA =>
        mpvState (d := d) (blocksA k) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin rB =>
        mpvState (d := d) (blocksB k) N))) :
    ∃ P Q : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μA) blocksA) ∧
      SameMPV₂ Q.toTensor (toTensorFromBlocks (d := d) (μ := μB) blocksB) ∧
      HasBNTSectorData (d := d) P ∧
      HasBNTSectorData (d := d) Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨P, hPblocks, hPbnt, hPdim, hPinj, hPnorm, hPself, hPoff, hPspan⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData_and_basisSpan
      (d := d) μA blocksA hTPA hIrrA hPrimA hInjA hμA
  obtain ⟨Q, hQblocks, hQbnt, hQdim, hQinj, hQnorm, hQself, hQoff, hQspan⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData_and_basisSpan
      (d := d) μB blocksB hTPB hIrrB hPrimB hInjB hμB
  have hSpan : ∀ N,
      Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
        mpvState (d := d) (P.basis j) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
        mpvState (d := d) (Q.basis k) N)) := by
    intro N
    calc
      Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
          mpvState (d := d) (P.basis j) N))
          = Submodule.span ℂ (Set.range (fun k : Fin rA =>
              mpvState (d := d) (blocksA k) N)) := hPspan N
      _ = Submodule.span ℂ (Set.range (fun k : Fin rB =>
              mpvState (d := d) (blocksB k) N)) := hBlockSpan N
      _ = Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
              mpvState (d := d) (Q.basis k) N)) := (hQspan N).symm
  refine ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, ?_⟩
  exact {
    left_dim_pos := hPdim
    right_dim_pos := hQdim
    left_injective := hPinj
    right_injective := hQinj
    left_normalized := hPnorm
    right_normalized := hQnorm
    left_self_overlap := hPself
    left_off_overlap := hPoff
    right_self_overlap := hQself
    right_off_overlap := hQoff
    span_eq := hSpan
  }

/-- **Two-sided overlap-span data from a common MPV phase cover.**

This is the common MPV phase-cover form of
`exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq`.  The cover
supplies the finite-length span equality for the two nonzero-weight block families,
and the one-sided BNT representative construction supplies the remaining overlap,
normalization, positive-dimension, and injectivity data. -/
theorem exists_bnt_sectorDecomp_pair_with_overlapSpan_of_commonPhaseCover
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hTPA : ∀ k, ∑ i : Fin d, (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin d, (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dimB k) (blocksB k)))
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (cover : MPVCommonPhaseCover blocksA blocksB) :
    ∃ P Q : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μA) blocksA) ∧
      SameMPV₂ Q.toTensor (toTensorFromBlocks (d := d) (μ := μB) blocksB) ∧
      HasBNTSectorData (d := d) P ∧
      HasBNTSectorData (d := d) Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  exact exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
    (d := d) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB hPrimA hPrimB
    hInjA hInjB hμA hμB (fun N => cover.span_eq N)

/-- **Two-sided overlap-span data from BNT proportional-decomposition data.**

A proportional-decomposition comparison gives a common MPV phase cover of the two
nonzero-weight block families. Therefore it supplies the finite-length span equality
needed by the two-sided BNT representative construction, without assuming that span
equality as a separate hypothesis. -/
theorem exists_bnt_sectorDecomp_pair_with_overlapSpan_of_proportionalDecompositionConclusion
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hTPA : ∀ k, ∑ i : Fin d, (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin d, (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dimB k) (blocksB k)))
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (hMatch : ProportionalDecompositionConclusion (d := d) blocksA blocksB) :
    ∃ P Q : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μA) blocksA) ∧
      SameMPV₂ Q.toTensor (toTensorFromBlocks (d := d) (μ := μB) blocksB) ∧
      HasBNTSectorData (d := d) P ∧
      HasBNTSectorData (d := d) Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨cover⟩ := nonempty_mpvCommonPhaseCover_of_proportionalDecompositionConclusion
    (d := d) blocksA blocksB hMatch
  exact exists_bnt_sectorDecomp_pair_with_overlapSpan_of_commonPhaseCover
    (d := d) μA blocksA μB blocksB hTPA hTPB hIrrA hIrrB hPrimA hPrimB
    hInjA hInjB hμA hμB cover

/-! ### Conditional sector construction under BNT linear independence -/

/-- **One-sector-per-block sector decomposition carrying current `HasBNTSectorData`.**

This is the formulation of the conditional sector construction.  The
predicate `HasBNTSectorData` now means eventual linear independence of the sector
basis MPV states.  TP, irreducibility, primitivity, and nonzero weights do not by
themselves provide that linear-independence statement for the one-sector-per-block basis; the
one-sided BNT construction must first choose representatives forming a basis of normal tensors.

Accordingly this theorem gives the direct structural construction: if the
one-sector-per-block basis is already known to satisfy the current BNT
linear-independence hypothesis, then `trivialSectorDecomp` gives the requested
`SectorDecomposition` and the `HasBNTSectorData` certificate is exactly the supplied `hLI`. -/
theorem exists_bnt_sectorDecomp_of_linearIndependent
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun k : Fin r => mpvState (blocks k) N)) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P := by
  refine ⟨trivialSectorDecomp μ blocks hμne,
    sameMPV₂_trivialSectorDecomp μ blocks hμne, ?_⟩
  simpa [trivialSectorDecomp] using hLI

/-- Signature-compatible reformulation for TP / primitive / irreducible block data.

The extra block-normality hypotheses are intentionally retained here to match the
shape expected by the one-sided BNT-construction route, but only nonzero weights and the
current BNT linear-independence hypothesis are used.  Use
`exists_bnt_sectorDecomp_of_linearIndependent` when those extra hypotheses are not
already present. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_linearIndependent
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (_hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (_hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (_hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun k : Fin r => mpvState (blocks k) N)) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P :=
  exists_bnt_sectorDecomp_of_linearIndependent μ blocks hμne hLI

end MPSTensor
