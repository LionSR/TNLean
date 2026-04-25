/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.CyclicSectorDecomposition

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter

/-!
# Structural after-blocking theorem for canonical-form reduction

This file collects the final structural statements in the current
arXiv:1606.00608 reduction chain. It gives a common-period blocking theorem
for two tensors and the resulting structural after-blocking statement that both
sides admit TP-primitive decompositions.

## Main statements

* `bilateral_commonPeriod_blocking_tp_primitive_normal` — two tensors with
  primitive blocked transfer maps admit a common positive blocking period that
  preserves primitivity, left-canonical normalization, and normality.
* `fundamentalTheorem_after_blocking_1606_structural` — two tensors with the
  same MPVs admit blocked TP-primitive decompositions on both sides.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, §2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]

## Tags

matrix product states, canonical form, common period, fundamental theorem
-/

namespace MPSTensor

variable {d D : ℕ}

/-!
## Fundamental Theorem of MPS (arXiv:1606.00608, after blocking)

### Overview

The fundamental theorem of MPS (1606.00608 version, after blocking) asserts:

For any MPS tensor `A`, there exists a blocking period `p > 0` such that
`blockTensor A p` admits a decomposition into a trivial block plus a direct sum
of TP sectors, where each sector is left-canonical and the direct sum is
`SameMPV₂`-equivalent to the blocked tensor.

The full end-to-end statement chains:
1. Zero-block separation (`exists_irreducible_blockDecomp_liveBlocks`)
2. TP gauge (`exists_tp_gauge_from_arbitrary_with_zeroTail`)
3. Common blocking to primitive (`exists_common_blocking_all_primitive_of_TP_irr`)
4. Cyclic sector decomposition per block (`exists_cyclic_sector_decomp_after_blocking`)

### Current status

The theorem `exists_tp_sector_decomp_after_blocking` below provides:
- A blocking period `p > 0`
- A trivial block of dimension `zeroTailDim`
- A family of TP sector blocks
- The MPV relationship: `blockTensor A p` is `SameMPV₂`-equivalent to
  `zeroMPSTensor + toTensorFromBlocks μ sectors` for some weights `μ`

The current library already settles the common-period blocking step and the
primitive / irreducible / normal bridges needed after blocking. The remaining
Gap §1 content is now more specific:
- a **general BNT sector construction** for the blocked output, matching the
  paper's basis-of-normal-tensors decomposition rather than only the restricted
  norm-class-collapse theorem `exists_bnt_grouping`, and
- a **witness-producing heterogeneous sector comparison theorem** deriving the
  basis permutation, gauge-phase data, and copy alignment for two such BNT
  sector decompositions from arbitrary `SameMPV₂`.

The downstream algebraic reduction after a matched basis is now formalized by
`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`, and
the matching data itself is recorded by the `SectorBasisMatching` witness type
used in
`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching`. The
remaining step is to construct such a `SectorBasisMatching` from arbitrary
`SameMPV₂` sector decompositions (fed by the general BNT sector construction
tracked separately).
-/

section FundamentalTheorem1606

-- **Structural decomposition of MPS tensors after blocking (1606.00608 reduction).**
--
-- For any MPS tensor `A`, there exists a blocking period `p > 0` and a
-- decomposition of the blocked tensor into:
-- 1. A trivial block (irreducible blocks with zero spectral weight)
-- 2. A family of TP blocks with primitive transfer maps
--
-- Additionally, the weights `μ k` satisfy `μ k ≠ 0` and the full MPV
-- identity is maintained.
--
-- This is `exists_tp_primitive_blockDecomp_after_blocking` — the main reduction
-- theorem from the first section. The FT chains from this through the cyclic
-- sector decomposition to produce the final canonical form.
-- (Already proved above as `exists_tp_primitive_blockDecomp_after_blocking`.)

/-- **Bilateral common-period theorem for two tensors.**

The proof chooses a common blocking period via `lcmPeriod` (on `Fin 2`), i.e. a
common multiple of `pA` and `pB`. The theorem statement itself only asserts the
existence of some positive period `p` for which both `blockTensor A p` and
`blockTensor B p` have primitive transfer maps.

If `A` and `B` are left-canonical (TP), then TP is preserved for this common
blocking. If `A` and `B` are normal, normality is also preserved for such a
common blocking period.

This is the building block for BNT canonical form alignment in subsequent
reduction steps; see issue #672 (Gap §1 step 2a). -/
theorem bilateral_commonPeriod_blocking_tp_primitive_normal
    {d D₁ D₂ : ℕ}
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (pA pB : ℕ) (hpA : 0 < pA) (hpB : 0 < pB)
    (hTPA : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hTPB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hPrimA : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d pA) (D := D₁)
        (blockTensor (d := d) (D := D₁) A pA)))
    (hPrimB : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d pB) (D := D₂)
        (blockTensor (d := d) (D := D₂) B pB)))
    (hNormalA : IsNormal A) (hNormalB : IsNormal B) :
    ∃ p, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D₁)
          (blockTensor (d := d) (D := D₁) A p)) ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D₂)
          (blockTensor (d := d) (D := D₂) B p)) ∧
      (∑ i : Fin (blockPhysDim d p),
        (blockTensor (d := d) (D := D₁) A p i)ᴴ *
          blockTensor (d := d) (D := D₁) A p i = 1) ∧
      (∑ i : Fin (blockPhysDim d p),
        (blockTensor (d := d) (D := D₂) B p i)ᴴ *
          blockTensor (d := d) (D := D₂) B p i = 1) ∧
      IsNormal (d := blockPhysDim d p) (D := D₁)
        (blockTensor (d := d) (D := D₁) A p) ∧
      IsNormal (d := blockPhysDim d p) (D := D₂)
        (blockTensor (d := d) (D := D₂) B p) := by
  let periods : Fin 2 → ℕ := ![pA, pB]
  let p := lcmPeriod periods
  have hpPeriods : ∀ i : Fin 2, 0 < periods i := by
    intro i
    fin_cases i
    · exact hpA
    · exact hpB
  have hp : 0 < p := lcmPeriod_pos hpPeriods
  have hA_dvd : pA ∣ p := dvd_lcmPeriod periods 0
  have hB_dvd : pB ∣ p := by
    simpa [periods] using dvd_lcmPeriod periods 1
  have hPrimA' : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := D₁)
        (blockTensor (d := d) (D := D₁) A p)) :=
    isPrimitive_transferMap_blockTensor_of_dvd
      (d := d) (D := D₁) A pA p hA_dvd hp hPrimA
  have hPrimB' : _root_.IsPrimitive
      (transferMap (d := blockPhysDim d p) (D := D₂)
        (blockTensor (d := d) (D := D₂) B p)) :=
    isPrimitive_transferMap_blockTensor_of_dvd
      (d := d) (D := D₂) B pB p hB_dvd hp hPrimB
  refine ⟨p, hp, hPrimA', hPrimB', ?_, ?_, ?_, ?_⟩
  · exact leftCanonical_blockTensor (d := d) (D := D₁) (A := A) p hTPA
  · exact leftCanonical_blockTensor (d := d) (D := D₂) (A := B) p hTPB
  · exact isNormal_blockTensor_of_isNormal (d := d) (D := D₁) A hp hNormalA
  · exact isNormal_blockTensor_of_isNormal (d := d) (D := D₂) B hp hNormalB

/-- **Fundamental Theorem of MPS (1606.00608, after blocking): current structural shell.**

For any two MPS tensors `A, B` with `SameMPV₂ A B`, this theorem records the
currently formalized one-sided reduction output on both sides: after blocking,
each tensor admits a decomposition into TP blocks with primitive transfer maps,
nonzero weights, and positive bond dimensions.

The theorem does **not yet** use `SameMPV₂ A B` to compare the two blocked
outputs. The remaining missing content is the sector-level comparison
described in the file documentation below: a general BNT sector construction
for each side, followed by a heterogeneous equal-case comparison theorem for
those sector decompositions.

This theorem therefore records the structural shell currently available on the
way to arXiv:1606.00608, Theorem 1. -/
theorem fundamentalTheorem_after_blocking_1606_structural
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (_hSame : SameMPV₂ A B) :
    -- Both tensors admit blocked TP-primitive decompositions
    ∃ (pA : ℕ) (_ : 0 < pA)
      (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d pA) (dimA k)),
    ∃ (pB : ℕ) (_ : 0 < pB)
      (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d pB) (dimB k)),
      -- Blocks are TP
      (∀ k, ∑ i, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      -- Blocks have primitive transfer maps
      (∀ k, _root_.IsPrimitive (transferMap (blocksA k))) ∧
      (∀ k, _root_.IsPrimitive (transferMap (blocksB k))) ∧
      -- Nonzero weights
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      -- Positive bond dimensions
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) := by
  obtain ⟨_, pA, hpA, rA, dimA, μA, blocksA, hTPA, hPrimA, hDimA, hμA, _⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking A
  obtain ⟨_, pB, hpB, rB, dimB, μB, blocksB, hTPB, hPrimB, hDimB, hμB, _⟩ :=
    exists_tp_primitive_blockDecomp_after_blocking B
  exact ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩

/-- A strengthened after-blocking structural interface that keeps the blocked `SameMPV₂`
relations at the reduction periods. This is a small but genuine step toward Gap §1 because the
common-equality input is no longer discarded by the public structural theorem. -/
theorem fundamentalTheorem_after_blocking_1606_structural_with_blockedSameMPV₂
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B) :
    ∃ (pA : ℕ) (_ : 0 < pA)
      (rA : ℕ) (dimA : Fin rA → ℕ) (μA : Fin rA → ℂ)
      (blocksA : (k : Fin rA) → MPSTensor (blockPhysDim d pA) (dimA k)),
    ∃ (pB : ℕ) (_ : 0 < pB)
      (rB : ℕ) (dimB : Fin rB → ℕ) (μB : Fin rB → ℂ)
      (blocksB : (k : Fin rB) → MPSTensor (blockPhysDim d pB) (dimB k)),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A pA)
        (blockTensor (d := d) (D := D₂) B pA) ∧
      SameMPV₂ (blockTensor (d := d) (D := D₁) A pB)
        (blockTensor (d := d) (D := D₂) B pB) ∧
      (∀ k, ∑ i, (blocksA k i)ᴴ * blocksA k i = 1) ∧
      (∀ k, ∑ i, (blocksB k i)ᴴ * blocksB k i = 1) ∧
      (∀ k, _root_.IsPrimitive (transferMap (blocksA k))) ∧
      (∀ k, _root_.IsPrimitive (transferMap (blocksB k))) ∧
      (∀ k, μA k ≠ 0) ∧
      (∀ k, μB k ≠ 0) ∧
      (∀ k, 0 < dimA k) ∧
      (∀ k, 0 < dimB k) := by
  obtain ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩ :=
    fundamentalTheorem_after_blocking_1606_structural A B hSame
  refine ⟨pA, hpA, rA, dimA, μA, blocksA, pB, hpB, rB, dimB, μB, blocksB,
    ?_, ?_, hTPA, hTPB, hPrimA, hPrimB, hμA, hμB, hDimA, hDimB⟩
  · exact sameMPV₂_blockTensor A B hSame pA
  · exact sameMPV₂_blockTensor A B hSame pB

/-- **Conditional after-blocking sector endpoint (issue #877 target shape).**

Given two tensors with `SameMPV₂` and the two missing Gap §1 inputs tracked by
issues #876 and #860, this theorem produces the target assembly endpoint: a
common blocking period, a `SectorDecomposition` on each side carrying BNT basis
data, and matched sector-weight data closing the canonical-form reduction.

The two hypotheses express the missing paper-level inputs:

* `bntSectorPair` supplies a common-period BNT sector decomposition for both
  sides, `SameMPV₂`-equivalent to the blocked tensors and carrying
  `HasBNTSectorData`.  This is the endpoint tracked by issue #876 and replaces
  the current single-norm-class result `bnt_grouping_single_norm_class`.
* `matchedBasisData` supplies the matched-basis witness (permutation, copy
  alignment, per-block gauge-phase equivalence) from `SameMPV₂` between two
  sector decompositions whose first entry has BNT basis data.  This is the
  endpoint tracked by issue #860.

The body is a kernel-checked composition of the existing structural wrapper's
blocking compatibility (`sameMPV₂_blockTensor`), the two hypotheses, and the
matched-basis algebraic endpoint from PR #844
(`fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`).

Once #876 and #860 land on `main`, the unconditional endpoint
`fundamentalTheorem_after_blocking_1606_sector` of issue #877 is obtained by
instantiating this theorem with the delivered constructors. -/
theorem fundamentalTheorem_after_blocking_1606_sector_of_bntPair_matched
    {d D₁ D₂ : ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (bntSectorPair :
      ∃ p : ℕ, 0 < p ∧
      ∃ P Q : SectorDecomposition (blockPhysDim d p),
        SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
        SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
        HasBNTSectorData P ∧ HasBNTSectorData Q)
    (matchedBasisData : ∀ {d' : ℕ} (P Q : SectorDecomposition d'),
      HasBNTSectorData P → SameMPV₂ P.toTensor Q.toTensor →
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
        (∀ j, P.copies j = Q.copies (perm j)) ∧
        ∀ j : Fin P.basisCount,
          ∃ hdim : P.basisDim j = Q.basisDim (perm j),
            GaugePhaseEquiv (d := d')
              (cast (congr_arg (MPSTensor d') hdim) (P.basis j))
              (Q.basis (perm j))) :
    ∃ p : ℕ, 0 < p ∧
    ∃ P Q : SectorDecomposition (blockPhysDim d p),
      SameMPV₂ (blockTensor (d := d) (D := D₁) A p) P.toTensor ∧
      SameMPV₂ (blockTensor (d := d) (D := D₂) B p) Q.toTensor ∧
      HasBNTSectorData P ∧ HasBNTSectorData Q ∧
      ∃ perm : Fin P.basisCount ≃ Fin Q.basisCount,
      ∃ hCopies : ∀ j, P.copies j = Q.copies (perm j),
      ∃ ζ : Fin P.basisCount → ℂ,
        (∀ j, ζ j ≠ 0) ∧
        ∀ j : Fin P.basisCount,
          Finset.univ.val.map (P.weight j) =
            Finset.univ.val.map
              (fun q => ζ j * Q.weight (perm j) (Fin.cast (hCopies j) q)) := by
  obtain ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt⟩ := bntSectorPair
  have hAB : SameMPV₂ (blockTensor (d := d) (D := D₁) A p)
                      (blockTensor (d := d) (D := D₂) B p) :=
    sameMPV₂_blockTensor A B hSame p
  have hPQeq : SameMPV₂ P.toTensor Q.toTensor := by
    intro N σ
    calc
      mpv P.toTensor σ
          = mpv (blockTensor (d := d) (D := D₁) A p) σ := (hPeq N σ).symm
      _ = mpv (blockTensor (d := d) (D := D₂) B p) σ := hAB N σ
      _ = mpv Q.toTensor σ := hQeq N σ
  obtain ⟨perm, hCopies, hBasisGPE⟩ := matchedBasisData P Q hPbnt hPQeq
  obtain ⟨ζ, hζne, hMultiset⟩ :=
    fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis
      P Q perm hCopies hBasisGPE hPbnt hPQeq
  exact ⟨p, hp, P, Q, hPeq, hQeq, hPbnt, hQbnt,
          perm, hCopies, ζ, hζne, hMultiset⟩

/-!
### What remains for the full 1606.00608 Fundamental Theorem

The complete end-to-end FT should take two tensors `A, B` with `SameMPV₂ A B`
and pass from the blocked reduction output to the paper's basis-of-normal-tensors
sector comparison. The remaining formalizations are now:

1. **General one-sided BNT construction**: starting from the blocked TP-primitive
   decomposition, construct a sector decomposition in the paper's general BNT
   sense. This is stronger than the current special-case theorem
   `exists_bnt_grouping`, which only collapses norm classes already known to
   represent one MPV family.

2. **Witness-producing heterogeneous sector comparison**: the algebraic
   reduction from a matched basis to per-sector weight multiset equality is
   formalized by
   `fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_matched_basis`
   (with phase-match core
   `fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_phaseMatch`), and
   the matching data is bundled by the `SectorBasisMatching` witness type
   exposed through
   `fundamentalTheorem_equalMPV_sectorDecomposition_hetero_of_sectorMatching`.
   What is still missing is the theorem that constructs such a
   `SectorBasisMatching` — deriving the basis permutation, gauge-phase data,
   and copy alignment — from arbitrary equal total MPVs of two sector
   decompositions.

3. **Final global construction**: once steps 1–2 are available, combine them with the
   already-formalized common-period blocking, blocked irreducibility,
   `isNormal_of_tp_primitive_irreducible`, and the global gauge construction of
   the equal-case FT.

So the common-period blocking step is no longer the blocker; the missing content
is specifically the paper-level sector comparison theorem.

The conditional theorem
`fundamentalTheorem_after_blocking_1606_sector_of_bntPair_matched` above gives
the target after-blocking sector comparison shape from issue #877: once the two
missing paper-level inputs (issues #876 and #860) land on `main`, the
unconditional after-blocking sector theorem is a one-line instantiation of that
result.
-/

end FundamentalTheorem1606

end MPSTensor
