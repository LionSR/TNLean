# Issue #652 Gap §1 unconditional CPSV17 Thm 1 — scouting audit

Date: 2026-05-02
Branch: `feat/652-gap1-scout`
Context: After all Wave 27 merges, main has substantial canonical-form infrastructure.
Goal: Document exactly what remains for the unconditional after-blocking fundamental theorem
(the equal-MPV case of CPSV17 Thm 1, arXiv:1606.00608, without the periodic Fundamental Theorem).

## Executive summary

The project now has a structured, paper-faithful chain of conditional theorems that
reach from `SameMPV₂ A B` to the sector-weight comparison conclusion, given four
explicit extra hypotheses.  Each hypothesis is named by a Lean structure, and
each maps to a specific issue.  Two of the four hypotheses are pure Lean
bookkeeping; the other two are genuine paper-level mathematics.

The four remaining hypotheses are:

| # | Hypothesis | Lean structure | Issue | Nature |
|---|-----------|----------------|-------|--------|
| H1 | Blocked-word Fintype coordinate equality | `flattenWordOfBlock_cast_eq` `sorry` | #1075 / #990 / #1113 (`flattenWordOfBlock_cast_eq` → `CommonGroupedBlockCastHypothesis d`) | Pure Lean bookkeeping (Fintype instance compatibility) |
| H2 | Common nonzero-block decomposition after relabeling | `CommonSectorRelabelingHypothesis d` | #942 | Derived from H1 (H1 → H2 via `CommonGroupedBlockCastHypothesis.toRelabelingHypothesis`) |
| H3 | Zero-tail equality + injectivity + common phase cover / BNT-cover comparison | `CommonPrimitivePhaseCoverHypotheses` (or the `CommonPrimitiveBNTCoverHypotheses` bridge) | #1068 / #652 | Genuine paper-level math |
| H4 | (Resolved: one-sided BNT construction with overlap data) | `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho` | #877 / #945 / #923 | Resolved (Wave 17G PR #945) |

The conditional after-blocking theorem `fundamentalTheorem_afterBlocking_of_comparisonHypotheses`
in `TNLean/MPS/CanonicalForm/Assembly.lean` already accepts H1–H3 as explicit hypotheses
and produces the full sector-weight conclusion.  The remaining work to reach the
unconditional theorem is the proof of H1 and the derivation of H3 from the
structural reduction.

## Dependency chain traced

The full chain from the individual issues to #652 is:

```
#1113 (Fintype gap: `flattenWordOfBlock_cast_eq`)
  → #990 (blocked-word comparison via `CommonGroupedBlockCastHypothesis`)
    → #942 (common exact nonzero sector decomposition)
      → #1114/#969 (common-length sector construction / common-blocking)
        → #1068 (common phase cover or span from common sectors)
          → #652 (Gap §1 — unconditional CPSV17 Thm 1)
```

Each step in this chain is now explained in detail.

## Step-by-step audit

### Step 0: The conditional endpoint (already proved)

**File:** `TNLean/MPS/CanonicalForm/Assembly.lean` lines 67–201

**Structure:** `AfterBlockingFundamentalTheoremHypotheses` bundles:
- `relabel : CommonSectorRelabelingHypothesis d`
- `comparison :` (a forall accepting the produced common nonzero-sector families and requiring BNT-cover data for them)

**Theorem:** `fundamentalTheorem_afterBlocking_of_comparisonHypotheses` takes
`SameMPV₂ A B` and `AfterBlockingFundamentalTheoremHypotheses A B` and produces
the BNT sector-weight comparison conclusion.

This conditional theorem is already proved.  It composes:
1. The structural `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` (uses `h.relabel`) → produces common nonzero-block families
2. The BNT-cover consumer uses the converted phase-cover hypotheses to produce the sector-weight conclusion.

### Step 1: H1 — Fintype coordinate equality (#1075 / #990 / #1113)

**File:** `TNLean/MPS/CanonicalForm/Assembly/CyclicSectorDecomposition.lean` lines 1467–1495

**Theorem:** `flattenWordOfBlock_cast_eq {d m n p : ℕ} (hp_eq : p = m * n) ... i : flattenBlockedWord d m (wordOfBlock ... n (Fin.cast h_card.symm i)) = wordOfBlock d p i`

**Status:** `sorry` (single remaining `sorry` in the Gap §1 chain).

**Nature:** Pure Lean bookkeeping.  The equality is mathematically true
(it compares two equivalent Fintype enumerations of `Fin p → Fin d` under lexicographic ordering).
The proof requires chasing `Fintype.equivFin` instances for `Pi` types
through the currying isomorphism `Fin (m*n) → Fin d ≃ Fin n → Fin m → Fin d`.

**Chain:**
- `flattenWordOfBlock_cast_eq` → `CommonGroupedBlockCastHypothesis d` (via `groupedBlockCastAgrees_of_flattenWordOfBlock_cast_eq`)
- `CommonGroupedBlockCastHypothesis d` → `CommonSectorRelabelingHypothesis d` (via `CommonGroupedBlockCastHypothesis.toRelabelingHypothesis`)
- `CommonSectorRelabelingHypothesis d` → unconditional `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` (via `unconditional_commonPrimitiveIrreducibleBlocks`)

**Relevant audit:** `audits/2026-05-01_issue1075_fintype_coordinate_obstacle.md`

### Step 2: H2 — Common nonzero-block decomposition (#942)

**File:** `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean` lines 1213–1477

**Theorem:** `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts`
takes `SameMPV₂ A B` and `CommonSectorRelabelingHypothesis d` to produce one
common blocking length `p`, zero-tail decompositions on both sides, and
trace-preserving, primitive, irreducible block families with nonzero weights
at that common length.

**Theorem:** `unconditional_commonPrimitiveIrreducibleBlocks` shows that
`flattenWordOfBlock_cast_eq` eliminates the relabeling hypothesis.

**Status:** Both theorems are proved (the second is proved modulo H1's `sorry`).

**What is remaining for H2:** Exactly H1.

### Step 3: H3 — Common phase cover or span equality (#1068 / #652)

**File:** `TNLean/MPS/CanonicalForm/Assembly/ProportionalComparison.lean` lines 30–180, 550–750

Once H1 and H2 give us the common nonzero-block families, we still need:

**Structure:** `CommonPrimitivePhaseCoverHypotheses` requires:
- `zeroTail_eq : zeroTailA = zeroTailB` — equality of zero-tail dimensions
- `left_injective : ∀ x, IsInjective (blocksA x)` — left injectivity
- `right_injective : ∀ x, IsInjective (blocksB x)` — right injectivity
- `cover : Nonempty (MPVCommonPhaseCover blocksA blocksB)` — a common MPV phase cover

**BNT-cover form:** `CommonPrimitiveBNTCoverHypotheses` packages the normal
canonical-form data, gauge-phase separation, injectivity, zero-tail equality, and
proportional-decomposition data needed to construct a common MPV phase cover.

**Status:** These structures are defined, and the theorems that use them are proved.
The question is: can we discharge them from the structural reduction?

**What is remaining for H3 (genuine paper-level mathematics):**

1. **Zero-tail equality** (`zeroTailA = zeroTailB`):
   The structural theorem gives `SameMPV₂ A B`, which does not imply
   equality of the zero-tail dimensions.  This is a genuine paper-level
   condition: the two tensors must have the same number of zero-weight trivial
   blocks.  In the CPSV17 paper, the zero-block separation is done before
   comparison, and equality is argued (or the zero blocks are handled
   separately).  This is not yet proved from `SameMPV₂ A B` alone.

2. **Injectivity** (`IsInjective (blocksA x)`):
   The after-blocking blocks are known to be trace-preserving, primitive, and
   irreducible.  For MPS tensors, irreducibility (irreducible transfer map) does
   **not** automatically imply one-site injectivity without a Wielandt-type
   argument or an additional hypothesis.  In the CPSV17 paper, the BNT
   construction uses a Wielandt theorem to obtain this.  The current code
   accepts injectivity as a hypothesis; deriving it from the structural
   reduction needs a Wielandt / injectivity argument at the chosen blocking
   level.

3. **Common phase cover** (`MPVCommonPhaseCover`):
   This is the heart of the paper-level equal-case comparison: after both
   tensors are decomposed into their BNT sectors, one proves that the
   sectors can be paired.  The current code gives a common phase cover
   theorem via `exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq`,
   which takes equality of finite-length MPV spans for the nonzero-block families
   and produces the needed overlap-span data.  The span equality itself must
   be derived from `SameMPV₂ A B`.  This is a genuine paper-level gap.

### Step 4: H4 — One-sided BNT construction (resolved)

**Resolved by:** PR #945 (Wave 17G) via `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho`

This theorem takes TP/primitive/irreducible blocks with nonzero weights and
produces a sector decomposition BNT representative with:
- `HasBNTSectorData`
- `SectorBasisOverlapOrthoHypotheses` (positive dims, normalization, self-overlap=1, off-overlap=0)
- Transported injectivity

The one-sided BNT construction is now fully available.  The resolved issue is
tracked in `audits/2026-04-26_issue877_after_blocking_sector.md`.

## The current theorem landscape (after all Wave 27 merges)

Here is the complete list of theorems currently available for the equal-MPV
case, organized by dependency level:

### Level 0: Structural reduction (unconditional)
- `fundamentalTheorem_after_blocking_structural` — both sides have blocked TP-primitive decompositions
- `fundamentalTheorem_after_blocking_structural_with_blockedSameMPV₂` — same with blocked `SameMPV₂`
- `afterBlocking_tpPrimitiveBlockDecompositions_of_sameMPV₂` — same with zero-tail equations
- `fundamentalTheorem_after_blocking_perBlock_cyclic_live_with_zeroTail` — cyclic sectors per block
- `fundamentalTheorem_after_blocking_commonBlocked_cyclic_live_with_zeroTail` — common-blocked cyclic sectors
- `fundamentalTheorem_after_blocking_reindexed_commonSector_live_with_zeroTail` — relabeled common sectors
- `fundamentalTheorem_after_blocking_commonLength_commonSector` — common physical length

### Level 1: One-sided BNT construction (unconditional)
- `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` — collapsed phase-class representatives
- `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho` — plus overlap data
- `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData_and_basisSpan` — plus span preservation

### Level 2: Two-sided BNT matching (conditional on span/hypotheses)
- `exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq` — from nonzero-block span equality
- `exists_bnt_sectorDecomp_pair_with_overlapSpan_of_commonPhaseCover` — from common MPV phase cover
- `SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching` — basis matching witness

### Level 3: Conditional common nonzero-block decomposition
- `afterBlocking_commonPrimitiveIrreducibleBlocks_of_reindexedNonzeroParts` — needs H1
- `unconditional_commonPrimitiveIrreducibleBlocks` — needs H1 (`sorry`)

### Level 4: Conditional sector comparison
- `afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_spanHypotheses` — needs H1+H2+H3
- `afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_commonPhaseCover` — needs H1+H2+H3
- BNT-cover sector comparison — needs H1+H2+H3

### Level 5: Conditional full FT statement
- `fundamentalTheorem_afterBlocking_of_comparisonHypotheses` — clean conditional form, proved

### Level 6: Special-case unconditional
- `fundamentalTheorem_after_blocking_sector_of_common_blocks_injectiveSpan` — unconditional **if** exact common blocks, injectivity, and span equality are supplied as hypotheses
- `fundamentalTheorem_after_blocking_sector_of_common_blocks_blockSpan` — variant with block span hypothesis
- `fundamentalTheorem_after_blocking_sector_of_common_blocks_overlapSpan` — variant with overlap span hypothesis
- `fundamentalTheorem_after_blocking_sector_of_common_blocks_phaseCover` — variant with phase cover hypothesis
- `fundamentalTheorem_after_blocking_sector_of_common_blocks_commonPhaseCover` — variant with common phase cover (no separate injectivity, derived from cover)

## Blueprint status

**File:** `blueprint/src/chapter/ch11_assembly.tex`

- `\ref{thm:ft_equal}` (line 192): marked `\notready` — this is the equal-MPV FT
- `\ref{sec:assembly_equal_remark}` (line 1714): marked `\notready` — remark describing the remaining gap

The blueprint correctly documents that the comparison theorems cover the latter
part of the argument (sector-weight multisets, phase-and-gauge pairing), and that
the remaining open gap is the reconstruction of the common nonzero-block families
and the associated injectivity/span/zero-tail data.

## What the remaining gaps look like in detail

### Gap A: `flattenWordOfBlock_cast_eq` (pure Lean, Fintype compatibility)

This is a single `sorry` in `CyclicSectorDecomposition.lean`.  The reduction
chains in `StructuralTheorem.lean` (lines 1406–1477) and
`groupedBlockCastAgrees_of_flattenWordOfBlock_cast_eq` (lines 1497–1510)
show that this one lemma instantaneously resolves H1.

**Proposed proof strategy:**
The key observation is that both `wordOfBlock d p` and the grouped version
use `Fintype.equivFin` to convert a `Fin (d^p)` to `Fin p → Fin d`.  Under the
canonical currying isomorphism `Fin (m*n) → Fin d ≃ Fin n → Fin m → Fin d`,
the two `Fintype.equivFin` instances are compatible because they both use the
lexicographic enumeration defined by `Fintype` for `Pi` types.  The proof
would use `Fintype.equivFin` applied to both sides, plus a lemma that the
`Finset` enumerations match under currying.  A lemma of the form
`card_product_eq` or `Pi_fintype_equivFin_curry` in Mathlib would be the
natural dependency, or the proof can be done by `dec_trivial` since we are
working over `Fin` types with decidable equality (the physical dimension `d`
is a parameter, not a variable that changes within the proof).

### Gap B: Zero-tail equality (paper-level)

The structural theorem gives `SameMPV₂ A B`.  At length zero,
`mpv A (Fin.elim0) = D₁` and `mpv B (Fin.elim0) = D₂`, so `D₁ = D₂`.
But the zero-tail decomposition splits `D₁ = zeroTailA + sum_of_nonzero_dims`.
Equality of the total bond dimensions does **not** directly imply equality
of `zeroTailA` and `zeroTailB`, because the nonzero block dimensions could
differ even if their sums match.

This is not a Lean bookkeeping issue — it is a genuine paper-level condition:
the decomposition into zero-tail plus nonzero blocks is not unique a priori.
The CPSV17 paper handles this by working with the canonical form directly,
where the zero-block separation isolates the invariant subspace carrying zero
spectral weight.  The current code needs a lemma that, under the additional
conditions available after the after-blocking reduction (TP, primitive,
irreducible blocks), `zeroTailA = zeroTailB` follows from `SameMPV₂ A B`
at the same blocking level.

**Proposed intermediate lemma:**
```lean
theorem zeroTail_eq_of_sameMPV₂_after_blocking
    {d D₁ D₂ p zeroTailA zeroTailB rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hp : 0 < p)
    (hA : ∀ (N : ℕ) (σ : Fin N → Fin (blockPhysDim d p)),
      mpv (blockTensor A p) σ =
        mpv (zeroMPSTensor (blockPhysDim d p) zeroTailA) σ + ...
    (hB : ...similar...)
    (conditions: TP, primitive, irreducible, nonzero weights) :
    zeroTailA = zeroTailB
```

This lemma would require a paper-level argument: under these structural
conditions, the zero-tail dimension can be recovered as the dimension of
the invariant subspace where the blocked transfer map has zero spectral weight,
which is a property that `SameMPV₂` preserves.

### Gap C: Injectivity (paper-level)

The after-blocking blocks of an irreducible tensor are not automatically
injective at one site.  Wielandt's theorem (or a blocked variant) is needed.

The current code already has:
- `IsInjective (A : MPSTensor d D)` defined as injectivity of the map
  `X ↦ ∑_i A_i X (A_i)ᴴ` (the Kraus map)
- Spectral gap infrastructure in `TNLean/Spectral/`
- Wielandt-related theorems (see issue #1085)

The injectivity gap can be closed by:
1. Proving that irreducible TP tensors with primitive transfer maps are injective
   (Wielandt's theorem for MPS), or
2. Adding injectivity as an additional hypothesis at the blocking level
   and noting that the structural reduction can choose a blocking length
   where injectivity holds.

**Proposed intermediate lemma:**
```lean
theorem isInjective_of_tp_primitive_irreducible
    {d D : ℕ} {A : MPSTensor d D}
    [NeZero D]
    (hTP : ∑ i, A iᴴ * A i = 1)
    (hPrim : IsPrimitive (transferMap A))
    (hIrr : IsIrreducibleTensor A) :
    IsInjective A
```

This is a genuine Wielandt theorem for MPS.

### Gap D: Common phase cover / span equality (paper-level, the hardest)

Given two families of TP primitive irreducible nonzero-weight blocks at a
common blocking length, constructed from `SameMPV₂ A B`, we need to prove
that the nonzero-block tensors admit a common MPV phase cover.

This is essentially the paper's equal-case comparison at the block level.
It requires:
1. Pairing blocks by their MPV families (using the global `SameMPV₂`)
2. Proving that paired blocks are gauge-phase equivalent (using the BNT uniqueness theorem)
3. Assembling the common cover from the gauge-phase equivalence data

The current code provides:
- `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` — one-sided rep construction
- `exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq` — two-sided from span equality
- `MPVCommonPhaseCover` structure and its `span_eq` lemma

But the derivation of span equality from `SameMPV₂ A B` is not yet formalized.

**Proposed intermediate lemma:**
```lean
theorem nonzero_block_span_eq_of_sameMPV₂_after_blocking
    {d D₁ D₂ p rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂ A B)
    (hp : 0 < p)
    (blocksA : ...) (blocksB : ...)
    (hA : SameMPV₂ (blockTensor A p) (toTensorFromBlocks ... blocksA))
    (hB : SameMPV₂ (blockTensor B p) (toTensorFromBlocks ... blocksB))
    (structural conditions: TP, primitive, irreducible, nonzero weights) :
    ∀ N, span {mpvState (blocksA k) N | k} = span {mpvState (blocksB l) N | l}
```

## Summary table

| Hypothesis | Status | Type | Bound to issue(s) | Resolution approach |
|-----------|--------|------|-------------------|-------------------|
| `flattenWordOfBlock_cast_eq` | `sorry` | Lean bookkeeping | #1075, #990, #1113 | Fintype.equivFin compatibility via currying; `dec_trivial` or Mathlib lemma |
| `zeroTailA = zeroTailB` | unproved | paper math | #652 | Lemma from spectral weight analysis after blocking |
| `IsInjective (blocksA/B x)` | unproved | paper math | #652, #1085 | Wielandt theorem from TP+primitive+irreducible |
| `MPVCommonPhaseCover` | unproved | paper math | #652, #1068 | Equal-case BNT comparison from `SameMPV₂` |
| One-sided BNT construction | ✅ proved | paper math | #877, #945 | `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho` |
| Two-sided BNT matching from span | ✅ proved | paper math | #860, #935 | `SectorBasisOverlapSpanHypotheses.exists_sectorBasisMatching` |
| Common-period blocking arithmetic | ✅ proved | bookkeeping | — | `lcmPeriod`, `isPrimitive_transferMap_blockTensor_of_dvd` |
| Conditional full FT | ✅ proved | organizational | — | `fundamentalTheorem_afterBlocking_of_comparisonHypotheses` |

## References

- `TNLean/MPS/CanonicalForm/Assembly.lean` — conditional endpoint
- `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean` — structural chain + "What remains" (lines 2339–2379)
- `TNLean/MPS/CanonicalForm/Assembly/ProportionalComparison.lean` — common phase/span hypotheses
- `TNLean/MPS/CanonicalForm/Assembly/CyclicSectorDecomposition.lean` — `flattenWordOfBlock_cast_eq` (line 1482)
- `TNLean/MPS/CanonicalForm/BNTGrouping.lean` — norm-class collapse; docstring documents restricted scope
- `TNLean/MPS/CanonicalForm/EqualNormBridge.lean` — one-sided BNT construction with overlap data
- `blueprint/src/chapter/ch11_assembly.tex` — `\notready` at `thm:ft_equal` (line 192) and remark (line 1714)
- Previous audits: `audits/2026-04-21_issue652_gap1_blocker.md`, `audits/2026-04-23_issue652_gap1_followup.md`, `audits/2026-04-26_issue877_after_blocking_sector.md`, `audits/2026-05-01_issue1075_fintype_coordinate_obstacle.md`, `audits/2026-05-01_issue1068_common_phase_cover_from_common_sectors.md`
