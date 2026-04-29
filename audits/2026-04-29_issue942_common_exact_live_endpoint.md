# 2026-04-29 — Common exact live-sector endpoint predecessor (#942/#969/#970/#944/#652)

## Scope

This audit records a non-Gemma predecessor toward the common exact live-sector
endpoint needed before the common phase-cover and BNT span theorems can close
#970/#944 and then the #652 Gap §1 umbrella.

The new Lean declarations are:

- `MPSTensor.exists_commonBlockedCyclicSectorFamily_of_commonMultiple`
- `MPSTensor.CommonBlockedCyclicSectorFamily.sameMPV₂_weightedCanonicalBlock_commonFlat_of_oneShot`
- `MPSTensor.fundamentalTheorem_after_blocking_1606_commonLength_commonSector_endpoint`
- `MPSTensor.zeroTail_commonFlat_of_oneShot_labelCompat`

They deliberately do not assert the full arbitrary `SameMPV₂` fundamental theorem.
The remaining paper inputs are stated below.

## Source anchors

- `Papers/1606.00608/MPDO-22-12-17-2.tex:214--231` describes replacing an
  arbitrary tensor by a block diagonal live tensor and then blocking by the
  periods.  In particular line 217 gives
  `A^i = ... = \oplus_{k=1}^r \mu_k A^i_k`, and lines 227--231 state that
  blocking by the least common multiple of the periods removes the peripheral
  periodicity.
- `Papers/2011.12127/TN-Review-main.tex:1798--1808` gives the same block
  diagonal live form and transfer-operator normalization.  Lines 1815--1820
  explain that an irreducible block may have peripheral period `p` and that
  blocking `p` sites yields a primitive transfer operator.
- `Papers/2011.12127/TN-Review-main.tex:1841--1859` introduces bases of normal
  tensors and their phase/gauge equivalence classes.  Lines 1864--1884 rewrite
  a canonical form in a BNT basis with coefficients
  `\sum_q \mu_{j,q}^N`; this is the downstream comparison consumed by the
  phase-cover and BNT matching theorems.

## What this branch proves

1. **One-sided common sectors at a prescribed length.**
   `exists_commonBlockedCyclicSectorFamily_of_commonMultiple` strengthens the
   earlier least-common-multiple constructor.  If a positive integer `p` is a
   common multiple of every period-removal length in a live family, then the
   one-sided `CommonBlockedCyclicSectorFamily` may be constructed with exactly
   that `p`.  The proof writes `p = m_k e_k` for each live block, blocks each
   cyclic sector by `e_k`, and transports trace preservation, primitivity,
   tensor irreducibility, positive dimension, and MPV equivalence.

2. **Two-sided common-length endpoint from structural reduction.**
   `fundamentalTheorem_after_blocking_1606_commonLength_commonSector_endpoint`
   starts from `SameMPV₂ A B`.  It takes the per-block cyclic live reduction,
   lets `p_A` and `p_B` be the one-sided least common multiples, and chooses the
   single two-sided length `p = p_A p_B`.  At this common length it records:

   - exact zero-tail equations for `blockTensor A p` and `blockTensor B p`
     against the canonically blocked live tensors;
   - positive-length equality of those canonically blocked live tensors;
   - the exact length-zero zero-tail bookkeeping identity at the common length;
   - relabeled one-shot cyclic-sector families on both sides at that same `p`;
   - nonzero transported sector weights and TP / primitive / tensor-irreducible /
     positive-dimension properties for those derived sectors.

3. **One-sided theorem for the remaining physical-label step.**
   `sameMPV₂_weightedCanonicalBlock_commonFlat_of_oneShot` and
   `zeroTail_commonFlat_of_oneShot_labelCompat` state the exact conversion needed
   after the physical-label compatibility is proved: if the canonical blocked
   live tensor agrees with the explicitly relabeled one-shot live tensor, then
   the zero-tail equation can be rewritten directly with the weighted derived
   common-sector family.

## Remaining paper inputs

The exact blockers are now narrower than before:

1. **Physical-label compatibility for the flat live tensor.**
   The current common sectors are expressed through `oneShotReindexedBlock`, which
   uses the iterated-blocking relabeling `iteratedBlockIndex` for each original
   live block.  The canonical zero-tail equations use the ambient blocked
   alphabet of `blockTensor (blocks k) p`.  One still needs the global statement
   identifying the weighted canonical blocked live tensor with the weighted
   relabeled one-shot live tensor, or an equivalent downstream theorem formulated
   directly for the relabeled families.

2. **Injectivity/Wielandt endpoint.**
   The new endpoint proves trace preservation, primitive transfer maps, tensor
   irreducibility, and positive bond dimension.  The #944/#652 overlap-rigidity
   route also needs one-site injectivity of the final live blocks, or a theorem
   replacing the one-site injectivity input by a later blocked variant.  This is
   the later Wielandt stage mentioned in #969 and is not conflated with the
   period-removal length.

3. **Common phase-cover or BNT comparison data.**
   PRs #987/#988 provide `MPVCommonPhaseCover`, `SectorBasisPreMatching`, and the
   BNT cover construction once proportional-decomposition matching data is
   available.  This branch supplies the common-length sector endpoint needed
   before those theorems can be applied, but it does not construct the
   cross-side class maps or phase equivalences from arbitrary `SameMPV₂`.

4. **Final exact-live span input.**
   After items 1--3, `MPVCommonPhaseCover.span_eq` or the BNT pre-matching
   theorem should provide the finite-length live-sector span equality needed by
   `fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_commonPhaseCover`.
