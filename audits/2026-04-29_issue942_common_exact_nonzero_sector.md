# 2026-04-29 — Common exact nonzero-sector construction predecessor (#942/#969/#970/#944/#652)

## Scope

This audit records a non-Gemma predecessor toward the common exact nonzero-sector
statement needed before the common phase-cover and BNT span theorems can close
#970/#944 and then the #652 Gap §1 umbrella.

The new Lean declarations construct a prescribed common reblocking of cyclic sectors,
compare the canonical blocked nonzero part with the relabeled cyclic-sector tensor,
state the two-sided common-length theorem, and rewrite the zero-tail equation with the
derived common-sector family.

They deliberately do not assert the full arbitrary `SameMPV₂` fundamental theorem.
The remaining paper hypotheses are stated below.

## Source references

- `Papers/1606.00608/MPDO-22-12-17-2.tex:214--231` describes replacing an
  arbitrary tensor by a block diagonal nonzero part and then blocking by the
  periods. In particular line 217 gives
  `A^i = ... = \oplus_{k=1}^r \mu_k A^i_k`, and lines 227--231 state that
  blocking by the least common multiple of the periods removes the peripheral
  periodicity.
- `Papers/2011.12127/TN-Review-main.tex:1798--1808` gives the same block
  diagonal nonzero block form and transfer-operator normalization. Lines 1815--1820
  explain that an irreducible block may have peripheral period `p` and that
  blocking `p` sites yields a primitive transfer operator.
- `Papers/2011.12127/TN-Review-main.tex:1841--1859` introduces bases of normal
  tensors and their phase/gauge equivalence classes. Lines 1864--1884 rewrite
  a canonical form in a BNT basis with coefficients
  `\sum_q \mu_{j,q}^N`; this is the later comparison consumed by the
  phase-cover and BNT matching theorems.

## What this branch proves

1. **One-sided common sectors at a prescribed length.**
   `exists_commonBlockedCyclicSectorFamily_of_commonMultiple` strengthens the
   earlier least-common-multiple constructor. If a positive integer `p` is a
   common multiple of every period-removal length in a nonzero-weight family, then the
   one-sided `CommonBlockedCyclicSectorFamily` may be constructed with exactly
   that `p`. The proof writes `p = m_k e_k` for each nonzero-weight block, blocks each
   cyclic sector by `e_k`, and transports trace preservation, primitivity,
   tensor irreducibility, positive dimension, and MPV equivalence.

2. **Two-sided common-length theorem from structural reduction.**
   The two-sided common-length theorem starts from `SameMPV₂ A B`. It takes the
   per-block cyclic-sector reduction, lets `p_A` and `p_B` be the one-sided least
   common multiples, and chooses the single two-sided length `p = lcm(p_A,p_B)`.
   At this common length it records:

   - exact zero-tail equations for `blockTensor A p` and `blockTensor B p`
     against the canonically blocked nonzero parts;
   - positive-length equality of those canonically blocked nonzero parts;
  - the exact length-zero zero-tail identity at the common length;
   - relabeled cyclic-sector families on both sides at that same `p`;
   - nonzero transported sector weights and TP / primitive / tensor-irreducible /
     positive-dimension properties for those derived sectors.

3. **One-sided theorem for the remaining blocked-word reindexing step.**
   The one-sided conversion theorems state the exact step needed after agreement under
   reindexing of blocked physical words is proved: if the canonical blocked nonzero
   part agrees with the explicitly relabeled nonzero part, then the zero-tail equation
   can be rewritten directly with the weighted derived common-sector family.

## Remaining paper hypotheses

The remaining mathematical obligations are now narrower than before:

1. **Agreement after reindexing blocked physical words for the flat nonzero part.**
   The current common sectors are expressed through the explicitly reindexed block, which
   uses the iterated-blocking relabeling `iteratedBlockIndex` for each original
   nonzero-weight block. The canonical zero-tail equations use the ambient blocked
   alphabet of `blockTensor (blocks k) p`. One still needs the global statement
   identifying the weighted canonical blocked nonzero part with the weighted
   relabeled nonzero part, or an equivalent later theorem formulated directly for the
   relabeled families.

2. **Injectivity/Wielandt stage.**
   The new theorem proves trace preservation, primitive transfer maps, tensor
   irreducibility, and positive bond dimension. The #944/#652 overlap-rigidity
   route also needs one-site injectivity of the final nonzero-weight blocks, or a theorem
   replacing the one-site injectivity hypothesis by a later blocked variant. This is
   the later Wielandt stage mentioned in #969 and is not conflated with the
   period-removal length.

3. **Common phase-cover or BNT comparison data.**
   PRs #987/#988 provide `MPVCommonPhaseCover`, `SectorBasisPreMatching`, and the
   BNT cover construction once proportional-decomposition matching data is
   available. This branch supplies the common-length sector data needed before those
   theorems can be applied, but it does not construct the cross-side class maps or
   phase equivalences from arbitrary `SameMPV₂`.

4. **Final exact nonzero-part span hypothesis.**
   After items 1--3, `MPVCommonPhaseCover.span_eq` or the BNT pre-matching theorem
   should provide the finite-length nonzero-block span equality needed by the sector
   comparison theorem using common phase-cover data.
