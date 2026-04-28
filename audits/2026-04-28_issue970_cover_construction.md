# 2026-04-28 — Issue #970 cover construction predecessor

## Scope and issue-thread check

This branch starts from PR #987 (`issue970-common-phase-cover`, head `5efa33ac`) and keeps the #970/#944 goal focused on the non-Gemma CPSV/CPGSV path.  Before writing Lean statements I re-read the bodies and comments for issues #970, #944, #969, #942, and #652.

The current issue-thread conclusions are:

- #970 asks for the finite-length live-block span equality from equal MPVs after the common live-sector reduction.
- #944 now needs that span equality as the remaining input after one-sided BNT representative-span transport.
- #969 has produced common blocking and explicitly relabeled common sectors, but it has not yet produced the final weighted exact-live tensor equality with a common cross-side phase family.
- #652 remains open until the common-sector construction, injectivity/Wielandt refinement, and zero-tail bookkeeping all feed the sector comparison endpoint.

This branch does not claim the final exact-live construction from arbitrary `SameMPV₂`.  It records the strongest non-circular predecessor available from the existing BNT comparison layer: a BNT pre-matching, or the existing proportional-decomposition BNT comparison theorem, now produces `MPVCommonPhaseCover` data and therefore supplies the span field used by #944.

## Paper route checked

The Lean statements follow the BNT comparison step in the papers.

- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 271--280 define a basis of normal tensors and its minimality characterization.  In particular, line 279 says each canonical-form normal tensor is related to a basis tensor by a nonsingular matrix and a phase, and line 279 also states the minimality condition.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 283--302 write a canonical-form tensor in terms of BNT blocks and give the MPV decomposition `|V^{N}(A)\rangle = \sum_j (\sum_q \mu_{j,q}^N)|V^{(N)}(A_j)\rangle` on lines 300--301.
- `Papers/1606.00608/MPDO-22-12-17-2.tex` lines 349--352 state the BNT matching conclusion of the Fundamental Theorem: equal/proportional MPV families have BNT blocks matched by a permutation, phases, and nonsingular matrices.
- `Papers/2011.12127/TN-Review-main.tex` lines 1846--1859 give the same BNT definition and minimality characterization; lines 1864--1885 give the BNT block decomposition and MPV expansion; lines 1891--1894 state the matching conclusion for proportional MPVs.

## Lean progress in this branch

### `TNLean/MPS/CanonicalForm/EqualNormBridge.lean`

New declarations:

- `MPSTensor.SectorBasisPreMatching.commonPhaseCover`:
  a sector-basis pre-matching between sector decompositions `P` and `Q` gives a concrete `MPVCommonPhaseCover P.basis Q.basis`.  The common family is the left basis; the left class map is the identity; the right class map is the inverse permutation; the pre-matching gauge phases give the MPV-phase equivalences.
- `MPSTensor.SectorBasisPreMatching.span_eq`:
  applying `MPVCommonPhaseCover.span_eq` to the preceding construction gives equality of the finite-length MPV spans of the two sector bases.
- `MPSTensor.SectorBasisPreMatching.to_overlapSpan`:
  combines the pre-matching span equality with the one-family overlap-orthogonality and injectivity fields to produce `SectorBasisOverlapSpanHypotheses P Q`.
- `MPSTensor.nonempty_mpvCommonPhaseCover_of_proportionalDecompositionConclusion`:
  a BNT proportional-decomposition comparison conclusion already contains enough data (permutation, bond-dimension equalities, gauge phases) to produce a common MPV phase cover.
- `MPSTensor.nonempty_mpvCommonPhaseCover_of_separated_normalCFBNT_data`:
  the existing span-equality-free irreducible trace-preserving BNT comparison theorem supplies the preceding conclusion, hence produces common-cover existence directly from separated normal BNT data and proportional-decomposition hypotheses.

The key point is non-circularity: these declarations do not use `SectorBasisOverlapSpanHypotheses`, the live-block span equality, or `mpv_span_eq_of_common_phase_cover` as an input to obtain the BNT pre-matching.  The direction is the paper direction: BNT matching data gives the common cover; the common cover then gives span equality.

### `blueprint/src/chapter/ch11_assembly.tex`

New entries at lines 814--899 document:

- common phase cover from a sector basis pre-matching (`def:sector_basis_pre_matching_common_phase_cover`);
- sector-basis span equality from a pre-matching (`lem:sector_basis_pre_matching_span_eq`);
- primitive overlap-span hypotheses from a pre-matching (`thm:sector_basis_pre_matching_to_overlap_span`);
- common phase cover from a BNT proportional-decomposition conclusion (`thm:common_phase_cover_of_proportional_decomposition`);
- common phase cover from separated normal BNT data (`thm:common_phase_cover_of_separated_normal_bnt`).

## Remaining paper input

The full #970/#944 theorem is still blocked upstream of these declarations.  The remaining mathematical input is:

1. convert the common-length cyclic-sector output of #969 into final exact live block families, including the weighted direct sum and zero-tail equations at the final blocking length;
2. add the common injectivity/Wielandt blocking stage required by the overlap-rigidity endpoint;
3. obtain the proportional-decomposition data for the final BNT basis families from the exact live equality without reintroducing a finite-length span assumption;
4. apply `nonempty_mpvCommonPhaseCover_of_separated_normalCFBNT_data` (or the pre-matching construction directly) to produce the `MPVCommonPhaseCover` consumed by `fundamentalTheorem_after_blocking_1606_sector_of_common_blocks_commonPhaseCover`.

Thus the new Lean code moves the #970 bottleneck from an assumed span equality to the paper-level BNT matching/proportional-decomposition data, while keeping the missing #969 exact-live and Wielandt inputs explicit.
