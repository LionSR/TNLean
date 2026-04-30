# Issue #877 Wave 17 Slot F — common nonzero-block / zero-tail audit

Date: 2026-04-26
Branch/worktree: `wave17-F-877-common-live-blocks`

## Checked Lean progress

This branch advances the nonzero-block side of #877/#652 without discharging the
separate overlap/span hypotheses owned by Slot G.

1. `MPSTensor.exists_primitive_irreducible_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`
   in `TNLean/MPS/CanonicalForm/Assembly/CyclicSectorDecomposition.lean` exposes a
   public one-block cyclic-sector API.  From a trace-preserving irreducible tensor
   `A`, it returns a period `m > 0` and a unit-weight decomposition of
   `blockTensor A m` into sector blocks which are all trace-preserving, primitive,
   tensor-irreducible, and nonzero-dimensional.  The proof reuses the existing
   cyclic sector construction and the unconditional
   `primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking` theorem.

2. `MPSTensor.liveBlock_positive_sameMPV₂_and_zeroTail_bookkeeping_of_sameMPV₂`
   in `TNLean/MPS/CanonicalForm/Assembly/StructuralTheorem.lean` records the exact
   zero-tail identity: if two equal-MPV tensors are each written as
   `zeroMPSTensor zeroTail + nonzeroPart`, then the nonzero parts agree for every
   positive length, and the length-zero equation is exactly
   `(zeroTailA : ℂ) + nonzeroA₀ = (zeroTailB : ℂ) + nonzeroB₀`.

3. `MPSTensor.liveBlock_sameMPV₂_of_sameMPV₂_of_zeroTail_eq` packages the previous
   result with the additional datum `zeroTailA = zeroTailB`, yielding full
   `SameMPV₂` of the two nonzero-block tensors.  The equality of zero tails is deliberately
   not asserted automatically here.

4. `MPSTensor.fundamentalTheorem_after_blocking_structural_with_zeroTail`
   strengthens the existing structural wrapper by retaining the zero-tail MPV
   equations returned by `exists_tp_primitive_blockDecomp_after_blocking`, together
   with the blocked `SameMPV₂` relations from the original equality.

Blueprint entries were added for these checked declarations at:

- `blueprint/src/chapter/ch08_canonical.tex:1405`, label
  `thm:cyclic_sector_decomp_irr_tp_prim_irr`, source quote:
  “there is a period $m \ge 1$ and a unit-weight decomposition of $A^{[m]}$ into
  sector blocks … every $C_k$ is left-canonical, has primitive transfer map, is
  tensor-irreducible, and has nonzero bond dimension.”
- `blueprint/src/chapter/ch08_canonical.tex:2541`, label
  `thm:live_block_zero_tail_bookkeeping`, source quote:
  “the two nonzero-block tensors agree on every positive system size, and at size
  $0$ the equality is exactly the equality of the two zero-tail contributions
  plus the two nonzero-block bond-dimension traces.”
- `blueprint/src/chapter/ch08_canonical.tex:2560`, label
  `thm:live_block_same_mpv_zero_tail_eq`, source quote:
  “if the two zero-tail dimensions are equal, then the two nonzero-block tensors are
  fully SameMPV$_2$-equivalent, including the length-zero case.”
- `blueprint/src/chapter/ch08_canonical.tex:2578`, label
  `thm:ft_after_blocking_structural_zero_tail`, source quote:
  “each tensor admits a blocked decomposition into a zero-tail tensor plus
  nonzero left-canonical blocks with primitive transfer maps and positive
  bond dimensions.”

## Paper anchors

- CPSV17, arXiv:1606.00608, §2.3 and Appendix A: split off vanishing blocks,
  reduce irreducible trace-preserving tensors by cyclic blocking, and compare the
  surviving nonzero sectors.
- CPGSV21, arXiv:2011.12127, §IV / Appendix A: the cyclic sector blocks after
  the period blocking are the primitive irreducible components used in the BNT
  sector construction.

## Remaining blocker for #877/#652

The new cyclic-sector theorem exposes the one-block primitive irreducible output,
but the full common nonzero-block theorem still needs the multi-block flattening
step: starting from the zero-tail TP-gauge reduction, choose a common physical
blocking level, transport all per-block cyclic sector decompositions to that
level, flatten the nested `(nonzero block, cyclic sector)` index into one `Fin r`
family, and prove the exact MPV equation for the resulting nonzero-block tensor.  This is
a genuine dependent-index / blocking-associativity construction, not an overlap
or span hypothesis.

The zero-tail lemmas isolate the `N = 0` obstruction.  Positive lengths compare
the nonzero-block tensors immediately after the zero-tail terms vanish.  Full `SameMPV₂`
of nonzero-block tensors requires either equality of the zero-tail dimensions or a
positive-length variant of the downstream sector comparison.  This branch records
that boundary explicitly rather than hiding it inside the PR #935 overlap-span
assumption.
