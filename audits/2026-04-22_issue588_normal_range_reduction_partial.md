# Issue #588 audit update — open-chain route and Wave 14 formal step

Date: 2026-04-22
Branch: `feat/588-chainGroundSpace-normal`
Target theorem: `MPSTensor.chainGroundSpace_eq_mpvSubmodule_normal`

## 2026-04-25 Wave 14 update

Current branch `wave14-A-588-range-reduction` lands the reusable open-chain step
that this audit had identified as missing:

- `MPSTensor.tailRestrictₗ_contiguousRestrictₗ` in
  `TNLean/MPS/ParentHamiltonian/RestrictTransport.lean` identifies a suffix
  restriction of a contiguous `(K + L)` window with the contiguous `L`-window
  beginning at `s + K`, after inserting the fixed prefix into the outside
  configuration.
- `MPSTensor.contiguous_mem_groundSpace_of_isNBlkInjective` in
  `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` iterates
  `groundSpace_extend_right_of_isNBlkInjective`: contiguous `(L₀ + 1)`-window
  ground-space constraints now imply full open-chain membership
  `ψ ∈ groundSpace A N`.

The public theorem
`MPSTensor.chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction` is still
not closed by this update. The remaining work is now the periodic reintegration:
turn cyclic `L`-window membership into the reduced contiguous `(L₀ + 1)`-window
hypotheses, then use the existing wrapped-window compatibility results in
`WrappingWindow.lean` to force scalar boundary matrices.

## Historical 2026-04-22 outcome

The original `feat/588-chainGroundSpace-normal` pass identified the correct
open-chain route but did not land a Lean theorem. Its intended argument was:

1. shrink cyclic windows from length $L$ down to $L_0 + 1$ by peeling the last
   site;
2. identify non-wrapping cyclic windows with contiguous windows;
3. iterate `MPSTensor.groundSpace_extend_right_of_isNBlkInjective` to regrow
   from contiguous `(L_0 + 1)`-window conditions to full open-chain membership.

That 2026-04-22 branch reverted its non-compiling Lean partial because dependent
arithmetic reindexing around `contiguousRestrictₗ` produced type mismatches.
Wave 14 addresses exactly that reverted transport layer by adding
`tailRestrictₗ_contiguousRestrictₗ` and then landing the chain-level theorem
`contiguous_mem_groundSpace_of_isNBlkInjective`.

## 2026-04-25 Wave 15D update

Current branch `wave15-D-588-normal-range` lands the cyclic-to-open-chain part of
periodic reintegration:

- `MPSTensor.eq_cyclic_site_of_offset_eq` and
  `MPSTensor.cyclicRestrictₗ_restrictLast` in
  `TNLean/MPS/ParentHamiltonian/CyclicWindow.lean` record the modular-index
  calculation and the one-site peeling identity for cyclic windows.
- `MPSTensor.chainGroundSpace_le_chainGroundSpace_succ` and
  `MPSTensor.chainGroundSpace_le_chainGroundSpace_of_le` in
  `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` show that periodic-chain
  constraints are antitone in the interaction range.
- `MPSTensor.chainGroundSpace_le_groundSpace_of_isNBlkInjective` combines that
  cyclic monotonicity with the Wave 14 open-chain theorem, proving that cyclic
  range-$L$ constraints with $L_0 < L \le N$ imply the full open-chain membership
  `ψ ∈ groundSpace A N` whenever `A` is `L₀`-block-injective and `0 < L₀`.

This leaves the final scalar-boundary step untouched: after writing
`ψ = groundSpaceMap A N X`, the proof still has to turn the reduced wrapped
window constraints into a long-word commutation family for `X`, and then apply
`MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes`.

## Remaining blocker after Wave 15D

The final target

```lean
chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction
```

still needs the scalar-boundary closure step. The full cyclic
`chainGroundSpace A L N` hypothesis is now connected to the open-chain
representation `ψ ∈ groundSpace A N`, so one can write
`ψ = groundSpaceMap A N X`. The remaining proof must turn the reduced wrapped
window constraints into a long-word commutation family for `X`, then use the
existing block-stripping theorem to force generator commutation and hence
scalarity.

The expected next formal piece is a periodic closure theorem using the wrapped
window compatibility and mirror compatibility lemmas in `WrappingWindow.lean`,
together with
`MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes`,
to obtain the same generator-commutation conclusion as in the injective proof.

## Tracking / linkage

- Parent issue: #588
- Related wrapped-window work: #730 / #761
- Related transport work: #869 / #883
- Paper reference: CPGSV21, §IV.C

## Files changed by the Wave 14 and Wave 15D branches

- `TNLean/MPS/ParentHamiltonian/RestrictTransport.lean` (Wave 14)
- `TNLean/MPS/ParentHamiltonian/CyclicWindow.lean` (Wave 15D)
- `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`
- `blueprint/src/chapter/ch14_parent_hamiltonian.tex` (Wave 15D)
- `audits/2026-04-22_issue588_normal_range_reduction_partial.md`

## Status after Wave 15D

Wave 14 lands the contiguous open-chain theorem, and Wave 15D lands the
cyclic-window reduction from periodic constraints to that open-chain theorem. The
remaining proof obligation in
`chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction` is now concentrated
in the wrapped-boundary scalar-closure step.
