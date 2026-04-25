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

## Remaining blocker after Wave 14

The final target

```lean
chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction
```

still needs the periodic reintegration step. The open-chain representation
`ψ ∈ groundSpace A N` is now available from contiguous `(L₀ + 1)`-window
constraints, but the periodic proof must still connect the full cyclic
`chainGroundSpace A L N` hypothesis to that reduced open-chain hypothesis and
then force the boundary matrix in `ψ = groundSpaceMap A N X` to be scalar.

The expected next formal pieces are:

1. a cyclic-window range monotonicity / peeling theorem reducing cyclic
   `L`-window constraints to cyclic `(L₀ + 1)`-window constraints;
2. a periodic closure theorem using the existing wrapped-window compatibility
   and mirror compatibility lemmas in `WrappingWindow.lean`, together with
   `MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes`,
   to obtain the same generator-commutation conclusion as in the injective proof.

## Tracking / linkage

- Parent issue: #588
- Related wrapped-window work: #730 / #761
- Related transport work: #869 / #883
- Paper reference: CPGSV21, §IV.C

## Files changed by the Wave 14 branch

- `TNLean/MPS/ParentHamiltonian/RestrictTransport.lean`
- `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`
- `audits/2026-04-22_issue588_normal_range_reduction_partial.md`

## Status after Wave 14

Wave 14 lands the open-chain theorem but does **not** discharge the remaining
periodic `sorry` in
`chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`. The remaining work
is the cyclic-window reduction and wrapped-boundary scalar-closure assembly.
