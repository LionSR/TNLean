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

## Outcome of this pass

I explored the **open-chain** half of the normal-range reduction and found a
credible proof route through the recently landed suffix-window / regrowth API.
In particular, the intended argument is:

1. shrink cyclic windows from length $L$ down to $L_0 + 1$ by peeling the last
   site;
2. identify non-wrapping cyclic windows with contiguous windows;
3. iterate `MPSTensor.groundSpace_extend_right_of_isNBlkInjective` to regrow
   from contiguous `(L_0 + 1)`-window conditions to full open-chain membership.

I attempted to formalize this directly in
`TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`, but the resulting Lean
partial did **not** survive honest `lake build` / CI: the dependent arithmetic
reindexing around `contiguousRestrictₗ` produced nontrivial type mismatches and
proof-argument transport failures. To keep the branch compiling, I reverted that
non-compiling Lean partial instead of forcing it through with brittle casts or
new `sorry`s.

So this pass leaves **no new Lean theorem landed** in `UniqueGroundState.lean`.
The branch now contains only this updated audit note together with a tiny import
cleanup in `TNLean.lean` (dropping `TNLean.MPS.ParentHamiltonian.OpenChainRangeReduction`
from the top-level imports). The concrete duplicate-declaration failure was
`MPSTensor.groundSpace_extend_right_of_isNBlkInjective`, defined in both
`TNLean.MPS.ParentHamiltonian.ExtendRight` and
`TNLean.MPS.ParentHamiltonian.OpenChainRangeReduction`.

## Exact remaining blocker

To finish

```lean
chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction
```

one still needs the block-injective wrapped-window theorem from follow-up issue
#730.

The precise missing ingredient is a wrapped-window comparison theorem which, for
`ψ = groundSpaceMap A N X` satisfying all cyclic `(L₀ + 1)`-window constraints,
produces the missing second one-sided compatibility (or an equivalent common
middle matrix) needed to force boundary commutation.

A representative missing statement is:

```lean
-- schematic shape
∀ τ, ∃ Yτ,
  (∀ j, Cτ τ * A j * X = Yτ * A j) ∧
  (∀ j, X * A j * Cτ τ = A j * Yτ)
```

with `Cτ τ` the complement word determined by `τ`.

Current `WrappingWindow` methods give the **first** compatibility after replacing
one-site injectivity by `groundSpaceMap_injective_of_isNBlkInjective`, but not
the second from the same witness. Once that missing comparison theorem exists,
chunking plus

```lean
MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes
```

should complete the periodic step.

## Tracking / linkage

- Downstream blocker issue: #730
- Parent issue: #588
- Paper reference: CPGSV21, §IV.C

## Files changed on the final compilable branch state

- `audits/2026-04-22_issue588_normal_range_reduction_partial.md`
- `TNLean.lean` (import cleanup)

## Honest status

This pass does **not** discharge the final `sorry` in
`chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`.
It sharpens the roadmap for the open-chain side, but the actual Lean
formalization was reverted after CI showed it was not yet robust. The true
remaining blocker is still the periodic wrapped-window comparison theorem from
#730.
