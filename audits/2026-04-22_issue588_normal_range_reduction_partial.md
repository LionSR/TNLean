# Issue #588 partial progress audit — open-chain normal-range reduction landed, periodic closure still blocked

Date: 2026-04-22
Branch: `feat/588-chainGroundSpace-normal`
Target theorem: `MPSTensor.chainGroundSpace_eq_mpvSubmodule_normal`

## What this pass completed

The **open-chain** half of the normal-range reduction is now formalized in
`TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`.

New proved theorem:

```lean
theorem MPSTensor.chainGroundSpace_le_groundSpace_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ L N : ℕ}
    (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hL : L₀ < L) (hLN : L ≤ N) :
    chainGroundSpace A L N ≤ groundSpace A N
```

Lean ingredients added locally in `UniqueGroundState.lean`:
- cyclic-window shrinking by peeling the last site;
- reduction from window length `L` to `L₀ + 1`;
- a contiguous suffix-restriction identity;
- induction with `groundSpace_extend_right_of_isNBlkInjective` to regrow from
  `(L₀ + 1)`-windows to the full open chain.

So the remaining `sorry` is now *purely periodic*.

## Exact remaining blocker

To finish

```lean
chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction
```

one still needs the block-injective wrapped-window theorem from follow-up issue
#730.

The precise missing ingredient is **not** the open-chain grow-back step anymore.
It is a wrapped-window comparison theorem which, for
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
one-site injectivity by `groundSpaceMap_injective_of_isNBlkInjective`, but not the
second from the same witness. Once that missing comparison theorem exists,
chunking plus

```lean
MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes
```

should complete the periodic step.

## Tracking / linkage

- Downstream blocker issue: #730
- Parent issue: #588
- Paper reference: CPGSV21, §IV.C

## Files changed in this partial branch

- `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`
- `blueprint/src/chapter/ch14_parent_hamiltonian.tex`

## Honest status

This pass does **not** discharge the final `sorry` in
`chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`.
It does isolate the remainder to the periodic wrapped-window comparison theorem,
with the open-chain side now formalized and reusable.
