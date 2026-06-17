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

## 2026-04-26 Wave 16A update

Current branch `wave16-A-588-wrapped-boundary-scalar` does **not** close the final
MPV-line containment theorem; the existing proof placeholder in
`MPSTensor.chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction` remains.
It lands the next reusable Lean statement on the closure-property path:

- `MPSTensor.chainGroundSpace_wrapped_boundary_compatibilities_of_isNBlkInjective`
  in `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`.

The theorem starts from exactly the post-open-chain situation: an $N$-site vector
`ψ ∈ chainGroundSpace A L N` with `ψ = groundSpaceMap A N X`, an
`L₀`-block-injective tensor with `L₀ > 0`, and `L₀ < L ≤ N`. It first reduces the
cyclic constraints to range `L₀ + 1`, then applies the existing wrapped-window
compatibility theorem at the last site and the mirror compatibility theorem at
the opposite wrapped position. The output is the two one-sided boundary identities
for some boundary families `Ywrap` and `Ymirror`:

```text
C⁺_τ · A_j · X = Ywrap_τ · A_j,
X · A_j · C⁻_τ = A_j · Ymirror_τ,
```

where `C⁺_τ` and `C⁻_τ` are the complementary word products of length
`N - (L₀ + 1)` exposed by the two reduced wrapped windows.

This is paper-faithful to the CPGSV21 closure-property sentence at
`Papers/2011.12127/TN-Review-main.tex:2078--2079`, especially the source text
"Once we have reached $k=L_0$, we can resort to the above Theorem, or
alternatively apply a similar argument when closing the boundaries". It also
feeds the theorem statement at lines `2087--2090`, labelled
`thm:4:unique-gs-L0_plus_1`.

The remaining blocker is now sharper: prove the common-middle comparison turning
the two one-sided identities above into a long-word commutation family
`X A^ω = A^ω X` for some positive word length (then amplify to length at least
`L₀` if necessary) and apply
`MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes`.

## 2026-04-26 Wave 17A update

This branch still does **not** close
`MPSTensor.chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`; the
pre-existing proof placeholder remains.  It lands two small Lean pieces that
remove algebraic endgame noise from the remaining closure-property blocker:

- `MPSTensor.eq_zero_of_mul_evalWord_eq_zero_of_wordSpan_eq_top` and
  `MPSTensor.eq_zero_of_mul_evalWord_eq_zero_of_isNBlkInjective_of_le_mul` in
  `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean`.  These formalize the
  padding observation from the 2026-04-21 audit: if an operator annihilates all
  complement words of length `k`, then padding to any full exact word span
  length `n ≥ k` forces the operator to be zero; for an `L₀`-block-injective
  tensor, any positive multiple of `L₀` is such a full span.
- `MPSTensor.groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_long_word_commutes`
  in `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`.  Once the wrapped
  boundary identities are upgraded to a long-word commutation family
  `X A^ω = A^ω X` for some `|ω| = m ≥ L₀`, this theorem applies the existing
  block-stripping centrality theorem and the matrix-center calculation to put
  `Γ_N(X)` directly in `mpvSubmodule A N`.

Paper anchor retained: CPGSV21 §IV.C,
`Papers/2011.12127/TN-Review-main.tex:2078--2079`, especially
"Once we have reached $k=L_0$, we can resort to the above Theorem, or
alternatively apply a similar argument when closing the boundaries", and theorem
`thm:4:unique-gs-L0_plus_1` at lines 2087--2090.

Remaining blocker after Wave 17A: the genuine common-middle / closure-property
comparison.  Starting from
`MPSTensor.chainGroundSpace_wrapped_boundary_compatibilities_of_isNBlkInjective`,
one still has to turn the two one-sided identities
`C^+_τ A_j X = Y^+_τ A_j` and `X A_j C^-_τ = A_j Y^-_τ` into long-word
commutation for the same boundary matrix `X`.  The new MPV-line endgame shows
that no further scalar-center work remains once that commutation family is
available.

## 2026-04-27 Wave 18E update

Current branch `wave18-E-588-common-middle` still does **not** close
`MPSTensor.chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`; the
pre-existing proof placeholder remains.  It lands the exact algebraic
common-middle endgame that was missing after Wave 17A, without assuming
commutation directly:

- `MPSTensor.commutes_words_of_two_sided_middle_compatibility` in
  `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean`: if the two one-sided
  identities have been compared to a single same-witness family indexed by a
  common middle word,
  ```text
  A^μ A^b X = Y_μ A^b,
  X A^a A^μ = A^a Y_μ,
  ```
  then `X` commutes with every product `A^a A^μ A^b`.
- `MPSTensor.commutes_words_mul_of_commutes_words` in the same file: fixed-length
  commutation amplifies to all multiple lengths by chunking words.
- `MPSTensor.groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_positive_word_commutes`
  and
  `MPSTensor.groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_two_sided_middle_compatibility`
  in `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`: same-witness
  common-middle compatibilities now put `Γ_N(X)` directly in the MPV line via the
  positive-length amplification and the Wave 17A centrality endgame.

Paper anchor retained: CPGSV21 §IV.C,
`Papers/2011.12127/TN-Review-main.tex:2078--2079`, especially
"Once we have reached $k=L_0$, we can resort to the above Theorem, or
alternatively apply a similar argument when closing the boundaries", and theorem
`thm:4:unique-gs-L0_plus_1` at lines 2087--2090.

Remaining blocker after Wave 18E: prove the actual witness comparison for the two
wrapped windows produced by
`MPSTensor.chainGroundSpace_wrapped_boundary_compatibilities_of_isNBlkInjective`.
Concretely, one must reindex their complements to a common middle `μ` and show
that the wrapped witness `Y^+` and mirror witness `Y^-` reduce to a single
family `Y_μ` satisfying the two same-witness identities above.  Once that
comparison is available, the new Wave 18E theorem
`MPSTensor.groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_two_sided_middle_compatibility`
closes the MPV-line containment.

## 2026-05-01 Wave 25 update

Current branch `wave25-961-wrapped-window-witness` still does **not** close
`MPSTensor.chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`; the
pre-existing proof placeholder remains.  It lands the reindexing and conditional
endgame layer for the actual wrapped-window witness comparison:

- `MPSTensor.wrappedMiddleBackground` and `MPSTensor.mirrorMiddleBackground` in
  `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean` build the two background
  configurations whose exposed complements are the same middle word `μ`.
- `MPSTensor.wrappedMiddleBackground_complement` and
  `MPSTensor.mirrorMiddleBackground_complement` prove the corresponding
  complement-extraction identities.
- `MPSTensor.two_sided_middle_compatibility_of_wrapped_witness_comparison` turns
  the concrete comparison
  `Ywrap (wrappedMiddleBackground L₀ N η μ) =
   Ymirror (mirrorMiddleBackground L₀ N η μ)`
  into the same-witness common-middle hypotheses used by the Wave 18E algebraic
  endgame.
- `MPSTensor.groundSpaceMap_mem_mpvSubmodule_of_isNBlkInjective_of_wrapped_witness_comparison`
  and
  `MPSTensor.chainGroundSpace_le_mpvSubmodule_of_isNBlkInjective_of_wrapped_witness_comparison`
  integrate this comparison into the MPV-line containment argument.

This narrows issue #961 to the remaining comparison theorem itself: for the
witness families produced from the two reduced wrapped windows, prove equality
after filling the complements by the same middle word through the two background
maps above.  Once that theorem is available, the new conditional reduction theorem
feeds directly into the existing normal-range containment target.

Paper anchor retained: CPGSV21 §IV.C,
`Papers/2011.12127/TN-Review-main.tex:2078--2079`, especially
"Once we have reached $k=L_0$, we can resort to the above Theorem, or
alternatively apply a similar argument when closing the boundaries", and theorem
`thm:4:unique-gs-L0_plus_1` at lines 2087--2090.
