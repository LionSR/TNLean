# Necessary window size for the current AKLV square-degree estimates

Issues: [#9838](https://github.com/LionSR/TNLean/issues/9838) and
[#9839](https://github.com/LionSR/TNLean/issues/9839).
Inspected baseline: `cbf482955f46f36c71c95ab1547b3cc86b6d58c2`.

## Existing work and scope

Both leaves remain open for the sharper rate without inverse-gap logarithms.
The integrated clipping, Chebyshev filter, original-vector frustration-free
entropy, and general entropy results are preserved. The old draft-owner and
pin blockers in the historical issue records are superseded by their latest
current-disposition sections. A live search for open PRs mentioning either
issue found no active overlapping PR. No dependency, toolchain, or manifest is
changed; the baseline selects QICLean `c457682404aa548b4acd16ac27be5d3835e68892`.
This audit makes no additional release-acceptance claim about that selection.

The remaining source inference is AKLV, arXiv:1301.1162v1,
`1dfrustrated34.tex`, proof of `t:ent`, lines 827–846. Its sharper choice
`s = O(log²(q)/g)` does not follow from the numerical rank bound currently
used in `FavorableParameters.lean` and `FrustrationFreeParameters.lean`.
The new module analyzes that explicit bound, without repeating the physical
constructions or adding premises to the source entropy theorem.

## Quantitative necessary condition

For integers `q,s ≥ 1`, nonnegative `gamma`, and `R ≥ s`, set

    D = (q(s²+1))^(32(2s+1)),
    delta = 4 exp(-4s² sqrt(gamma/R)).

If `D delta ≤ 1`, then

    1024 (log s)² ≤ gamma s.

Indeed, `log D ≥ 128s log s`. Taking logarithms of the product inequality
and dropping `log 4 ≥ 0` yields `32 log s ≤ s sqrt(gamma/R)`.
Squaring the nonnegative sides gives
`1024(log s)² ≤ s² gamma/R ≤ gamma s`.
At the frustration-free clipped gap `gamma=g/2`, this becomes

    2048 (log s)² ≤ g s.

Consequently, if `g s ≤ A` for any fixed `A ≥ 0`, a favorable product
requires `log s ≤ sqrt(A/2048)`. Thus these bounds cannot certify favorable
tradeoff along any unbounded sequence of windows with bounded `g s`.
For fixed local dimension this includes the proposed linear inverse-gap
window scale. This consequence is ordinary real algebra from the displayed
necessary inequality; only the two finite inequalities are stated in Lean.

The general lemma also applies to the generic shrinking gap `9g/10`.
It concerns the explicit exponent-32, degree-`s²` bounds only. It excludes
neither an improved rank bound, another degree choice, nor an improved
shrinking estimate. In particular it supplies no lower bound on actual rank
and no counterexample to the sharper entropy theorem.

## Validation and remaining gates

- Read the pinned Mathlib log, square-root, and ordered-square declarations
  through the GitHub connector; reuse `log_mul`, `log_pow`, `log_le_log`,
  `sq_sqrt`, and `sq_le_sq₀`. No equivalent AKLV-specific condition was found
  in the local scalar or rank modules.
- Symbolic algebra checks passed for cancellation, squaring, and the ceiling
  comparison. A deterministic 10,000-point log-domain diagnostic included
  4,885 favorable products, all satisfying the necessary inequality. These
  checks are diagnostics, not kernel verification.
- Generated imports, blueprint roles, source integrity, and whitespace checks
  pass. Both new blueprint statements and proofs remain `notready`.
- Full source/blueprint sync has exactly the same 563 missing dependency
  references as an archived untouched baseline; both new declarations are
  found, and the missing-reference and duplicate-tag lists are unchanged.
  The tactic scan identifies no repeated block in the new module. The
  added-line reader-facing prose check also passes.
- No Lean or Lake command ran: neither executable nor `.lake` exists in this
  environment. The pinned Lean release request returned HTTP 403, and the
  environment reports outbound networking disabled. No Mathlib source build
  or dependency repin was attempted. Targeted linter-bearing compilation and
  compiled blueprint declaration checks remain required.

Keep both issues open. This is supporting analysis of the existing numerical
bounds, not completion of the sharper source rate.
