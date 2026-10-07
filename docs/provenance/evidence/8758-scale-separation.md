# Uniform separation of dyadic scales

For each fixed real factor M, one nonnegative integer threshold gives
M t_k ≤ r_k and M r_k ≤ s_k at every later scale. The threshold is chosen
before the domain, cut, origin and radius. For a dyadic factor 2^d, an explicit
threshold is 10^7 d. The three theorems use the previously defined rounded
fine and pitch scales and the fixed exponents.

These are the scale-separation estimates in OpenAI, *A two-dimensional area
law from a global spectral gap*, September 24, 2026, Section 11,
`prop:two-families`, lines 200–207, and `geometry:exponents`, lines 70–78,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No upstream Lean proof text is reused.

## Exact source and canonical evidence

The verified source is `4be0ad6b5e6bc2d1523ba02b8675377c05549da5` in
[TNLean #8846](https://github.com/LionSR/TNLean/pull/8846).
`ScaleSeparation.lean` is byte-identical to its original mathematical source
`c5c7c38e61880b821d2d840768312cb5d93fc4bc`.

| Check | Command | Result | Elapsed seconds |
|---|---|---|---|
| Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Exit 0 | 5.699 |
| Imported-declaration audit | `lake env lean docs/provenance/evidence/8758-scale-separation-axioms.lean` | Exit 0 | 2.751 |

The new leaf compiled in 1.8 seconds without warnings. Each of the three
exact imported declarations uses only `propext`, `Classical.choice` and
`Quot.sound`. No placeholder or prohibited proof mechanism was introduced.

The commands ran through the own-worktree `scripts/lake_build_locked.sh --`
under the shared repository lock, reusing the warmed cache and pinned prebuilt
Mathlib artifacts. The adjacent polynomial-budget check ran afterward under
the same lock; each check records its own frozen source revision. No local
full-library or Mathlib source build was repeated, and lock waiting consumed
no CPU.

Committed evidence hashes:

- `8758-scale-separation-build.log`: `b2024a2dff18bf63dfbfbfdda49d303882700e85497fa2469c5fd4844251eb7b`.
- `8758-scale-separation-axioms.log`: `d83490d103b37175e2cee92c82500081a0ee7b8374725e5501cfc10220eba192`.

The log headers record command, source revision, elapsed time and exit code.
Only trailing whitespace in captured output is removed. The provenance update
promotes precisely these three rows; the other 182 rows and all previous
evidence remain unchanged. Complete current-policy validation includes the
pinned source, license, notices, hashes and actual quoted axiom output.

## Integration and remaining mathematics

The original source head passed all CI checks, including the full Lean build,
compiled blueprint declarations and rendering, in
[workflow 37644526706](https://github.com/LionSR/TNLean/actions/runs/37644526706).
The later source merge incorporates only the verified fine-belt evidence,
with no change to the scale-separation module. Fresh checks accompany the
final evidence update.

Polynomial absorption is a separate follow-up in #8848. Primary tiles,
contacts, repairs, birth separation, the full two-family partition, and both
manuscript headline theorems remain open.
