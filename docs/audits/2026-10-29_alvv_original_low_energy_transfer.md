# Viability transfer between original low-energy windows

The buffered physical family of commit
`259dd9c52d55f81b5a1e29dac2676cc43a2e9401` improves viability between two
spectral spaces of one clipped Hamiltonian. The present corollary transfers
that same family to the original upper and lower spectral windows. It is
an auxiliary to ALVV, arXiv:1602.08828v2, Theorem 4.8 (`t:aisgapless`,
source lines 1027–1041), using the closeness composition in `l:close`,
lines 484–489.

Every regional energy, threshold, clipped operator, family member, actual
polynomial and exterior factor is obtained from the physical constructor.
All these choices precede the viable subspace and its error parameter.
There is no supplied spectral-comparison or tensor-decomposition hypothesis.
The family cardinality and dimension-growth bounds are unchanged.

Write `G(c)` for the original centered spectral space below `E0+c`.
If `S` is delta-viable for `G(eta)`, with `delta ≥ 0` and
`2(delta+epsilon)<1`, it is `2(delta+epsilon)`-viable for the clipped upper
target. Filtering and transferring through the clipped lower target gives

```
delta_out = 2 * (Delta / (1 - 2*(delta + epsilon))^2 + epsilon).
```

The conclusion concerns `G(eta-3w)`. Both losses are explicit. In particular,
the error for the original windows is not identified with the smaller error
between the clipped targets.

The strict buffer `3w < eta`, interior five-region geometry and exact finite
filter estimate remain. The source substitution, short and boundary regions,
favorable dimension-error tradeoff, low-density bootstrap and sampled tree
are not asserted. The paper-gap note records these restrictions.

## Verification provenance

The new module imports the separately compiled `PhysicalLowEnergyFamily`
object from commit `259dd9c`. Its remaining imports use the frozen compiled
TNLean source snapshot `7881dbe5a91f1436913a0a97d9812b0149aa3165` and exact
QICLean revision `b66600027b2e60ccafea43d041d563cdd00cf05b`. The private
namespace contains links to the unmodified compiled objects and new private
outputs; no compiled cache is copied or modified. The package revision and
load-bearing imported-object hashes are checked before and after compilation.
The common integration worktree may contain subsequent source-only additions;
those source changes are not used by this imported-object check.

Ordinary integration and blueprint declaration checks remain pending.
No permanent theorem fixture is added.

The strict separate-module check passed in 12.717 seconds, below the
45-second changed-module budget, at source SHA-256
`7e8bd073da38c0104b340818634cc4ae166baf98a69acc9edcfe7c6d28ec3332`.
The imported foundation audit reports only `propext`, `Classical.choice`
and `Quot.sound`. The public statement retains the explicit threshold
formula, its lower bounds, the actual regional minima and original ground
data, the clipped norm budget, the family cardinality, and the two original
windows. The polynomial decomposition is constructed internally by the
imported physical theorem rather than repeated as additional returned data.

The updated paper-gap note compiles without unresolved references or
overfull boxes. Import-aggregator validation, the proof-pattern scan and
whitespace checks pass. Completion marks await ordinary integration gates.
