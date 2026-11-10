# Low-energy improving families on prescribed intervals

This contribution extends the physical low-energy family to every prescribed
chain interval, including empty intervals and intervals meeting either endpoint.
It supports ALVV, arXiv:1602.08828v2, Theorem 4.8 (`t:aisgapless`, source
lines 1027–1041). It does not start the low-density sampling/bootstrap or
sampled-tree induction.

## The cap and the source-scale count

For `w>0`, `6w≤eta_LD`, `g=min(w,1)` and `M=max(1,eta_LD/6)`,
`Real.low_energy_cap_bound` proves

```
1/g ≤ M/w,
log(1/g) = max(log(1/w),0).
```

`Real.low_energy_count_le_source_scale` converts the previously established
capped count into the explicit estimate

```
log D ≤ 3 K M (log L/mu)
          [1+log q+max(log(3log L/mu),0)]³.
```

The proof does not identify `g` with `w` when `w>1`.

## Strictness at the joint regional count

The new `Real.exists_low_energy_joint_scalar_parameters` chooses its
constant at fixed positive density bandwidth, before the chain length,
buffer coefficient, local dimension and Hamiltonian. It controls the full
count `D=(q ell²)^(22ell)`, including the cost of enlarging the region by
at most two window lengths. The strict width margin `w≥g>4g/5` gives a
strictly smaller physical contraction than the scalar comparison contraction.
Consequently `D^12 Delta < 1/100000` holds at the full joint count.

The existing `Real.exists_low_energy_scalar_parameters` retains its public
statement at the smaller interior count. Its proof now derives that result
from the stronger joint estimate. The old interface remains unchanged.

## Actual long-interval and short-interval constructions

`exists_physical_low_energy_interval_family` chooses the constant before
`L,q,mu,eta,H`, and constructs a family before every viable subspace.
It derives `w=mu/(3log L)>0` and `eta≥6w` from the source bandwidth condition.
The count and its logarithmic estimate are given before the interval and
Hamiltonian.

For a long interval, `inward_effective_cuts` supplies the existing five-region
geometry on an interior core. The physical constructor supplies actual
regional energies, clipping threshold, attained original ground energy and
the two buffered comparisons. The existing arbitrary-target polynomial-family
constructor decomposes the same actual clipped polynomial on the prescribed
interval. Its collar count fits the joint budget. Zero extension preserves
all image spans. No supported two-window rank theorem is duplicated.

For a short interval, the original matrix-unit construction is reused.
Its former private full-span helper is now public as
`exists_short_actual_region_spanning_family`; its two existing consumers
use that name. The previous private name is not retained as an alias.
The public short improving-family statements remain unchanged.
The new nested-target application chooses
`Delta=1/(200000 D^12)`, giving a strict budget. Nonzero viable subspaces
are enlarged to the whole regional space; zero targets are included directly.
There is no second matrix-unit construction.

## Original Hamiltonian and original-window losses

The result returns an actual centered copy `C=H-sI`, a normalized vector
attaining its ground energy `E0`, and a positive-semidefinite lower bound
`C-E0 I`. These facts fix the original spectral windows independently of
the chosen shift. In the long case the shift is the sum of the actual
regional minima; in the short case it is zero.

The result returns nested improving targets and both physical comparisons,
together with the strict joint tradeoff and its common family.
`exists_physical_original_low_energy_interval_family` retains these same
choices and adds the original-window conclusion. For `delta≥0` and
`2(delta+1/200)<1`, its error is

```
2*(Delta/[1-2(delta+1/200)]²+1/200).
```

The improving-target parameter and this final original-window error remain
distinct. No final original-window error of `1/100` is claimed. The finite
statement uses `L≥2`, nontrivial qudit dimension `q≥2`, fixed positive density
bandwidth and the displayed source-scale estimate. The low-density bootstrap,
sampled tree, efficient central tensor representation and running-time
conclusions remain separate.

## Verification provenance

All new and modified production modules were checked separately with the
package's strict options and warnings as errors. The read-only provider has
proof-source commit `5cec1958d1a56d1f20cfdbd1161ef946a410f41c`, documentation-only
successor `d0ddc83b8bafec64a83cf450e2232cc60f9aa8f0`, and exact package QICLean
revision `cc9e79084d26336c95e843c13928a3963a9debb2`. Existing imported sources,
build inputs and load-bearing object hashes were guarded. Private namespaces
contain links to existing objects and new private outputs only. No cache was
copied or modified, and no Mathlib source was compiled.

| Module | Seconds | Source SHA-256 |
|---|---:|---|
| `LowEnergyFilterParameters` | 3.968 | `edf90ede6712ef1dfc29a8241871726f80317bc69354be5dc31b73bea5c4d6e7` |
| `ShortRegionViableFamily` | 4.902 | `d04964fc31a98e4ca0f9336d044398b8cfdc59fb3844494766b4d6366eb53e27` |
| `LowEnergySourceScale` | 2.520 | `f619e542377af9dcff744cdbbd6750aebe85acdf9cdcb438221a4287881aee91` |
| `LowEnergyIntervalFamily` | 25.231 | `d7caf2051eda5db15a49e0479f2feffc302775827caed37e4a04e12dd7313d67` |

The unchanged-interface source regressions passed for
`InteriorLowEnergyFamily` (12.117 s) and `PhysicalDGViability` (26.989 s),
using the exact provider sources with the new private imported modules.
All changed modules remain below the 45-second budget. An imported foundation
audit of all nine new or modified public declarations reports only
`propext`, `Classical.choice` and `Quot.sound` (5.789 s).
The revised paper-gap note compiles without unresolved references or overfull
boxes. Import-aggregator, proof-pattern and whitespace checks pass.

Ordinary combined library and compiled-blueprint verification remain pending.
New blueprint statements omit completion marks until those gates succeed.
No permanent theorem fixture is added.

The collection-wide verdict check accepts the revised buffer note but still
reports the pre-existing malformed marker in
`alvv16_approximation_parameters.tex`; that older note is unchanged.
