# Issue #590 blocker report — April 23, 2026

## Outcome

I could **not** honestly close issue #590 on current `origin/main`.

The reason is subtle but important: the orbit-sum **combination theorem requested by the
original issue is already present** on current `main`, after the recent
`SectorIrreducibility` split. The remaining missing step is **not** the orbit-sum assembly
itself, but the still-abstract one-step projection-preservation hypothesis `hProjStep`.

Concretely, current `main` already contains the theorem

- `MPSTensor.hLift_cyclicDecomp_mps_of_fixUpgrade`

in

- `TNLean/MPS/CanonicalForm/SectorIrreducibility/HLift.lean`

and its wrappers

- `MPSTensor.hLift_cyclicDecomp_mps_of_projStep`
- `MPSTensor.isIrreducibleOnCorner_of_cyclic_decomp_mps_of_projStep`
- `MPSTensor.isIrreducibleOnCorner_of_cyclic_decomp_mps_of_fixUpgrade`.

So the public orbit-sum lift infrastructure is already there. What is still missing is the
specialized theorem that removes the remaining abstract input

```lean
hProjStep :
  ∀ k X,
    IsOrthogonalProjection X →
    X * P k = X →
    P k * X = X →
    IsOrthogonalProjection (transferMap (fun i => (A i)ᴴ) X)
```

for cyclic-sector MPS data.

## What is already formalized on current `main`

Inside `TNLean/MPS/CanonicalForm/SectorIrreducibility/HLift.lean`, the current development
already proves the following chain.

1. `hFixUpgrade_of_peripheral`

   From
   $$
   \operatorname{PreservesCorner}(Q, (E_A^\dagger)^m)
   $$
   and irreducibility/trace preservation of $A$, one obtains
   $$
   (E_A^\dagger)^m(Q) = Q.
   $$

2. `hLift_cyclicDecomp_mps_of_fixUpgrade`

   Assuming the orbit iterates remain orthogonal projections, the orbit sum
   $$
   R := \sum_{l=0}^{m-1} (E_A^\dagger)^l(Q)
   $$
   satisfies the required `hLift` conclusion:

   - `R` is an orthogonal projection,
   - `R` preserves its corner under `E_A^\dagger`,
   - $Q = 0 \iff R = 0$,
   - $Q = P_k \iff R = 1$.

3. `hLift_cyclicDecomp_mps_of_projStep`

   This discharges the fixed-point upgrade using `hFixUpgrade_of_peripheral`, but it **still
   leaves `hProjStep` abstract**.

Therefore the precise remaining obstruction is:

> prove that if `X` is an orthogonal projection supported on one cyclic sector `P k`, then
> `transferMap (fun i => (A i)ᴴ) X` is again an orthogonal projection.

## Why the recent split does not remove the blocker

I re-read the split files

- `ProjectionOrtho.lean`
- `OrbitSum.lean`
- `HLift.lean`

and checked the relevant paper passage in `Papers/1708.00029/main.tex`, Lemma `lem:bdcf`
("Blocking a single periodic block").

The split exposes the orbit-sum ingredients more clearly, but it does **not** add a theorem of
the shape needed to eliminate `hProjStep`.

More precisely:

- `pairwise_mul_zero_of_orthogonalProjection_sum_one` gives orthogonality of distinct sectors;
- `orbit_iterate_supported_on_shifted_sector` tracks support of the orbit iterates;
- `orbitSumProjection_fixed_of_pow_fix` and `orbitSumProjection_eq_one_of_full_sector` handle the
  fixedness/full-sector parts of the orbit sum;
- `orbit_iterate_isOrthogonalProjection` is exactly the point where the argument still depends on
  the abstract hypothesis `hProjStep`.

So the new modular structure helps readability, but the mathematical gap is unchanged.

## Search / audit evidence

I checked the surrounding API in the current repository for a theorem that would bridge sector
support to one-step projection preservation.

### 1. Multiplicative-domain API

`TNLean/Channel/Schwarz/MultiplicativeDomainFull.lean` provides:

- `krausMap_mul_right_of_mem_multiplicativeDomain`
- `krausMap_mul_left_of_mem_multiplicativeDomain`
- closure of the multiplicative domain under `+`, `*`, and `conjTranspose`.

But it does **not** provide a theorem turning corner support
$$
X = P_k X = X P_k
$$
into
$$
X \in \mathrm{MD}(E_A^\dagger).
$$

### 2. Fixed-point algebra API

`TNLean/Channel/FixedPoint/Algebra.lean` provides genuine fixed-point results such as

- `mem_multiplicativeDomain_of_mem_fixedPoints`
- `fixedPoints_in_multiplicativeDomain`.

These apply when an element is already a fixed point of the **same** map. They do **not** convert
sector support under `P k` into multiplicative-domain membership for the one-step map
`E_A^\dagger`.

### 3. Existing negative evidence already in the repo history

The follow-up audit

- `audits/2026-04-21_issue599_corner_multiplicativeDomain_counterexample.md`

records that the naive statement

```lean
P * X = X → X * P = X → X ∈ KadisonSchwarz.multiplicativeDomain K
```

is false, even for unital TP selfadjoint Kraus maps. So the gap cannot be closed by a simple
"corner support implies multiplicative-domain membership" lemma.

## Why the obvious shortcut fails

A tempting argument is:

1. sector projections `P k` lie in the multiplicative domain of `E_A^\dagger`,
2. `X` is supported on `P k`,
3. therefore `X` should also lie in the multiplicative domain,
4. hence `E_A^\dagger(X)` is again a projection.

This is false in general. The counterexample audit above already shows that support inside a fixed
projection corner is much weaker than multiplicative-domain membership.

Likewise, from
$$
(E_A^\dagger)^m(Q) = Q
$$
we only get fixed-point information for the **blocked** map $(E_A^\dagger)^m$.
That does not imply that the one-step images $(E_A^\dagger)^l(Q)$ are projections for
$1 \le l < m$.

## What the paper suggests is actually missing

Lemma `lem:bdcf` in `Papers/1708.00029/main.tex` does not merely use corner support. It uses a
stronger description of the blocked dynamics:

- the fixed points of $E_A^m$ are the sectorwise blocks $P_u \Lambda_A P_u$,
- the fixed points of $(E_A^\ast)^m$ are the sector projections $P_u$,
- the compressed blocked sector tensors are primitive / normal.

In Lean terms, the missing ingredient appears to be one of the following stronger statements.

1. A theorem describing the fixed-point algebra of the blocked corner map.
2. A theorem identifying the sector transition dynamics with a genuine `*`-homomorphic or
   compression-level map on the relevant fixed-point algebra.
3. A direct formalization of the `lem:bdcf` fixed-point / blocked-sector argument that implies the
   needed one-step projection-preservation statement.

Without one of these stronger ingredients, I do not see an honest way to discharge `hProjStep`.

## Practical downstream consequence

The downstream private placeholder

- `hLift_cyclicDecomp_mps_of_fixUpgrade_missingBridge`
  in `TNLean/MPS/Periodic/Overlap/SelfOverlap.lean`

still cannot be replaced by the public `SectorIrreducibility` theorem alone, because its statement
requires the fully specialized `hLift` conclusion with **no remaining `hProjStep` parameter**.

## Recommended next step

Repurpose the next task away from "assemble the orbit-sum lemmas"—that part is already done—and
instead target the actual missing theorem:

- either a blocked fixed-point-algebra theorem in the style of `lem:bdcf`, or
- a sectorwise theorem proving the required one-step projection preservation for
  `transferMap (fun i => (A i)ᴴ)`.

At the current library state, I do not see a sound minimal patch that closes issue #590 exactly as
written.