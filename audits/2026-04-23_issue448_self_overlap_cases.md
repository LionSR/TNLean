# Issue #448 blocker refresh — Cases 1–2 are still gated upstream by cyclic-sector `hLift` and orthogonal-corner rigidity

## Scope

Target files re-read for this retry:
- `TNLean/MPS/Periodic/Overlap/SelfOverlap.lean`
- `TNLean/MPS/Periodic/Overlap/Case1.lean`
- `TNLean/MPS/Periodic/Overlap/Case2.lean`
- `TNLean/MPS/Periodic/Overlap/Dichotomy.lean`
- `Papers/1708.00029/main.tex` (Appendix A, especially lines 908–960)
- issue #448 and its full comment history

Worktree / branch used:
- `.worktrees/issue-448-cases12`
- `feat/448-overlap-cases-1-2`

## What I confirmed this session

### 1. Case 1 is already done; the remaining Case 1–2 frontier is smaller than the issue title suggests

On current `main`:
- `TNLean/MPS/Periodic/Overlap/Case1.lean` has **no** `sorry`
- `periodicOverlap_tendsto_zero_of_ne_period` is already proved

So the remaining work inside issue #448 is now concentrated in:
- the self-overlap file `SelfOverlap.lean`
- the same-period / no-sector-match file `Case2.lean`
- the two final wrappers in `Dichotomy.lean`

### 2. Remaining `sorry`-backed declarations in the Case 1–2 split files

#### `TNLean/MPS/Periodic/Overlap/SelfOverlap.lean`
- `hLift_cyclicDecomp_mps_of_fixUpgrade_missingBridge` (line 187)
- `not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces` (line 798)
- `periodicSelfOverlap_tendsto` (line 1044)

#### `TNLean/MPS/Periodic/Overlap/Case1.lean`
- none

#### `TNLean/MPS/Periodic/Overlap/Case2.lean`
- `exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp` (line 126)
- `exists_sector_match_of_gaugePhaseEquiv` (line 245)
- `not_gaugePhaseEquiv_of_no_sector_match` (line 288)
- `periodicOverlap_tendsto_zero_of_no_sector_match` (line 352)

#### `TNLean/MPS/Periodic/Overlap/Dichotomy.lean`
- `periodicOverlapDichotomy` (line 43)
- `periodicBasis_eventuallyLinearlyIndependent` (line 69)

### 3. One older blocker note is now stale

The April 17 issue comment said Cases 1–2 were still routed through the old
`compressedTensor_adjointTransferMap_cornerBridge` gap.

That is no longer the first missing step on current `main`: in the split file
`SelfOverlap.lean`, the theorem

```lean
private lemma compressedTensor_adjointTransferMap_cornerBridge
```

is now present and fully written.

The honest frontier has moved **earlier** in the argument.

## Two concrete targets I tried to reduce

I focused on the two smallest-looking unsolved declarations that are not just
wrappers.

### Target A. `not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces`

This is the finite-dimensional-looking rigidity statement in
`SelfOverlap.lean:798`.

Available input in the current API:
- orthogonal projections `P u`, `P v`
- `P u * P v = 0`
- the trace realization
  ```lean
  mpv (blocks k) σ = (P k * evalWord (blockTensor A m) (List.ofFn σ)).trace
  ```
- same-index commutation of blocked letters with each `P k`

From an assumed gauge-phase equivalence one can indeed derive, via
`mpv_eq_pow_mul_of_gaugePhase`, exact proportionality of the sector trace
functionals on **all blocked words**:

```lean
trace (P v * evalWord (blockTensor A m) w)
  = ζ ^ |w| * trace (P u * evalWord (blockTensor A m) w)
```

for every blocked word `w`.

#### Where the proof stops

To turn this into a contradiction from `P u * P v = 0`, one still needs an
additional theorem saying that those blocked-word trace functionals already
**separate the orthogonal corners**. Concretely, one needs one of the following:

1. a sector-corner spanning result: blocked words generate enough of the corner
   algebra that equality of the traces on all words forces equality of the
   corner trace functionals on the full corner; or
2. a translation-eigenspace theorem for the sector states showing that distinct
   cyclic sectors cannot have proportional MPV families.

Neither statement is exported on current `main` before the later sector
normality/primitivity pipeline is available.

So this lemma is genuinely blocked on a missing **orthogonal-corner trace
rigidity** theorem, not on a local tactic search failure.

### Target B. `exists_nondecaying_sectorOverlap_of_blockedGaugePhaseEquiv_cyclicDecomp`

This is the finite-sum / asymptotic extraction step in `Case2.lean:126`.

The purely algebraic part is straightforward: exactly as in the self-overlap
proof, `hA_mpv` and `hB_mpv` expand the blocked mixed overlap into the finite
double sum

```lean
mpvOverlap (blockTensor A m) (blockTensor B m) N
  = ∑ u, ∑ v, mpvOverlap (blocksA u) (blocksB v) N.
```

Hence if every mixed sector overlap tended to `0`, then the total blocked
overlap would also tend to `0` by `tendsto_finset_sum`.

#### Where the proof stops

To contradict that, one needs an **honest** reason that the total blocked
overlap is non-decaying under the global gauge-phase equivalence.

The natural routes are both downstream-blocked:

1. use self-overlap asymptotics of the blocked tensor
   (`periodicSelfOverlap_tendsto` or the private blocked-sector version), or
2. prove directly that the blocked gauge-phase factor has unit norm and hence
   preserves the nonzero self-overlap limit.

At present:
- `periodicSelfOverlap_tendsto` is itself still `sorry`-backed, and
- the private blocked self-overlap theorem in `SelfOverlap.lean` depends on the
  same unresolved `SelfOverlap` blockers.

So this Case-2 finite-sum lemma is **not independent**: it sits strictly
*downstream* of the unresolved self-overlap infrastructure.

## The actual upstream blocker on current `main`

After re-reading `TNLean/MPS/CanonicalForm/SectorIrreducibility/HLift.lean`,
the real load-bearing missing statement is now clearer.

`SelfOverlap.lean:187` is a local placeholder for an `hLift` statement, but the
generic orbit-sum machinery already exists in

```lean
TNLean/MPS/CanonicalForm/SectorIrreducibility/HLift.lean
```

There the corresponding theorem

```lean
theorem hLift_cyclicDecomp_mps_of_projStep
```

reduces everything to one still-unavailable hypothesis:

```lean
∀ k : Fin m, ∀ X : MatrixAlg D,
  IsOrthogonalProjection X →
  X * P k = X →
  P k * X = X →
  IsOrthogonalProjection
    (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) X)
```

This is the one-step **sector-supported projection preservation** statement
(`hProjStep`) discussed explicitly in that file.

### Why this matters for #448

Once this `hProjStep`-level theorem exists (or an equivalent MPS-specific
wrapper proving the local `hLift`), the rest of the chain becomes honest:

1. `hLift_cyclicDecomp_mps_of_fixUpgrade_missingBridge` is discharged
2. `cornerRestriction_primitive_and_irreducible_of_cyclicDecomp` becomes honest
3. `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp` becomes honest
4. `sectorBlocked_isNormal_of_isPeriodic` becomes genuinely available
5. the remaining Case-2 overlap-decay wrappers reduce to the finite-sum and
   no-sector-match arguments already sketched in the source comments

So the current blocker is **not** primarily a new operator-norm estimate or a
new spectral contraction lemma. On the split `main`, the first missing theorem is
an earlier cyclic-sector projection-transport fact.

## Bottom line

I do **not** see an honest proof increment for issue #448 that closes one of the
remaining Case 1–2 declarations without first supplying at least one of the
following reusable results:

1. **Sector-supported projection preservation (`hProjStep`)** for the adjoint
   transfer map inside a cyclic decomposition; or
2. **Orthogonal-corner trace rigidity** for the blocked-word trace functionals
   attached to distinct cyclic sectors.

The first item is the more upstream blocker: it makes the sector blocks honestly
primitive/irreducible, after which the Case-2 wrappers should collapse quickly.

No Lean proof code is committed in this branch at the time of writing this note.
