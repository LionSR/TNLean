# Issue #704 blocker audit — periodic reintegration layer for normal-range reduction

Date: 2026-04-22
Branch: `feat/704-periodic-reintegration`
Scope: add the periodic reintegration layer requested by #704 without new `sorry`/`axiom` and without touching the parallel-work files (`UniqueGroundState.lean`, `IntersectionProperty.lean`, `SuffixWindow.lean`).

## Files / context re-read

- `CLAUDE.md`, `docs/PROOF_INTEGRITY.md`, `docs/style.md`, `docs/blueprint_style_guide.md`
- issue #704 body / comments
- `audits/2026-04-22_issue699_open_boundary_region_blocker.md`
- `audits/2026-04-21_issue588_chainGS_bridge_blocker.md`
- `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean`
- `TNLean/MPS/ParentHamiltonian/CyclicWindow.lean`
- `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` (read-only)
- `TNLean/MPS/ParentHamiltonian/IntersectionProperty.lean` (read-only)
- `TNLean/Wielandt/RectangularSpan/Basic.lean`
- `TNLean/MPS/FundamentalTheorem/FiniteLength.lean`
- `Papers/2011.12127/TN-Review-main.tex` lines 2049–2078

## Baseline verification

Using the requested isolated worktree bootstrap (`real .lake/`, `.lake/packages -> ../../../.lake/packages`, copied `.lake/build`),

```bash
cd .worktrees/issue-704-periodic-reintegration
lake build
```

succeeds on the untouched branch head (only the repository’s pre-existing warnings / admitted declarations remain).

## Main conclusions

### A. The periodic range-reduction statement looks locally approachable

The **window-monotonicity** direction itself does not look like the real blocker.

The right low-level theorem is not the exact `chainGroundSpace` statement from the issue body, but a lower-layer cyclic-window lemma that can live below `UniqueGroundState.lean`, e.g. a theorem of the form

```lean
theorem cyclicRestrict_mem_groundSpace_of_mem_groundSpace_le
```

saying that if a length-`L` cyclic restriction lies in `groundSpace A L`, then every shorter cyclic restriction with the same start point and the same outside configuration lies in the corresponding smaller ground space.

The key one-step identity is a cyclic analogue of `contiguousRestrictₗ_restrictLast`:

```lean
restrictLast (cyclicRestrictₗ hN (L + 1) i τ ψ) τ[(i+L) mod N]
  = cyclicRestrictₗ hN L i τ ψ.
```

Then `groundSpace_inLeftGround` gives the one-step reduction `L+1 -> L`, and an induction gives the full monotonicity.

This part appears implementable in `CyclicWindow.lean` without touching the forbidden files.

### B. The requested wrapping theorem is still blocked on current main

The real obstacle is the **block-injective analogue of the stripping step** inside
`WrappingWindow.wrapping_window_matEq`.

In the current injective proof, the crucial extraction is at lines 241–254 of
`WrappingWindow.lean`:

```lean
apply groundSpaceMap_injective hA (show 0 < 1 from by omega)
```

This uses **one-site injectivity** to strip the distinguished boundary letter from the wrapped trace identity.

For `IsNBlkInjective A L₀`, we only know

```lean
wordSpan A L₀ = ⊤,
```

not `span (Set.range A) = ⊤`.  So the present argument does **not** have any substitute for the length-`1` trace-injectivity step.

Concretely, the current API lets one extract the following two families of equations from the wrapped `(L₀+1)`-window state:

1. from the right restriction of the wrapped window,
   $$
   C_\tau A_j X = Y_\tau A_j,
   $$
2. from the left restriction of the wrapped window,
   $$
   X A_j C_\tau = A_j Y_\tau,
   $$

where $C_\tau$ is the complement word of length $N-L₀-1$ and $Y_\tau$ is the boundary matrix witnessing membership in `groundSpace A (L₀ + 1)`.

Combining them yields commutation only for words of length
$$
(N - L₀ - 1) + 2 = N - L₀ + 1.
$$
That is,
$$
X (A_j C_\tau A_i) = (A_j C_\tau A_i) X.
$$

This is **not enough** to conclude centrality from `IsNBlkInjective A L₀` when
`N - L₀ + 1 < L₀`, i.e. whenever
$$
N < 2L₀ - 1.
$$
In the minimal case `N = L₀ + 1`, the currently extractable equations control only **two-letter words**.  The #588 padding argument repairs the *complement-length* span step, but it does **not** repair this earlier loss from length `L₀` down to length `1`.

So the missing ingredient is sharper than the issue body suggests:

> we still need a new theorem family that converts the wrapped `(L₀+1)`-window ground-space condition into a matrix identity on **length-`L₀` block words**, not merely on single letters.

Without that, the present proof strategy cannot recover a block-injective analogue of
`boundary_matrix_commutes`.

## What is still missing

A viable next target must supply one of the following.

### Option 1: a genuine block-word stripping theorem

A theorem replacing the one-site use of `groundSpaceMap_injective hA 1` by an exact-length-`L₀` statement, producing directly

```lean
X * evalWord A (List.ofFn σ) * C_τ = evalWord A (List.ofFn σ) * Y_τ
```

for all `σ : Fin L₀ → Fin d`.

This would let the rest of the `WrappingWindow` proof go through with the repaired complement-padding argument.

### Option 2: a different periodic closure theorem

Instead of forcing a commutation theorem for boundary matrices, prove a direct periodic closure result that sends

```lean
groundSpaceMap A N X ∈ chainGroundSpace A (L₀ + 1) N
```

to

```lean
X ∈ Set.center _
```

(or directly to `groundSpaceMap A N X ∈ mpvSubmodule A N`) using all cyclic positions together, rather than trying to imitate the injective `WrappingWindow` proof line-by-line.

## Honest stop point

Because issue #704 asked for **both** the periodic range-reduction theorem and the block-injective wrapping theorem, and the second one is still blocked by the missing block-word stripping theorem above, I am not landing a partial Lean edit here.

The honest outcome for this scoped run is therefore an **audit-only draft PR**:

- the range-reduction piece seems locally formalizable,
- but the wrapping theorem is *not* just a complement-padding exercise,
- so the full issue remains blocked on a new periodic closure / block-word extraction theorem.
