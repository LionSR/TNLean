# Issue #460 blocker audit — Friedrichs-angle layer and degenerate-GS fallback

Date: 2026-04-22
Branch: `feat/460-ph-friedrichs-analytic`
Scope: continue the post-PR-#757 work on issue #460 by first attempting the
remaining analytic theorem
`MPSTensor.parentHamiltonianES_gap_bound_of_friedrichs`, and if that does not
close cleanly, re-check the fallback theorem
`MPSTensor.parentHamiltonianGroundSpace_le_bntSpan_of_block_decomposition`,
without adding new `sorry`/`axiom`.

## PR / branch status

- PR #757 `fix(MPS/ParentHamiltonian): package parentHamiltonian_gapped (#460)`
  is **merged** on current `main`.
- Following the issue instructions, I resumed in a fresh worktree
  `.worktrees/issue-460-friedrichs` on branch
  `feat/460-ph-friedrichs-analytic`.

## Files / context re-read

- `CLAUDE.md`, `docs/PROOF_INTEGRITY.md`, `docs/style.md`,
  `docs/blueprint_style_guide.md`
- issue #460 full thread, including the owner comments after PRs #694 and #757
- `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`
- `TNLean/MPS/ParentHamiltonian/Defs.lean`
- `TNLean/MPS/ParentHamiltonian/Basic.lean`
- `TNLean/MPS/ParentHamiltonian/CyclicWindow.lean`
- `TNLean/MPS/ParentHamiltonian/Martingale.lean`
- `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`
- `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean`
- Mathlib files:
  - `Mathlib/Analysis/InnerProductSpace/Positive.lean`
  - `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
  - `Mathlib/Analysis/Normed/Lp/WithLp.lean`

## Current theorem surface on `main`

There is **no** `TNLean/MPS/ParentHamiltonian/SpectralGap.lean` on current
`main`; the spectral-gap work lives in `Martingale.lean`.

The remaining analytic theorem is exactly:

```lean
 theorem parentHamiltonianES_gap_bound_of_friedrichs
     (A : MPSTensor d D) (_hA : IsInjective A) (L : ℕ) (_hL : 1 < L) :
     0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
     ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
       (v : EuclideanSpace ℂ (Cfg d N)),
       v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
         ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
           ‖parentHamiltonianES A L N v‖
```

The remaining fallback theorem is exactly:

```lean
 theorem parentHamiltonianGroundSpace_le_bntSpan_of_block_decomposition
     (A : (j : Fin r) → MPSTensor d (dim j))
     (_hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (_hL : 1 < L) (_hN : N ≥ L + 1) :
     parentHamiltonianGroundSpace (μ := μ) A L N ≤ bntSpan A N
```

The current sorry surface relevant to this issue is:

- `TNLean/MPS/ParentHamiltonian/Martingale.lean`
  - `parentHamiltonianES_gap_bound_of_friedrichs`
- `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean`
  - `parentHamiltonianGroundSpace_le_bntSpan_of_block_decomposition`
- `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`
  - `chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`
    (upstream dependency for the degenerate-GS route)

## Result of the analytic attempt (A)

### 1. Negative scouting result: no packaged Friedrichs-angle / principal-angle API

I explicitly searched Mathlib for a subspace-angle / Friedrichs-angle layer.
The result is still negative.

Search evidence:

- `lean_loogle` queries like `Friedrichs angle submodule projection`,
  `principal angle submodule`, `Submodule.starProjection angle` returned no
  relevant results.
- `grep` through `.lake/packages/mathlib/Mathlib/` for `Friedrichs`,
  `principal angle`, `orthogonalProjection.*angle`, and
  `starProjection.*angle` found no subspace-angle API; the only hits were the
  unrelated scalar trigonometric namespace `Real.Angle`.

So the quantitative step

$$
 h_i h_j + h_j h_i \ge - c_{ij}(1-\gamma)(h_i + h_j)
$$

is not waiting on a hidden theorem search result. It would require a new formal
projection-geometry layer.

### 2. Positive scouting result: the operator-theoretic base is present

Mathlib *does* provide the operator API needed for a future positivity package:

- `Submodule.starProjection`
- `Submodule.isSymmetricProjection_starProjection`
- `LinearMap.IsSymmetricProjection.isPositive`
- `LinearMap.IsPositive.add`
- `LinearMap.isPositive_sum`
- `LinearMap.IsPositive.conj_adjoint`
- `LinearMap.isPositive_linearIsometryEquiv_conj_iff`

So the obstruction is not the absence of positivity infrastructure *per se*.
The missing part is the exact connection from the current `localTerm`
definition to a positive operator on `EuclideanSpace`.

### 3. New candidate route for positivity packaging

While re-reading `Defs.lean` and `CyclicWindow.lean`, I found a concrete route
that seems mathematically correct, but it is **not yet formalized** in current
TNLean.

For fixed `hN : 0 < N`, window length `L`, site `i : Fin N`, and outside
configuration `τ : Fin N → Fin d`, define the transported cyclic restriction
map

```lean
Rᵢ,τ := LinearMap.withLpMap 2 (cyclicRestrictₗ hN L i τ)
       : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L).
```

Let

```lean
P_L := ((groundSpaceES A L)ᗮ.starProjection.toLinearMap)
     : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L).
```

Then the current `localTerm` formula strongly suggests the exact averaging
identity

$$
 h_{i,\mathrm{ES}}
   = \frac{1}{d^L}
     \sum_{\tau : \mathrm{Cfg}(d,N)}
       R_{i,\tau}^{\dagger}
       P_L
       R_{i,\tau}.
$$

Reason: `cyclicRestrictₗ hN L i τ` depends only on the complement data carried
by `τ`; changing the window coordinates of `τ` does not change the restricted
map. Averaging over all `τ` with the same complement should therefore cancel the
`d^L` overcount introduced by summing over all ambient configurations in the
present `localTerm` definition.

If this identity were formalized, positivity would be immediate:

- `P_L` is positive because it is an orthogonal projection;
- each `R_{i,τ}^{\dagger} P_L R_{i,τ}` is positive by
  `LinearMap.IsPositive.conj_adjoint`;
- the finite average is positive by `LinearMap.isPositive_sum` and nonnegative
  scalar multiplication.

This would yield `localTermES_isPositive`, hence
`parentHamiltonianES_isPositive` by summing over `i`.

### 4. Scratch confirmation for the candidate route

I checked that the relevant building blocks already typecheck on current
`main`. To reproduce:

```bash
cd .worktrees/issue-460-friedrichs
lake build TNLean.MPS.ParentHamiltonian.Martingale
lake build TNLean.MPS.ParentHamiltonian.CyclicWindow
lake env lean /tmp/issue460_friedrichs_scratch.lean
```

with

```lean
import TNLean.MPS.ParentHamiltonian.Martingale
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import Mathlib.Analysis.InnerProductSpace.Positive

namespace MPSTensor

noncomputable def cyclicRestrictES {d N : ℕ} (hN : 0 < N) (L : ℕ) (i : Fin N)
    (τ : Fin N → Fin d) : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L) :=
  LinearMap.withLpMap 2 (cyclicRestrictₗ (d := d) hN L i τ)

#check cyclicRestrictES
#check (cyclicRestrictES (d := 1) (N := 1) (hN := by decide) 0 ⟨0, by decide⟩
  (fun _ => ⟨0, by decide⟩)).adjoint
#check (Submodule.isSymmetricProjection_starProjection
  ((groundSpaceES (d := 1) (D := 1) (A := (0 : MPSTensor 1 1)) 0)ᗮ)).isPositive

end MPSTensor
```

This confirms two important facts:

1. the lifted cyclic restriction maps `Rᵢ,τ` exist as linear maps between the
   relevant Euclidean spaces and have adjoints; and
2. the local projector `P_L` is already packaged as a positive operator.

### 5. Why I am not claiming a proof

The missing lemma is the exact operator identity connecting the current
configuration-wise definition of `localTerm` to the averaged positive-conjugate
formula above. That equality is combinatorial and nontrivial; it is not a one-
line theorem search exercise.

Even if that positivity package were landed, the **quantitative** part of
`parentHamiltonianES_gap_bound_of_friedrichs` would still remain:

- the Friedrichs-angle / anti-commutator estimate for overlapping local ground
  spaces, and
- the finite-overlap row-sum bound in the exact coefficient form expected by the
  martingale inequality.

So sub-goal (A) is still honestly blocked on current `main`.

## Result of the fallback attempt (B)

The degenerate-ground-space fallback is still blocked for two separate reasons.

### 1. Upstream normal-range reduction is still sorry-backed

`UniqueGroundState.lean` still contains

```lean
theorem chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction ... := by
  sorry
```

and `chainGroundSpace_eq_mpvSubmodule_normal` depends on it. So even the
blockwise uniqueness ingredient needed by `DegenerateGS.lean` is not yet
available unconditionally.

### 2. Periodic block decomposition is still absent

Even setting the previous item aside, current `main` still has no theorem of the
form

```lean
chainGroundSpace (toTensorFromBlocks μ A) L N
  = ⨆ j, (embedded block j chain ground space)
```

for periodic chains. The docstring in `DegenerateGS.lean` already states this
precisely: to prove the `⊆` direction one needs a decomposition of the assembled
periodic ground space into block components before applying blockwise normal
uniqueness.

Without such a theorem, there is still no sound route from
`ψ ∈ chainGroundSpace (toTensorFromBlocks μ A) L N` to membership in the span of
block MPVs.

So sub-goal (B) is also still honestly blocked on current `main`.

## Recommended next PR targets

### A. Positivity-packaging infrastructure PR (local to `ParentHamiltonian`)

The most actionable next step on the martingale side is:

1. define transported cyclic restriction maps `Rᵢ,τ`;
2. prove the averaging identity
   $$
     h_{i,\mathrm{ES}} = d^{-L} \sum_\tau R_{i,\tau}^{\dagger} P_L R_{i,\tau};
   $$
3. derive `localTermES_isPositive` and `parentHamiltonianES_isPositive`.

This would remove the last non-quantitative operator-theoretic blocker inside
`Martingale.lean`.

### B. Separate quantitative Friedrichs-angle PR

After (A), the remaining content of
`parentHamiltonianES_gap_bound_of_friedrichs` would be exactly the finite-
overlap projection-geometry estimate. That work will likely need either:

- a new `Analysis` helper file for principal-angle / Friedrichs-angle lemmas on
  submodules, or
- a self-contained projection-anticommutator development in
  `Martingale.lean`.

### C. Degenerate-GS critical path remains separate

For the fallback route, the critical path is still:

- wrapped-window / open-boundary infrastructure (`#730` / `#588` line), then
- `chainGroundSpace_eq_mpvSubmodule_normal`, then
- periodic block decomposition for `toTensorFromBlocks μ A`.

## Why I am stopping here

I do not see a sound route to close either remaining theorem from current
`main` without adding a new layer of infrastructure. I also do not want to hide
that gap behind an ad hoc helper lemma with the same mathematical content.

So for this worktree run I am recording the blocker precisely instead of
claiming progress that has not been formalized.
