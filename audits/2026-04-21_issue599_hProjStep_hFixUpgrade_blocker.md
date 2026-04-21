# Issue #599 blocker report — April 21, 2026

> File name kept as `2026-04-21_...` to match the explicitly requested audit path for this task.

## Outcome

I could **discharge `hFixUpgrade`**, but I could **not** honestly discharge `hProjStep` on current `main`.

### Landed partial progress in `TNLean/MPS/CanonicalForm/SectorIrreducibility.lean`

I added:

- `MPSTensor.hFixUpgrade_of_peripheral`
- `MPSTensor.hLift_cyclicDecomp_mps_of_projStep`
- `MPSTensor.isIrreducibleOnCorner_of_cyclic_decomp_mps_of_projStep`

So the remaining abstract input is now only the one-step projection-preservation hypothesis `hProjStep`.

## What works: `hFixUpgrade`

Let
$$T := \operatorname{transferMap}(A^\dagger), \qquad F := T^m, \qquad E := \operatorname{transferMap}(A).$$

For an irreducible TP tensor $A$, the primal channel $E$ has a positive definite fixed point $\rho$.
If `PreservesCorner Q F` and `Q` is an orthogonal projection, then:

1. $Q - F(Q) = Q\,F(1-Q)\,Q$, so $Q - F(Q)$ is positive semidefinite.
2. Weighted trace is invariant: $\operatorname{tr}(\rho F(X)) = \operatorname{tr}(\rho X)$.
3. Hence $\operatorname{tr}(\rho (Q - F(Q))) = 0$.
4. Faithfulness of the weighted trace against $\rho > 0$ gives $Q - F(Q) = 0$.

So `F Q = Q` is now formalized without any appeal to `lem:bdcf`.

## Remaining blocker: `hProjStep`

The unresolved goal is still:

> if `X` is an orthogonal projection supported on the cyclic sector `P k`, show that
> `transferMap (fun i => (A i)ᴴ) X` is again an orthogonal projection.

### What current API already gives

From `TNLean/Channel/Schwarz/MultiplicativeDomainFull.lean` plus the existing cyclic-projection argument, we can prove only
$$P_k \in \mathrm{MD}(T),$$
where $\mathrm{MD}(T)$ denotes the multiplicative domain of the adjoint transfer map.
This is exactly enough to derive the already-existing hypotheses

- `hMulLeft`
- `hMulRight`

for the sector projections.

### What is still missing

To prove `hProjStep` via Kadison–Schwarz, one needs `X` itself to lie in the multiplicative domain, because projection preservation comes from
$$T(X^2) = T(X)^2 \quad\text{and}\quad T(X^\dagger) = T(X)^\dagger.$$
Since $X^2 = X$, this would imply $T(X)^2 = T(X)$.

But current `main` has **no bridge** from
$$X = P_k X = X P_k$$
(or even from the stronger hypotheses that $X$ is a projection and is fixed by $T^m$)
to
$$X \in \mathrm{MD}(T).$$

Concretely, the missing API is one of the following equivalent-strength statements:

1. **Corner-subalgebra multiplicative-domain closure**
   ```lean
   X * P k = X → P k * X = X → X ∈ KadisonSchwarz.multiplicativeDomain K
   ```
   for all `X` in the `P k`-corner.

2. **Specialized projection version**
   sector-supported orthogonal projections (or at least those fixed by `(T^m)`) lie in the multiplicative domain of `T`.

3. **Paper-level `lem:bdcf` fixed-point decomposition**
   formalize the statement that for a single periodic block,
   $$\operatorname{Fix}(E_A^m) = \operatorname{span}\{P_u \Lambda_A P_u\}_u,
   \qquad
   \operatorname{Fix}(E_A^{*m}) = \operatorname{span}\{P_u\}_u,$$
   from which the required multiplicative-domain closure on each sector should follow.

## Why I stopped here

With the new weighted-trace argument, `hFixUpgrade` is no longer the blocker. The only remaining obstruction is exactly the missing bridge from **sector support** to **multiplicative-domain membership of the supported projection**. I could not find such an API in Mathlib or in the current TNLean periodic/cyclic-decomposition stack, and I did not want to fake it with a new axiom.

## Recommended next step

Open or repurpose a follow-up issue for the missing bridge, ideally phrased as:

- `sector_supported_projection_mem_multiplicativeDomain`, or
- the stronger `cornerSubmodule_mem_multiplicativeDomain`, or
- a direct formalization of `lem:bdcf`.

Once that lands, `hProjStep` should become straightforward, and the remaining abstract hypothesis in the orbit-sum lift will disappear.
