# Issue #599 fixed-point route — April 23, 2026

## Outcome

I did **not** fully discharge the remaining `hProjStep` hypothesis on current `main`, but I did land a sharper single replacement hypothesis that packages the fixed-point route suggested by the issue discussion.

### Option picked

**Option C**: replace the old pair

- `hProjStep`
- `hFixUpgrade`

by a single structured hypothesis

- `MPSTensor.SectorFixedPointAlgebraRigidity`

and prove the orbit-sum lift / sector-irreducibility wrappers directly from it.

## Lean declarations landed

In `TNLean/MPS/CanonicalForm/SectorIrreducibility/HLift.lean` I added:

1. `MPSTensor.SectorFixedPointAlgebraRigidity`
2. `MPSTensor.hProjStep_of_sectorFixedPointAlgebraRigidity`
3. `MPSTensor.hLift_cyclicDecomp_mps_of_sectorFixedPointAlgebraRigidity`
4. `MPSTensor.isIrreducibleOnCorner_of_cyclic_decomp_mps_of_sectorFixedPointAlgebraRigidity`

## Mathematical content

Let
$$
T := \operatorname{transferMap}(A^\dagger).
$$

The new hypothesis `SectorFixedPointAlgebraRigidity` says that on each cyclic sector $P_k$, the one-step map $T$ is multiplicative on the algebra of $T^m$-fixed operators supported on the corner $P_k \mathcal M_D P_k$:
$$
X = X P_k = P_k X,\quad Y = Y P_k = P_k Y,\quad T^m(X)=X,\quad T^m(Y)=Y
\implies T(XY)=T(X)T(Y).
$$

This is the exact fixed-point-algebra package that the old `hProjStep` proof sketch was trying to access through the false multiplicative-domain shortcut.

### What is now proved from it

- `hProjStep_of_sectorFixedPointAlgebraRigidity`:
  if $X$ is an orthogonal projection, supported on $P_k$, and fixed by $T^m$, then $T(X)$ is again an orthogonal projection.

  Proof idea:
  - Kraus maps automatically preserve `conjTranspose`, so $T(X)$ is Hermitian.
  - Rigidity gives $T(X^2)=T(X)^2$.
  - Since $X^2=X$, we get $T(X)^2=T(X)$.

- `hLift_cyclicDecomp_mps_of_sectorFixedPointAlgebraRigidity`:
  the orbit-sum lift now follows from the **single** rigidity hypothesis together with the already-landed theorem `hFixUpgrade_of_peripheral`.

  The proof re-runs the orbit induction, but only on iterates $T^l(Q)$ of a projection $Q$ satisfying `PreservesCorner Q (T^m)`. After `hFixUpgrade_of_peripheral`, we know $T^m(Q)=Q`, hence also $T^m(T^l(Q))=T^l(Q)$ for all $l$, so the rigidity hypothesis applies exactly where the old `hProjStep` was needed.

- `isIrreducibleOnCorner_of_cyclic_decomp_mps_of_sectorFixedPointAlgebraRigidity`:
  sector irreducibility on each corner follows immediately from the new orbit-sum lift.

## Residual gap

The remaining honest gap is now sharply localized:

> derive `SectorFixedPointAlgebraRigidity` from the paper-level fixed-point description of a periodic block (arXiv:1708.00029, Lemma `lem:bdcf`).

Concretely, the missing theorem family is a Wolf-style statement that the one-step sector dynamics acts as a `*`-homomorphism on the $T^m$-fixed corner algebra (equivalently, on the primitive blocked sector algebra). Once that is formalized, the old abstract `hProjStep` hypothesis can be removed entirely in favor of the new rigidity theorem.

## Why this is better than the old state

Previously the file still exposed two abstract inputs:

- a one-step projection-preservation hypothesis `hProjStep`, and
- a fixed-point upgrade `hFixUpgrade`.

Now:

- `hFixUpgrade` is already discharged unconditionally by `hFixUpgrade_of_peripheral`, and
- the remaining input is a **single** structured fixed-point-algebra hypothesis that matches the paper's real missing endpoint.

So the issue is no longer blocked on a vague projection-preservation black box; it is blocked on a precise algebraic statement tied to `lem:bdcf`.

## Verification

Commands run in `.worktrees/issue-599-fixed-algebra`:

```bash
lake env lean TNLean/MPS/CanonicalForm/SectorIrreducibility/HLift.lean
lake env lean TNLean/MPS/CanonicalForm/SectorIrreducibility.lean
lake build
rg -n "sorry|axiom" \
  TNLean/MPS/CanonicalForm/SectorIrreducibility/HLift.lean \
  TNLean/MPS/CanonicalForm/SectorIrreducibility.lean
cd blueprint && leanblueprint web && leanblueprint checkdecls
```

No new `sorry` / `axiom` were introduced in the touched Lean files.
