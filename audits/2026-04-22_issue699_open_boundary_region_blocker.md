# Issue #699 blocker audit — open-boundary range reduction for `chainGroundSpace`

Date: 2026-04-22
Branch: `feat/699-open-boundary-region-api`
Scope: discharge the #588 / `UniqueGroundState.lean` range-reduction sorry without new `sorry`/`axiom`.

## Files / context re-read

- `CLAUDE.md`, `docs/PROOF_INTEGRITY.md`, `docs/style.md`, `docs/blueprint_style_guide.md`
- issue #699 body / comments
- `audits/2026-04-21_issue588_chainGS_bridge_blocker.md`
- `Papers/2011.12127/TN-Review-main.tex` lines 2049–2078
- `TNLean/MPS/Chain/OneSidedInverse.lean`
- `TNLean/MPS/ParentHamiltonian/{IntersectionProperty,WrappingWindow,CyclicWindow,UniqueGroundState}.lean`
- `TNLean/MPS/Defs.lean`
- supporting blocking API in `TNLean/MPS/Core/Blocking.lean` and `TNLean/MPS/Chain/BlockedChainFT.lean`

## Main new finding

The **core grow-back algebra is not the blocker**.

In a scratch Lean check, I could formalize the following reusable theorem pattern:

> If `IsNBlkInjective A L₀`, `L₀ > 0`, and a family `Z : Fin d → M_D(ℂ)` satisfies
> `∀ σ : Fin K → Fin d, ∃ Yσ, ∀ j, Z j * evalWord A (List.ofFn σ) = A j * Yσ`,
> then there exists a common `X` with `∀ j, Z j = A j * X`.

The proof is recursive on `K`.  The length-1 step uses a blocked identity decomposition for
`blockTensor A L₀`; the induction step strips the first letter and re-applies the theorem.
So the paper’s **"grow back and invert"** step really does have a workable Lean algebraic core.

## The actual remaining gaps

What I could **not** complete cleanly in scope is the passage from the existing parent-Hamiltonian
window predicates to that word-compatibility theorem, and then the periodic reintegration.
More precisely, two theorem families are still missing.

### 1. Open-chain suffix restriction / reindexing layer

The direct Option-B route wants a theorem of the form

```lean
theorem groundSpace_extend_right_of_isNBlkInjective
    [NeZero D] {K L₀ : ℕ} (hInj : IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hK : 0 < K) {ψ : NSiteSpace d (K + L₀ + 1)}
    (hLeft : InLeftGround A (K + L₀) ψ)
    (hTail : InTailGround A K (L₀ + 1) ψ) :
    ψ ∈ groundSpace A (K + L₀ + 1)
```

where `InTailGround` packages “the last `L₀ + 1` sites lie in `groundSpace A (L₀ + 1)` for every
fixed prefix”.  The **mathematics** reduces to the grow-back theorem above, but the repository is
missing a clean API for the necessary reindexing / restriction statements.

The missing declarations are essentially:

1. a suffix restriction map
   `tailRestrictₗ : (Fin K → Fin d) → NSiteSpace d (K + L) →ₗ[ℂ] NSiteSpace d L`,
2. the configuration identity
   `Fin.snoc (Fin.append u σ) j = Fin.append u (Fin.snoc σ j)`,
3. a packaged compatibility theorem turning
   - `restrictLast ψ j ∈ groundSpace A (K + L₀)` and
   - `tailRestrictₗ u ψ ∈ groundSpace A (L₀ + 1)`
   into
   `Z j * evalWord A (List.ofFn u) = A j * Y u`
   via `groundSpaceMap_injective` on `blockTensor A L₀`.

I could get very close to this in scratch, but the current `Fin (a+b)` casts / `Fin.append` /
`Fin.snoc` normalization are not exposed cleanly enough to finish it without building a dedicated
mini-API first.

### 2. Periodic reintegration after the open-chain theorem

Even granting the open-chain theorem above, the actual #588 closure still needs two periodic-side
results:

1. **Range reduction for larger windows**
   ```lean
   chainGroundSpace A L N ≤ chainGroundSpace A (L₀ + 1) N
   ```
   for `L₀ < L ≤ N`, i.e. a theorem that a larger cyclic window condition implies the reduced
   `L₀ + 1` cyclic window condition.

2. **Block-injective wrapping theorem**
   ```lean
   boundary_matrix_commutes_of_isNBlkInjective
   ```
   replacing the current injective-only `boundary_matrix_commutes`.  The #588 audit already showed
   the complement-length part is repairable by padding with `wordSpan_top_of_mul`, but that padding
   has not yet been packaged into the existing wrapping-window proof.

## Honest stop point

So I am stopping without touching the public theorem in `UniqueGroundState.lean`.

The genuine next PR target is now sharper than the original issue wording:

1. first add a **suffix-window / `Fin.append` reindexing API** and use it to prove the open-chain
   theorem `groundSpace_extend_right_of_isNBlkInjective` above;
2. then add the two periodic-side reductions
   `chainGroundSpace A L N ≤ chainGroundSpace A (L₀ + 1) N` and
   `boundary_matrix_commutes_of_isNBlkInjective`.

Once those land, the remaining `chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction` sorry
should be a short assembly proof rather than a new research step.
