# Scouting report: Fundamental Theorem for injective PEPS (arXiv:1804.04964, Section 3)

Date: 2026-03-29

## 1) Section 3 target statement (paper alignment)

Section 3 (“Injective PEPS”) proves Theorem 2 (`thm:inj`):

- For PEPS on a graph **without double edges and self-loops**, two **injective** PEPS generate the same state iff they are related by **local edge gauges**.
- Edge gauges are **unique up to multiplicative constants**.

Proof shape in the paper:

1. Block a neighborhood around each edge into a 3-site injective MPS (`eq:block_to_mps`).
2. Apply the injective-MPS edge-isomorphism lemma (`lem:inj_isomorph`) to assign a gauge to each edge.
3. Absorb gauges into one tensor family to get edge-insertion invariance (`eq:inj_equal_edge`).
4. Use the 2-tensor injective lemma (`lem:inj_equal_tensors_2`) after blocking “one vertex vs all others” to deduce per-vertex scalar proportionality.
5. Fold those scalars into gauges to get local-gauge equivalence + uniqueness up to constants.

## 2) Current Lean PEPS status (`TNLean/PEPS/Defs.lean`)

The current file is intentionally exploratory and minimal:

- graph-indexed edge and incident-edge index types,
- `Tensor` structure with edge-dependent bond dimensions and local components,
- global virtual assignments (`VirtualConfig`),
- full contraction coefficient `stateCoeff`,
- semantic equality `SameState`,
- local notion `IsVertexInjective`.

This is enough to represent finite PEPS amplitudes, but not enough to express the paper’s gauge theorem or proof route.

## 3) MPS FT pattern to mirror (`TNLean/MPS/FundamentalTheorem/*`)

Observed pattern in MPS formalization:

- **Layered theorem pipeline**:
  - core defs (`MPS/Defs`, `MPS/Chain/Defs`),
  - structural bridge lemmas (linear extension / multiplicativity / canonical decomposition),
  - endpoint theorem wrappers in `MPS/FundamentalTheorem/*`.
- **State equivalence first**, then **gauge equivalence**, then **uniqueness/corollaries**.
- Use of small reusable interfaces (`SameMPV`, `GaugeEquiv`, injectivity predicates), then stronger results in staged modules.

Recommendation: keep same architecture for PEPS:

- `PEPS/Defs` (data),
- `PEPS/Gauge` (edge gauge actions + invariance),
- `PEPS/Injective` (injectivity lemmas, blocking closure),
- `PEPS/FundamentalTheorem/*` (edge-gauge existence, uniqueness, assembled theorem).

## 4) Infrastructure gap analysis: PEPS vs MPS

### A. Graph-indexed tensor-network infrastructure (new)

Needed beyond MPS chain machinery:

1. **Half-edge / incidence orientation model**
   - MPS has fixed left/right ports; PEPS needs per-vertex incident ports with consistent per-edge pairing.
   - Need robust API for “endpoint port extraction” and transport along edge endpoints.

2. **Heterogeneous bond dimensions by edge**
   - Existing `bondDim : Edge G → ℕ` is good start.
   - Need coercion/casting lemmas when comparing networks under graph isomorphisms or blocking.

3. **Local gauge action on virtual indices**
   - Define gauge family `Z_e` per edge and action “insert `Z_e` at one endpoint, `Z_e^{-1}` at the other”.
   - Prove contraction invariance under internal gauge cancellation.

4. **Contraction combinatorics over finite graphs**
   - MPS uses ordered products/traces; PEPS needs finite products/sums over incident-edge-indexed maps.
   - Need canonical rewrites for reindexing virtual configurations under local modifications.

### B. Injectivity notions (stronger than current exploratory predicate)

5. **Paper-faithful vertex injectivity map**
   - `IsVertexInjective` is now the linear-independence formulation `∀ v, LinearIndependent ℂ (A.component v)` (issue #633); the earlier function-level `Function.Injective` surrogate was strictly weaker and admitted counterexamples to `gauge_unique_up_to_scalar`.
   - Still open: packaging the resulting left inverse as a `LinearMap` from the free space on virtual configurations into `Fin d → ℂ` (with an explicit one-sided inverse), so that the PEPS FT derivation can consume it as a linear-algebraic object rather than as a linear-independence hypothesis.

6. **Blocking closure of injectivity**
   - Formal theorem: contraction of injective tensors over internal edges remains injective on exposed boundary.
   - This is central for both edge-blocking and two-partition blocking arguments.

### C. Graph separation / blocking theorems (new combinatorics)

7. **Edge-centered blocking to 3-site chain surrogate**
   - For each edge `(u,v)`, build a blocked network with three effective tensors satisfying MPS assumptions.
   - Requires finite graph partition lemmas and induced boundary index bookkeeping.

8. **One-vs-rest blocking for scalar proportionality step**
   - Needed to instantiate the generalized `inj_equal_tensors_2` argument in graph form.

9. **No-double-edge/no-loop constraints as reusable graph class**
   - `SimpleGraph` already excludes loops/multi-edges, which aligns with theorem assumptions.
   - Need explicit bridging lemmas from graph assumptions to PEPS index constructions.

### D. Theorem-level relation types (missing)

10. **PEPS local gauge equivalence predicate**
    - Analog of chain `GaugeEquiv`, but edge-indexed and vertex-localized.

11. **Gauge uniqueness modulo scalar cocycle**
    - Need statement and normalization conventions (e.g., choose one root/anchor or quotient by global scaling class).

## 5) Proposed dependency list (Mathlib + TNLean-local)

### Mathlib dependencies likely required

- `SimpleGraph` finite incidence API (already partly used).
- `Fintype` big operators over subtype indices (`∑`, `∏` over edge/incident sets).
- Linear algebra for finite-dimensional spaces:
  - linear maps, injective/surjective equivalences,
  - tensor-product-friendly finite-dimensional lemmas (may need to keep first phase at function-level without full tensor product abstractions).
- Matrix/GL facts for gauge insertions and inverses.

### TNLean-local dependencies to reuse/adapt

- MPS chain gauge-equivalence pattern (`TNLean/MPS/Chain/Defs.lean`).
- Injective-MPS FT scaffolding (`TNLean/MPS/FundamentalTheorem/Basic.lean` and downstream wrappers) as module-organization template.
- Existing algebra lemmas on invertibility/conjugation where applicable.

## 6) Effort estimate (no code yet)

Rough estimate for a first **injective-PEPS FT endpoint** (excluding normal-PEPS extensions):

- **Phase 0 (design + specs): 1–2 days**
  - finalize exact Lean definitions for ports, gauges, and injectivity.
- **Phase 1 (core PEPS gauge infra): 4–7 days**
  - local gauge action, invariance of `stateCoeff`, reindexing lemmas.
- **Phase 2 (blocking + injectivity closure): 7–12 days**
  - graph blocking constructions and main injectivity-preservation proofs.
- **Phase 3 (FT assembly + uniqueness): 5–9 days**
  - edge-wise gauge existence, scalar-ambiguity bookkeeping, final iff theorem.
- **Phase 4 (cleanup/docs/root exports): 1–2 days**.

Total: **18–32 focused days** (single contributor), with highest risk in Phase 2 (blocking combinatorics + dependent index transport).

## 7) Risk register / blockers

1. **Dependent indexing complexity** (incident-edge subtypes + casts) can dominate proof effort.
2. **Injectivity formalization choice** (function-level vs explicit linear map/tensor products) affects all downstream theorems.
3. **Blocking construction ergonomics** on arbitrary finite graphs may need auxiliary combinatorics library.
4. **Uniqueness-up-to-constants** may require an explicit quotient-normalization strategy to avoid awkward equalities.

## 8) Suggested implementation order (when coding starts)

1. Freeze PEPS core API (`Edge`, incidence ports, virtual configs, `stateCoeff`).
2. Add edge-gauge action + invariance theorem.
3. Introduce paper-faithful injectivity predicate + prove equivalence/implications from current exploratory one (if possible).
4. Prove injectivity under contraction/blocking.
5. Build edge-to-3-site reduction lemma.
6. State/prove injective-PEPS FT existence direction.
7. Add converse (local gauge ⇒ same state) + uniqueness modulo scalar constants.
