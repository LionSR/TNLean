# Issue #1077: scout for tensor-network proof tactics

Issue #1077 asks whether the project should develop proof tactics for tensor-network arguments.  This note scopes the recurring proof patterns before adding any tactic code.  The main conclusion is that the first useful step is not a large tactic, but a small family of normalization lemmas and thin tactic wrappers around them.

## Recurrent proof shapes

A scan of the current MPS and channel files shows five proof shapes that recur often enough to deserve support.

### 1. MPV extensionality and positive-length extensionality

Many proofs start from one of the predicates

```text
SameMPV₂ A B
SameMPV₂Pos A B
```

and immediately introduce a length and a physical word.  The informal argument is always the same: reduce a family equality to the scalar equality of the corresponding MPV coefficient.

```text
SameMPV₂ A B
    │ intro N σ
    ▼
mpv A σ = mpv B σ
```

A small tactic `mpv_ext` could do only this introduction and leave the coefficient goal visible.  It should not try to solve transfer-matrix algebra.

### 2. Zero-tail cancellation

The canonical-form assembly layer repeatedly compares expressions of the form

```text
mpv (blockTensor A p) σ = mpv (zeroMPSTensor _ zA) σ + mpv NA σ
mpv (blockTensor B p) σ = mpv (zeroMPSTensor _ zB) σ + mpv NB σ
```

At positive length, the zero-tail terms vanish; at length zero, the zero-tail dimensions remain.  The useful automation is a normal form that knows the two cases separately.

```text
positive length N > 0:       zero tail disappears
length zero N = 0:           zero-tail dimension remains as a scalar
```

A tactic here should probably be called only after the proof has chosen the length case.  A good first target is a lemma collection, not a tactic that performs case splits automatically.

### 3. Blocking-word normalization

The blocked-word work in `TNLean/MPS/Core/BlockingInfrastructure.lean` now has a clean vocabulary:

```text
direct blocked index i
        │ group into length-m chunks
        ▼
iterated blocked index j
        │ flatten
        ▼
direct blocked index i
```

The key diagram is:

```text
Fin (blockPhysDim d (m * n))
        directToIteratedBlockIndex d m n
                 ─────────────────────────▶
Fin (blockPhysDim (blockPhysDim d m) n)
                 ◀─────────────────────────
        iteratedBlockIndex d m n
```

PR #1096 added the equivalence
`eq_directToIteratedBlockIndex_iff_iteratedBlockIndex_eq`.  The next useful tactic support is a `simp` normal form for this diagram:

- rewrite `directIteratedBlockEquiv` to its two maps;
- reduce a grouped index equality to a flattened-index equality;
- normalize `wordOfBlock` after grouping and flattening.

A tactic name such as `block_words` would be reasonable, but the tactic should initially be only a wrapper around a carefully curated simp set.

### 4. Transfer-map and trace normalization

The channel and overlap files repeatedly use identities such as `transferMap_apply`, `trace_smul`, and adjoint simplifications.  The pattern is less MPS-specific than the block-word pattern, but it is common in this repository.

```text
transferMap A X
    │ unfold once
    ▼
∑ i, A i * X * (A i)ᴴ
    │ trace and scalar rules
    ▼
standard trace expression
```

A useful helper would be a tactic `transfer_simp` that unfolds only the intended transfer-map definitions and applies a small trace-scalar simp set.  It should avoid broad `simp` over matrix multiplication, since that tends to make goals harder to read.

### 5. Span consequences from common phase or proportional data

The common-sector comparison layer now uses two direct implications:

```text
MPVCommonPhaseCover blocksA blocksB
        ───────────────▶ finite-length span equality

ProportionalDecompositionConclusion blocksA blocksB
        ───────────────▶ finite-length span equality
```

These are already lemma-shaped.  A tactic is not the first need here.  The useful reorganization is to keep theorem statements consuming named structures such as `CommonPrimitiveSpanHypotheses`, `CommonPrimitivePhaseCoverHypotheses`, and the proportional bridge data, so that downstream proofs do not destruct raw conjunctions.

## Proposed tactic layers

The tactics should be staged from least to most ambitious.

### Layer 0: named simp sets

Add local theorem attributes only after the relevant lemmas are stable.  Candidate groups:

```text
[mps_block_words]
[mps_transfer]
[mps_zero_tail]
```

This layer is often enough.  It also gives reliable benchmarks for any later tactic.

### Layer 1: thin wrappers

Introduce very small tactics whose behavior can be described in one sentence:

| tactic | intended behavior |
|---|---|
| `mpv_ext` | introduce MPV length and word variables for `SameMPV₂` or `SameMPV₂Pos` goals |
| `block_words` | normalize direct/iterated blocking maps and `wordOfBlock` expressions |
| `transfer_simp` | unfold transfer maps and simplify trace/scalar side conditions using the curated set |
| `zero_tail_simp` | simplify zero-tail MPV terms after the length case is already fixed |

The wrappers should be intentionally simple.  When the normal form does not apply, they should leave clear unsolved goals rather than search.

### Layer 2: proof-pattern tactics

Only after Layer 1 is tested should the project consider higher-level tactics, for example a tactic that turns a common MPV phase cover into the corresponding span hypothesis.  That layer should be restricted to the canonical-form assembly files, where the target structures are known.

## Suggested first implementation target

The safest first PR for actual tactic code would be a small `block_words` wrapper, because #1096 has just supplied a clean equivalence between grouped and flattened blocked indices.  A minimal first implementation would:

1. create a small module under `TNLean/MPS/SharedInfra` or `TNLean/MPS/Core` for block-word simp support;
2. tag only the direct/iterated block equivalence lemmas that have stable statements;
3. add two or three example lemmas showing that the wrapper rewrites grouped-index equalities to flattened-index equalities;
4. avoid changing mathematical theorem statements.

## What not to build yet

A broad tactic that tries to prove tensor-network equalities from diagrams would be premature.  The diagrams are useful for choosing normal forms, but Lean should first see explicit lemmas for the normal forms.  Once the block-word, zero-tail, and transfer-map normal forms are stable, a diagrammatic interface can be considered as notation for those lemmas.

## Answer to the issue question

Yes, the project can develop tensor-network proof tactics, but the first step should be a small infrastructure layer: named simp sets and thin wrappers for MPV extensionality, block-word normalization, transfer-map simplification, and zero-tail simplification.  The block-word normalizer is the best first candidate because it now has a precise direct-versus-iterated blocking equivalence to build on.
