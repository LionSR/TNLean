# Issue #1093: non-Gemma fundamental-theorem and canonical-form reorganization scout

Issue #1093 asks whether the current fundamental-theorem and canonical-form reduction is as clean as it can be without using the Gemma-route periodic fundamental theorem.  Here “non-Gemma” means the route through the CPSV/CPGSV normal form and basis-of-normal-tensors comparison, rather than an appeal to the periodic fundamental theorem of arXiv:1708.00029.

## Current state

The direct canonical-form files are now in a much better state than they were before the common-sector waves.  In the present `main`, the assembly layer contains named hypotheses and bridge theorems for the previously implicit comparison data:

- `MPSTensor.CommonSectorRelabelingHypothesis` names the remaining blocked-word relabeling assertion.
- `MPSTensor.CommonPrimitiveSpanHypotheses` and `MPSTensor.CommonPrimitivePhaseCoverHypotheses` name the two common primitive comparison inputs.
- `MPSTensor.afterBlocking_sectorComparison_zeroTail_of_reindexedNonzeroParts_commonPhaseCover` composes the common primitive sector output with the common-cover comparison theorem.

A useful high-level picture is:

```text
SameMPV₂ A B
    │
    ▼
zero-tail split and TP primitive nonzero blocks
    │
    ▼
common cyclic-sector blocking
    │
    ▼
reindexed common primitive nonzero-sector families
    │
    ├── blocked-word relabeling hypothesis
    ├── zero-tail and injectivity hypotheses
    └── common phase cover or proportional-decomposition data
            │
            ▼
finite-length nonzero-sector span equality
            │
            ▼
BNT sector comparison and matched sector weights
```

A scan of `TNLean/MPS/CanonicalForm` and `TNLean/MPS/FundamentalTheorem` found no local `sorry` or `admit` occurrences.  The remaining issue is therefore not proof integrity; it is the shape of the public and intermediate API.

## Conditional CPSV theorem formulation

The declaration group in `TNLean/MPS/CanonicalForm/Assembly.lean` records a
conditional statement in the language of the Cirac--Pérez-García--Schuch--Verstraete
Fundamental Theorem:

- `MPSTensor.AfterBlockingFundamentalTheoremHypotheses` names the remaining
  comparison data.  It includes blocked-word relabeling, and its comparison field
  is supplied with the produced sectors' trace-preserving, primitive, and
  irreducible structure before returning the remaining zero-tail, injectivity, and
  BNT proportional-comparison hypotheses for those same sectors.
- `MPSTensor.AfterBlockingFundamentalTheoremConclusion` records the conclusion:
  after a positive blocking, there are BNT sector decompositions `P` and `Q`; the
  original blocked tensors agree with them at positive lengths; `P` and `Q`
  generate the same full MPV family; and the basis sectors, multiplicities, and
  sector-weight multisets match up to a permutation and nonzero phases.
- `MPSTensor.fundamentalTheorem_afterBlocking_of_comparisonHypotheses` derives the
  conclusion from `SameMPV₂ A B` and those named hypotheses by applying the
  existing relabeled-common-sector proportional theorem.

The statement is conditional.  It mirrors the source assertions that bases of
normal tensors match up to permutation, phases, and gauge transformations
(`Papers/1606.00608/MPDO-22-12-17-2.tex` lines 347--360 and
`Papers/2011.12127/TN-Review-main.tex` lines 1887--1900), while keeping the real
remaining inputs explicit rather than hiding them behind a vague convenience
hypothesis.

## What is still not clean

The derivation without the periodic theorem is not yet a single unconditional CPSV/CPGSV theorem.  The remaining mathematical inputs are still visible, and this is the right kind of incompleteness:

1. **Blocked-word coordinate agreement.**  The current path isolates this as `CommonSectorRelabelingHypothesis d`.  PR #1096 narrowed the direct-versus-iterated blocking equivalence, but the exact common-sector coordinate agreement is still part of the #990 line of work.
2. **Transport of weights and zero tails through the final common-sector choice.**  The #971 line remains relevant wherever the statement needs the produced common sectors to carry the exact weights and zero-tail comparison in the final form.
3. **Common phase cover or proportional decomposition for the produced sectors.**  PR #1082 records the span consequences, and PR #1097 adds a proportional bridge, but the unconditional common-cover construction is still not closed.
4. **Injectivity after any further blocking that the comparison theorem requires.**  The current theorems keep injectivity explicit, which is mathematically faithful.  It should remain explicit until the Wielandt/injectivity refinement is proved in the same language as the produced common sectors.

These are real hypotheses, not mere naming artifacts.

## Reorganization targets

The next cleanup should avoid proving new mathematical content by hiding it inside broad theorem statements.  The useful reorganizations are local and structural.

### 1. Keep intermediate theorem names in the `afterBlocking` family

The old names beginning with `fundamentalTheorem_after_blocking_*` mix two roles: some are final theorem shapes, while others are intermediate structural facts.  The rename merged in PR #1099 is a good example of the desired direction.  Intermediate results should read like the mathematical operation they perform, for example:

```text
afterBlocking_*_of_sameMPV₂
afterBlocking_*_of_reindexedNonzeroParts
afterBlocking_*_of_commonPhaseCover
```

This makes the final fundamental theorem easier to state later, because the intermediate statements no longer claim to be the theorem itself.

### 2. Continue replacing long anonymous hypotheses by named structures

The structures added around #1080--#1083 are the right pattern.  When a theorem takes a long function returning many residual assumptions, the codomain should usually be a named structure.  The useful structures now are:

```text
CommonSectorRelabelingHypothesis
CommonPrimitiveSpanHypotheses
CommonPrimitivePhaseCoverHypotheses
```

The next proportional bridge should follow the same style.  A proportional-decomposition structure is better than another raw conjunction, provided its fields are the exact mathematical data needed downstream.

### 3. Separate public entry points from construction lemmas

`TNLean/MPS/CanonicalForm/Assembly.lean` should remain a public import file, but the module docstring can eventually contain a short table with three levels:

| level | role |
|---|---|
| structural output | zero-tail split, TP primitive blocks, common cyclic sectors |
| comparison hypotheses | blocked-word relabeling, zero-tail equality, injectivity, common phase/proportional data |
| sector comparison | BNT sector data and matched sector weights |

This is a documentation reorganization, but it prevents future theorem names from carrying the whole proof outline.

### 4. Keep `MPS/FundamentalTheorem` and `MPS/CanonicalForm/Assembly` distinct

`TNLean/MPS/FundamentalTheorem` contains the equal-case and proportional BNT comparison layer.  `TNLean/MPS/CanonicalForm/Assembly` builds the after-blocking canonical-form reduction.  The derivation without the periodic theorem uses both, but they should not be collapsed into one file or one theorem family yet.  The clean final theorem should import the comparison layer, not duplicate it.

## Suggested next PRs

1. Audit the remaining `fundamentalTheorem_after_blocking_*` intermediate names after the #1099 rename, and rename only those whose role is clearly structural rather than final.
2. Continue the #1097 proportional-bridge style: any remaining proportional hypotheses should be named structures rather than anonymous conjunctions.
3. Add a compact public-roadmap docstring to `TNLean/MPS/CanonicalForm/Assembly.lean`, once the active canonical branches have settled.
4. Only after #990, #971, #1068, and the injectivity/Wielandt refinement are discharged should the project add a final theorem whose statement no longer exposes these hypotheses.

## Answer to the issue question

The derivation is much clearer now, in the most important sense: the non-Gemma assumptions are exposed rather than hidden.  It is not yet as clean as it can be.  The remaining cleanup is mostly API reorganization around theorem names and named hypothesis structures, while the remaining mathematical work is exactly the blocked-word, zero-tail/weight transport, common-cover/proportional, and injectivity data listed above.
