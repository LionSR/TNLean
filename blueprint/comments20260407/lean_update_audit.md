# Lean update audit for blueprint cleanup from PR #507

Date: 2026-04-08
Repo: `/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean`

## Summary

I did not find any theorem/definition in the audited set that needs a mathematical hypothesis change to match the blueprint cleanup.

I did find several Lean docstrings that still use repository-internal or workflow-oriented language that the blueprint has now cleaned away.

I also checked the relevant blueprint-tagged declarations for missing `[NeZero D]` assumptions and found none that mathematically require a new `[NeZero D]`.

## Files that need docstring updates

### `TNLean/MPS/CanonicalForm/Assembly.lean`

- Lines 83-90
  Issue: uses workflow language: "pipeline integration", "assembly", "helper layer", "packages".
  Proposed fix: rewrite this paragraph in mathematical terms, e.g. say that the remaining step is to pass from the per-block cyclic-sector decompositions to a single common-period direct-sum decomposition.

- Lines 120-122
  Issue: "blocked live blocks" is stale formalization jargon.
  Proposed fix: replace with "nontrivial blocked blocks" or "weighted blocked blocks".

- Lines 353-355 and 360
  Issue: repeated use of "live blocks".
  Proposed fix: replace with "nonzero-weight blocks" or "blocks coming from the nontrivial summands of the decomposition".

- Lines 607-614 and 622
  Issue: "packages" and "downstream FT" are workflow terms.
  Proposed fix: say directly that the theorem applies the fundamental theorem for separated normal canonical forms to the reduction output.

- Lines 1101-1114
  Issue: "iterated blocking infrastructure" and "downstream FT".
  Proposed fix: replace with "an iterated blocking lemma" and "the fundamental theorem from `Full.lean`" or equivalent mathematical wording.

### `TNLean/PiAlgebra/CanonicalFormSepAux.lean`

- Line 31
  Issue: "Bundled predicates".
  Proposed fix: replace with "bundled conditions" or "bundled properties".

- Line 199
  Issue: section heading "Canonical form predicate".
  Proposed fix: replace with "Canonical form conditions" or "Canonical form property".

- Line 271
  Issue: section heading "Normal canonical form predicate".
  Proposed fix: replace with "Normal canonical form conditions" or "Normal canonical form property".

- Line 280
  Issue: "primitive predicate" when the meaning is a mathematical condition/property.
  Proposed fix: replace with "primitive condition" or "primitive property".

### `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`

- Lines 86-89
  Issue: "embedding API" and "operator formalization lands" are implementation-facing.
  Proposed fix: replace with a mathematical status note, e.g. say that the present file only introduces the chain ground-space interface and postpones its realization via local window operators.

### `TNLean/MPS/ParentHamiltonian/Martingale.lean`

- Lines 9-20
  Issue: "scaffolding", "formal scaffold", and "quantitative assembly" are workflow terms.
  Proposed fix: retitle/rewrite as a preliminary martingale-method framework or outline for spectral-gap estimates.

### `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean`

- Lines 13-15
  Issue: "declaration-level interface" is formalization-speak.
  Proposed fix: replace with a direct mathematical description, e.g. say that for a canonical-form/BNT decomposition the periodic parent-Hamiltonian ground space is the span of the corresponding block MPV states.

### `TNLean/MPS/FundamentalTheorem/PeriodicOverlap.lean`

- Lines 63-70
  Issue: "compressed corner API", "live cyclic-sector API", "skeleton / proof sketch", and "completed formalization" are implementation-facing.
  Proposed fix: replace with a plain status note stating that the same-period sector statements are formulated using compressed sector tensors and that the proofs are still incomplete.

- Lines 584-597
  Issue: "Case 3 assembly" and "mirror the compressed corner API".
  Proposed fix: rename the result in prose to something like "Sector match implies repeated-block equivalence", and describe the hypotheses directly in terms of compressed cyclic-sector tensors and their relation to the blocked tensors.

- Lines 654-655
  Issue: "downstream theorems".
  Proposed fix: replace with "subsequent theorems" or name the dependent results explicitly.

### `TNLean/MPS/Symmetry/StringOrderDefs.lean`

- Line 20
  Issue: "`IsLocalSymmetry` and `HasStringOrder` predicates".
  Proposed fix: replace with "`IsLocalSymmetry` and `HasStringOrder` conditions" or "definitions".

### `TNLean/MPS/Symmetry/StringOrder.lean`

- Lines 19-20
  Issue: "TP-gauge infrastructure" is implementation-facing.
  Proposed fix: replace with "auxiliary TP-gauge lemmas and supporting proofs".

- Lines 145-146
  Issue: "reuse-heavy bridge" is non-mathematical prose.
  Proposed fix: replace with a mathematical sentence such as "This is the bridge from non-decay of string order to the peripheral spectrum of the mixed transfer map."

### `TNLean/MPS/RFP/ZeroCorrelationLength.lean`

- Line 18
  Issue: "Three predicates are introduced".
  Proposed fix: replace with "Three conditions are introduced" or "Three notions are introduced".

### `TNLean/MPS/Core/Correlations.lean`

- Lines 18-19
  Issue: "downstream chapters can consume".
  Proposed fix: replace with "later chapters use" or "later results use".

### `TNLean/Channel/FixedPoint/WedderburnDecomp.lean`

- Lines 44-46
  Issue: "require additional representation-theoretic infrastructure".
  Proposed fix: replace with "require additional representation-theoretic results" or "require further representation theory".

## Gauge-convention audit

I did not find a docstring in the audited files that incorrectly states the gauge convention after the new chapter 6 remark.

In particular:

- `TNLean/PiAlgebra/CanonicalFormSepAux.lean:53-58` correctly identifies `∑ᵢ Aᵢ† Aᵢ = I` as the trace-preserving / left-canonical convention.
- `TNLean/MPS/CanonicalForm/Assembly.lean` consistently describes the canonical-form reduction as using the TP gauge.
- `TNLean/MPS/Symmetry/StringOrder.lean:61-65` describes the actual code path there, which gauges to trace-preserving form before applying the mixed-transfer bound.

So category (2) does not currently require Lean code changes.

## `[NeZero D]` audit

I checked the blueprint-tagged declarations in the audited files, including:

- `MPSTensor.weakFundamentalTheorem_conditional`
- `MPSTensor.periodicOverlap_gaugeEquiv_of_sector_match`
- `MPSTensor.periodicOverlapDichotomy`
- `MPSTensor.periodicBasis_eventuallyLinearlyIndependent`
- `MPSTensor.IsLocalSymmetry`
- `MPSTensor.HasStringOrder`
- `MPSTensor.CondC1`, `CondC2`, `CondC3`
- `MPSTensor.twistedTransfer_spectralRadius_le_one`
- `MPSTensor.localSymmetry_iff_spectralRadius_one`
- `MPSTensor.stringOrder_iff_localSymmetry`
- `MPSTensor.virtualUnitary_of_stringOrder`
- `MPSTensor.hasStringOrder_of_symmetric_injective`
- `MPSTensor.stringOrder_invariant_of_samePhase`
- `Kraus.fixedPointAlgebra_wedderburnArtin`
- `Kraus.adjointFixedPoints_wedderburnDecomp`

Result: no missing `[NeZero D]` assumptions found.

Reasoning:

- The periodic-overlap declarations already carry `[NeZero D]` where the nonzero bond dimension is genuinely needed.
- `twistedTransfer_spectralRadius_le_one` and `twistedTransfer_modulus_one_implies_gaugePhase` derive `NeZero D` internally from the nonzero eigenvector hypothesis.
- The symmetry theorems with `Λ.PosDef` and `Matrix.trace Λ = 1` are already vacuous at `D = 0`; they do not need an extra typeclass assumption.
- `Kraus.fixedPointAlgebra_wedderburnArtin` and `Kraus.adjointFixedPoints_wedderburnDecomp` do not divide by `D` or use `D⁻¹`.

## Note on the requested path

`TNLean/MPS/Core/Defs.lean` does not exist in the current tree. I audited `TNLean/MPS/Defs.lean` instead and did not find any update needed there.
