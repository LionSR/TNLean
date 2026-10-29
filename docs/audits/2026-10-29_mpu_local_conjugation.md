# Actual source factors and local conjugation equations for #7017

Base: origin/main at `3af48c184`, including merged #8808. Source:
`Papers/1703.09188/paper_v2.tex`, Proposition `prop1conj`, lines 1006–1039,
equations `uconjugation` and `vconjugation`.

## Forward argument now written

`IsMPUCanonicalFormII.exists_local_conjugation_gauges_common_transpose_case`
derives both literal local equations and one common symmetric/skew-symmetric
case from finite-chain conjugation invariance at every applicable length
`N > 1`. The gates come from the actual supplied source factors. No premise
asserts the existence of the missing gauges.

The forward theorem concerns a reduced canonical-form-II presentation and
supplied source factors whose unshifted gate is unitary. Its same-tensor
full-support restriction is explicit in the docstring and Blueprint and
recorded in `docs/paper-gaps/mpu_canonical_form_full_support.tex`. This is an
auxiliary forward result, not the unrestricted source-labelled equivalence.

`ConjugationSourceFactors.lean` supplies the actual comparison:

- Both source cuts conjugate coefficientwise and retain their ranks.
  Normalized flattening commutes with conjugation.
- `SourceCutSVD.mapStar` conjugates the supplied compact decomposition
  itself, retaining the positive diagonal singular-value and inverse matrices.
- `IsMPUCanonicalFormII.mapStar` reuses physical-adjoint canonical transport
  followed by the inverse physical swap. It preserves block dimensions,
  ambient full support and the same real diagonal fixed matrix.
- `SourceFactors.mapStar` conjugates all six supplied factors and their
  weight, reindexing only through canonical equalities of source-rank
  dimensions. `sourceU_mapStar` and `sourceV_mapStar` identify its gates
  with exactly the conjugates of the supplied gates.
- `exists_supplied_source_gate_unitary_gauges_of_mpo_eq` uses the existing
  letter Fundamental Theorem and normalized comparison of arbitrary supplied
  factors. The existing factor-to-gate contraction in
  `SelectedSourceGateVirtualGauge.lean` is made public with a source
  docstring, so its proof is reused.
- `exists_local_conjugation_gauges` compares with the actual conjugated
  factors and transports the two resulting unitaries back through the rank
  identifications, removing both reindexings.
- The literal unshifted gate equation, applied twice and cancelled against
  the adjoint gate, gives the Kronecker identity needed by #7711's common
  transpose-sign theorem. Rank nonemptiness follows from gate unitarity and
  positive physical dimension.

The normalized-factor comparison uses the conjugated factors directly; no
additional matrix-square-root conjugation theorem or new SVD choice is needed.

## Contraction and remaining scope

`ConjugationSymmetry.lean` identifies coefficientwise conjugate periodic
operators by products and traces, conjugates the actual supplied open
standard form, and contracts both local equations through the two actual
circuit layers. Internal unitaries cancel their adjoints. No generic MPS
symmetry theorem is used. `Matrix.IsUnitaryBetween.map_star` handles both
rectangular unitary identities and is reused at three sites in two modules.

The contraction holds at every positive length of the supplied blocked
tensor. For a standard form of `blockTwo U`, these are original lengths
`2*N`. The parity issue in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex` prevents inferring an
unblocked all-length converse from that API. This audit does not claim that
its parity witness alone refutes the conjugation proposition.

The source node `prop1conj` and all new auxiliary nodes stay `notready`.
No unrestricted all-length equivalence, removal of the reduced-presentation
restriction, or kernel-checked proof is claimed. No parallel symmetry or
source/admissible predicate family, compatibility alias, sorry or axiom is
introduced. Issue #7017 remains open.

## Validation and hosted diagnostic repair

No local Lean build, elaboration, cache mutation or compilation is run, per
the user's instruction. The proof text remains uncompiled locally. Source
checks inspect the pinned Mathlib/QICLean rectangular map, adjoint,
reindex-multiplication, Kronecker-reindex, rank, isometry and trace APIs,
as well as the existing TNLean canonical-data and factor-comparison signatures.
Generated imports, tactic-pattern scan, TeX formatting, new-declaration tag
coverage, whitespace/line-length and proof-integrity scans are checked.
The repository-wide source Blueprint scan has 547 unresolved references
outside this addition; full synchronization and compiled checkdecls are not
claimed.

Hosted job `123398370707` found three errors in the initial contraction
draft. Repair `16f7fe07f` unfolds function composition under List.ofFn, uses
a shared universe-polymorphic unitary helper with explicit gate arguments,
and supplies the ring length to the circuit equality. Existing hosted logs
were used for that source repair. No new local Lean command was run.

## Hosted follow-up on `a754965fb`

Job `123406987298` compiled the supplied gate-comparison module and reported
`ConjugationSymmetry.lean:114,145`: the new tensor-level `mapStar` definition
remained opaque in the two `simpa only` calls. Both calls now explicitly
unfold `MPOTensor.mapStar`. No local Lean command was run; the repair still
requires exact-head hosted validation.
