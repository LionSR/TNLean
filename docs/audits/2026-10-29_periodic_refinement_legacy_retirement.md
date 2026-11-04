# Retire the refuted forward canonicalization premises

Issue #7762 asks for the corrected forward implication of DCCSP17,
arXiv:1708.00029, Theorem 4.1. Its corrected mathematical construction is
already on main in #9221, not an absent proof:

- `Fin.stepOrbitEquiv` and `Fin.exists_stepOrbit_phases` give the unique
  residue decomposition and phase redistribution, including wraparound.
- `IsPeriodic.exists_stepOrbit_blockDecomposition` and the actual unitary
  orbit decomposition supply prescribed blocking with the original sectors.
- `exists_unitWeight_periodic_presentation_of_blocked_sameMPV₂Pos`
  normalizes the arbitrary refinement input from its blocked comparison.
- `exists_isLeftCanonical_blockTensor_eq_toTensorFromBlocks` assembles
  the full multiplicity-bearing construction.
- `isPDivisibleChannel_of_isPRefinable_toTensorFromBlocks` proves the
  corrected forward implication for actual left-canonical periodic blocks
  with unit-modulus weights, without any further construction hypothesis.

The remaining loose end was a parallel obsolete route: four forward/root
premises refuted by the recorded scaling counterexample, reductions
between them, a conditional forward theorem and the old bundled
biconditional. They have no production consumers outside this obsolete
route. Remove them and the unused bundled module, and remove the
corresponding Blueprint nodes. Keep the meaningful equal-case application,
the actual refinement-isometry construction, and all bounded-root reverse
APIs. The corrected forward theorem and its proofs are unchanged.

The source error and its genuine counterexamples are retained in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. The note now
records the corrected forward result and retirement of the refuted route.
No deprecated aliases preserve the misleading theorem statements.

The converse remains explicitly conditional on compatible root selection
or a bounded-Kraus-rank root. Nothing here proves that every divisible
channel admits a root with the required physical Kraus size. Issue #664
and its separate paper-gap note remain open; the unrestricted printed
biconditional is not marked proved.

Native import generation, declaration synchronization, reference census,
prose, TeX formatting, ChkTeX, proof-integrity and diff checks cover this
deletion. No new Lean proof or hypothesis is introduced. No local Lean
build, elaboration or checkdecls was run, as requested; hosted acceptance
and integration of this cleanup remain pending, so #7762 stays open.
