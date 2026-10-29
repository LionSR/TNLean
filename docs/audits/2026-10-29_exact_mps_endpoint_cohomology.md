# Prescribed endpoint cohomology of an independent exact MPS phase

Source: arXiv:1010.3732, Sections II.C.1–2, II.F.2 (lines 929–993), and Appendix C.

The three new symmetry modules derive the endpoint obstruction from the actual
physical path theorem. No conclusion about virtual cohomology is included in
the physical phase predicate or supplied as an intermediate premise.

1. `PositiveRayVirtualCohomology.lean` uses the existing nonzero two- and
   three-site trace data to identify injective bond dimensions and reconstruct
   a scalar gauge. The gauge transports the virtual action without changing
   its factor system. If the two actions remove different physical characters,
   injective gauge-phase uniqueness forces their ratio to be one. Existing
   cocycle gauge independence then proves equality of their classes.
2. `ExactGroundPathEndpointClass.lean` compares prescribed endpoint actions
   with the representatives derived by `exists_constant_virtual_class`.
   It permits different endpoint bond dimensions and independent physical
   character changes; neither a continuous minimal gauge nor a transfer
   estimate is an input.
3. `ExactMPSPhaseCohomologyObstruction.lean` unpacks the independent phase
   definition. Its actual common blocking preserves injectivity and the
   virtual factor system. Each recorded physical isometry preserves
   injectivity; its physical intertwining identity gives covariance after
   the endpoint character is removed. The previous endpoint comparison
   yields equality of the prescribed original virtual classes. The final
   biconditional combines this implication with the existing forward
   construction on exactly the same endpoint domain.

The final theorem concerns one-site injective original endpoints with
prescribed exact virtual covariance, the domain of the existing forward
construction. It does not assert the unrestricted several-block
classification or the forward construction for arbitrary original scalar
symmetry characters. Those scopes remain recorded in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex` and
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.

Validation is source-only: declaration and dependency inspection, proof-integrity
scan, generated import check, tactic-pattern scan, prose checks, whitespace and
line-width checks, and Blueprint formatting. No local Lean command was run.
All four new Blueprint entries remain `notready`; hosted elaboration and
strict linters must accept the full dependent stack before proof completion
or source-theorem acceptance is claimed.
