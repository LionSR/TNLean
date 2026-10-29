# Supplied-source time-reversal sign invariance for #9880

Source: `Papers/1703.09188/paper_v2.tex:1595–1631`, equation
`eq:sigma-from-trace` and Proposition `prop:sigma-well-defined`.
This work is stacked on draft #10303 at `a754965fb`, reusing its arbitrary
supplied-factor Fundamental Theorem instead of duplicating that proof.

## Mathematical proof text delivered

`timeReversalSign` is the source's normalized four-site trace. The local
time-reversal equation for an actual supplied two-site standard form determines
this value: cancel the middle gate against its adjoint, then apply the
existing scaled swap-trace identity. The normalization is nonzero for `d>0`.
This extracts the actual sign without a hypothesis that assumes the trace
formula itself.

`IsMPUCanonicalFormII.source_timeReversalSign_eq_of_mpo_eq` derives equality
of the normalized expressions for two actual supplied source representatives
of the same finite-chain MPU. It applies the supplied-factor Fundamental
Theorem to equality of periodic operators at every `N>1`, obtains the two
gate gauges, and transports them through the canonical rank identifications.
Only then does it reuse `timeReversalTrace_gauge`. The gauge-existence clause
is proved, not an input. The old trace algebra is not reproved.

`continuous_timeReversalSign` proves polynomial continuity of the expression
in the actual gates. `timeReversalSign_eq_on_supplied_path` applies this to
continuous gates of actual supplied standard forms. The literal local
time-reversal equation at each point gives a value in `{1,-1}`. Mathlib's
preconnected-square-one theorem then gives constancy. The local unitary and
sign witnesses need not vary continuously.

## Scope and remaining obligations

Representative independence is proved for reduced canonical-form-II tensors
in the same ambient bond dimension and zero-index coordinates, with both
source ranks equal to physical dimension. The supplied source gates are
assumed unitary as in the standard form. The theorem does not construct a
reduced presentation for arbitrary padded tensors or derive those rank
equalities from global time-reversal symmetry.

The path theorem requires actual continuous supplied gates and the pointwise
literal local time-reversal equation. It does not add an axiom or hypothesis
asserting the existence of a missing continuous supplier. Instead it states
the supplied-path theorem explicitly. No Lean admissible-source path datum
currently provides those continuous suppliers from a bare continuous MPU
path; the existing datum in the Blueprint and gap note remains a mathematical
target. The local characterization deriving the certificate from global
time reversal also remains a prerequisite for that unrestricted deduction.

The restrictions are documented in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. Both the unrestricted
and existing admissible umbrella nodes stay `notready`; the three new scoped
auxiliary entries also stay `notready` pending compilation. No parallel
symmetry predicate family or compatibility alias is added. Issue #9880 stays
open.

## Validation boundary

No local Lean build, compilation, elaboration or cache mutation is run, per
the user's explicit instruction. These are uncompiled proofs. Source checks
inspect pinned Matrix reindex/unitary/trace APIs, the existing swap-trace
theorem, rectangular and Kronecker continuity, and Mathlib's preconnected
square-one theorem. Generated imports, tactic-pattern scan, new-declaration
Blueprint coverage, TeX formatting, whitespace/100-column checks and the
proof-integrity placeholder scan are checked. These do not establish kernel
acceptance. The stacked #10303 dependency has no successful exact-head Lean
validation claimed here.
