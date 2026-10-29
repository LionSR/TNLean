# Actual physical-transpose transport for #7020

Source: `Papers/1703.09188/paper_v2.tex:1258–1288`, transposition subsection,
`prop:local-char-transposition` and `UUtransposetrick`.

## Delivered source construction

The literal physical tensor is `mapStar (physicalAdjointTensor U)`, proved
letterwise to exchange only the physical input/output. Its actual periodic
operators are transposes, its two source ranks are exchanged, and its reduced
canonical presentation retains exactly the same real diagonal boundary.
Simplicity follows from the actual exchanged-rank product.

At square source ranks, the actual physical-adjoint factor record is
conjugated entrywise. The real diagonal boundary is fixed under conjugation;
only that derived weight equality is used to retain its normalization.
No normalization, gate, transform or decomposition witness is assumed.
The actual factor fields are the conjugated old adjoint fields, so their
gates are exactly `vᵀ,uᵀ` in canonical exchanged-rank coordinates.

The square ranks are also derived from actual even-chain transposition
symmetry by the existing even-family virtual comparison. It forces the
exchanged ranks to agree; simplicity's product then forces both to be the
physical dimension. A final supplier derives these conditions internally
from that symmetry. No additional physical blocking occurs in this module.

## Scope and remaining obligations

This is actual transpose and source-factor transport, not the global/local
transposition equivalence. The general canonical and rank/simplicity
transports do not require a local gate certificate. The factor construction
uses square ranks explicitly; the symmetry supplier derives them. All
factors use the recorded canonical boundary. Arbitrary ambient presentations
remain covered by `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

The phase-sensitive forward local equations are now written as described
below. Their even-ring converse, arbitrary supplied standard forms, and the
phase-deformation conclusion remain. The
source transposition proposition and all new auxiliary tags remain
`notready`; #7020 stays open. The time-reversal construction and its
PropChiral scope are separate and unchanged in this isolated worktree.

## Dependencies and validation

Stacked on draft #10315, source base `36f753cb8`, to reuse its actual adjoint
factor normalization and even-family comparison; these prerequisite modules
compiled in hosted job `123474427200` on earlier unchanged source head
`6a7636710`. Current #10315 cut/local repairs have their own pending checks.
This new module is source-written and uncompiled.

No local Lean build, elaboration, compilation or cache mutation was run.
Validation is limited to pinned source APIs, generated imports, dependency
acyclicity, whole-repository declaration names, changed-declaration Blueprint
coverage, reader prose, tactic scan, TeX formatting, 100-column/whitespace
and proof-integrity checks.

## Hosted diagnostics on `441a34f6c`

Job `123488165005` checked the actual transpose operation, canonical data,
rank exchange and factor construction. It reported expected-type inference
inside the simplicity TFAE specialization and two residual opaque transpose
submatrix evaluations in the gate identities. The simplicity rank product
now has an explicit type, and the gate proofs finish their actual entry
identities by definitional reduction after the conjugation simplification.
No mathematical statement changes and no local Lean command was run.

## Actual even-family forward phase criterion

`TranspositionLocalNecessity.lean` now derives both source-factor gauge
equations from the actual even periodic family, using the transported
transpose record and the existing even-family FT. Transposing the second
relation and cancelling the coisometric gate gives
`(conj(Y)*X) ⊗ (conj(X)*Y) = 1`. The scalar Kronecker theorem supplies a
scalar matrix; unitarity gives its unit norm. Substituting it gives the actual
local phase certificate, with no assumed comparison gauge or transform.
Mathlib's existing `Matrix.mul_left_injective_of_inv` performs the cancellation.

For the standard form actually constructed from a simple reduced canonical
source, the coarse ranks derive the original rank identifications. The
existing four-original-spin dictionary then yields exactly
`V23(u₀⊗u₀)=c(x⊗xᵀ)V23ᵀ`, with `norm c=1`. Its finite-chain premise is
only on even lengths of `W=blockTwo U` (original multiples of four); no
extra physical block or odd-length symmetry is inserted. Exponential forms
are also written using the principal argument. This is pointwise existence,
not continuity of the argument choice.

The four new phase declarations remain source-written and uncompiled.
The actual even-ring converse and the explicit phase deformation are still
open. The full source proposition remains `notready` and #7020 remains open.
