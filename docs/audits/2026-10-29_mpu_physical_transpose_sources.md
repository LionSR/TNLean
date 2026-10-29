# Actual physical transpose and canonical local phase criterion for #7020

Current source state: actual factor transport, forward local phase and even-ring
converse for the chosen simple reduced canonical standard form are written.
The explicit phase deformation is also written on arbitrary supplied standard
forms. Unrestricted local criteria and exact-head hosted acceptance remain. Earlier stage-specific scope notes below describe
the transport and forward/converse pieces separately.

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

## Written actual even-ring converse

`TranspositionLocalSufficiency.lean` now derives both gauge relations from a
unit-modulus local phase with `X=x†` and `Y=conj(c)*conj(x)`. The scalar and
matrix unitarities are proved, not assumed as extra witnesses. The actual
normalized source/transpose records supply their own standard forms; the
existing periodic gauge cancellation then proves transposition symmetry on
every even ring. The literal four-original-spin converse transports only
that original antecedent through the existing rank/physical dictionary.

The final `standardForm_even_transposition_iff_exists_local_certificate`
combines this actual converse with the forward criterion for the chosen
simple reduced canonical source. Its RHS includes the rank identifications,
which are derived in the forward implication; no zero-index hypothesis is
added to the global side. This equivalence is source-written and uncompiled.
The unrestricted supplied-standard-form scope, explicit phase deformation
and exact-head hosted validation remain open; source and auxiliary Blueprint
nodes stay `notready` and #7020 stays open.

## Explicit phase deformation on actual supplied standard forms

`TranspositionPhaseDeformation.lean` writes the source path
`δ(t)=exp(-itφ/2)`, `u(t)=δ(t)u`, `W(t)=δ(t)W`, leaving the half factors
and shifted gate unchanged. The constructor proves both unitary gate
identities and the actual open tensor contraction. Its tensor and gate paths
are continuous and start at the originals. Every original transpose symmetry
is retained at exactly the same chain lengths by the actual MPO scalar law.
The literal four-spin equation has phase `exp(i(1-t)φ)`, hence phase one at
`t=1`, with the same virtual unitary and shifted gate.

This path result applies to any supplied standard form; it does not require
a canonical presentation, continuous choices of source factors, or a
continuous argument function. The initial real phase is fixed. All ten new
public declarations are source-written and remain uncompiled. The source
local-characterization scope outside the chosen canonical construction and
exact-head hosted acceptance remain open.

The child stack is refreshed onto parent #10315 head `e960a6cb9`. The four
rank transports in its transpose necessity proof use explicit entry
identities, matching the concrete canonical reindex defect diagnosed in the
adjoint parent. No statement or hypothesis changes, and no local Lean was run.

## Refreshed parent kernel-checking repair

Parent #10315 head `e960a6cb9` cleared the prior elaboration errors and
reached a deterministic kernel timeout on the coarse local certificate.
The parent splits its abstract normalized-source comparison from the large
coarse constructor. This child is refreshed onto the repair and uses explicit
canonical entry identities in both converse gate transports as well. No
mathematical statement or hypothesis changes. Hosted acceptance remains
pending and no local Lean was run.
