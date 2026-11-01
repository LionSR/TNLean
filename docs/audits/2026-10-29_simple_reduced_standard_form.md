# Simple reduced MPU representatives at the original scale

Addresses #7127. Sources: arXiv:1703.09188, canonical-form discussion and
Definition III.2, lines 257–374; Theorem III.8, `StandardForm`, and `SF`,
lines 563–622. The corrected literal source gates are the existing
`sourceU = Y₂ Y₁` and `sourceV = X₁ X₂` definitions.

The existing reduced canonical representative preserved every positive-length
periodic operator but did not assert simplicity at the original physical scale.
The new proof uses the normal-target reduction theorem to obtain an actual
rectangular reduction of every open word. It does not infer local identities
from periodic equality without this structural step.

`SimpleReduction.lean` carries this reduction through doubled open words by
applying the existing rectangular double-layer identity to physical blocks.
The source simplicity identity permits inserting the normalized diagonal
between two letters. Its reduction uses only two- and three-letter doubled
words. For a canonical target, its already established rank-one transfer power
then supplies the rank-one insertion in `simple2`. This transfer power is an
internal matrix identity; the target tensor is not physically blocked again.

`SimpleCanonicalRepresentative.lean` derives a simple canonical representative
of positive bond dimension at most the original dimension, equal to the input
at every positive periodic length. Its final theorem returns the existing
`TwoSiteStandardFormData (blockTwo V)` with the literal source gates of `V`.
The input assumptions are only positive physical/bond dimension and simplicity.
There is no supplied canonical presentation, full-support hypothesis, prescribed
factor witness, or gauge between unequal bond spaces.

Reuse: existing private doubled rectangular helpers become public at their
original owner. The positive-power insertion proof is extracted at its existing
owner and reused by both the old supplied-witness theorem and the new reduction
argument. No compatibility aliases or parallel source predicates are introduced.

Validation: source and diff checks, generated import checks, blueprint declaration
coverage, reader-facing prose checks, theorem-role checks, and the tactic scan.
No local Lean/Lake command was run. The hosted full build passed at the
merged head `ed6f043b00a742a112a92bb71fd62efd4f445535` (job 124454337247),
after the auto-fix to `SimpleReduction.lean`, with no `sorry` in the new
declarations, so the six new blueprint entries are `\leanok`. An earlier
build at `fcb226ee` predates that fix and is not the verifying record.
#7127 stays open pending integration.
