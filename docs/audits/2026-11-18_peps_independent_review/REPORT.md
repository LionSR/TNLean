# Independent PEPS migration review

Reviewed head: 5cef6f44c4334b7dd09acb47cf96eb2df7067d20
Base: b2c72008326f3166d3bcdc9e79013443142b0aa8
QIC: 729428582b78ab7529b3796099193649f947354a

Read-only source review of all 107 allocated production paths and three fixtures.
All changed declaration/proof hunks were examined, with focused full-statement
reads for scope-sensitive owners and the nine generic-helper call chain. The
unchanged AngularWholeCellInformationFromCollar helper was additionally read.
The author's ledger and f8e80bac five-fixture acceptance checklist were consulted.
There are no unexamined allocated paths; this is not a reproof of unchanged
mathematics or a kernel/elaboration result. During the review phase no build,
strict run, source edit, branch change, commit or push was performed. This
evidence-only publication records that review; it changes no production source
and claims no new Lean validation. Publication checks confirmed 110 unique
examined paths, the 107-path allocation plus three fixtures, all 110 source
hashes at the reviewed head, and agreement between the JSON and TSV ledgers.

## Findings

A1 (architecture cleanup, not a mathematical counterexample):
TNLean/PEPS/AreaLaw/GraphPropagation.lean:126-128 retains private `interaction`.
The input already is the canonical PlaneInteraction abbreviation; constructing
`⟨h.term, fun X => h.mem X⟩` is an identity adapter. Remove it and pass `h`
directly at lines 178, 201, 229 and 290, then verify those callers. This does
not introduce a different mathematical model, but retains an unnecessary
migration shim contrary to the requested single-path cleanup.

S1 (source style, not a claimed strict execution failure): six new lines exceed
100 characters:

- TNLean/PEPS/AreaLaw/Amplification/LatticeChannelSpatialOmission.lean:391 (102), 487 (104).
- TNLean/PEPS/AreaLaw/BoundaryTheorem.lean:427 (102).
- TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean:137 (104), 299 (101).
- scripts/generic_gap_boundary_regression.lean:75 (108).

No mathematical narrowing was found in the inspected migration delta. This is a
source-review conclusion, not a claim that every migrated application elaborates.

## Scope reasoning

The old LocalHamiltonian structure has exactly term, supported, hermitian and
norm_le fields. PlaneInteraction supplies term/mem, and the added explicit
Hermitian/norm premises recover the other two fields without imposing a new
restriction. Universal and existential signatures retain those data adjacent to
the same interaction, before E0/state parameters; global constants remain chosen
before domain/interaction. Support indices and the finite sum are unchanged.
Dropping unused term hypotheses from algebraic and norm-only statements broadens
them; it does not remove an original conclusion.

RangeSquare keeps the broad normalized projector-positive/member triple. Its
square conversion feeds total original Hermiticity into projector transport and
separately proves Hermitian-part term facts; it does not demand original
termwise Hermiticity. Canonical and pinned zero-floor statements preserve all
natural m and q, arbitrary J and gap, explicit maximality, nonzero output norm,
normalization, absolute energy error and gap-weighted fidelity. The latter stays
vacuous at zero gap, rather than becoming an unweighted overlap guarantee.

All four BoundaryTheorem generic bounds and the nine helper chain keep arbitrary
gap PSD/member input. Positive-gap wrappers use the canonical uniqueness bridge
only with their existing positive-gap premise. AmplificationProof explicitly
preserves the q=0/J<0 empty-domain branch and derives a nonnegative budget only
from an actual support when the domain is nonempty.

Box values retain the same existential physical data, safety and size constraints.
BoxEntropySupremum retains hbox and positive exponent with the explicit entropy
upper bound; TemplateSourceEntropy calls the bound using Q.one_le_size. No
unconditional nonpositive-gap entropy theorem is asserted.

Scanner normalization now passes J explicitly to positiveTerm,
truncatedEnergyTerm and actualEnergyTerms, since J is no longer in the object
type. The examined consumers consistently pass the same budget. Existing
spectral, spectator, geometric, time/integrability and truncation conclusions
are retained. SourceScanner keeps projectorGap/member fields.

## Fixtures and remaining gate

The range fixture is unchanged and still invokes the production square-to-range
conversion with an explicit one-site q=2 zero-gap target. The migrated generic
fixture retains the independent-vector non-singleton proof and all four
conditional generic-bound checks. The box fixture retains a size-one rectangle
with empty physical intersection, r=0 emptiness/supremum assertions, and he/hbox
with the explicit entropy conclusion. No fixture was deleted.

review.json and paths.tsv record all 110 paths with examined/issues/blocked
fields. Every path records exact-pin Lean/strict as unrun, not passed. The source
review does not replace final integrated builds, all five complete fixture runs,
selectors or CI; the other two fixtures belong to the shared/MPS lanes.
