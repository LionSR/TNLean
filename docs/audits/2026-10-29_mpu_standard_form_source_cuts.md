# Actual standard-form source cuts and local time reversal for #7020

## Current written scope (supersedes the earlier staged notes below)

The local-certificate theorem now assumes symmetry only at even lengths of
`W=blockTwo U`, exactly the source's two-original-spins-per-site convention.
The earlier stronger even-original-length premise is removed, without adding
another physical block. `EvenFamilySourceGauges.lean` derives the unblocked
sign gauge, preserves cut ranks under that sign, constructs the actual scaled
source record, applies the existing normalized factor comparison, and
transports the resulting unitaries back. Since the source U gate contracts
two right factors, the sign contributes its square and cancels. Source V is
unchanged. The zero-index derivation and all three literal certificate/supplier
theorems now use this actual even-family comparison. No local certificate,
gauge, rank, normalization or inverse witness is assumed.

The actual even-ring converse is now written as well. Arbitrary normalized
records at the canonical weight supply standard-form data with their own
gates by comparison with the selected record of the same tensor. The local
sign equation gives both adjoint gauge equations with `X=x†`, `Y=σx`.
The actual source/adjoint records then contract on every even ring through
`TwoSiteStandardFormData.mpo_eq_of_gate_gauges`. The literal four-spin
converse transports its antecedent with the existing explicit dictionary.
A final equivalence combines this with the forward theorem; the forward
implication derives the rank identifications appearing on its right side.

Remaining: arbitrary supplied standard-form presentations, transposition,
and exact-head hosted validation. The chosen simple reduced
canonical construction remains a load-bearing restriction. The exact source
proposition and auxiliary Blueprint entries all remain `notready`; #7020 stays
open. The new phase/factor/assembly/converse proofs are source-written and uncompiled.
No local Lean build, elaboration, compilation or cache mutation was run.

Source review also found that rank relabeling already belongs to
`FundamentalTheoremGatesBlocked.lean`. The redundant definition from the new
source-cut module is removed; the final pointwise supplier reuses the existing
`TwoSiteStandardFormData.reindexRanks`. No compatibility alias is introduced.

The converse is written in `TimeReversalLocalSufficiency.lean`. It does not
require a supplied standard-form transform or opaque decomposition witness.
The local antecedent still acts on exactly four original spins. The two-site
block used while closing the conclusion only identifies the even periodic
ring; it is not a new eight-spin local hypothesis. The arbitrary-record
standard-form supplier lives in `SourceFactorsStandardForm.lean`.

## Earlier staged source audit


Source: `Papers/1703.09188/paper_v2.tex:1237–1252`, proof of `PropChiral`,
particularly the blocked standard-form comparison `eq:block-twosites`.

## Delivered algebra

For actual supplied two-site data `S : TwoSiteStandardFormData W u v`,
with `W` of physical dimension `d*d`, the new module constructs four explicit
matrices factoring the two cuts of `W` itself. Their pair-index intermediate
spaces have cardinalities `d*r` and `ℓ*d`; no zero-index assumption is needed. The source-cut identities use only the actual
open contraction; there is no assumed gauge, local certificate, or existence
premise asserting the missing comparison.

The two right factors contract to exactly `staircaseMiddle v * (u ⊗ u)`.
The two left factors contract to exactly `staircaseMiddle v`. Both act on
four original `d`-dimensional spins. Taking source cuts after first blocking
`W` again would act on eight original spins and is not substituted for the
source's four-spin local equation.

The actual canonical-source standard form also has both required coarse
left-factor normalizations. The first is `I_d ⊗ X₁`, after regrouping its
physical coordinates, and the second is `X₂ ⊗ I_d`. Their weighted and
ordinary isometries follow by Kronecker multiplication from the original
recorded source-factor fields. The two public canonical corollaries assume
no new normalization witnesses.

The actual rank identifications now follow from existing blocking-rank
saturation and persistence of simplicity. The block-one physical equivalence
is explicit, and the two-site rank calculation passes through the exact
`blockTwo`/direct-block-two coordinate equivalence. No endpoint rank product
is assumed: both are derived from canonical simple-block equivalence.

The new `twoSiteSourceFactors` record retains the original canonical boundary.
Its right factors have full row rank because each actual cut factors through
its pair space and that space has exactly the actual cut rank. Mathlib's
finite-dimensional range and matrix right-inverse theorems then construct the
two right inverses. Thus the whole normalized record is now derived, with no
normalization, inverse, rank or gauge-existence witness added as an input.

The necessary zero-index rank conclusion is also derived, with its input
stated at the even original lengths. Adjoint invariance of `mpo U (2*N)`
compares the direct two-site block of U with its physical adjoint. Existing
same-family canonical FT identifies the ranks; adjunction exchanges them.
The proved growth formulas give `d*r = ℓ*d`; canceling the positive d gives
`r=ℓ`, and simplicity's `r*ℓ=d*d` then gives `r=ℓ=d`. The canonical datum
for the direct block is constructed by the existing blocking theorem and
its adjoint by the existing physical-adjoint theorem; neither is an input
witness. Only one two-site blocking is used, and no odd-length symmetry is
inferred.

## Remaining source steps

The forward certificate below is restricted to symmetry at every even
original length. The source proposition only assumes symmetry at even
standard-form lengths, corresponding to original multiples of four. Removing
this load-bearing restriction requires a phase-sensitive even-family FT
and descent before constructing gates. The mathematical scalar witness and
elimination plan are recorded in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`.

Arbitrary supplied standard forms, the converse and the transposition
criterion also remain. The exact and admissible Blueprint propositions
remain `notready`; #7020 stays open. The full-support restriction is recorded
in `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## Validation

No local Lean build, elaboration, compilation or cache mutation was run,
per user instruction. These proofs remain uncompiled. Pinned source APIs,
generated imports, changed-declaration Blueprint coverage, tactic-pattern
scan, TeX formatting, whitespace/100-column and placeholder scans are
source-only checks. The promoted `Finset.sum_congr₂` helper is reused.

## Actual adjoint-factor extension

`SourceFactorsPhysicalAdjoint.lean` transports both source Y Gram formulas
from the selected factors to every normalized supplied record at the same
canonical boundary. The private cut-cancellation proof uses the actual
right inverse to identify the left-factor ranges. The common normalization
then makes the comparison coisometric, so scalar Y Gram matrices agree.
No gauge or physical-closure witness is assumed. Canonical simplicity of
the physical adjoint is derived by the rank-product criterion and cut
exchange, and its two previous duplicated proofs are replaced.

At zero index the scalar constants are one. Swapping cuts and taking
adjoints constructs the actual physical-adjoint record from Y†/X†; its
right inverses are the old X isometry/weighted-isometry identities. Both
gate adjoint identities are written explicitly. Canonical physical
reindexing preserves the recorded boundary, so the actual `blockTwo` datum
and its adjoint coarse record are now constructed with no extra canonical,
normalization, rank or simplicity witness. The exact local gauge/sign
consequence still needs the final Fundamental Theorem contraction.

## Hosted diagnostics on `3951cb53f`

Job `123429251031` reported namespace shadowing of raw tensor operations,
partially unfolded four-leg matrix expressions, spectator identity entries,
cardinality normalization and an existential elimination into the source
record's Type. The repair qualifies raw MPO operations, uses explicit
matrix entry formulas, resolves spectator cases and actual rank equivalences,
and uses `Classical.choose` for the right inverses. These are source repairs;
new extension proofs and the repaired head remain uncompiled pending hosted
validation. No local Lean command was run.

## Hosted diagnostics on stacked `0f8c0d5c4`

Job `123436139104` accepted the canonical physical reindex construction,
then found namespace shadowing in the promoted simplicity declaration,
a parenthesis mismatch in the normalized-cut calculation, and continuation
syntax in the selected first Y-Gram application. The raw tensor operation
is qualified and the two explicit proof expressions are corrected; reported
unused map simplifications are removed. Blueprint job `123436138960`
rejected a raw equation-label citation in prose; it is replaced by the
source line reference. These repairs still await exact-head hosted checks.

## Written literal forward certificate

`TimeReversalLocalNecessity.lean` now derives the coarse certificate from
actual even-original-length family equality using the arbitrary supplied-
factor Fundamental Theorem. This is a genuine dependency on draft #10303,
so #10315 is stacked on its current branch; #10311 remains independent.
The two gauge equations give `(YX) ⊗ (XY)=I` after cancelling the actual
coisometric coarse gate. The existing scalar Kronecker lemma gives reciprocal
scalar matrices; unitarity then makes the scalar equal to its inverse and
hence ±1. No local certificate or gauge-existence premise is assumed.

The explicit four-spin coordinate dictionary is also written. Coarse-rank
identifications compose with the source pair encodings, and the original
source-rank equalities give their exact physical-pair encodings. Reindexing
the middle and unshifted layers identifies the actual coarse gates with
`V23(u₀⊗u₀)` and `V23` for the original selected gates transported only by
the derived canonical rank equalities. Transporting the actual coarse sign
certificate back therefore gives the literal four-original-spin equation.

This completes the written restricted forward argument for the constructed
simple reduced canonical source standard form under symmetry at every even
original length. It does not establish unrestricted
arbitrary supplied standard forms, the converse, transposition or kernel
acceptance. All source and auxiliary Blueprint nodes remain `notready`, and
#7020 stays open. The whole extension is source-only and awaits hosted
verification; no local Lean commands were run.

The actual pointwise supplier is also written:
`exists_twoSiteStandardFormData_timeReversal_certificate` returns the square
standard-form record and its derived literal certificate together. The
record is constructed by `TwoSiteStandardFormData.reindexRanks` from the
existing half factors, rather than assumed. This discharges the pointwise
certificate/data premise of the intrinsic-sign theorem for these constructed
canonical source forms. No continuity of gates, factors, gauges or sign
witnesses is required for that application. An unrestricted source path
still needs the availability of these source presentations pointwise.

The length hypothesis is load-bearing: the premise is on U at every even
original length 2N, so its supplied standard-form tensor W=blockTwo U has
adjoint symmetry at every blocked length N>1. This argument does not replace
that premise by symmetry only at even lengths of W, which would amount to
original lengths divisible by four. No such stronger deduction is claimed.

The one-site-blocking physical relabeling step reached three occurrences
across the identity-index, injective-index and new coarse-rank proofs. It is
promoted at its existing `PhysicalBlocking` owner and both identical private
helpers are removed. The final dictionary's finite-pair arithmetic uses the
pinned encoding literally as `s + r*a`, then the derived rank equality;
no alternate index convention is introduced.

## Length-scope audit and prerequisite repair

The module scope marker, Blueprint statement, and parity paper-gap note now
explicitly distinguish even original lengths from even standard-form lengths.
The scalar example `U=exp(i*pi/4)`, `W=U₂=i`, `u=i`, `v=1` has the latter
symmetry and a negative local sign, while violating our stronger input.
The remaining descent must retain an unblocked phase `η` with `η²=1`;
its square cancels in the two-letter source gate. Another gate-level block
would change the required four-spin equation and does not resolve this step.
The stack also incorporates #10303's explicit inverse-reindex cancellation
repair from `0d5a17aee`; exact-head hosted verification is still pending.

## Written even-family virtual descent

`EvenFamilyVirtualGauge.lean` now proves an actual unblocked virtual gauge
with sign from equality of the even periodic families. No new family/gauge
existence premise is introduced and no additional physical blocking occurs.
The existing normal overlap dichotomy rules out vanishing cross-overlap
because along `2*n` the cross-overlap is the self-overlap and tends to one.
Its other branch supplies an invertible gauge and unit phase. A nonzero
length-two periodic vector forces the phase square to one. Existing
canonical irreducible normalization then makes the virtual gauge unitary
while retaining the sign. The scalar must still be threaded through the
source-factor comparison before this removes the local criterion's length
restriction. The new theorem is source-written and uncompiled.

## Actual scalar factor transport

`SourceFactorsScalar.lean` now constructs the actual scaled normalized record:
keep both X factors, scale both Y factors by `c`, and scale both Z factors by
`c⁻¹`. Nonzero scaling preserves the two exact cut ranks. Its public gate
identities prove that the transported source U gate is `c²` times the old
gate in canonical rank coordinates, while source V is unchanged. Thus the
new even-family virtual sign does cancel in the actual gate contractions;
no gate equality is added as a premise. The assembly with the existing
unitary factor comparison remains to be written and verified.

## Hosted diagnostics on `263232656`

Job `123461441038` reached the scalar transport module and reported unknown
`sourceU`/`sourceV` identifiers: its dependency closure did not include their
owner. The import now names `SourceUV` directly. The record-construction
proofs reported no errors in this run; dependent phase/assembly modules did
not receive successful exact-head verification. This is a source repair;
no local Lean commands were run.

## Hosted diagnostics on `80c8951d6`

Job `123467082476` accepted the scalar record construction and then found
an incompletely unfolded reindex in `sourceU_smul`: the right side was still
an opaque gate evaluation, so the sum rewrite did not match. The proof now
changes the entry goal directly to its fully scalar two-factor sum before
extracting the common scalar. No source statement changes. The subsequent
phase/local/converse modules still await hosted verification; no local Lean
command was run.

## Hosted diagnostics on `f3d8d96a2`

Job `123470118050` compiled `SourceFactorsScalar`, including both gate
transport identities. The next diagnostic is field notation on the explicitly
quantified eventual cross/self-overlap equality. The proof now invokes
`Filter.EventuallyEq.symm` explicitly, with the same mathematical limit
argument. The subsequent local/converse closure remains pending. No local
Lean build, elaboration, compilation or cache mutation was run.

## Hosted diagnostics on `6a7636710`

Job `123474427200` compiled the actual even-family virtual theorem, normalized
physical-adjoint factors, arbitrary normalized-record standard-form supplier,
and even-family supplied-gate comparison. The remaining failure reached the
actual source cuts: a triple sum was reordered by a transposition instead of
a cycle; the block/rank proof exposed a raw lambda instead of the physical
reindex operation; matrix equality used a pointwise adjoint rewrite; and the
file had an extra namespace terminator. These source issues are repaired,
reported unused simp arguments removed, and the same matrix-level adjoint
rewrite/qualified raw tensor operations are applied at the dependent local
sites. No hypothesis or conclusion changes; no local Lean commands.

## Hosted diagnostics on `1e269afe1`

Job `123481504409` compiled the entire actual source-cut/rank/normalized-record
module. The next failure reached the final necessity module: an unnecessary
`dsimp`, an untyped second finite-pair equivalence, and an opaque local adjoint
factor alias before the two gate rewrites. The source now removes the empty
simplification, specifies both pair dimensions, and unfolds exactly that
factor alias before applying the existing gate identities. The converse has
not yet been accepted; no local Lean command was run.

## Hosted diagnostics on `36f753cb8`

Job `123487768537` found dependent rewriting of a source-rank natural inside
finite-index coercions, two nested reindex conversions, and the canonical
weight alias in the final necessity comparison. The proof now applies the
rank equality to an explicit natural-valued function, composes the matrix
linear equivalences with their existing composition theorem, and types the
actual coarse factor record at the coarse canonical boundary from the start.
This preserves all statements and uses no local Lean commands. Necessity and
converse acceptance remains pending.

## Hosted diagnostics on `fef804677`

Job `123518221809` accepted the four-spin dictionary and reached the last
two necessity comparisons. Their only diagnostics were unresolved nested
canonical rank reindexings. Four explicit matrix entry identities now
identify those two actual adjoint and two actual FT transports before the
gauge equations are used. They preserve all source assumptions/conclusions
and do not replace a mathematical comparison by an input witness. No local
Lean commands were run; the final necessity/converse gate remains pending.

## Kernel checking on `e960a6cb9`

Hosted job `123531678652` cleared the two rank-transport type mismatches.
Its only primary failure was a deterministic kernel timeout checking
`exists_coarse_timeReversal_certificate`; the later unknown constant was a
cascade. The actual normalized-source adjoint comparison is now a private
theorem over an abstract source record. The public coarse wrapper derives
its actual ranks and applies that theorem, so the large coarse constructor
is no longer unfolded throughout the generic comparison proof. Statements
and hypotheses are unchanged; no local Lean command was run.
