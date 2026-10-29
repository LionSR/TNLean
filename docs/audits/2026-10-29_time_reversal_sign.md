# Intrinsic time-reversal sign invariance for #9880

Source: `Papers/1703.09188/paper_v2.tex:1595–1631`, equation
`eq:sigma-from-trace` and Proposition `prop:sigma-well-defined`.

## Mathematical proof text delivered

`timeReversalSign` is the normalized four-spin gate trace. The local
certificate for an actual supplied two-site standard form determines this
value by cancelling the middle gate against its adjoint and applying the
existing scaled swap-trace identity. No input assumes the trace formula.

The decisive identity is intrinsic. For pair exchange `P` and middle gate
`V`, the actual shifted layer at two blocks is `P V P V`. The actual
periodic operator is therefore `P V P V (u ⊗ u)`. Cyclicity and `P²=1`
give

    tr(P U_W(2)) = tr(V P V (u ⊗ u)) = tr(P V (u ⊗ u) V).

`TwoSiteStandardFormData.timeReversalTrace_eq_periodicTrace` derives this
from the actual finite-ring contraction, with the four-site index order
checked explicitly. The normalized expression consequently depends only
on `mpo W 2`. Representative independence permits different ambient bond
dimensions and assumes only equality of that actual finite-chain operator.
It needs no canonical form, same-bond comparison, rank identification or
Fundamental Theorem.

`continuous_intrinsicTimeReversalSign` proves continuity directly in the
actual tensor by the finite word-product formula. The path theorem needs
only a continuous tensor path and pointwise actual square standard forms
with the literal local certificate. The witnesses need not vary
continuously. Their pointwise sign extraction puts the intrinsic continuous
value in `{1,-1}`; Mathlib's preconnected square-one theorem gives constancy.

The earlier same-bond canonical source-factor comparison and supplied
continuous-gate path theorem are removed, rather than retained as aliases.
The new proof has no dependency on draft #10303 and is based directly on main.
The existing `timeReversalTrace_gauge` remains useful trace algebra and is
not duplicated.

## Scope and remaining obligations

The gate-to-intrinsic identity is for actual supplied square two-site
standard forms. It describes two physical blocks, or four original spins;
no additional blocking or odd-length conclusion is hidden. Representative
independence is unconditional once these actual standard forms are supplied.

The path theorem still needs pointwise local time-reversal certificates.
Deriving those from global time reversal is #7020; it is not added here as
an existence theorem or a new source-predicate family. General availability
of the required square standard forms remains subject to the reduced/full-
support restriction in `docs/paper-gaps/mpu_canonical_form_full_support.tex`.
Both source and admissible umbrella Blueprint nodes remain `notready`.
The new auxiliary entries are also `notready` pending kernel verification.
Issue #9880 remains open.

## Validation boundary

No local Lean build, elaboration, compilation or cache mutation was run.
These proofs are uncompiled. Source checks inspect pinned reindex, trace,
continuity and preconnectedness APIs. Exact integer coordinate sanity checks
for arbitrary gates at dimensions 1, 2 and 3 agree with the shifted-layer and
trace identities; these are not proof verification. Generated imports,
tactic-pattern scan, declaration Blueprint coverage, TeX formatting,
whitespace/100-column and placeholder scans are source-only checks.

## Hosted diagnostics on `4bd1b8735`

Job `123420319446` reported two errors in the sign-extraction prerequisite:
conjugating the spectator Kronecker deltas needed explicit equality cases,
and the reindex/smul simplification needed the linear-equivalence coercion
and Kronecker transport as a separate equality. Both are repaired in source;
the reported unused simp arguments and proof-local `letI` warning are also
removed. The intrinsic module was not reached by this failed job, so no
kernel acceptance for its proof is inferred. No local Lean command was run.

## Main integration on 2026-10-29

Merged `origin/main` at `55b8f9d56d909a1d32d58dad3a2b25ed967128c6`.
The chapter conflict retained all intrinsic-trace and pointwise-certificate
results and their scope. Supporting statements use the current mathematical
role classification; both independent tactic-ledger entries were retained.
The two sign Lean modules are byte-for-byte unchanged from the previously
accepted `4695979e5` head. Role application/check and its eight Python tests,
import generation, reader prose, declaration coverage, TeX formatting,
ChkTeX and whitespace checks were run. Combined-head hosted checks remain
pending; no local Lean or PDF/web build was run.
