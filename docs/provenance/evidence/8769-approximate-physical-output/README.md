# Approximate original gates and physical output

Source revision: `1213a68ed511bf20c357b72f4ac5a03078b7c677`.
Parent revision: `0fa31ddad11ab7a8f06a3a34f1381c3ff974e8bf`.
QICLean remains pinned to `caac4b549c1b5c14fcedbee647567f51e27b296d`.

## Mathematical scope

For each recorded original gate occurrence, the approximation data consist of
its original contraction and an actual ordered monomial expansion with local
operator error at most δ. The approximate sum need not itself be contractive.
Dividing its coefficients by 1+δ constructs a contraction circuit on the same
register layouts. The construction preserves its monomials, participating
sets and lifetime counts, and does not increase absolute coefficient sums.
Its chronological operator error is at most 2δN, where N counts the original
nonprivate occurrences. For an input of norm at most one, the corresponding
physical trace-norm error is at most 4δN, independently of private dimensions.
One fixed integer accuracy exponent suffices for every real inverse-power
target at all sizes L ≥ 2. The coefficient-bound results derive the required
absolute sums from bounds on the actual list lengths and individual coefficients.

The physical-output construction exchanges the retained auxiliary registers
with the original physical registers using an actual source-free permutation.
It preserves original gate and source occurrences, their branch labels,
coefficients, endpoint spaces and vectors. Its coordinate identity exchanges
only the order of the two discarded factors. Their partial trace therefore
agrees exactly with the earlier replacement physical density, and the same
original gate-count error bound applies. Every constructed auxiliary register
is finite-dimensional. Original private registers retain precisely the paper's
finite-dimensionality assumption, without a numerical dimension bound.
No positivity is claimed for arbitrary sampled source operators. Tensor-network
representation and the subsequent assembly of these results remain separate.

## Source preservation

The twelve new modules contribute 74 declarations. The seventy-fifth is the
existing two-factor composition estimate, made public in `EffectCircuitError`.
Its signature and proof are unchanged. The identical duplicate in
`ApproximateCircuitError` is removed, so both chronological error arguments use
the same theorem. Apart from this promotion and duplicate removal, the frozen
source proofs are unchanged; canonical provenance notices are comments only.
The legal headers of the incoming files are preserved. The four physical-output
modules originate at source commit `f15416476c61b343f79d19602dffe8b5489a49f0`;
their earlier evidence was published at `ce14f5d903d8e83f9c5bba3fe0ef32f0113b4994`.
Original source snapshots and earlier approximate-gate, regression and
physical-output evidence are retained in compressed form.

Only the verification fields of the eleven inherited `EffectCircuitError`
provenance entries are refreshed. Their previous shard and verification records
are preserved. No dependency pins or predecessor evidence are overwritten.

## Verification

All 28 modules in the affected import closure, including the root aggregators,
were checked directly with the pinned Lean compiler, package options and
warnings as errors. Every check returned zero with no diagnostics; total
recorded compilation time was 147.836 seconds. The imported audit covers all
75 new public declarations and all eleven inherited declarations in the changed
module. All 86 depend only on `propext`, `Classical.choice` and `Quot.sound`.
The 14,719 actual imported artifacts were hashed and rechecked at the source pin.

Four unchanged regression theorems were rebuilt and audited independently:
a scalar approximate sum has norm two although its original target is the
identity; it satisfies the local approximation assumptions; two repeated
empty-participant gates remain distinct occurrences; and rescaling gives
exactly the identity. Their audit records 4,966 imported artifacts.

The verification uses immutable dependency artifacts and a separate temporary
output directory. It is direct Lean verification, not a local Lake build or a
`leanblueprint checkdecls` invocation. No Mathlib build or shared-cache mutation
was performed. A direct imported-root check confirms all 21,376 synchronized
blueprint declaration names.

The two new chapters contain all 75 declarations exactly once. Full source
synchronization passes with 21,243 blueprint entries and 44,265 Lean declarations;
the full dependency graph has no cycle or duplicate label. The focused PDF has
63 pages. All new pages, PDF pages 58–62, were inspected visually. Seven web pages
with 5,156 mathematical expressions passed the browser checks. One inherited
0.99057-point overfull heading in the common-source chapter is unchanged; there
are no new overfull boxes. The copied TNLean and QICLean source files are checked
against their exact committed trees.

The canonical provenance checker validates all 1,084 entries, including the
75 new records and the eleven refreshed records. `validate-evidence.py` checks
the archived hashes, exact committed source bytes, complete audit scope,
inherited-record preservation and blueprint records without compiling Lean.
The recorded scripts reproduce individual checks when the recorded dependency
artifacts are available; they do not fetch or rebuild dependencies.
