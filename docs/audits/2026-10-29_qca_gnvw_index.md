# Homogeneous GNVW index from the actual support factors

Issue #7039, stacked on draft #10332 (`efdeb443a`), using current main
`fef336fe11c51e82136111e58af90e22cfbaf9e6`. No overlapping QCA-index PR
was present among the 100 current open PRs at the start of this work.

`GNVWIndex.lean` chooses the coherent positive matrix-size family already
derived for the actual support algebras. Its positivity, full-matrix
presentations and both size identities come from #10332, rather than new
hypotheses. It defines one index at cut zero in the exact carrier
`{q : ℚ // 0 < q}`, importing Mathlib's positive ordered-field group.

Cancelling the common positive odd size in the two actual product
identities makes even sizes constant between consecutive cuts. Integer
induction in both directions gives independence of every integer cut.
All three source dimtransfer ratios follow. A matrix presentation at
any actual even support algebra computes the same index by the existing
matrix-algebra equivalence size theorem, so the construction does not
assume presentation independence.

The source is GNVW arXiv:0910.3675v2, equation dimtransfer, lines 1317–1329.
The standing data are a positive homogeneous physical dimension, an actual
star-automorphism, and its supplied nearest-neighbour presentation. No
translation covariance or bundled IsQCA premise is used. The existing
homogeneous-chain scope note remains load-bearing. This is independence
of the integer cut in that presentation, not independence of arbitrary
regrouping or cell structures.

`KroneckerSupportAlgebra.lean` supplies reusable coefficient calculations
for the full left and right tensor factors: full support on that factor
and scalar support on its spectator. The configuration-cardinality
lemma in LocalAlgebra identifies a pair's matrix size with d², including
the general zero-dimension case for the cardinality identity itself.

Remaining in #7039: the direct finite image calculations for translations
by -1 and +1, and their d and d⁻¹ index values. These are not assumed or
claimed by the current ratio layer. The source shift moves observables
left and is translation by -1, not by +1.

The induced stabilized MPU QCA and its local evaluation required by #7040
are not yet present in the current QCA source tree. The existing
CompatibleLocalAutomorphism API supplies generic completion only; it does
not establish the actual MPU support equality. No comparison theorem is
manufactured by adding that equality as a hypothesis.

Validation is source-only: generated imports, reader-facing prose,
Blueprint formatting, whitespace and integrity checks. No local Lean
invocation, build, cache mutation or checkdecls, as requested. New Blueprint
entries remain notready. The stacked source is not yet hosted-verified.
