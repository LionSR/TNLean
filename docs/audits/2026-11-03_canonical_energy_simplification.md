# Energy and Ritz corollary: compilation simplification

The public statement of
`exists_physical_dg_canonical_ritz_polynomial_approximation_with_energy`
is byte-identical to the statement in commit
`82a6852e93db47401d58068ace0004a50dfd6c11`. In particular, the
physical family is selected once, the energy function is chosen once for
each successful seed before the vector-wise conclusions, and the same
canonical root, literal refinement and actual Ritz space are retained.
The existing green canonical approximation theorem is unchanged.

The proof now separates the calibrated-word energy argument into
`ALVV/CalibratedRootEnergy.lean`. Its lemma identifies the prescribed ground
energy with the actual spectral minimum, proves the needed count bound,
and applies the existing root energy-assignment theorem to the same
targets and operator words. It has no arbitrary terminal proposition as an
argument. The final corollary retains its energy function together with the
unchanged refinement and Ritz conclusions. No mathematical assumption,
resource limit, dependency revision or proof option was changed.

## Verification

The read-only provider was TNLean
`88ab31ce57bdbc4bcb65be00055d1db50df4f259`, with its own QICLean package
`e817ea0a8a46440eddc361d41cc46b9e61ba10f4`. Private strict checks passed
in 5.888 seconds for the energy lemma and 19.291 seconds for the corollary.
The ordinary single-threaded production gate used the unchanged CI flags,
`lean -j1`, and a 50-second timeout. It passed in 11.859 seconds and
33.252 seconds, respectively. The corollary retains the 25-second timing
warning; both modules meet the 50-second limit.

The ordinary gate used a temporary Lean search namespace containing only
read-only links to guarded existing artifacts and to the newly checked
auxiliary artifact. It used no import override or setup file, copied no
artifact bytes, and wrote no ordinary build object. Source, object,
sidecar, dependency-input and provider hashes were checked before and after.
No Mathlib source was built and no provider, package, pin or cache changed.

An imported inspection of both public declarations passed in 8.225 seconds;
each depends only on `propext`, `Classical.choice` and `Quot.sound`. The
temporary inspection source was deleted. Generated imports, blueprint roles,
reader prose, scoped source-to-blueprint references, proof integrity and
whitespace checks pass. The complete library and compiled blueprint checks
remain the coordinated integration gates.

The original 98.169-second private result and the original production timeout
(exit 124, 54.9 seconds including interruption and shutdown) are preserved.
Exploratory partial-normalization and refolding failures are also preserved
under `/tmp/tnlean-canonical-energy-simplification-20261103`; none is counted
as verification evidence. The previous audit
`2026-11-03_canonical_ritz_energy.md` records the original contribution.
The present result resolves its local compilation-time condition without
altering its mathematical scope.
