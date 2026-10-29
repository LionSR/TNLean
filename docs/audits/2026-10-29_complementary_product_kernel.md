# The common kernel of complementary projection products

The fixed space of the actual finite product (I-h_(n-1))...(I-h_0)
is the common kernel of the orthogonal projections h_i for i<n.
The projections need not commute. The statement applies on any complete
inner-product space over a real or complex scalar field, without a
finite-dimensional, unit-vector or gap assumption.

The proof uses the already checked removed-mass identity in
QICLean/Analysis/DetectabilityLemma.lean. If the final product fixes x,
the sum of squared removed norms is zero. Every summand vanishes, and
induction identifies each intermediate vector with x. Conversely each
complementary factor fixes a common-kernel vector. The empty product
and zero vector are included directly.

This is the common-kernel step of ALVV, arXiv:1602.08828v2,
def:FF-tH and thm:FF-tH, source lines 1467–1487 and 1543–1550. It
introduces no new projection or kernel definition. Mathlib's existing
nonnegative-sum and squared-norm lemmas are reused. The physical
consumer replaces the existing local prefix induction in
PhysicalDetectability.lean and supplies the corresponding characterization
for actual parity products. The regional truncated Hamiltonian and its
corrected rank bound d²+3 remain separate constructions.

The private strict module check passed in 33.551 seconds while the combined
TNLean build was rechecking unrelated dependencies. This reaches the
25-second warning threshold, but remains below the 50-second limit.
The read-only QICLean provider is 4175de302e6b580d1bbb4a022f57424ab9f05e73.
Sources and objects remain outside the repository under
/tmp/tnlean-frustration-free-truncation-20261029. No provider source or
ordinary build cache was changed; Mathlib was not rebuilt and no
modified-worktree artifacts were copied. Imported foundations and
ordinary integration verification are recorded separately.

## Imported foundations and the physical consumer

The actual separately compiled generic module was imported and its public
theorem inspected: only propext, Classical.choice and Quot.sound occur.
The imported inspection took 18.221 seconds. The subsequent physical
characterization and refactored kernel argument passed strict checking
in 26.625 seconds; five imported public physical declarations have only the
same standard axioms. Their object hashes remained fixed.
The exact records are kernel-manifest.json and physical-kernel-manifest.json
in the temporary directory above, with the selected imported-artifact
hashes in physical-import-guards.json. The generic detectability object
was byte-identical in the two checked provider environments.

The physical consumer replaces the previous prefix induction by the shared
characterization. Its public statements are unchanged except for the new
explicit fixed-space equivalence. Ordinary combined-library and compiled
blueprint checks remain for coordinated integration. The source-only
worktrees have no local Lake cache, and no ordinary build is queued there.
