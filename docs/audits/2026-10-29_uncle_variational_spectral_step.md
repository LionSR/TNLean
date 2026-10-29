# The finite uncle variational spectral step

For the actual finite uncle Hamiltonian, a strict Rayleigh bound on a vector
in the kernel complement produces an actual positive real eigenvalue below
that bound. Hamiltonian positivity is derived from its actual projector and
cyclic restriction formula, including empty chains and configuration spaces.

The finite-dimensional argument uses Mathlib's orthonormal eigenbasis of a
positive operator. Zero eigenvalues have zero vector coordinates by kernel
orthogonality. If every other eigenvalue were at least the proposed bound,
the quadratic form would contradict the strict Rayleigh inequality.

This is the finite spectral step in arXiv:1210.6613, proof of Theorem
thm:gapless, lines 1302–1314. It is a separate analytic lemma, with all of its
pointwise vector hypotheses visible. It does not establish the source
asymptotic gaplessness theorem until the actual two-wall norm, energy and
ground-overlap estimates construct the required kernel-complement vectors.

Validation: source inspection of the Mathlib eigenbasis, nonnegative
eigenvalue, orthogonality and coordinate-norm APIs; import/declaration,
prose, formatting and branch diff checks. No local Lean compilation or
elaboration was run. The new Blueprint lemma remains pending validation.
