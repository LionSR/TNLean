# General weighted-canonical C2 half-chain spectrum

Source: PGVWC07, arXiv:quant-ph/0608197, Condition C2 and Theorem 6,
`Papers/quant-ph_0608197/MPSarchive.tex:954–993`.

The actual general weighted-canonical statement is now written without
assuming a dominant block, a stationary density, normalization, physical
decay, fixed physical dimension, or a spectral-convergence conclusion.
Draft #10342 supplies the actual sector eigenvectors, normalized generic
C2 with algebraic multiplicity, unique dominant normal block, physical
remainder decay and normalized diagonal dual fixed point.

The new physical comparison reads each ring vector as its actual two-half
coefficient matrix. Its operator norm is bounded by the Euclidean vector
norm. Factoring the reduced-matrix difference gives

    ||R_psi - R_phi|| <= (||psi|| + ||phi||) ||psi - phi||.

This has no dimension factor. The finite normalization is exactly the
actual squared ring norm, including zero-norm finite lengths. The actual
normalizations satisfy

    ||hat(psi) - hat(phi)|| <= 2||psi-phi|| + 2 abs(||phi||-1).

Weyl's inequality at each finite length therefore bounds every difference
of ordered, zero-padded half-chain eigenvalues by twice the normalized
vector distance. This passage does not invoke continuity in a fixed
physical dimension.

For the derived dominant normal block, the existing one-block result
gives both the norm-one limit and the doubled fixed-point spectrum. The
derived physical remainder, actual normalization comparison and physical
eigenvalue bound transport this spectrum to the original weighted tensor.
The same physical norm estimates make its finite even-length norm
eventually positive. Multiplicities and zero padding are retained.

The exact new capstone is
`PGVWC07CanonicalFormData.exists_halfChainSpectrumLimit_of_c2` in
`HalfChainGeneralCanonicalSpectrum.lean`. Its source C2 counts algebraic
multiplicity, as the paper's generic exclusion of degeneracy in magnitude
requires. The old one-block distinct-value condition is not silently
strengthened. The source interpretation and the nonliteral dominant-block
reading are recorded in
`docs/paper-gaps/pgvwc07_half_chain_spectrum_conventions.tex`.

All new Blueprint nodes and proofs remain notready pending hosted Lean
acceptance. Independent source/API reviews found no concrete mismatch in
the normalization, growing-dimension comparison or capstone. Native
imports, declaration synchronization, roles, prose, TeX formatting,
ChkTeX, proof-integrity and diff checks do not replace proof acceptance.
No local Lean build, elaboration or checkdecls was run, as requested.
Issue #6088 stays open for hosted acceptance and integration.
