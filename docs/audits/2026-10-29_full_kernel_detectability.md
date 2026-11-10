# Detectability above the full zero-energy kernel

The new physical theorem takes a gap in the actual real spectrum of the
original projection-chain Hamiltonian. Every nonzero eigenvalue is at least
gamma>0. For every vector x orthogonal to the entire kernel, it proves

    ||DL(H)x||^2 <= 4/(4+gamma) ||x||^2.

The proof first derives Hermiticity from the original projection terms,
then applies the proved full-kernel invariance of the actual even/odd
product. The shared QICLean spectral lemma gives the quadratic-form bound
on the resulting vector; the physical energy estimate finishes the proof.
The argument assumes neither a chosen one-dimensional ground line nor an
upper bound on gamma. It also does not assume the desired contraction as
an input condition.

Both the generic spectral lemma and the physical consumer passed strict
private checks and an imported two-declaration foundation audit. Only
propext, Classical.choice and Quot.sound occur. Exact source and object
hashes are recorded in
`/tmp/tnlean-kernel-detectability-20261029/manifest.json`.
The integrated theorem subsequently passed the full 15,106-job library
build, strict production checks, an imported foundation audit, and compiled
blueprint declaration checks at revision
`908de62f163b9505312b914a2fad03dafa23948d`. The companion spectral theorem
was checked at `d41577c2965094ee0f1067fce107aa59088d653e`, with the
documentation-only successor `01f237e808b03fb0612ceb617f9bca2c407da927`
pinned by TNLean. Neither library rebuilt Mathlib from source.
Range-projectivization and the regional truncated Hamiltonian remain
separate parts of the frustration-free argument.
