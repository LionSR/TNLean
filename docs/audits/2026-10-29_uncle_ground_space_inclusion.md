# The two parent sectors in the actual uncle kernel

Issue: #10285; source: arXiv:1210.6613, Theorem `thm:gs-subspace-uncle`,
lines 1050–1068 in `Papers/1210.6613/UncleHMPS.tex`.

The new `UncleGroundSpaceInclusion.lean` supplies the first direction of
the source proof on the existing explicit interaction and Hamiltonian.
A diagonal virtual boundary matrix recovers either original two-site MPS
boundary map from the uncle tensor. Thus each original local parent space
lies in the uncle local kernel. The cyclic restriction/adjoint definition
then annihilates every periodic vector satisfying either sector's two-site
parent constraints. In particular the span of the two MPS vectors lies in
the actual periodic uncle Hamiltonian kernel for every N≥2.

No injectivity, normalization, nonzero bond dimension or extra parent-space
inclusion is assumed by the public theorems. These formulas hold for the
explicit uncle projector even when its identification with a perturbative
limit needs a separate injectivity argument. The limit theorems remain in
`UncleParentLimit.lean`; draft #10308 derives their injectivity premise from
the source perturbation condition. This PR is independent of that draft.

The reverse kernel inclusion is not supplied: the source's open-chain
intersection identity and periodic closure identity remain necessary.
Neither equality nor exact degeneracy follows from the containment alone.
The issue stays open and the new Blueprint entry is pending verification.

Validation: exact pinned Mathlib/QICLean source inspected, import generator,
reader-facing prose check, tactic-pattern scan, Blueprint source-reference
check, TeX formatting, line/integrity checks and `git diff --check`. No local
Lean elaboration or build, and no persistent Lean test fixture.
