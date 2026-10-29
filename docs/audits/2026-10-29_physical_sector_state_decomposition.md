# Exact physical-sector state decomposition

Context: #10386, child of #10411. This change derives the actual state
splitting needed after mixed-sector exclusion; it does not supply the
remaining component Hamiltonian kernel identifications.

For a nonempty chain and an alphabet with first a and last b letters,
the two constant-sector word embeddings have disjoint images. Their
ranges are characterized by the literal letter values being respectively
less than a or at least a. A word outside both ranges contains one
letter in each part.

A vector with zero mixed coefficients is therefore exactly the sum of the
extensions of its actual coefficient restrictions along those two word
embeddings. There are no supplied component vectors, scalar factors,
normalizations or state-decomposition hypotheses. The component coefficients
are exactly ψ applied to the embedded configuration.

For the actual periodic projector Hamiltonian of the sum of two embedded
local spaces, #10411 derives mixed-coefficient vanishing from positivity and
cyclic induction. The final theorem consumes the actual Hamiltonian equation
to produce the exact decomposition at every M ≥ R ≥ 2. Arbitrary local
spaces permit insertion of the Weyl boundary range and pure particle line.

No local Lean, Lake, build, elaboration or checkdecls is run, as requested.
The two public declarations and their Blueprint statement/proof are notready.
Native checks and source review do not establish hosted kernel acceptance.
No persistent Lean fixtures are introduced.
