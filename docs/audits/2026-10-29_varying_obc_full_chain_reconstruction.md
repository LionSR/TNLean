# Full-chain reconstruction from adjacent OBC sections

Source: PGVWC07, `Papers/quant-ph_0608197/MPSarchive.tex`, Theorem 9 proof,
lines 1212–1237. The proof first matches overlapping pair representations,
then uses canonical adjoints to enlarge the represented block, and finally
uses the scalar endpoint bonds. This continuation implements that finite-chain
induction after the rectangular three-site result.

`VaryingOBCReconstruction.lean` uses the existing QICLean
`Kraus.rectangularEval` on the actual varying bond spaces. It derives its
last-letter product identity and row-isometry for every actual prefix. The
normalization proof reuses the preceding two-family blocking identity.

The induction starts from the original adjacent-pair coefficient conditions.
At the step from a prefix of length m to m+1, its first family is the actual
prefix product of length m-1. For each next physical letter the inductive
hypothesis gives the left representation; for each prefix word the original
pair condition gives the right representation. The source's three-site
adjoint construction produces the enlarged boundary. No full-block boundary,
one-sided inverse, C1 assumption for an unspecified blocked tensor, or separate
canonical supplier is supplied to the final theorem.

List words describe fixed physical configurations outside a pair; the theorem
is restricted to a fixed total length. Its conclusion uses ordinary Fin-indexed
physical configurations. Length N is at least two, the domain where adjacent
pairs are present. No short-chain counterexample or new canonical predicate
family is introduced. Singleton endpoint bonds give a scalar multiple of the
represented chain, rather than literal equality of normalized state vectors.

This is the full representation-intersection step for issue #7684, not the
complete Theorem 9 parent-Hamiltonian theorem. The remaining step is to define
or assemble the actual varying-bond local parent terms and prove that their
common kernel gives precisely the adjacent-pair coefficient sections. Neither
that implication nor the final Hamiltonian kernel equality is assumed or
claimed here. Existing OBCChainTensor data are not duplicated.

No local Lean, Lake, elaboration or build was run. All new Blueprint entries
and proofs remain notready. Source checks cover the pinned rectangular-product
and finite-configuration APIs, source scope, imports, declaration ownership,
mathematical roles, proof integrity, whitespace and width. Hosted validation
remains required for the new proofs and their parent.
