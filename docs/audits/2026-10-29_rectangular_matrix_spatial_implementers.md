# Unitary implementers between distinct finite matrix coordinate spaces

Source use: Schumacher–Werner, Papers/quant-ph_0405174/qca.tex,
blockdims/bruleU/bruleV, lines 977–1001. Reuses the actual same-index
Skolem–Noether theorem in QICLean/Algebra/SkolemNoetherUnitary.lean,
with its cited CPSV16 Appendix C.4 source.

`Matrix.exists_unitary_conj_of_starAlgEquiv_matrix_between` takes an actual
star-algebra equivalence Matrix I I C ≃⋆ₐ Matrix J J C on nonempty finite
coordinate types and derives a rectangular unitary U:J×I with both unitary
identities and the exact formula f(A)=U A U†. The equality of coordinate
cardinalities is derived from the square algebra dimensions, not supplied.
An explicit coordinate equivalence reduces to QICLean's same-index theorem;
reindexing the implementing unitary's columns gives the actual rectangular map.
All three equivalences in the reindexed matrix-product identity are explicit.

This is the finite spatial tool needed for the actual Margolus gates in
issue 7035. It does not assume or reconstruct the QCA support-algebra proof,
construct an alternating action from arbitrary factor data, or identify a
chosen QCA with a circuit. Those are consumer obligations.

No local Lean, Lake or checkdecls runs. Native source checks are recorded
in the PR, and the new Blueprint lemma and proof stay notready pending
exact-head hosted acceptance. The source constructor parent is #10374.
