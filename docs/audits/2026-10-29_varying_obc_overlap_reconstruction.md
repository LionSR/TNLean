# Rectangular varying-bond OBC overlap reconstruction

Source: PGVWC07, `Papers/quant-ph_0608197/MPSarchive.tex`, Theorem 9
statement at lines 1206–1210 and proof at lines 1212–1237, especially
the middle-site C1 argument and canonical adjoint construction at
lines 1222–1234.

The local result uses independent virtual spaces a,b,c,e and independent
finite physical alphabets I,J,K. It does not flatten the chain into a
translation-invariant square tensor. Equality of overlapping two-site
trace representations and C1 for the middle family give X_k A_i=C_k Y_i.
The first family's actual canonical row identity then gives the exact
source boundary Z=sum_i Y_i A_i† and X_k=C_k Z. Cyclicity of rectangular
trace identifies the actual three-site coefficients. A section-level
corollary chooses the two boundary families from the local section
conditions and derives a common three-site representation.

The code reuses Mathlib's rectangular matrix multiplication linear maps,
`LinearMap.ext_on_range`, and `Matrix.ext_iff_trace_mul_right`. There is
no second trace-duality development and no one-sided-inverse hypothesis.
The blocking lemma also derives the actual row-isometry identity for the
product family (i,j)↦A_i B_j from the two original row identities.

This is a necessary reconstruction ingredient for issue 7684. It is not
the full Theorem 9 parent-Hamiltonian uniqueness result: finite-chain
iteration, the actual varying-bond local Hamiltonian/kernel relation and
scalar-endpoint closure still require assembly. The arbitrary-interaction
Theorem 11 work and its distinctness boundary are separate. No new OBC
model, parallel canonical predicate or parent-kernel conclusion is added.

Current main supplies OBCChainTensor with scalar endpoints but no
varying-bond parent-Hamiltonian kernel theorem. The simultaneous
canonical construction and original-site canonical Gram results are
separate active drafts; this finite matrix reconstruction is independent
of their uncompiled implementations.

No local Lean invocation, elaboration or build was run. Every new
Blueprint entry remains notready. Source-only checks cover pinned APIs,
generated imports, Blueprint declarations including duplicate tags,
mathematical roles, reader-facing prose, formatter, width/whitespace,
proof integrity and tactic-pattern scanning. Hosted checking is required.
