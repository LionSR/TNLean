# PGVWC07 one-block unital periodic decomposition

Issue: #6232. Source: `Papers/quant-ph_0608197/MPSarchive.tex`, Theorems 4 and 5, lines 740–766 and 849–880.

The source supplies unitality, a faithful adjoint fixed matrix and scalar fixed matrices. The implementation derives irreducibility from these conditions using QICLean's public spectral characterization. It derives the cyclic period from the cardinality of the peripheral spectrum, and proves that each peripheral maximal generalized eigenspace has dimension one. Thus the count agrees with algebraic multiplicity.

The final theorem uses the original unital transfer map and its orthogonal cyclic projectors. Public Kraus letter-shift results supply the source orientation directly. Existing projector-component chains, trace decomposition and componentwise non-divisible-length vanishing provide the physical conclusion with the original bond dimension. No new Hamiltonian, tensor convention, transfer map or normalized periodic predicate is introduced.

The source's diagonal faithful adjoint fixed matrix is included as a specialization of a positive-definite matrix. No unsupported equivalence between unital and trace-preserving conditions on the same tensor is asserted. The normalized companion declarations remain available, with their former source-boundary markers retired because the source-facing result is now separate.

A live audit of all 38 open PR changed-file lists found no overlap in the periodic modules, canonical chapter or periodic-decomposition source note. The half-chain owner confirmed no competing source-hypothesis API. The local narrow probe checks the exact cyclic-cardinality and peripheral generalized-eigenspace proof bodies with all package options and no diagnostics. The broad public irreducibility wrapper and existing state-vector consumer are reserved for exact-head full remote CI; this is not yet a complete local module build.

The revised source note compiles to three PDF pages with no final TeX warnings; all rendered pages were visually checked. The existing normalized theorem/proof token streams are unchanged.

Independent read-only mathematical/source review passed on the exact new theorem sources. It checked the original Theorems 4–5, the public spectral characterization and cyclic-decomposition APIs, the unital orientation, multiplicity count, original bond dimension and componentwise vanishing. No source-scope blocker was found.
