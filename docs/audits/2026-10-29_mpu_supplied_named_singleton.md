# Actual named singleton action of a directly supplied tensor

Source: CPSV17, StandardForm/SF, lines 603–622; actual finite conjugation
in eq:appendix-1, lines 2300–2306; physical reindexing in IndexTh(ii),
lines 824–847.

The new finite caller uses the actual named bare-MPU automorphism of the
tensor obtained from a directly supplied standard form. It permits any
physical alphabet equivalent to the two-half-site alphabet. No global
quasi-local relabelling map is introduced: only the actual finite MPO
matrices and finite configuration coordinates are transported.

Physical reindexing preserves the MPU property by the existing actual
periodic reindexing formula and matrix unitary reindexing. The existing
complete input/output head bijections now have a common public owner;
their former private proofs are unchanged. The singleton coordinate is
literally the constant function with letter e.symm(finProdFinEquiv c).
The output three-cell coordinates retain the four actual output halves,
with the two exterior halves as identity spectators.

The arbitrary-buffer supplied-window identity is converted to canonical
identity buffering and then transported sitewise through the physical
bijection. The three-cell input equals the canonical singleton matrix
with one identity cell on each side. Choosing p=s=4*D^4+1 gives a finite
chain which contains the named bare-MPU evaluation's full source buffer.
Actual finite conjugation and canonical local inclusions then give the
named completed automorphism's output on cells -1,0,1.

The public theorem assumes only the directly supplied standard-form
datum, equivalent physical alphabet, and the positive physical dimension
needed by the quasi-local algebra. It does not assume a compatible action,
a tensor preimage under blocking, a second blocking scale, an output
support identity or an inverse datum. Construction of the standard-form
datum and identification after physical two-site blocking remain
separate capstone work.

No Lean invocation, elaboration or build was run. New Blueprint entries
remain notready. Source-only checks cover imports, full declaration and
duplicate-tag synchronization, mathematical roles, prose, formatter,
width/whitespace, proof integrity and tactic patterns. Hosted checking is
required before acceptance.
