# Four actual primal toric-code torus sectors

Issue: #8039, item 4. This continuation is based on the local primal
G-isometry in PR #8563 at `7b85a47d2a9d2d411cadf49930b88f139f4358f9`,
merged locally with main `b9b093adafcdbe4d0eaa5c6517fe8313c80da34f`.
The parent PR's mathematical files are preserved.

## Reuse and source scope

The bond action is the literal diagonal binary character, with identity
and Pauli Z as its two matrices. Its oriented four-leg action is proved
equal to the existing primal parity representation. Linear independence
of I and Z implies semi-regularity through the existing representation
result. Actual torus closure independence and dimension use the existing
G-injective sector theorems and the existing abelian pair-class
cardinality. No new quotient or representation-theory definitions are
introduced, and no Hadamard change of physical tensor is assumed.

The amplitude proof contracts the original primal tensor. A physical
configuration uniquely fixes all four virtual labels of each site, so
exactly one assignment of bond ends survives. Identity/Pauli-Z seam
matrices give the bond-compatibility indicator and the two seam signs.
There is no unrecorded scalar factor. The four states share the same
configuration support; their independence is due to their relative signs.

The source anchors are the review's Appendix A, equation
`eq:app:tcode-rep-primal`, lines 2451–2465, and SCP10 Definition 5.6 and
Theorem 5.9, lines 1515–1621. This completes the four-vector span claim,
not the distinct assertion that this span exhausts a parent-Hamiltonian
kernel. Positive rectangular periods use the oriented-bond contraction;
the simple-graph PEPS interpretation has both periods at least three.

## Overlap audit

All 53 live open PR filename lists were read at 20:46 UTC on 2026-10-04.
Only #8563 touches the relevant toric-code, quantum-double, torus-sector,
pair-conjugacy or torus-closure source families, and it explicitly leaves
item 4 open. PRs #8595/#8603 concern checkerboard reduction to the dual
tensor, not these primal torus sectors. No active PR contains a competing
primal-sector file. The dependency on #8563 is explicit rather than
silently copying its unmerged local result.

## Validation

Both new modules and their 37 prerequisite modules passed exact-source
isolated-output compilation with all package options and no diagnostics.
Reused artifacts were checked against source bytes and actual Lake trace
hashes; dependencies of changed modules were rebuilt. The 3-by-3 physical
seam-sign tests also passed the strict CI options. The dimension and
amplitude capstones use only propext, Classical.choice and Quot.sound.
Final exact-head root and blueprint CI are recorded in the pull request.
The prerequisite closure excludes whole-Mathlib imports; Mathlib itself
uses only the official pinned prebuilt cache. The modified standalone note
compiled without undefined references or overfull boxes, and the two pages
containing the new section were visually inspected. The tactic scan found
only pre-existing repeated blocks in other example modules; this proof
uses the standard finite-sum single-survivor lemma.
