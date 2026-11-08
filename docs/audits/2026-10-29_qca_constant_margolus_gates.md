# Fixed Margolus gates in transported intermediate coordinates

Source: Schumacher–Werner, `Papers/quant-ph_0405174/qca.tex`,
`bruleU`/`bruleV` lines 980–1001, translation compatibility and basis
freedom lines 1033–1041, and `defBBq` lines 1199–1226.

This extends the position-dependent actual gate construction. The next
even factor uses the inverse of the actual two-site translation from
the cut-zero even factor, followed by the cut-zero presentation. It is
not identified with an independent classical choice of next-even basis.
The already proved support covariance supplies the range equality.

The common shifted rule maps odd/even matrices to the actual product of
the cut-zero odd observable and the two-site-translated cut-zero even
observable. Applying that same rule to identity/even and odd/identity
recovers the two neighbouring factors; the former is translated back by
two. The full matrix-unit expansion therefore uses one fixed output gate
on both neighbours. Original covariance translates the same expression
to every integer-translated input block.

The final gates have physical coordinate type `Fin d × Fin d` in
increasing site order. They are obtained directly by spatial
implementation of the reindexed actual rules. The output gate has
intermediate order odd/even, `r × ell`, matching the Cirac forward gate;
Schumacher–Werner's alternate ordering can be obtained by the physical
factor permutation. No raw tensor source-factor or selected-SVD
identification is asserted.

Thin star-preserving adapters reuse Mathlib's existing subalgebra
image/equality equivalences. Their ambient evaluations are definitional.
The finite-support embedding and previous range-equality coordinate
helper now use these shared adapters. The actual ordered-pair coordinate
bijection has one common owner; the former private index-comparison copy
has been removed in the corresponding parent branch.

Public inputs are only positive homogeneous physical dimension, an
actual nearest-neighbour automorphism, and its actual translation
covariance. No output action, circuit identity, coordinate equality,
extra factorization, gate pair, or spectral premise is supplied. The
constant-gate formula is derived for every physical pair matrix and every
integer translate. The existing even-pair generation and density result
makes such pair values determine the global action; conversion to one
MPU tensor is handled separately.

No Lean invocation, elaboration, or build was run. New Blueprint entries
remain notready and hosted checking is required. Source validation covers
pinned API scouting, independent source review, generated imports,
Blueprint/role/prose synchronization, formatter, whitespace/width,
proof integrity and tactic-pattern scans.
