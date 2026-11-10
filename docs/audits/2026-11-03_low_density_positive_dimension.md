# Positive local dimension and strict low-energy approximation

The three new physical results extend the already proved entropy, fixed-cut
approximation and global MPS consequences to every positive local dimension.
Their bandwidth-dependent coefficients remain chosen before the physical
chain, deficit, accuracy and vector. The global integer bond factor remains
chosen before the vector. No existing theorem statement or proof is changed.

The source is ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines
1096–1105. Its physical setting is the positive-contraction nearest-neighbour
chain at lines 267–284, with fixed bandwidth as in Assumption (LD).
The capped-width comparison is unchanged and is documented in
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.

For local dimension at least two, the entropy proof is the existing actual
original-band proof. The two approximation statements use the same physical
construction at accuracy `delta/2`. This gives overlap strictly greater than
`1-delta`, as printed. The exact fixed-cut accuracy variable is now
`16 + log(1/g) + log(2/delta)`; the exact global one is
`16 + log(1/g) + log(32(L+1)/delta)`. No new scalar asymptotic premise is
introduced. The same three-quarter power and the same bandwidth coefficients
are retained. The global squared distance is at most `delta/4`.

For scalar local dimension, every regional configuration space has dimension
one. The existing regional dimension estimate gives entropy at most zero.
The original unit vector is used as its own fixed-cut approximation, whose
rank is at most one by the actual coefficient-matrix dimension bound.
For the global conclusion, the actual internal-cut factorization theorem
constructs a bond-one MPS for this same vector. The positive-band target
contains an actual ground eigenvector, so its dimension is at least one and
the allowed bond `dim G(eta) * 1` suffices. This includes empty and short
chains, every prescribed interval, and every positive deficit. It changes
no physical family or sequential construction for larger local dimensions.

Positive local dimension is the usual qudit convention. A statement allowing
local dimension zero needs an endpoint distinction: a positive-length chain
then has zero Hilbert space, but an empty chain still has a one-dimensional
configuration space. The present statements quantify over positive local
dimension and do not invoke an incorrect universal zero-space claim.

The fixed-cut and global approximation statements provide separate witnesses.
A stronger simultaneous conclusion, retaining the sharper designated-cut
bound and global MPS bounds in one vector, would use nonuniform sequential
rank budgets. It is not inferred by identifying two existential choices.
No claim that this stronger conclusion or a running-time estimate has been
proved is made by the present contribution.
