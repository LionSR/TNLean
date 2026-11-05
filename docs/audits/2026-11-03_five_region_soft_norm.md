# Norm of the same five-region soft Hamiltonian

The public estimate retains the original five regional Hamiltonians and
crossing bonds, the supplied attained minimum energies e_j and their common
normalized eigenvector x, and the actual estimated centers p_j. Only the
three bulk regions 0,2,4 are softened. No regional minimum or soft ground
energy is selected by this theorem.

The primitive assumptions are nearest-neighbour support and positive unit
bounds on the original terms, four ordered cuts inside the chain, two
site-window widths at most 2ell, the same unit/eigenvector/positive-shift
minimum certificates, p_j in [e_j-10,e_j] on the selected regions, t > 0,
and integer m >= 1. Positivity of the original terms and the supplied
normalized eigenvector derive e_j >= 0. The one-sided centers and those
same positive shifts derive positivity of A_j-p_j I.

The existing finite commuting-family theorem gives a common positive
correction of 30I. The upper cap uses t(1+log m) for each softened term,
2ell for each actual window and four for the actual crossing sum.
Consequently -30I <= G <= (3t(1+log m)+4ell+4)I. The existing Mathlib
self-adjoint max-norm estimate then gives
norm(G) <= 3t(1+log m)+4ell+34. The scalar instance needed to normalize
identity norms follows from the supplied unit vector; no additional
positive local-dimension hypothesis is required.

The harmonic-cap correction and retention of every original regional shift
remain explicit. This is an auxiliary to ALVV, arXiv:1602.08828v2,
`def:soft-trunc` and `t:aisefficient`, lines 1178–1185 and 1348–1392.
It supplies neither a residual estimate nor a complete filter calibration.
The companion harmonic-cap note remains owned by QICLean and is cited by
its published URL; the TNLean note records only the physical norm and
regional-centering consequence.
