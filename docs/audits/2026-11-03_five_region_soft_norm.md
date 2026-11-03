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

## Verification

The exact named production module passes strict private checking at default
limits in 8.932 seconds, with 104 guarded TNLean/QICLean source/object pairs,
against immutable TNLean 88ab31ce57bdbc4bcb65be00055d1db50df4f259 and its own
QICLean package e817ea0a8a46440eddc361d41cc46b9e61ba10f4. The imported public
foundation inspection passes in 4.526 seconds with 105 pairs and only
propext, Classical.choice and Quot.sound. Its temporary source is deleted.

Earlier broad-import private-cap checks took 58.230 and 55.571 seconds.
The unnecessary residual-theory import was replaced by the actual original
region, commuting soft-family and operator-cap dependencies, plus the
existing Module tactic. The unchanged private cap then passed in 5.241
seconds. This is a genuine dependency reduction; no unchanged-source
check was repeated for timing. The first full public check's scalar-cast
and proof-instance-style errors were repaired and are retained as failed
diagnostics, not counted as successful evidence. No resource option was
raised.

Complete source/blueprint synchronization uses the immutable provider's
QICLean and Mathlib source trees read-only, without adding a local cache.
Generated imports, the public declaration's reader coverage, reader prose,
integrity, whitespace and pattern checks pass. The new mathematical entry
and physical note passage are rendered and inspected. Ordinary combined
compilation and complete compiled blueprint declarations remain integration
checks. The source-only worktree has no Lake environment; no provider,
cache, pin or Mathlib source has changed.
