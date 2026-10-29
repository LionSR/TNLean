# The gap of the actual frustration-free regional truncation

Let the nearest-neighbour interactions be orthogonal projections and let every
nonzero spectral value of their sum be at least γ>0. The actual regional
truncation has the same full kernel and every nonzero spectral value is at
least γ/[3(4+γ)]. No uniqueness, interval-interiority, local-dimension or upper-gap
hypothesis is imposed. For 0<γ≤1 this is at least γ/15.

This proves the gap conclusion of ALVV, arXiv:1602.08828v2,
`thm:FF-tH`, lines 1562–1568. The original detectability product is retained.
Its two removed masses are bounded by the energy of the actual regional
Hamiltonian: regroup each parity into internal and outside factors, apply the
orthogonal-projection residual inequality, and sum the outside bond energies.
The two-projection converse then gives 1−3E≤‖DL x‖². Detectability on the common
full-kernel complement bounds the right side by 4/(4+γ). The spectral conclusion
follows by applying the resulting quadratic-form bound to the Hermitian
orthonormal eigenbasis.

The printed additive rank constant remains false and is not asserted by this
contribution. Its correction and nondegenerate counterexample remain in
`docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`. A formal proof of
the corrected rank bound is a separate task.

## Local verification

Both changed physical modules pass strict elaboration against fixed TNLean
f93bc77b3dddcc292125eea18b96af153225251b and QICLean
4276de2eeb5c4122f4482ef5e4fa205be5b71bd9, with the new generic projection
residual lemma from QICLean 85e84732c0f5ebf1e2e61312fc2d428460156465.
The final regional module takes 10.241 seconds. Imported foundation audits cover
all twelve public declarations of the physical detectability module and all
nine of the regional module; only propext, Classical.choice and Quot.sound
occur. The generic residual helper also passes its imported foundation audit.
Selected source/object pairs and the Mathlib artifact remain unchanged.

All elaboration outputs are private temporary files. No Mathlib source was
rebuilt, no modified-worktree artifacts were copied, and no permanent test
fixture was introduced. Combined builds and compiled blueprint declaration
checks remain subsequent integration requirements. Local evidence is retained
under `/tmp/tnlean-frustration-free-gap-20261029` and
`/tmp/qiclean-projection-residual-20261029`.
