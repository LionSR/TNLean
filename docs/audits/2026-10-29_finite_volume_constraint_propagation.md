# One finite-ring equation determines the local MPS constraint

Parent draft: #10361. Issue: #10280 (SPWC10 Theorem 5).
Source: `Papers/0909.5347/main.tex:869–880`, the final finite-to-all-volumes
step in the dichotomy proof; also PGVWC07 Theorem 11, proof 1418–1422.

## Result

For an arbitrary positive L-site interaction h, assume H_N annihilates the
actual periodic vector of A on a nonempty ring N≥L. If the words of length
N−L span the bond matrix algebra, derive G_L(A)⊆ker h. Consequently the same
actual tensor A gives a zero-energy vector for H_M at every M≥L, with no
word-span condition at M. No local-kernel inclusion or future-volume equation
is supplied as a premise.

The family version derives the entire local kernel inclusion for every block
from a nonzero weighted sum and simultaneous complementary spanning. The
already-written local separation proof from #10361 now exports its stronger
boundary-annihilation conclusion once, and both its existing local-component
consumer and the new local-kernel consumer reuse it. There is no second
entrywise interaction proof or a new Hamiltonian model.

## Scope

This proves the actual finite-to-all-volumes implication. It does not prove
that the vectors on all new rings are nonzero, that their Hamiltonians have
unique ground states, or that arbitrary prime-length representations have a
sufficiently small injectivity length. The full fixed-dimension versus
prime-length obstruction dichotomy therefore remains open in #10280. The
single-block theorem adds no gauge-phase separation assumption. Its
complementary injectivity is the explicit hypothesis discharged by the
Wielandt bound in the source's last step.

All new Blueprint statements/proofs are `notready`. No local Lean build,
elaboration or declaration checker was run. Pinned Mathlib/QICLean source
scouting, native import generation, integrity/prose/width checks, role check,
reference synchronization and duplicate ownership, pinned TeX formatting,
ChkTeX and diff checks pass. Hosted proof acceptance and integration remain
pending. No proof bypass or persistent Lean fixture is introduced.
