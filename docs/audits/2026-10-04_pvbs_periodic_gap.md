# Exact finite-ring PVBS gap

## Source and normalization

Bachmann–Nachtergaele, arXiv:1112.4097, Section II after equation (8), gives
one-particle dispersion and a conjectural multi-species thermodynamic gap
formula. The present result is the finite periodic, one-species, zero-phase
case with positive real hopping μ ≠ 1. The broader conjecture is not claimed.
The distinction is recorded in
[`bn12_pvbs_periodic_gap`](../paper-gaps/bn12_pvbs_periodic_gap.tex).

The local formula is proved equal to the existing canonical orthogonal
projector, with the forbidden one-particle vector divided by 1 + μ².
Periodic summation includes both oriented windows at N = 2. It gives the
exact identity Hμ = [2μ/(1+μ²)] H1 + [(μ−1)²/(1+μ²)] N_particles.
Positivity of the actual critical parent H1 and the particle count on
nonvacuum configurations give the lower bound. The existing uniform
one-magnon vector attains it. The final statement gives both the norm-gap
bound on the actual kernel complement and optimality of its constant.

At μ = 1 the uniform particle joins the ground space. This does not claim
that a fixed finite ring has zero gap above its enlarged kernel.

## Reuse and dependency placement

- Reuse the PVBS model, local ground space, vacuum and periodic-kernel facts.
- Reuse the canonical parent interaction, cyclic local-term embedding,
  positivity and Euclidean-space norm-gap formulation; define no second
  Hamiltonian or gap predicate.
- Reuse `SpinChain.oneMagnon`, finite matrix-vector notation helpers,
  orthogonal-projection uniqueness, and Mathlib finite-sum and inner-product APIs.
- Move the existing cyclic successor, cyclic-group coordinate and window-swap
  declarations into `CyclicWindowPermutation`. Names, signatures and proof
  blocks are unchanged. Their old modules import the new module.
- This geometry no longer requires the Knabe/spectator/FNW chain merely to
  exchange two sites. No generic geometry proof is duplicated.
- A live audit of all 45 open PR changed-file lists found no overlap with
  the two source modules before the extraction.
