# Critical PVBS Fourier magnons

The source is Bachmann–Nachtergaele, arXiv:1112.4097, Section II after
equation (8), with one species, zero phase and critical hopping μ = 1.

- The existing actual local-projector formula is restricted to the whole
  one-particle sector, not just the constant-amplitude W vector.
- Double occupation vanishes there, leaving the singlet exchange term.
- `SpinChain.oneMagnon_edge_sum` gives the cycle Laplacian action.
- Existing `ZMod.cycleLaplacian_stdAddChar`, `cycleFourierGap_pos`, and
  `exists_large_cycleFourierGap_pos_lt` supply the first Fourier eigenpair,
  positivity at every length at least two, and arbitrarily small energies.
- Positive energy and symmetry prove orthogonality to the entire actual
  kernel. Vacuum orthogonality alone would be insufficient at criticality.
- No eventual positive norm-gap constant exists. This does not assert a
  zero gap above the enlarged ground space at any fixed finite length.
- The noncritical exact-gap consumer reuses the generalized one-particle
  argument; its theorem signatures and bounds remain unchanged.

No new Hamiltonian, Fourier transform, state representation, or gap
predicate is introduced. The multi-species conjecture and an explicit
infinite-volume operator construction remain outside the result.
