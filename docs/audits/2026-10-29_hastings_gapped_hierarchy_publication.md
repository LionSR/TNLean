# The periodic hierarchy from the original unique ground-state gap

For a periodic finite-range Hamiltonian with a specified unique gapped
ground vector, the local residual condition needed by Hastings' hierarchy
can be derived from the original gap. This result supplements the existing
physical hierarchy, whose statement assumes that condition.

The reference is Hastings, *Solving gapped Hamiltonians locally*,
arXiv:cond-mat/0508554v3, `proj3new.tex`: the unique-ground estimate at
lines 375–387, the local residual condition at lines 493–507, and the
hierarchy at lines 609–743.

For interaction radius `R`, norm bound `J`, and gap `Delta`, the constants
are selected before the chain length, local dimension, interactions and
ground data. If `c1`, `etaLoc`, and `C` are the localization constants,
choose `eta = min(etaLoc, c1 Delta/2)` and `Jb = 2 max(J, JC)`.
The local residual is then bounded by

`J exp(-c1 ell Delta/2) + JC exp(-etaLoc ell) ≤ Jb exp(-eta ell)`.

The existing quadratic-logarithmic radius gives a normalized vector in
the final retained space and all descendant spaces. Its distance from the
specified ground vector is at most `2 (3^(h+1)-1) exp(-eta ell/8)`.
The original rank-one ground projection has trace one, so the existing
physical-gap comparison bounds the final retained dimension by two.

The spectral windows are centred at expectations in the specified ground
vector. No claim is made about obtaining those centres without that
vector, algorithmic running time, intermediate tensor dimensions, or a
basis construction for a general degenerate ground space. The existing
notes `hastings05_hierarchical_projection.tex`,
`hastings05_hierarchical_energy.tex`, and
`hastings05_two_dim_ground_basis.tex` record the corresponding corrections
and distinctions. The blueprint states this unique-ground scope explicitly.

## Source and verification

The new module is extracted without proof changes from TNLean revision
`5148dccca8`; its SHA-256 is
`e833d3541f9b21a2d611fdc03dc1cdac4cab77ad81f51aacfd907bc7d6961927`.
The existing source definitions and dependency pins are preserved. In
particular, older integration copies of `Lattice/ProductForm.lean` and
`Lattice/GaussianFilteredTermLocalization.lean` are not included.

The source passed an initial strict elaboration with Mathlib standard
linters and warnings as errors in the AKLV verification checkout. The
ordinary build at the unchanged main dependency pin, axiom check and
blueprint checks are recorded in the pull request when complete.
