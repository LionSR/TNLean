# Canonical original spectral targets for the physical low-energy family

The new `exists_fixed_bandwidth_five_region_canonical_low_energy_family`
uses the actual fixed-bandwidth family from
`exists_fixed_bandwidth_five_region_low_energy_family`. It retains the
same regional ground data, clipped matrix, middle operators, actual
polynomial and tensor factors. The constructed normalized ground vector
and positive-semidefinite lower bound identify the original canonical
minimum as $E_0+\sum_j e_j$. Every original centered spectral window is
then identified with the raw Hamiltonian's canonical window at its
minimum plus the requested bandwidth. Degeneracy and arbitrary real
cutoffs are included; no global spectral gap is assumed.

The resulting original targets depend only on the original Hamiltonian
and the requested cutoff. They do not depend on the selected regional
shifts or clipping scale. The identity is substituted into the upper
and lower original-window comparisons, retaining the actual filter. The
fixed bandwidth and interior five-region conditions remain unchanged.

This is a supporting corollary for ALVV, arXiv:1602.08828v2, Theorem
`t:aisgapless`, lines 1027–1041, and Proposition `prop:albootstrap-ld`,
lines 1112–1128. It is not the strict minimal-dimension induction. The
native interval $[a+\ell,b+\ell+1)$ varies with the scale. An induction
for one fixed physical interval still needs the arbitrary-interval
extension, including short and boundary intervals, or an explicitly
bounded common-fit range. An infinite interior-only schedule would not
discharge that requirement.

The generic centered-presentation comparison belongs to QICLean and
applies its existing scalar-shift theorem after eliminating matrix
equality. This avoids duplicating a matrix eigenbasis calculation in the
physical theorem. The derived nonempty configuration instance comes from
$q\ge2$; no additional physical hypothesis is imposed.

All selected source, object and input hashes, including the prebuilt Mathlib
sentinel, are guarded before and after checking. Changed-dependency importers
are re-elaborated. No provider, ordinary build or cache is changed.

This remains a 25-second review warning and is below the 50-second limit.
These are source-changing proof refinements, not timing-only retries or raised
verification limits.

The temporary diagnostic source was deleted. Ordinary compilation,
full-library verification and compiled blueprint checks remain integration
requirements.
