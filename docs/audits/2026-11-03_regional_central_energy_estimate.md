# A one-sided energy center for the middle region

The actual original interaction sums on [l,u), [u,v), [v,r) and [l,r)
are used, with l<=u<=v<=r<=L. The positive local dimension and designated
nearest-neighbour support assumptions are those of the existing chain
Hamiltonian estimates, with 0<=h_i<=I. No regional energy or minimizing
vector is an input.

`exists_regional_central_energy_estimate` constructs attained minima
(eLeft,eMiddle,eRight,eParent), normalized attaining vectors and positive
centered matrices before every parent estimate. It proves

    eLeft+eMiddle+eRight <= eParent <= eLeft+eMiddle+eRight+2.

Consequently every pParent in [eParent-8,eParent] gives

    pMiddle = pParent-eLeft-eRight-2 in [eMiddle-10,eMiddle].

The two adjacent-interval constructions are applied at u and v. They
construct two possibly different normalized ground vectors for the
remaining interval [u,r). Their ground energies agree by the existing
comparison of normalized eigenvectors attaining positive-semidefinite
lower bounds. Combining the two one-bond bounds gives two. No common
minimizing vector for all three child intervals is assumed or needed.
Weak cuts, empty intervals, L=0 and local dimension one are retained.

The comparison does not require short collars. In the intended central
soft replacement, the collar supports have at most 2ell sites. The
energies here are the minima of precisely those original internal sums,
not of substituted local matrices. Identity extension does not change
these minima. No algorithm or running-time estimate for computing them
is asserted.

This is a corrected auxiliary to ALVV, arXiv:1602.08828v2,
`def:soft-trunc`, lines 1178-1185, and `eq:defjgapped`, lines 1380-1384.
It supplies the source's one-sided middle interval from an explicit
width-eight one-sided parent estimate. It does not establish the source
efficient-generation theorem for its broader absolute-error input.
The recursive construction of the required parent estimate remains a
separate task. See the updated energy-centering paper-gap note.

The actual production module passed strict private checking in 4.740
seconds at default budgets against immutable TNLean
20cad76ebfa6e770263c4a5d5333917c5b226ed9 and its own QICLean
98ba564e3c9603dc93d2173e3dc87a85ce750456, with 115 selected source/object
pairs guarded. The imported public foundation audit reports only
propext, Classical.choice and Quot.sound. Its exact result and all source
hashes are recorded in the manifest. New objects and temporary foundation
commands remain under /tmp; no provider or shared cache was modified,
and no Mathlib source was compiled. Ordinary combined and compiled
blueprint checks remain required after adoption.
