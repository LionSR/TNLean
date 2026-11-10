# Finite Gaussian error reduction for a positive nearest-neighbour chain

The physical construction begins with positive contractions on adjacent pairs of
sites. It chooses one finite family of Gaussian approximants from the Hamiltonian,
gap parameter and precision, before a ground energy or ground vector is supplied.
The energy window is the fixed interval from minus the chain length to the chain
length. The actual finite quadrature and actual local propagation approximation
are used at every mesh point.

For each unit ground vector with the prescribed spectral gap, one member is within
four times the filter precision of a positive multiple of the rank-one ground
projection. The ground amplitude lies between one half and one. Taking a union of
the left factors of all members gives at most the energy count times the rank
budget operators. Acting with every factor on every input vector constructs a
finite output set. An input half-viable set gives an output set viable with error
at most the prescribed constant divided by the chain length. The proof constructs
the support witness and derives the individual MPS bounds from cut ranks.

The main conclusions are `exists_positive_chain_ground_filter_family` and
`exists_positive_chain_error_reduced_set`. Their quantifier order is essential:
the finite family is chosen before the universal quantifiers over ground pairs.
The true ground energy occurs only in the proof that some mesh point is suitable.
The spectral gap, the approximate projection, and the left-factor decompositions
are not supplied as construction hypotheses. Only the physical local terms and a
positive gap parameter are supplied; the gap condition is required when asserting
the improvement for a particular ground pair.

The parameters satisfy a uniform polynomial count and rank estimate at fixed local
dimension, gap and precision constant. This is a conservative replacement using
Huang, arXiv:1406.6355v6, Section 5.4, Lemmas 18--19. It does not assert the sharper
printed LVV quantitative bounds or a running-time theorem. The distinction from
the energy-dependent LVV power sampler is recorded in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`.

Strict checks of the complete preliminary mathematical modules passed before
promotion into the final files: the three filter-family theorems in 24.979 seconds,
and the two factor-collection and viable-filter theorems in 17.352 seconds. These
checks used only existing dependencies and temporary outputs. The final production sources passed strict checks in 26.355 and 5.730 seconds,
respectively. Manual imported foundation checks of all five public declarations
report only `propext`, `Classical.choice` and `Quot.sound`. The 26.355-second
check exceeds the local warning threshold of 25 seconds; it is below the
50-second failure threshold. Ordinary integration remains a separate required check. No permanent test or foundation fixture is added.
Mathlib is supplied entirely by the pinned prebuilt cache.

The successive induction still has to compose this improvement with extension,
size trimming and independent bond trimming. This report does not count that
induction as completed by the single-step result.
