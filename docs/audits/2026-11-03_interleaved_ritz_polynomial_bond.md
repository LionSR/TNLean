# Uniform polynomial bond for the actual interleaved Ritz output

The theorem `exists_physical_dg_interleaved_ritz_polynomial_approximation`
selects the actual compressed Ritz space constructed by
`exists_physical_dg_interleaved_tree_ritz_approximation`. Its coefficient and
natural degree depend only on the local dimension and positive gap, and precede
length, Hamiltonian, ground multiplicity and requested accuracy. The output has
the full ground-space dimension, both closeness errors are at most half the
requested accuracy, and every vector in that same space has the stated uniform
polynomial open-MPS bond.

The proof derives the logarithmic bound for the actual length-dependent filter
count, its sample ceiling and both reference accuracies. It uses the positive
contraction Hamiltonian estimate to bound the spectral width by the length.
No desired polynomial bound, reference space, trial-energy condition or final
viable space is assumed. The proof uses neither the older one-final-trim tree
nor an independent MPS existence theorem.

The result supports ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817, within
the explicitly modified construction. Block leaves, the fixed nominal sampling
scale and failure target, the capped gap and enlarged integer counts remain.
The quantitative bound is coarse; the printed sharp dependence, adaptive joint
probability, energy-estimation invariant and running time are not claimed.
The relevant deviations remain in `docs/paper-gaps/alvv16_approximation_parameters.tex`
and `docs/paper-gaps/alvv16_final_filter_gain.tex`.
