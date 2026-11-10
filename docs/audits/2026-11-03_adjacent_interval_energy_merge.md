# Actual adjacent-interval energy estimates

For arbitrary adjacent intervals `[l,m)` and `[m,r)`, including empty intervals and endpoints, the proof constructs the attained minima of their actual internal Hamiltonians and of the parent internal Hamiltonian. The child operators have a common unit minimizing vector. The parent minimum lies between the sum of the child minima and that sum plus one. Consequently, two lower child estimates each within three add to a lower parent estimate within seven.

All data come from the original nearest-neighbour positive contractions and positive local dimension. The parent bonds are partitioned into the two internal child sets and the internal bonds crossing `m`. That last set has cardinality at most one, so its actual sum is a positive contraction. Support and positivity of the two actual child sums are supplied by the existing five-region bond decomposition. No spectral gap, regional minimum, eigenvector, norm cap or separate decomposition is assumed.

The theorem is auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1627–1632, and the energy-estimation argument at lines 1805–1807. It establishes an original-Hamiltonian energy relation. It does not identify the source's generated soft Hamiltonian with that original regional operator, prove the full recursive energy invariant, or assert running time.

Combined adoption checks remain required.
