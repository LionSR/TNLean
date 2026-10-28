# Gap normalization for a unique ground state

For a nonempty open chain of local dimension at least two, let
\(H=\sum_{j=0}^{L-2}h_j\), where each \(h_j\) is supported on the adjacent
sites \(j,j+1\) and \(0\le h_j\le I\). If a unit ground vector \(\Omega\)
satisfies the rank-one gap inequality
\(H-E_0I\ge\Delta(I-|\Omega\rangle\langle\Omega|)\), then
\(\Delta\le1\).

This is the normalization stated in AKLV, arXiv:1301.1162v1,
Section 5 before equation (4). The declaration
`TNLean.MPS.AreaLaw.gap_le_one_of_positive_nearest_neighbor_terms`
proves it directly for the original physical interactions. A cyclic unitary
in an eigenbasis of the first-site marginal gives an orthogonal unit trial
vector. All bonds except the first commute with this unitary; the change
of the remaining expectation is at most one.

The rank-one gap inequality matters. This argument does not establish the
same normalization for a degenerate ground space and does not remove the
capped gap from the separate ALVV estimates.

The strict module check and ordinary module build passed; the latter
completed 3,731 jobs with cached Mathlib artifacts. An imported foundations
inspection of the new theorem reports only `propext`, `Classical.choice`,
and `Quot.sound`. The blueprint statement and proof have been synchronized.
Further integration checks are recorded separately with their exact revision.
