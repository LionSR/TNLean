# Physical buffered targets at a prescribed error

The five-region low-energy target comparison is factored with an
arbitrary nonnegative projection-loss parameter `nu`. The actual
regional minima, common regional ground vector, centered global ground
vector, clipped matrix, norm bound and spectral bases are still
constructed from supported positive-contraction nearest-neighbour terms.
There is no global spectral-gap premise or assumption that the inner
spectral band consists of one eigenvalue.

The explicit residual is

    xi = 288 * exp(11/8) * exp(-(ell - etaLD)/8).

Under `xi ≤ 1`, the numerical budget
`2 * (6 + etaLD) * xi ≤ nu * w²` gives both original/clipped
comparisons with loss `nu`. The comparison uses the same centered
ground energy and the same two clipped spectral cutoffs as before.
The old public `1/200` statement has a byte-identical signature and
specializes this one proof. The spectral-cutoff inclusion reuses the
shared companion order lemma.

This is a conditional supporting comparison for ALVV,
arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1027–1041. The
residual budget is displayed, not assumed to hold for every choice of
accuracy. Deriving its decreasing values from the actual enlarged
count bases and constructing the corresponding improving families
remain the next steps. No entropy or MPS theorem is asserted here.

The temporary diagnostic source was removed. Ordinary combined compilation and
compiled blueprint checking remain integration checks.
