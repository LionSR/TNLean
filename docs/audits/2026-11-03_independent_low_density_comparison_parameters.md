# Independent scales for the low-density comparison

The actual buffered-target construction now allows an independent real clipping
threshold t and integer window ell. The original supported positive-contraction
nearest-neighbour data still determine the regional minima, common regional
ground vector, centered original ground energy, clipped matrix and eigenbases.
The norm bound is 3t+4ell. A residual budget over the fixed bandwidth supplies
both original/clipped spectral comparisons with prescribed nonnegative error.
No spectral gap, invariance or supplied spectral-basis premise is introduced.

The one physical proof and its one ceiling-budget calculation were moved to
IndependentLowDensityBufferedTargets. The two existing public statements in
LowDensityBufferedTargets have byte-identical signatures and specialize t=ell.
Their norm bound follows from 3ell+4ell=7ell; no comparison proof is copied.

The new scalar choice reuses the existing independent-threshold estimate at
buffer g squared and accuracy delta/(6+eta). With a=16+log(1/g)+log(1/delta),
one fixed-bandwidth constant gives t=C_eta*a, actual residual xi<=1 and
2(6+eta)xi<=(delta/100)g^2. The existing fourth-root window selection gives
ell<=8/g+(7C_eta)^(1/4)g^(-1/4)a^(3/4) and Chebyshev squared error<=delta/8
for every positive denominator at most 3t+4ell. No exponential-threshold or
fourth-root argument is duplicated. The physical dimension and terms remain
unchanged.

This supports ALVV, arXiv:1602.08828v2, the low-density improving family at
lines 1027–1041 and approximation theorem at 1096–1105. The fixed bandwidth
is explicit. These are conditional physical-comparison and scalar results;
the actual sharp family, fixed-cut approximation and global MPS are not
claimed here. The scope note remains
`docs/paper-gaps/alvv16_low_energy_family_scope.tex`.
