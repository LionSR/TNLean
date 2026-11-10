# Capped-gap dependence of the actual interleaved output degree

The exact degree chosen by the variable-count estimate is
`10 * (24 * p + 21) * p0 + 60 * p + 43`, where
`p = ceil (2 KD)` and `p0 = ceil (K (u³/g + 5 g^(-1/4) u))`.
The new theorem exposes this actual degree. The earlier public theorem keeps
its signature and is an active corollary; the substantial polynomial proof
is shared without copying it.

For U at least one, u between zero and U, and a capped gap 0 < g ≤ 1,
KD ≤ CD U^7/g implies
k ≤ Cdegree U^10/g². The constant is explicitly
10(24(2CD+1)+21)(6K+1)+60(2CD+1)+43.
The physical count coefficient satisfies the needed bound with
CD = A(18^7+18^4). No fixed-count substitution is made.

The corresponding TNLean consequence applies this degree to the actual
interleaved-tree Ritz output. It chooses one universal positive degree
constant before local dimension and gap. The prefactor is kept as a separate
finite function of those parameters. Neither a comparable prefactor bound
nor a running time is claimed. When the original gap exceeds one, the
estimate continues to use its cap; no unrestricted sharp-gap claim is made.
