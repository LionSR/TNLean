# An actual native soft middle with its own spectral cluster

The public auxiliary `ALVV.exists_physical_soft_middle_cluster` chooses
one soft order, scale and residual cutoff from the positive gap and requested
error before the chain. Its natural geometry has endpoints
`0,a+1,a+2ell,b+1,b+2ell,N+1`, with `q >= 2`, `ell >= 1`,
`a+2ell <= b` and `b+2ell <= N`.

The uniform five-region construction is called once. It supplies the same
actual regional minima, one common normalized minimizing vector and a
centered ground energy in `[0,4]`, before every estimated center. The lower
order bound for the middle follows from its minimum certificate and
`p2 <= e2`; it is a conclusion, not an additional hypothesis.

For each admissible center tuple, the native approximation theorem is called
once at the explicit precision
`xi = min(1,tau*g^2/(20000*(M+g+8)))`, where
`M = 3*t*(1+log m)+4*ell+34`. The actual native tensors, their closing
matrix, exact principal-slice reconstruction, native error and full-chain
error are all retained. The raw middle term is replaced in the same
centered soft matrix, so `Ghat = G-F2+Zphys` and
`norm(Ghat) <= M+xi`.

These tensors precede every original ground spectral value satisfying the
original gap condition. The uniform comparison is applied to this very
`Ghat`. It derives the energy shift, equality of its closed low spaces at
`E+g/4` and `E+3g/4`, equality with the original full ground-space dimension,
and both directed errors `3*tau/200`. No soft gap, target comparison,
residual estimate, tensor representation or successful construction is
supplied as a premise.

## Scope

This is a pointwise approximation after the estimated centers are chosen.
Its tensors are not identified with a different approximation merely
because the two have the same error bound. In particular, it does not
assert one common tensor expansion before the centers, adaptive center
measurability, a sampling law, an improving family or running time.
The scalar order is selected by an existence theorem; no fixed order of
four or quantitative bound on that selection is asserted. The corrected
interaction-label and soft-residual estimates are cited in the module and
blueprint, and the unrestricted efficient source theorem is not marked
complete by this auxiliary.

## Verification

The immutable provider was TNLean
`6dcb693b498041f9f0e2efb8df37a5474aac2b17`, with its own QICLean package
`79fb1403dd2ec8ca448204f89ccef73c1a77f509`.
The final actual module passed strict private checking in 9.598 seconds,
with 561 selected source/object pairs guarded before and after. No import
overrides were required. An imported inspection passed in 9.142 seconds
with 562 guarded pairs and reported only `propext`, `Classical.choice`
and `Quot.sound`. Its temporary source was deleted.

All attempt sources and their diagnostics remain separate and immutable
under `/tmp/tnlean-physical-soft-middle-cluster-20261103`. The final
handoff uses `frozen-overrides.json`; the earlier provisional map remains
attached to its original, also checked source. No in-flight source,
provider, dependency pin or cache was changed, and no Mathlib source was
built. Full library and compiled blueprint verification remain coordinated
integration checks.
