# A common low-density count and suppression scale

The physical low-energy interval construction now admits an analytic count
base m≥q chosen before the filter degree. Its original local dimension is
still q. At fixed density bandwidth etaLD>0, one constant A≥100 precedes
L,q,m,mu, the interval and the nearest-neighbour Hamiltonian. With

    w = mu/(3 log L),       g = min(w,1),
    u = 1 + log m + log(1/g),
    ell = ceil(A*u²/g),     D = (m*ell²)^(22ell),

the construction proves both an actual family with at most D² members and
D¹²*Delta<10⁻⁵ for that same family and degree. It retains the original
upper and lower spectral windows, the two clipped target spaces and their
comparison errors, and the literal image span of each chosen viable
subspace. The choices still precede every viable subspace.

The suppression estimate is obtained by applying the scalar theorem at m,
then comparing its denominator and width with those of the physical
polynomial filter. It is not inferred by padding a native-q count after
choosing that filter. On a short region, actual configuration matrix units
are extended to the chosen count, and their positive error is chosen after
D. The prior public native-count signatures remain their m=q
specializations.

For later dyadic use, QICLean's `PolynomialFilterCounts` proves an exact
logarithmic comparison for this actual natural count when A≥100 and
log m≥100. Halving a capped width changes log D by at most 13/6. This
contribution supplies the common calibrated scale, not the subsequent
low-density dimension induction.

## Ownership and source scope

The existing two-sided ceiling estimate was moved unchanged into QICLean's
Mathlib-only `Analysis/PolynomialFilterCeil`. Both known TNLean consumers
now use that one shared proof. No generic companion theorem imports
TNLean. The companion source checkpoint is
`c15787d256b42289c5037252ab1381b23b1919ca`.

These are auxiliaries to ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`,
lines 1027–1041, and the dyadic argument at 1112–1128. The original length
and dimension scope L≥2,q≥2 and the distinction between clipped improvement
and original-window comparison loss remain explicit. The paper-gap note
`docs/paper-gaps/alvv16_low_energy_family_buffers.tex` records them.
No low-density bootstrap, adaptive sampled tree, entropy, MPS approximation
or running-time conclusion follows from this checkpoint alone.

## Verification

Actual-name strict private checks used the read-only common TNLean revision
`9ad6cdd3c23da0ce9b5e6cc36edfec99f0211ff7` and its own QICLean package
`e51354163d2dd9cf2a15d65722c544c6b4736182`. Fresh outputs and import overrides
are below `/tmp/tnlean-alvv-ld-calibration-20261029`. Each invocation
checked selected source/object hashes and build inputs before and after
elaboration. No cache was copied or changed; no ordinary build or Mathlib
source compilation was started.

- `PolynomialFilterParameters`: strict private check passed in 13.147 seconds; source SHA256 `6e7cbb48799ab35fa1ca850df4d9894bf70ddcbabd1167ef87d8b23ab210d621`.
- `LowEnergyFilterParameters`: strict private check passed in 28.679 seconds; source SHA256 `07481cbd6ee40c4b97a8f8d88b7850f59186c36f5b04249021fa8bbb16937686`.
- `ShortRegionViableFamily`: strict private check passed in 26.958 seconds; source SHA256 `845549f848b66e7dfb378627f35d71efd1ac69ab081b495a88d2931b80a409d4`.
- `InteriorLowEnergyFamily`: strict private check passed in 34.595 seconds; source SHA256 `5eeb232cd975802d26f5ac653afb3a21edc581fd4377458529c5e7c38996aa53`.
- `LowEnergyIntervalFamily`: strict private check passed in 18.012 seconds; source SHA256 `8ca52b5d5f24561ad3b16760756351c20e4749807a432937323011fc5f875731`.

The first interval check took 117.441 seconds under contention. The final
check against the extracted companion helper and updated private import
context took 18.012 seconds.
The original contention measurement is retained; no timing limit was raised.

A temporary imported inspection of nine public declarations found only
`propext`, `Classical.choice` and `Quot.sound`. It is kept under `/tmp`,
not as a permanent fixture. Ordinary coordinated-library and compiled
blueprint gates remain pending. Source synchronization is checked using
read-only dependency source paths because this source-only worktree has
no Lake directory.
