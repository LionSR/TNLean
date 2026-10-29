# Interior low-energy parameter substitution

The source is ALVV, arXiv:1602.08828v2, Theorem 4.8 (`t:aisgapless`,
`local_alg_arxiv_v2.tex`, lines 1027–1041). Assumption (LD), lines 279–286,
fixes a positive density bandwidth. The local source SHA-256 is
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

## Statements and quantifiers

`Real.low_energy_threshold_le` bounds the prescribed physical threshold at
comparison error `1/200`, uniformly over smaller target bandwidths. With
`C = 288 exp(11/8)` and `g = min(w,1)`, it proves

```
t ≤ T + 16 log(1/g),
T = 21 + eta_LD + 8 log(400 C (6+eta_LD)).
```

`Real.exists_low_energy_scalar_parameters` chooses one constant at fixed
`eta_LD > 0`, before the local dimension, target bandwidth and buffer.
For `u = 1+log q+log(1/g)` and `ell = ceil(A u²/g)`, its actual count is
`D = (q ell²)^(20 ell)`. It proves the exact logarithmic estimate

```
log D ≤ 22(A+1)(6+2log(A+1)) u³/g
```

and the strict finite inequality `D^12 Delta < 1/100000` for the physical
Chebyshev parameter. The scalar statement takes the threshold formula and
physical lower bound `19+eta ≤ t` as explicit numerical inputs. The physical
corollary constructs both of those inputs; they are not additional
Hamiltonian assumptions.

`TNLean.MPS.AreaLaw.exists_interior_low_energy_original_filter_family`
chooses that constant before the chain length `L`, coefficient `mu`, local
dimension `q`, target bandwidth `eta` and Hamiltonian. It substitutes
`w = mu/(3log L)` under `L ≥ 2` and `2mu/log L ≤ eta ≤ eta_LD`, deriving
`eta ≥ 6w > 3w`. For the stated interior geometry, it applies the actual
physical family constructor. Its regional minima, attained original ground
energy, threshold formula, clipped norm budget and common family are derived
internally. The family precedes every viable subspace and error parameter.
No rank, closeness, contraction or tensor decomposition is assumed.

## The strict tradeoff

The existing scalar theorem allows the auxiliary count
`D_aux = (q ell²)^(22 ell)` and width `4g/5`. The actual filter width is
`w ≥ g`, and its denominator is bounded by `(3T+52)ell`. Thus its squared
contraction is no larger than the auxiliary contraction. Since `q ell² ≥ 2`
and `ell ≥ 21`, the actual count satisfies `D < D_aux`. Positivity of the
actual contraction turns the existing non-strict auxiliary budget into
`D^12 Delta < 1/100000`.

## Original spectral windows and remaining scope

The same family transfers viability between the original windows
`E0+eta` and `E0+eta-3w`, the latter equal to `E0+eta-mu/log L`.
For `delta ≥ 0` and `2(delta+1/200)<1`, the exact output error is

```
2 * (Delta / (1 - 2*(delta+1/200))² + 1/200).
```

The clipped-filter parameter and this original-window error remain distinct.
In particular, the additive comparison error is already `1/100`; no final
original-window `1/100` bound is asserted. A smaller target requires retuning
the comparison accuracy.

The exact count retains `g = min(mu/(3log L),1)`. It is not identified with
an uncapped finite-length formula or asserted to be the printed soft
asymptotic rate. The statement is restricted to the interior five-region
geometry. It does not construct short or boundary regions, the low-density
bootstrap or the sampled tree. These remaining tasks and the finite-length
qualifications are recorded in
`docs/paper-gaps/alvv16_low_energy_family_buffers.tex`.

## Verification

Both new modules were checked separately against frozen TNLean proof-source
commit `22519023a42896c04763ad0497970964481daaff` and exact package QICLean
revision `637184a66a8c2215adec3bd28fc1a872ca382836`. The provider's
`cf425db58435d5316ee9ce0087abc221d9029002` successor changes only completion
documentation. Subsequent unrelated source-only additions were permitted;
existing imported sources, build inputs and load-bearing object hashes were
guarded. Private output namespaces contain links to existing compiled
objects and new outputs only. No cache was copied or modified, and no
Mathlib source was compiled.

Strict checks passed with warnings as errors:

- `LowEnergyFilterParameters`: 3.933 s, source SHA-256
  `3c7b2781383ee4d7e087801664556bd6869700bdff7b0dcdac596ac3a52f83d0`.
- `InteriorLowEnergyFamily`: 10.374 s, source SHA-256
  `84b83ec72562a6a411268088d7e99fa512ece90aaafe7314926629bdac50b796`.

The imported foundation audit of all three public declarations reports only
`propext`, `Classical.choice` and `Quot.sound`. Both source checks are below
the 45-second changed-module budget. Import-aggregator validation,
proof-pattern scanning, whitespace checks and compilation of the revised
paper-gap note pass. Ordinary integration and blueprint declaration checks
remain pending; no new completion marks or permanent theorem fixtures are
included.

The collection-wide paper-gap verdict check accepts the revised buffer note
but still reports the pre-existing malformed marker in
`alvv16_approximation_parameters.tex`; that older note is unchanged here.
