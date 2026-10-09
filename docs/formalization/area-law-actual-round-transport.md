# Transport for the actual finite family of scan rounds

`TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport` applies
`TensorPower.ReplicaTransport.transport_finite_family` to the actual fill and
charge rounds of one collar scanner. The statement is a finite-family
consequence of Proposition 7.4 of *A two-dimensional area law from a global
spectral gap*.

## Computed finite family

For one fixed `S : CollarScan`, the round index is literally
`Fin (2 * S.n * S.m)`. The family is defined by:

- `actualRoundHistory S j`: `History S.K S.m S.M (j.val / 2)`.
- `actualRoundChoice S j h`: `ChargeChoices S.K S.M` when
  `IsChargeRound j.val` holds, and `Unit` otherwise.
- `actualRoundData S hm hM j`: the actual charge data in the odd branch and
  the actual fill data in the even branch, both at history length `j.val / 2`.

Round zero is a fill. The first fill and charge use history length zero;
rounds two and three use history length one. The fill/charge parity does not
replace the physical-side scheduler, whose argument remains `j.val / 2`.
All slots, including blank physical moves, are retained. The inequality
`j.val / 2 + 1 ≤ S.n * S.m` is derived from the bounded index rather than
assumed. It covers the final charge at history length `S.n * S.m - 1`.
Finite and decidable instances for the conditional choice types follow by
parity. These are computed definitions, not a new structure storing desired
transport conclusions.

Both branches use exactly `S.K` bands, one common dimension family
`augmentedDimensions q aux`, and one common energy family
`S.actualEnergyTerms h Ω Δ L aux`. Neither padding nor a maximum band count
is needed. There is no positivity assumption on `S.K` and no requirement that
`q > 1`. The two nonzero auxiliary dimensions are arbitrary and fixed before
the common errors; they are excluded from physical subsystem dimension caps.
Original Hamiltonian support labels, repeated or zero terms, and both
split-probability factors in `energyError` are retained.

## Statement and quantifiers

`actualRounds_transport_domainGraph` uses this order:

1. Universal `c₀, Cent, eent, Cen, een`, with `0 < c₀`, selected once from
   QICLean's finite-family theorem.
2. The fixed physical system, ordered admissible interaction supports,
   Hamiltonian, unit vector, positive filter scale, scanner, truncation depth,
   auxiliary dimensions, and positive `a` with
   `a * transportLogDimBound q S.r₀ ≤ c₀`.
3. Common `β rem : ℕ → ℝ` and `Cβ : ℝ`, with `0 ≤ Cβ`, `β ≥ 0`,
   `rem ≥ 0`, `β k ≤ Cβ * log(k+2)` for every natural `k`, and
   `rem k → 0`.
4. Every round `j`, replica count `k`, and supplied nonzero symmetric `pre`.
5. Interior interpolation parameters for the derivative, entropy, and energy
   conclusions; ordered endpoints in `[0,1]` for the integrated entropy bound.
6. Only within the energy clause: `E₀` and the equation
   `Hbar k *ᵥ pre = (E₀ : ℂ) • pre` for the actual replica energy.

The physical premises are the induced domain graph, ambient depth relative to
nonempty `T`, anchors in their support labels, positive `Δ`, unit `Ω`, `0 < S.n`, `S.r₀ ≤ S.D`, `1 ≤ S.D`,
`4 * S.D ≤ S.m`, `8 * S.K * S.m ≤ L`, positive `S.C₁`, the shell-cardinality
bound through `L`, and boundary clearance `2*L+10*S.r₀`. The round-length
hypothesis is replaced by the derived inequality above.

The conclusions are the exact log-filtered-norm derivative, entropy lower
bound with coefficient `Cent * k * a * S.K * a^(1/4) * ℓ^eent`, conditional
energy upper bound with coefficient `Cen * a^2 * ℓ^een`, and integrated entropy
bound including both endpoints. Here `ℓ = transportLogDimBound q S.r₀`.
The common error sequences and their coefficient are chosen before `j`, `k`,
`pre`, parameters, or eigenvalue; they may depend on all fixed physical data,
auxiliary sizes, `a`, and the finite family. There is no uniform assertion for
a family of physical systems or auxiliary dimensions growing with `k`.

The complete mathematical statement and proof sketch are in
`blueprint/src/chapter/ch24_peps_area_law_scan_histories.tex`, at
`def:al_scan_actual_round_family` and `thm:al_scan_actual_round_transport`.
This is a finite-family consequence of Proposition 7.4, not a claim that all
of the source scanner has been constructed.

## Mathematical dependencies and energy identification

The module imports `TNLean.PEPS.AreaLaw.Scan.ActualTransportEstimates`,
`TNLean.PEPS.AreaLaw.Scan.Defs`, and
`QICLean.Representation.ReplicaTransport.FiniteFamily`. The first supplies the
actual fill and charge constructions, the truncated positive energy terms,
physical support compatibility, commutation, and physical dimension estimates;
the second supplies the round-parity convention. No literal sphere-measure or
normalized-coefficient construction enters the theorem.

The theorem applies the QICLean finite-family theorem once, rather than
combining independently quantified constants from the two per-round results.
For each parity it uses the existing producers:

| Premise | Fill | Charge |
| --- | --- | --- |
| Admissibility | `actualFillData_isAdmissible` | `actualChargeData_isAdmissible` |
| Support compatibility | `fillTransportData_supportCompatible_domainGraph` | `chargeTransportData_supportCompatible_domainGraph` |
| Cross-band commutation | `fillTransportData_crossBandCommute` | `chargeTransportData_crossBandCommute` |
| Moved dimensions | `fillTransportData_logDim_move_le` | `chargeTransportData_logDim_move_le_domainGraph` |
| Split-support dimensions | `fillTransportData_logDim_support_le_domainGraph` | `chargeTransportData_logDim_support_le_domainGraph` |

`actualEnergyTerms_spec` supplies positive supported contractions. The cap on
a designated support retains the nonempty-split-leaf premise; unsplit supports
are not bounded. `replicaEnergy_actualEnergyTerms` identifies the one replica
energy with the copy mean of the augmented sum of actual truncated terms.
The identity rewrites the energy expression and eigenvector premise only.
No assumed admissibility, compatibility, dimension, or common-error certificate
is added to the physical theorem.

## Zero-copy boundary

At zero copies, `copyMean n 0 H = 0`, so `Hbar 0 = 0`. For nonzero `pre`, its
energy premise therefore forces `E₀ = 0`. The all-count statement retains this
premise; it does not identify `E₀` with a fixed physical ground energy. A later
physical construction needs a genuine zero-copy argument. The statement does
not impose exact frustration-freeness.
