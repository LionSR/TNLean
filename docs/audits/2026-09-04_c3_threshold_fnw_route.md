# C3 threshold routed through the FNW projector estimate (2026-09-04)

The projector-defect estimate that Nachtergaele imports from
Fannes--Nachtergaele--Werner was formalized and then bypassed. The proved
source estimate `MPSTensor.wholeIncrement_groundProjection_defect_le_fnw_factored`
had no consumer, while the threshold feeding every gap theorem,
`TNLean/MPS/ParentHamiltonian/Martingale/C3Threshold.lean`, called an
inverse-Gram reconstruction whose coefficient `(1 - c*r^l)⁻¹ * (C*r^l)` carried
an unidentified constant `C` and a generic `D^{3/2}` reshuffle factor from
`Matrix.gramReshuffle_norm_sq_le_card_cube_mul_opNorm_sq`.

The threshold now runs through the source chain: FNW 1992 Lemma 6.2 gives the
coefficient `a(m)(1+a(m))/a_-(m)`; equation (5.9) gives `1 - a(m) ≤ a_-(m)`;
Lemma 5.2 gives `a(m) ≤ c*λ^m` for any prescribed rate above the rho-weighted
spectral radius of the transfer remainder. Composing them yields the printed
display, `References/cond-mat_9410110/main.tex` lines 1180--1194 and 2401--2412.

## Removed declarations

| Removed declaration | Replacement |
| --- | --- |
| `MPSTensor.IsPrimitiveMPS.wholeIncrement_groundProjection_defect_le_geometric` (`TNLean/MPS/ParentHamiltonian/WholeIncrementProjectorDefect.lean`) | `MPSTensor.IsPrimitiveMPS.exists_wholeIncrement_groundProjection_defect_le_fnw_geometric` (`TNLean/MPS/ParentHamiltonian/FNWGeometricDefect.lean`) |
| `MPSTensor.IsPrimitiveMPS.openChain_groundProjection_defect_le_geometric` (`TNLean/MPS/ParentHamiltonian/OpenChainProjectorDefect.lean`) | `MPSTensor.IsPrimitiveMPS.exists_openChain_groundProjection_defect_le_fnw_geometric` (`TNLean/MPS/ParentHamiltonian/FNWGeometricDefect.lean`) |
| `MPSTensor.c3CenteredProjectorResidualES` (`TNLean/MPS/ParentHamiltonian/WholeIncrementProjectorDefect.lean`) | none; the reconstruction it centred is gone |
| `MPSTensor.c3CenteredProjectorResidualES_norm_le` (same module) | none |
| `MPSTensor.c3_injectiveRangeProjector_residual_eq_centered_sub_corrections` (same module) | none |
| `MPSTensor.wholeIncrementCenteredProjectorResidualES_norm_le` (same module) | none |

The three deleted modules are
`TNLean/MPS/ParentHamiltonian/WholeIncrementProjectorDefect.lean`,
`TNLean/MPS/ParentHamiltonian/OpenChainProjectorDefect.lean`, and the re-export
shim `TNLean/MPS/ParentHamiltonian/FNWContraction.lean`, which became empty. The
two `**Scope restriction (Nachtergaele C3 coefficient)**` markers lived in the
first two modules and are gone with them.

## Statement changes

The C3 threshold theorems now quantify over positive prefix lengths only. The
FNW estimate is stated for `0 < r` and `0 < ℓ`, matching the source domain
`ℓ ≤ 1, r ≥ m` of the best overlap constant, and matching the domain of
Nachtergaele's martingale difference, which needs a nonwrapping window. Both
Lean consumers,
`MPSTensor.IsPrimitiveMPS.exists_fixedAmbient_martingaleDifference_norm_lt_c3_threshold`
and the blocked three-site route in
`TNLean/MPS/ParentHamiltonian/Martingale/BlockedGap.lean`, already supplied a
positive prefix length, so no downstream statement changed.

The affected theorems are
`MPSTensor.IsPrimitiveMPS.exists_uniform_wholeIncrement_defect_le_seven_sixteenths`,
`MPSTensor.IsPrimitiveMPS.exists_openChain_groundProjection_defect_lt_c3_threshold`,
and
`MPSTensor.IsPrimitiveMPS.exists_re_inner_openChain_anticommutator_ge_c3_threshold`.

## Remaining residue

The prescription for the rate is now the source's own: any number strictly
above the moduli of the nonunit transfer eigenvalues and strictly below one.
The prefactor is not. Nachtergaele states that it may be taken equal to `k²`,
the dimension of the auxiliary space of the pure state; the formal prefactor is
the existential rate-dependent constant of Lemma 5.2. Establishing `c = k²`
needs a quantitative theorem that the inspected primary sources do not supply
for an arbitrary faithful stationary density and every prescribed rate, plus an
identification of the minimal auxiliary dimension with the bond dimension used
here. That residue is recorded in
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`.

## Follow-up

`TNLean/MPS/ParentHamiltonian/WholeIncrementCorrectionBounds.lean` (618 lines,
15 public declarations) is now imported only by the root aggregator: its
finite-Gram correction maps and their norm estimates existed to feed the deleted
reconstruction. The same holds transitively for parts of the inverse-Gram
convergence chain it rests on. Removing that scaffolding is a separate deletion,
because it also removes about fifteen Chapter 13 blueprint nodes.

## Convention

The pass-through exception at `docs/project_conventions.md` §Style applies. No
`@[deprecated] alias` is warranted: TNLean promises no stable public Lean API,
every removed name is migrated or has no successor, and no surviving blueprint
`\lean{...}` tag or paper-gap `\leanid{...}` citation names a removed
declaration.
