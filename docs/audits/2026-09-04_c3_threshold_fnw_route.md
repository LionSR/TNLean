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

None. The C3 threshold theorems quantify over every prefix length, as they did
before the rewiring.

An intermediate revision of this work narrowed them to positive prefix lengths,
on the reasoning that the FNW estimate is stated for `0 < r`. That narrowing was
reverted. The prefix positivity was already dead where it entered the chain: it
was bound as `_hr` in
`MPSTensor.wholeIncrement_groundProjection_defect_le_fnw`, whose docstring said
the estimate also holds at the zero endpoints, and whose two ingredients take no
positivity in the prefix or the spectator length. Dropping `0 < r` through
`_fnw`, `_fnw_factored`, `exists_..._le_fnw`, `_fnw_geometric`,
`exists_..._le_fnw_geometric`, and `exists_openChain_..._le_fnw_geometric`
restores the original quantifier in
`MPSTensor.IsPrimitiveMPS.exists_uniform_wholeIncrement_defect_le_seven_sixteenths`,
`MPSTensor.IsPrimitiveMPS.exists_openChain_groundProjection_defect_lt_c3_threshold`,
and
`MPSTensor.IsPrimitiveMPS.exists_re_inner_openChain_anticommutator_ge_c3_threshold`.

The spectator positivity `0 < ℓ` is kept: it is the source's, and the open-chain
wrapper discharges it at `ℓ = 1`. The one statement still carrying a positive
prefix is
`MPSTensor.IsPrimitiveMPS.exists_openChain_martingaleDifference_norm_lt_c3_threshold`,
which carried it before this work too, because the martingale difference is only
defined for a positive prefix.

## Remaining residue

Two features of the source's display are not reproduced.

The rate condition proved here is that the rate lie strictly between the
weighted spectral radius of the transfer remainder and one. Nachtergaele
prescribes instead that it exceed the moduli of the nonunit transfer
eigenvalues. The remainder has exactly those eigenvalues together with zero, so
the two conditions describe the same rates once the spectral radius is known to
equal the largest such modulus; that equality is not formalized, and only the
spectral-radius form is used. The blueprint section head states the proved
condition and cites the paper-gap note, so the source's phrasing is not
presented as what is proved.

The prefactor is the second. Nachtergaele states that it may be taken equal to `k²`,
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
