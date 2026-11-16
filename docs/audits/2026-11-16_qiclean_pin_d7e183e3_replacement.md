# QICLean pin d7e183e3: gate modules and supported-operator lemmas

Date: 2026-11-16.

This audit records the declarations deleted from TNLean when its QICLean pin
moved from `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac` to
`d7e183e3aef2954ae9659381dfa264477ad7d057`. The range holds LionSR/QICLean#1055,
which ported the index-generic gate modules to `QICLean/Circuit/Gate`, and
LionSR/QICLean#1054, which added the closure lemmas of `Entropy.IsSupportedOn`.
Both ports keep the declaration names and statements, so between the two
merges and this pin move the declarations existed in both repositories. The
pin move and the deletions are one pull request: no commit of `main` has a
declaration twice or not at all. Tracker: #10718; the rule is the section
"No dual systems" of `docs/many_body_circuit_architecture.md`.

Mathlib and the Lean toolchain do not move (both repositories are on
v4.36.0-rc1). No deprecated alias and no module that only imports its
replacement is kept; every importer names the QICLean module.

## Deleted modules

Every declaration of these eight modules is in the QICLean module of the same
row, under the same fully qualified name.

| Deleted TNLean module | Declarations | QICLean module |
|---|---|---|
| `TNLean/Algebra/ComplexSqrt.lean` | 11 | `QICLean/Algebra/ComplexSqrt.lean` |
| `TNLean/Circuit/Gates/TwoLevel.lean` | 24 | `QICLean/Circuit/Gate/TwoLevel.lean` |
| `TNLean/Circuit/Gates/Givens.lean` | 23 | `QICLean/Circuit/Gate/Givens.lean` |
| `TNLean/Circuit/PartialIsometryDilation.lean` | 5 | `QICLean/Circuit/Gate/PartialIsometryDilation.lean` |
| `TNLean/Circuit/ExactSubspaceAmplification.lean` | 11 | `QICLean/Circuit/Gate/ExactSubspaceAmplification.lean` |
| `TNLean/Circuit/ExactAmplificationBudget.lean` | 8 | `QICLean/Circuit/Gate/ExactAmplificationBudget.lean` |
| `TNLean/Circuit/UniformPostselection.lean` | 15 | `QICLean/Circuit/Gate/UniformPostselection.lean` |
| `TNLean/Circuit/UniformSuccessAttenuation.lean` | 7 | `QICLean/Circuit/Gate/UniformSuccessAttenuation.lean` |

The declarations, by module:

- `Algebra/ComplexSqrt`: `Complex.ofReal_sqrt_sq`,
  `Complex.ofReal_sqrt_inv_mul_self`, `Complex.invSqrtTwo`,
  `Complex.invSqrtTwo_ne_zero`, `Complex.invSqrtTwo_mul_self`,
  `Complex.invSqrtTwo_sq`, `Complex.invSqrtTwo_pow_mul_self`,
  `Complex.invSqrtTwo_mul_sqrtTwo`, `Complex.sqrtTwo_mul_invSqrtTwo`,
  `Complex.conj_invSqrtTwo`, `Complex.star_invSqrtTwo`.
- `Circuit/Gates/TwoLevel`, all in the namespace `QuantumCircuit`:
  `twoLevelIdx`, `twoLevel`, `twoLevel_apply_of_not_mem_left`,
  `twoLevel_apply_of_not_mem_right`, `twoLevelIdx_self`, `twoLevelIdx_of_ne`,
  `twoLevel_mul`, `twoLevel_one`, `twoLevel_conjTranspose`,
  `twoLevel_mem_unitary`, `twoLevel_mulVec_apply`, `rotTwo`, `diagTwo`,
  `phaseTwo`, `quarterTwo`, `rotTwo_mul`, `rotTwo_one`, `rotTwo_conjTranspose`,
  `rotTwo_mem_unitary`, `phaseTwo_mem_unitary`, `quarterTwo_mem_unitary`,
  `diagTwo_mem_unitary`, `rotTwo_sq_eq_commutator`, `diagTwo_sq_eq_commutator`.
- `Circuit/Gates/Givens`, all in the namespace `QuantumCircuit`:
  `IsTwoLevelWord`, `IsTwoLevelWord.one`, `IsTwoLevelWord.mono`,
  `IsTwoLevelWord.mul`, `IsTwoLevelWord.single`, `IsTwoLevelWord.conjTranspose`,
  `IsTwoLevelWord.mem_unitary`, `FixesOutside`, `FixesOutside.mono`,
  `FixesOutside.mul`, `fixesOutside_twoLevel`, `fixesOutside_empty`,
  `det_twoLevel`, `IsSpecialTwo.det_eq_one`, `IsTwoLevelWord.det_eq_one`,
  `quarterTwo_eq_rotTwo`, `exists_twoLevel_elim`, `twoLevel_mul_apply`,
  `twoLevel_list_prod`, `isTwoLevelWord_twoLevel_list_prod`,
  `exists_isTwoLevelWord_elim`, `isTwoLevelWord_of_fixesOutside`,
  `isTwoLevelWord_of_det_eq_one`.
- `Circuit/PartialIsometryDilation`, all in the namespace `Matrix`:
  `partialIsometryDilation`, `partialIsometryDilation_mem_unitaryGroup`,
  `partialIsometryDilation_mul_fromRows`, `partialIsometryDilation_initial_gram`,
  `partialIsometryDilation_success_gram`.
- `Circuit/ExactSubspaceAmplification`, all in the namespace `Matrix`:
  `subspaceReflection`, `amplificationPlane`,
  `subspaceReflection_mem_unitaryGroup`, `orthogonality_symmetric`,
  `subspaceAmplificationStep`, `subspaceAmplificationStep_mul_plane`,
  `amplificationPlane_conjTranspose_mul_self`,
  `isStarProjection_mul_conjTranspose_of_isometry`,
  `subspaceAmplificationStep_mem_unitaryGroup`,
  `subspaceAmplificationStep_pow_mul_plane`,
  `subspaceAmplificationStep_pow_eq_good`.
- `Circuit/ExactAmplificationBudget`, all in the namespace `QuantumCircuit`:
  `amplificationRounds`, `amplificationAngle`, `amplificationRounds_pos`,
  `amplificationRounds_le`, `amplificationAngle_pos`,
  `amplificationAngle_lt_pi_div_two`, `amplificationAngle_le_inv`,
  `amplificationAngle_sin_pos_le_inv`.
- `Circuit/UniformPostselection`, all in the namespace `Matrix`:
  `postselectionSuccess`, `postselectionFailure`, `projection_gram`,
  `normalized_projection_gram`, `complement_probability`,
  `projected_parts_orthogonal`, `uniformPostselection_decomposition`,
  `postselectionAmplificationStep`,
  `postselectionAmplificationStep_mem_unitaryGroup`,
  `sin_bounds_of_first_quadrant`, `amplificationPlane_postselection_eq_self`,
  `postselectionAmplificationStep_pow_mul`, `exact_amplification_angle_bounds`,
  `postselectionAmplificationStep_pow_eq_success`,
  `projection_mul_eq_self_of_uniform_probability_one`.
- `Circuit/UniformSuccessAttenuation`, all in the namespace `Matrix`:
  `attenuationRotation`, `attenuationRotation_mem_unitaryGroup`,
  `attenuatedIsometry`, `attenuatedSuccessProjection`,
  `attenuatedIsometry_conjTranspose_mul_self`,
  `attenuatedSuccessProjection_isStarProjection`,
  `attenuatedIsometry_success_gram`.

## Deleted sections of modules that remain

| TNLean module | Deleted declarations | QICLean module |
|---|---|---|
| `TNLean/Circuit/Gates/Controlled.lean`, section on controlled elements of a ring | `QuantumCircuit.ctrlElem`, `ctrlElem_one`, `ctrlElem_ctrlElem`, `ctrlElem_mul`, `conj_ctrlElem`, `commute_ctrlElem`, `ctrlElem_commutator` | `QICLean/Circuit/Gate/Controlled.lean` |
| `TNLean/Circuit/Gates/ControlledProducts.lean`, section on the two-level targets | `QuantumCircuit.IsSpecialTwo`, `IsSpecialTwo.mem_unitary`, `diagTwo_conjTranspose`, `IsSpecialTwo.conjTranspose`, `exists_sq_eq_of_norm_eq_one`, `IsSpecialTwo.exists_commutator` | `QICLean/Circuit/Gate/TwoLevel.lean` |

`Circuit/Gates/Controlled` keeps the controlled operators on sites (`ctrlOp`
and its seven lemmas), and `Circuit/Gates/ControlledProducts` keeps the six
statements about products of two-site gates on a chain. Both use the site
operators and supported operators of `TNLean/Circuit`, which QICLean does not
have yet.

## Deleted supported-operator lemmas

| Deleted TNLean declaration | TNLean module | QICLean declaration |
|---|---|---|
| `Entropy.IsSupportedOn.add`, `Entropy.IsSupportedOn.neg`, `Entropy.IsSupportedOn.sub` | `MPS/AreaLaw/Hastings/PartCommutators.lean` | same names, `QICLean/Entropy/SupportedOperatorAlgebra.lean` |
| `Entropy.IsSupportedOn.smul` | `MPS/AreaLaw/Hastings/ProjectorFactorizationScaling.lean` | same name, same module |
| `Entropy.IsSupportedOn.conjTranspose` | `MPS/AreaLaw/Hastings/PositiveFactorization.lean` | same name, same module |
| `TNLean.Lattice.isSupportedOn_sum` | `Lattice/ZeroEntropy.lean` | `Entropy.isSupportedOn_sum`, same module |

The first five have the names of the QICLean declarations, so the old copies
would fail as redeclarations under the new pin. The last has the statement of
the QICLean declaration under another namespace; its seventeen uses in
`Lattice/ZeroEntropy` and `MPS/AreaLaw` now name `Entropy.isSupportedOn_sum`,
and the blueprint entry `lem:zero_entropy_cut` cites that name.

## Importers

Importers of a deleted module import the QICLean module of the same row.
`Circuit/Gates/TwoSiteUniversality` imported `Circuit/Gates/Givens`, which
imported `Circuit/Gates/ControlledProducts`; since the QICLean module has no
such import, `TwoSiteUniversality` now imports both. The four modules that lost
a supported-operator lemma import `QICLean.Entropy.SupportedOperatorAlgebra`.
The import aggregators `TNLean/Algebra.lean`, `TNLean/Circuit.lean` and
`TNLean/Circuit/Gates.lean` are regenerated.

## Other changes of the QICLean range

The range has 44 commits. Besides the two ports above, they add about 200
declarations to QICLean and remove two private ones
(`Matrix.rpow_mul_one_sub`, `QICLean.ComplexGaussian.sqrt_two_complex_sq`),
neither used in TNLean. Three declarations moved from
`QICLean/Entropy/FilterStationarity.lean` to
`QICLean/Entropy/SupportedOperatorAlgebra.lean`, which the former imports. The
statements of `Real.exists_softTruncation_order_of_residual_budget` and
`Real.exists_softTruncation_scaled_order_of_residual_budget` are unchanged.
No TNLean proof needed a change for these commits.

A comparison of fully qualified names found no other TNLean declaration
duplicated by a declaration added in the range. The following are left as
they are:

- `Entropy.IsSupportedOn.commutator` (`Hastings/PartCommutators`) and the
  other statements that take a reference configuration `σ₀` in order to use
  `Entropy.IsSupportedOn.mul`. The new `Entropy.IsSupportedOn.mul_mem` needs
  no reference configuration; removing these arguments changes statements
  and call sites and is left to the Sites steps of the plan.
- `QuantumCircuit.supportedOperators` and its lemmas
  (`TNLean/Circuit/SupportedOperators.lean`) beside the new
  `Entropy.supportedOperators`. These are two definitions of one notion, on
  `Set` and `Finset` regions; their unification is the Sites layer of the
  plan.
- `MPSTensor.conj_invSqrtTwo` (`MPS/Examples/AKLTReview.lean`), which has the
  statement of `Complex.conj_invSqrtTwo`. The pair existed inside TNLean before
  this range.
