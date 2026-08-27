# MPDO shared sign calculus and generic private helpers (2026-08-27)

Three cleanups in `TNLean/MPS/MPDO`. The private helper removals use the
repository-local pass-through exception of `docs/project_conventions.md`
§Style. Every non-`Archive` use is migrated, and the two blueprint `\lean{}`
tags affected are redirected in the same change. The four public sign-definition
names retain deprecated aliases to the shared owners; no private removed name
needs an alias, and no removed name encoded misleading terminology.

## 1. Generic helpers replaced by their owned equivalents

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.KatoDeformedRFPObstruction.sqrt2_sq_complex` (`TNLean/MPS/MPDO/KatoDeformedRFPObstruction.lean`) | `Complex.ofReal_sqrt_sq` (`TNLean/Algebra/ComplexSqrt.lean`), at three call sites |
| `MPOTensor.submatrix_equiv_injective` (private, `TNLean/MPS/MPDO/LocalPurificationRFP.lean`) | `(Matrix.reindex e.symm e.symm).injective`, the `Equiv` bundling the same submatrix map |
| `MPOTensor.cast_via_common_dimension` (private, `TNLean/MPS/MPDO/GroupedReferenceCorner.lean`) | `cast_cast` (Lean core, `Init/PropLemmas.lean`), whose single call site collapses to `exact cast_cast _ _ _` |

`sqrt2_sq_complex` was the last hand-rolled occurrence of the
"Complex squares of real square roots" pattern promoted in
`docs/tactic_patterns.md`; the three `rw [sqrt2_sq_complex]` steps become
`norm_num [Complex.ofReal_sqrt_sq 2 _]`, the form already used at
`TNLean/MPS/MPDO/CPSVExample410Operator.lean`.

`MPOTensor.reindex_kronecker_assoc`
(`TNLean/MPS/MPDO/IsometricAdjacentBondTransport.lean`) was examined in the same
pass and **retained**: Mathlib's `Matrix.kronecker_assoc` and `kronecker_assoc'`
prove only the forward reindex direction, while the local lemma is the inverse
and is consumed as a rewrite rule in that direction.

## 2. One owner for two duplicated model helpers

`TNLean/MPS/MPDO/BondTwoSingletonPhysicalGauge.lean` re-declared two helpers of
the base model it imports.

| Removed declaration | Replacement |
|---|---|
| `MPOTensor.BondTwoSingletonBaseModel.singletonScale_pos_physicalGauge` (private, `BondTwoSingletonPhysicalGauge.lean`) | `MPOTensor.BondTwoSingletonBaseModel.singletonScale_pos` (`BondTwoSingletonBaseModel.lean`), the identical statement, now public |
| the second `private abbrev I := Fin 2` (`BondTwoSingletonPhysicalGauge.lean`) | `MPOTensor.BondTwoSingletonBaseModel.I` (`BondTwoSingletonBaseModel.lean`), now public |

Both files open the same namespace and the gauge file imports the base model, so
the four uses of the removed lemma resolve to the survivor by name alone. The
other `private` helpers of the base model (`singletonScale_sq`,
`singletonScale_star_mul`, `singletonScale_mul`) have no second copy and stay
private.

The related overlapping-lift duplication surveyed alongside this
(`Matrix.leftOverlappingLift_mul`, `Matrix.rightOverlappingLift_mul`,
`Matrix.rightOverlappingLift_kronecker_one` in
`GSNNCHFourCycleMarkov/OverlappingLiftAlgebra.lean`) was already resolved
upstream and needed no change here.

## 3. One owner for the binary $Z$-string sign calculus

`KatoDeformedRFPObstruction.lean` and `CPSVExample412Literal.lean` each carried
a full copy of the same eight-declaration sign calculus. Both copies are
replaced by the new module `TNLean/MPS/MPDO/BinaryConfigurationSign.lean`, whose
site weight is the Pauli diagonal entry `SpinCover.pauli 2 i i` — the common
specialisation of the two local spellings (`pauliZ` and `sigmaZ`).

| Removed declarations (both namespaces) | Replacement in `MPOTensor` |
|---|---|
| `MPOTensor.KatoDeformedRFPObstruction.siteSign`, `MPOTensor.CPSVExample412Literal.siteSign` | `MPOTensor.siteSign` |
| `…KatoDeformedRFPObstruction.configurationSign`, `…CPSVExample412Literal.configurationSign` | `MPOTensor.configurationSign` |
| `…siteSign_eq_one_or_neg_one` (both) | `MPOTensor.siteSign_eq_one_or_neg_one` |
| `…configurationSign_eq_one_or_neg_one` (both) | `MPOTensor.configurationSign_eq_one_or_neg_one` |
| `…sum_siteSign_eq_zero` (both) | `MPOTensor.sum_siteSign_eq_zero` |
| `…sum_configurationSign_eq_zero` (both) | `MPOTensor.sum_configurationSign_eq_zero` |
| `…configurationSign_append` (both) | `MPOTensor.configurationSign_append` |
| `…configurationSign_append_cast` (both) | `MPOTensor.configurationSign_append_cast` |

Both consuming files sit in namespaces under `MPOTensor`, so no unqualified
internal reference needed requalifying. Because `siteSign` and
`configurationSign` were public in both old namespaces, those four qualified
names remain as deprecated aliases to the shared definitions.

Retained on purpose: `MPOTensor.KatoDeformedRFPObstruction.pauliZ` (blueprint
tagged, and used by the closure identities) and
`MPOTensor.CPSVExample412Literal.sigmaZ` with `sigmaZ_apply_ne` (used by the
tensor definition and the Kronecker factorisation). Retiring `pauliZ` as a
`SpinCover.pauli 2` shadow is a separate question, not settled here.

Blueprint labels redirected in the same change:

| Label | Old payload entry | New payload entry |
|---|---|---|
| `thm:kato_deformed_mpdo_fixed_tensor_obstruction` (`ch21_mpdo_rfp_foundations.tex`) | `MPOTensor.KatoDeformedRFPObstruction.siteSign`, `….configurationSign` | `MPOTensor.siteSign`, `MPOTensor.configurationSign` |
| `def:cpsv_example412_site_sign` (`ch21_mpdo_rfp_simple_local_structure_capstone.tex`) | `MPOTensor.CPSVExample412Literal.siteSign` | `MPOTensor.siteSign` |
| `def:cpsv_example412_configuration_sign` (same chapter) | `MPOTensor.CPSVExample412Literal.configurationSign` | `MPOTensor.configurationSign` |

The prose of `def:cpsv_example412_site_sign` ($z_a=(\sigma_z)_{aa}$) stays
correct under the Pauli-based body, and the other payload entries of the Kato
theorem tag are unaffected. `lake exe checkdecls blueprint/lean_decls` passes
after `python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls`.
