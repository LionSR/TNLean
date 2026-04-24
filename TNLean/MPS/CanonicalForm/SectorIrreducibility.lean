/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorIrreducibility.ProjectionOrtho
import TNLean.MPS.CanonicalForm.SectorIrreducibility.OrbitSum
import TNLean.MPS.CanonicalForm.SectorIrreducibility.HLift

/-!
# Sector irreducibility helpers

This module keeps the historical import path
`TNLean.MPS.CanonicalForm.SectorIrreducibility` available while the underlying
material is organized across three focused modules.

The supporting modules are:

* `TNLean.MPS.CanonicalForm.SectorIrreducibility.ProjectionOrtho` — pairwise
  orthogonality of orthogonal projections and corner preservation from adjoint
  fixed projections.
* `TNLean.MPS.CanonicalForm.SectorIrreducibility.OrbitSum` — orbit-sum
  fixed-point and sector-support lemmas.
* `TNLean.MPS.CanonicalForm.SectorIrreducibility.HLift` — the
  `hFixUpgrade`/`hProjStep`/`hLift` cluster and the resulting irreducibility
  theorems on cyclic sectors.

## Main statements

The imported modules provide the original declarations at their existing names,
including `pairwise_mul_zero_of_orthogonalProjection_sum_one`,
`preservesCorner_of_adjoint_fixed_projection`,
`orbitSumProjection_fixed_of_pow_fix`,
`orbit_iterate_supported_on_shifted_sector`,
`orbit_iterate_isOrthogonalProjection`,
`orbitSumProjection_eq_one_of_full_sector`,
`hFixUpgrade_of_peripheral`,
`SectorFixedPointAlgebraRigidity`,
`hProjStep_of_sectorFixedPointAlgebraRigidity`,
`sectorFixedPointAlgebraRigidity_of_irreducible_cyclicDecomp`,
`hLift_cyclicDecomp_mps_of_fixUpgrade`,
`hLift_cyclicDecomp_mps_of_projStep`,
`hLift_cyclicDecomp_mps_of_sectorFixedPointAlgebraRigidity`,
`hLift_cyclicDecomp_mps`,
`isIrreducibleOnCorner_of_cyclic_decomp_mps_of_hLift`,
`isIrreducibleOnCorner_of_cyclic_decomp_mps_of_projStep`,
`isIrreducibleOnCorner_of_cyclic_decomp_mps_of_fixUpgrade`,
`isIrreducibleOnCorner_of_cyclic_decomp_mps_of_sectorFixedPointAlgebraRigidity`, and
`isIrreducibleOnCorner_of_cyclic_decomp_mps`.

## Tags

matrix product states, cyclic sectors, irreducibility
-/
