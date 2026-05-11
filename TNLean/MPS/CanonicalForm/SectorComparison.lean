/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.SectorComparison.ProportionalComparison
import TNLean.MPS.CanonicalForm.SectorComparison.CommonPrimitiveProportionalData
import TNLean.MPS.CanonicalForm.SectorComparison.CommonPrimitiveReindexTransport
import TNLean.MPS.CanonicalForm.SectorComparison.BasicSectorComparison
import TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorData

/-!
# Canonical-form reduction after blocking

This module is the public entry point for the complete canonical-form
reduction after blocking. It keeps the historical import path
`TNLean.MPS.CanonicalForm.Assembly` available while the underlying development is
split across focused supporting modules.

The supporting modules are:

* `TNLean.MPS.CanonicalForm.SectorComparison.TPPrimitiveReduction` — blocked
  TP-primitive decomposition from arbitrary input.
* `TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain` — the normality chain for
  TP-primitive irreducible blocks and preservation of normality under blocking.
* `TNLean.MPS.CanonicalForm.SectorComparison.PrimitiveBlocks` — blocked irreducibility
  and the conditional weak block-matching theorem.
* `TNLean.MPS.CanonicalForm.SectorComparison.CommonBlockedCyclicSectorFamily` —
  definitions and lemmas for common-period cyclic-sector families.
* `TNLean.MPS.CanonicalForm.SectorComparison.CommonBlockedCyclicSectorRepresentatives` —
  definitions and lemmas for representative common-sector families.
* `TNLean.MPS.CanonicalForm.SectorComparison.CyclicSectorDecomposition` — cyclic sector
  decomposition after blocking.
* `TNLean.MPS.CanonicalForm.SectorComparison.CommonBlockedCyclicSectorConstruction` —
  construction of common-period cyclic-sector families.
* `TNLean.MPS.CanonicalForm.SectorComparison.ZeroTailTransport` — generic zero-tail
  MPV transport lemmas.
* `TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorData` — common-sector data
  after the zero-tail and TP-gauge structural reduction.
* `TNLean.MPS.CanonicalForm.SectorComparison.StructuralData` — common-period blocking
  and structural after-blocking data.
* `TNLean.MPS.CanonicalForm.SectorComparison.StructuralTheorem` — historical re-export
  path for structural data and common-sector transport.
* `TNLean.MPS.CanonicalForm.SectorComparison.CommonSectorTransport` — zero-tail and
  common-sector transport after the structural theorem.
* `TNLean.MPS.CanonicalForm.SectorComparison.CommonPrimitiveProportionalData` —
  common primitive span, phase-cover, proportional, and BNT comparison hypotheses.
* `TNLean.MPS.CanonicalForm.SectorComparison.CommonPrimitiveReindexTransport` —
  physical-reindex transport for primitive BNT-cover hypotheses.
* `TNLean.MPS.CanonicalForm.SectorComparison.BasicSectorComparison` — basic sector
  comparisons from block-span, phase-cover, and proportional data.
* `TNLean.MPS.CanonicalForm.SectorComparison.ProportionalComparison` — sector comparison
  from BNT block-permutation gauge-phase data.

## Main statements

The imported modules provide the canonical-form reduction theorems, including
`exists_tp_primitive_blockDecomp_after_blocking`,
`isNormal_of_tp_primitive_irreducible`,
`isIrreducibleTensor_blockTensor_of_tp_primitive_irr`,
`exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`,
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_projStep`,
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_fixedAlgebraRigidity`,
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking`,
`bilateral_commonPeriod_blocking_tp_primitive_normal`, and
`afterBlocking_structuralData_of_sameMPV₂`.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Section 2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, Section IV]

## Tags

matrix product states, canonical form, blocking, primitive transfer maps
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
