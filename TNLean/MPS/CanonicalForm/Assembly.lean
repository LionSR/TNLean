/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Assembly.StructuralTheorem

/-!
# Canonical-form reduction after blocking

This module is the public entry point for the end-to-end canonical-form
reduction after blocking. It keeps the historical import path
`TNLean.MPS.CanonicalForm.Assembly` available while the underlying development is
split across five focused supporting modules.

The supporting modules are:

* `TNLean.MPS.CanonicalForm.Assembly.TPPrimitiveReduction` — blocked
  TP-primitive decomposition from arbitrary input.
* `TNLean.MPS.CanonicalForm.Assembly.NormalityChain` — the normality chain for
  TP-primitive irreducible blocks and preservation of normality under blocking.
* `TNLean.MPS.CanonicalForm.Assembly.PrimitiveBlocks` — blocked irreducibility
  and the conditional weak block-matching theorem.
* `TNLean.MPS.CanonicalForm.Assembly.CyclicSectorDecomposition` — cyclic sector
  decomposition after blocking.
* `TNLean.MPS.CanonicalForm.Assembly.StructuralTheorem` — common-period blocking
  and the structural after-blocking theorem.

## Main statements

The imported modules provide the canonical-form reduction theorems at the
original names, including
`exists_tp_primitive_blockDecomp_after_blocking`,
`isNormal_of_tp_primitive_irreducible`,
`isIrreducibleTensor_blockTensor_of_tp_primitive_irr`,
`exists_cyclic_sector_decomp_of_TP_of_isIrreducibleTensor`,
`primitive_and_irreducible_sectorBlocks_of_cyclic_decomp_after_blocking_of_projStep`,
`bilateral_commonPeriod_blocking_tp_primitive_normal`, and
`fundamentalTheorem_after_blocking_1606_structural`.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, §2.3 + Appendix A]
* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:2011.12127, §IV]

## Tags

matrix product states, canonical form, blocking, primitive transfer maps
-/
