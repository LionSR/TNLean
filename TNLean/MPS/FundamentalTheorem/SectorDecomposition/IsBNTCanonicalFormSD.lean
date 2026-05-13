/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorDecomposition

/-!
# Paper-faithful BNT canonical form on the `SectorDecomposition` surface

The `Prop`-level predicate `IsBNTCanonicalFormSD` over a
`SectorDecomposition P` records the two paper-faithful hypotheses of
arXiv:1606.00608 Definition 4.2 / arXiv:2011.12127 Definition 4.2:

* every within-sector weight has unit modulus
  (`P.sectors.weight j q` with `‖P.sectors.weight j q‖ = 1`);
* the basis of normal tensors is eventually linearly independent
  (the `HasBNTSectorData` field from
  `TNLean.MPS.FundamentalTheorem.SectorDecomposition`).

The structure is the target signature for the
`IsCanonicalFormBNT`→`SectorDecomposition` reorganization described in
`audits/2026-05-13_cpsv16_ft_bridge_gap.md` §Resolution.

The `SD` suffix abbreviates "Sector Decomposition" — the predicate lives on
the `SectorDecomposition` surface, in contrast with the existing
`IsCanonicalFormBNT` predicate which lives on the assembled
`toTensorFromBlocks` surface and conflates the spectral level with the
within-sector multiplicities under `mu_strict_anti`.

## References

* CPSV16: Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.  Definition of the BNT
  canonical form, §II.
* CPSV21: Cirac--Pérez-García--Schuch--Verstraete, *Matrix product states
  and projected entangled pair states: Concepts, symmetries, theorems*,
  Rev. Mod. Phys. **93**, 045003 (2021); arXiv:2011.12127.
  Definition 4.2 (two-layer BNT canonical form).
* `audits/2026-05-13_cpsv16_ft_definition_audit.md` §10.
* `audits/2026-05-13_cpsv16_ft_bridge_gap.md`.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Paper-faithful BNT canonical form on the `SectorDecomposition` surface
(`SD = Sector Decomposition`).**

A `SectorDecomposition` `P` carries the BNT canonical form of CPSV16 §II
(arXiv:1606.00608; equivalently CPSV21 Definition 4.2, arXiv:2011.12127)
when its sector weights have unit modulus and its basis of normal tensors is
eventually linearly independent.

The unit-modulus field is the load-bearing hypothesis of the per-block
projection lemmas in
`TNLean.MPS.FundamentalTheorem.SectorDecomposition.PerBlockProjection`. -/
structure IsBNTCanonicalFormSD (P : SectorDecomposition d) : Prop where
  /-- Every within-sector weight has unit modulus. -/
  unit_modulus : ∀ j q, ‖P.sectors.weight j q‖ = 1
  /-- The basis of normal tensors is eventually linearly independent. -/
  bnt_data : HasBNTSectorData P

end MPSTensor
