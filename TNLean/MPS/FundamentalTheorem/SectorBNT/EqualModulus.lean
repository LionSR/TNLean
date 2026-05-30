/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic

/-!
# Optional equal-modulus weight layer for BNT canonical forms

This module introduces the **optional** structure
`HasEqualModulusWeightLayer P`, which layers a spectral level
`λ_j = spectral_level j` together with within-sector unit-modulus phase
weights `ν_{j,q} = phase_weight j q` on top of a `SectorDecomposition P`,
factoring the raw sector weights as `P.weight j q = λ_j · ν_{j,q}`.

This layer captures the **sub-class** of BNT canonical forms in which every
sector's copies share a common modulus.  It is NOT part of the
core BNT predicate `IsBNTCanonicalForm` in
`SectorBNT/Basic.lean`.  The counter-example `C ⊕ (1/2)C` is a single
BNT basis element with coefficient
`1 + (1/2)^N` whose copies have unequal moduli, so no `λ_j` factorization
with unit `ν_{j,q}` is possible.

The spectral level is required to be `Antitone` (≥) in `‖·‖`, not
`StrictAnti`: `C ⊕ D` with distinct non-gauge-equivalent normal basis tensors
and weights `(1,1)` has two BNT basis elements of equal modulus.

This layer is provided for downstream estimates that genuinely need an
equal-modulus normalization; CPSV16 §II Step 1 does not need it.

## References

* CPSV16: arXiv:1606.00608 §II.  Lines 217–246 (global `|μ_k| ≤ 1` with
  at least one of modulus 1).
* CPSV21: arXiv:2011.12127 §4.  Lines 1905–1908 (unital gauge optional).
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/--
**Optional equal-modulus weight layer.**

This optional structure layers a spectral level `λ_j` and within-sector
unit-modulus phase weights `ν_{j,q}` on top of a `SectorDecomposition`,
factoring `P.weight j q = spectral_level j · phase_weight j q`.

It captures the sub-class of BNT canonical forms in which every sector's
copies share a common modulus.  It is NOT required by, nor part of, the
core BNT predicate `IsBNTCanonicalForm` (see `SectorBNT/Basic.lean`).  The
valid CPSV BNT canonical form `C ⊕ (1/2)C` admits no such factorization.

Paper anchors:

* CPSV16 lines 217–246 — the optional global normalization
  `|μ_k| ≤ 1` with at least one of modulus 1.
* CPSV21 lines 1905–1908 — the unital gauge is optional.
-/
structure HasEqualModulusWeightLayer (P : SectorDecomposition d) where
  /-- The spectral level `λ_j`, one complex scalar per basis block. -/
  spectral_level : Fin P.basisCount → ℂ
  /-- The spectral level is everywhere nonzero. -/
  spectral_level_ne_zero : ∀ j : Fin P.basisCount, spectral_level j ≠ 0
  /-- The spectral-level moduli are antitone in `j` (≥, not strict).  The
  non-strict form admits equal-modulus distinct basis blocks. -/
  spectral_level_antitone :
    Antitone (fun j : Fin P.basisCount => ‖spectral_level j‖)
  /-- **Dominant normalization**: the leading basis block has spectral
  norm 1 (CPSV16 lines 217–246, optional convention). -/
  spectral_level_dom_norm_one :
    ∀ h : 0 < P.basisCount, ‖spectral_level ⟨0, h⟩‖ = 1
  /-- Within-sector unit-modulus phase weights `ν_{j,q}`. -/
  phase_weight : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ
  /-- Every phase weight has unit modulus. -/
  phase_weight_norm_one : ∀ (j : Fin P.basisCount) (q : Fin (P.copies j)),
    ‖phase_weight j q‖ = 1
  /-- Factorization of raw sector weights as `μ_{j,q} = λ_j · ν_{j,q}`. -/
  weight_factor : ∀ (j : Fin P.basisCount) (q : Fin (P.copies j)),
    P.weight j q = spectral_level j * phase_weight j q

namespace HasEqualModulusWeightLayer

end HasEqualModulusWeightLayer

end MPSTensor
