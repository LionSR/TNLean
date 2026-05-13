/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.FundamentalTheorem.SectorDecomposition

/-!
# Two-layer BNT canonical form on the `SectorDecomposition` surface

The `Prop`-level predicate `IsBNTCanonicalFormSD` over a
`SectorDecomposition P` records the two-layer BNT canonical form of
arXiv:1606.00608 §II / arXiv:2011.12127 Definition 4.2:

* a **spectral level** `λ : Fin P.basisCount → ℂ` with `λ_j ≠ 0` and
  strictly-decreasing modulus;
* **within-sector weights** factor as `P.sectors.weight j q = λ_j · ν_{j,q}`
  with `‖ν_{j,q}‖ = 1`, expressed as `‖P.sectors.weight j q / λ_j‖ = 1`;
* eventual linear independence of the basis blocks
  (`HasBNTSectorData`).

The spectral level is packaged inside an existential so the whole
predicate stays `Prop`-valued; the layer data is exposed via
`spectralLevel`, `spectralLevel_ne_zero`, `spectralLevel_strict_anti`,
and `weight_factor`.

This file also exposes the adapter `IsCanonicalFormBNT.toIsBNTCanonicalFormSD`
from the existing one-copy-per-sector `IsCanonicalFormBNT` data: the
spectral level is `μ`, the within-sector phase is `μ_j / ‖μ_j‖`, and
the assembled tensor `P.toTensor` is MPV-equal to
`toTensorFromBlocks μ A` via `sameMPV₂_trivialSectorDecomp`.

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
* `audits/2026-05-13_cpsv16_ft_path_beta_scout.md`.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Two-layer BNT canonical form on the `SectorDecomposition` surface
(`SD = Sector Decomposition`).**

A `SectorDecomposition` `P` carries the two-layer BNT canonical form of
CPSV16 §II (arXiv:1606.00608; equivalently CPSV21 Definition 4.2,
arXiv:2011.12127) when:

* there is a spectral level `λ : Fin P.basisCount → ℂ` with `λ_j ≠ 0`
  and `StrictAnti (fun j => ‖λ_j‖)`;
* the within-sector weight `P.sectors.weight j q` factors as `λ_j · ν_{j,q}`
  with `‖ν_{j,q}‖ = 1`, recorded as `‖P.sectors.weight j q / λ_j‖ = 1`;
* the basis of normal tensors is eventually linearly independent
  (`HasBNTSectorData`).

The spectral level is packaged inside an existential to keep the
predicate `Prop`-valued; the four layer projections are exposed via the
`spectralLevel`, `spectralLevel_ne_zero`, `spectralLevel_strict_anti`,
and `weight_factor` accessors below. -/
structure IsBNTCanonicalFormSD (P : SectorDecomposition d) : Prop where
  /-- A spectral level `λ_j` exists with the three two-layer properties:
  nonvanishing, strictly-decreasing modulus, and unit-modulus quotient
  by every within-sector weight `P.sectors.weight j q`. -/
  exists_spectralLevel :
    ∃ lam : Fin P.basisCount → ℂ,
      (∀ j, lam j ≠ 0) ∧
      StrictAnti (fun j : Fin P.basisCount => ‖lam j‖) ∧
      (∀ j q, ‖P.sectors.weight j q / lam j‖ = 1)
  /-- The basis of normal tensors is eventually linearly independent. -/
  bnt_data : HasBNTSectorData P

namespace IsBNTCanonicalFormSD

variable {P : SectorDecomposition d}

/-- **Spectral level** of the two-layer BNT canonical form.

One complex number `λ_j` per basis block, with `‖λ_j‖` strictly decreasing
in `j` (cf. arXiv:2011.12127 Definition 4.2). -/
noncomputable def spectralLevel (h : IsBNTCanonicalFormSD P) :
    Fin P.basisCount → ℂ :=
  h.exists_spectralLevel.choose

/-- The spectral level is everywhere nonzero. -/
theorem spectralLevel_ne_zero (h : IsBNTCanonicalFormSD P) (j : Fin P.basisCount) :
    h.spectralLevel j ≠ 0 :=
  h.exists_spectralLevel.choose_spec.1 j

/-- The spectral level moduli are strictly decreasing in `j`. -/
theorem spectralLevel_strict_anti (h : IsBNTCanonicalFormSD P) :
    StrictAnti (fun j : Fin P.basisCount => ‖h.spectralLevel j‖) :=
  h.exists_spectralLevel.choose_spec.2.1

/-- Every within-sector weight factors as `λ_j · ν_{j,q}` with `‖ν_{j,q}‖ = 1`:
the quotient `P.sectors.weight j q / λ_j` has unit modulus. -/
theorem weight_factor (h : IsBNTCanonicalFormSD P)
    (j : Fin P.basisCount) (q : Fin (P.copies j)) :
    ‖P.sectors.weight j q / h.spectralLevel j‖ = 1 :=
  h.exists_spectralLevel.choose_spec.2.2 j q

end IsBNTCanonicalFormSD

/-- **Adapter: `IsCanonicalFormBNT` produces a two-layer `IsBNTCanonicalFormSD`.**

The one-copy-per-sector BNT canonical form `IsCanonicalFormBNT μ A`
yields the two-layer `IsBNTCanonicalFormSD` on the trivial sector
decomposition (`trivialSectorDecomp μ A`, `copies j = 1`):

* the spectral level is `λ_j = μ_j` (the original block weights),
* the within-sector phase is `ν_{j,0} = μ_j / ‖μ_j‖`, witnessed by
  `weight_factor` because `(trivialSectorDecomp μ A).sectors.weight j q = μ j`
  and `‖μ_j / μ_j‖ = ‖1‖ = 1`;
* `HasBNTSectorData` follows from `IsCanonicalFormBNT.isBNT`'s
  `eventually_li` field, since the trivial sector decomposition has
  `basis = A`.

The assembled tensor `P.toTensor` is MPV-equal to `toTensorFromBlocks μ A`
via `sameMPV₂_trivialSectorDecomp`, so proportionality hypotheses on the
`IsCanonicalFormBNT` surface transfer to the SD surface unchanged
(cf. arXiv:1606.00608 §II / arXiv:2011.12127 Definition 4.2). -/
theorem IsCanonicalFormBNT.toIsBNTCanonicalFormSD
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hCF : IsCanonicalFormBNT μ A) :
    ∃ P : SectorDecomposition d,
      IsBNTCanonicalFormSD P ∧
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) A) := by
  have hμne : ∀ j, μ j ≠ 0 := hCF.toIsCanonicalForm.mu_ne_zero
  refine ⟨trivialSectorDecomp μ A hμne, ?_, sameMPV₂_trivialSectorDecomp μ A hμne⟩
  refine
    { exists_spectralLevel := ?_
      bnt_data := ?_ }
  · refine ⟨μ, hμne, hCF.mu_strict_anti, ?_⟩
    intro j q
    have hdiv : μ j / μ j = 1 := div_self (hμne j)
    simp [trivialSectorDecomp, hdiv]
  · -- `HasBNTSectorData (trivialSectorDecomp μ A hμne)` unfolds to eventual
    -- linear independence of `mpvState (A j) N`, which is the `eventually_li`
    -- field of `IsCanonicalFormBNT.isBNT`.
    simpa [HasBNTSectorData, trivialSectorDecomp] using hCF.isBNT.eventually_li

end MPSTensor
