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
`SectorDecomposition P` is a **project-specific refinement** of the
BNT decomposition of CPSV16 §II (`eq:II_ABasicTensors`, arXiv:1606.00608)
in which equal-modulus blocks are grouped into sectors:

* a **spectral level** `λ : Fin P.basisCount → ℂ` with `λ_j ≠ 0`,
  strictly-decreasing modulus, and **dominant normalization**
  `‖λ_0‖ = 1`;
* **within-sector weights** factor as `P.sectors.weight j q = λ_j · ν_{j,q}`
  with `‖ν_{j,q}‖ = 1`, expressed as `‖P.sectors.weight j q / λ_j‖ = 1`;
* eventual linear independence of the basis blocks
  (`HasBNTSectorData`).

The `StrictAnti` and `weight_factor` conditions are **not** present in
CPSV16's general `eq:II_ABasicTensors` (which allows arbitrary complex
`μ_{j,q}`); they arise from grouping equal-modulus coefficients into
sectors and extracting a common spectral factor `λ_j`.  The unit-modulus
condition `‖ν_{j,q}‖ = 1` is conceptually related to the RFP
characterization in CPSV16 `thm:charact-MPS` (§III, lines 543–555), which
is a strict sub-class.  The dominant normalization `‖λ_0‖ = 1` mirrors
the `IsNormalCanonicalFormBNT.mu_dom_norm_one` convention used throughout
`TNLean/MPS/BNT/Construction.lean`.

The spectral level is packaged inside an existential so the whole
predicate stays `Prop`-valued; the layer data is exposed via
`spectralLevel`, `spectralLevel_ne_zero`, `spectralLevel_strict_anti`,
`weight_factor`, and `spectralLevel_dom_norm_one`.

This file also exposes the adapter `IsCanonicalFormBNT.toIsBNTCanonicalFormSD`
from the existing one-copy-per-sector `IsCanonicalFormBNT` data.  Because
`IsCanonicalFormBNT` does **not** require the dominant weight to have
unit modulus, the adapter rescales: it sets `λ_j = μ_j / ‖μ_0‖` (and
`ρ = 1` when there are no blocks).  The assembled tensor `P.toTensor`
then differs from `toTensorFromBlocks μ A` by a uniform per-length
scalar `ρ^{-N}`, which is exposed as a `NonzeroProportionalMPV₂`
relation (the scalar is nonzero because `‖μ_0‖ > 0`).  This rescaling
is the **Choice B** discharge described in the audit memo: it absorbs
the dominant-block normalization at the adapter level so callers on
the `IsCanonicalFormBNT` surface do not have to add an extra
`‖μ ⟨0, _⟩‖ = 1` hypothesis.

The `SD` suffix abbreviates "Sector Decomposition" — the predicate lives on
the `SectorDecomposition` surface, in contrast with the existing
`IsCanonicalFormBNT` predicate which lives on the assembled
`toTensorFromBlocks` surface and conflates the spectral level with the
within-sector multiplicities under `mu_strict_anti`.

## References

* CPSV16: Cirac--Pérez-García--Schuch--Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.
  - `eq:II_ABasicTensors` (§II, line 286): the BNT decomposition shape
    `A^i = ⊕_j ⊕_q μ_{j,q} X_{j,q} A^i_j X_{j,q}^{-1}` with **arbitrary**
    complex `μ_{j,q}` (no strictness or unit-modulus condition).
  - `thm:charact-MPS` (§III, lines 543–555): the RFP characterization in
    which `|μ_{j,q}| = 1`; this is the conceptual ancestor of `weight_factor`.
* CPSV21: Cirac--Pérez-García--Schuch--Verstraete, *Matrix product states
  and projected entangled pair states: Concepts, symmetries, theorems*,
  Rev. Mod. Phys. **93**, 045003 (2021); arXiv:2011.12127.
  - Definition 4.3 (`def:4:BNT`, lines 1846–1850): eventual linear
    independence of the BNT vectors; this is what `bnt_data` captures.
  - **Note:** Definition 4.2 (`def:4:normal-tensor-mps`) is the one-layer
    canonical form `A^i = ⊕_k μ_k A^i_k` — it does *not* define the
    two-layer BNT structure, spectral levels, or unit-modulus conditions.
* `IsNormalCanonicalFormBNT.mu_dom_norm_one` in
  `TNLean/MPS/BNT/Construction.lean` for the dominant normalization
  convention that `spectralLevel_dom_norm_one` mirrors.
* `audits/2026-05-13_cpsv16_ft_path_beta_scout.md`, §"PR 1.5 amendment".
* `docs/paper-gaps/cpsv16_two_layer_sector_refinement.tex` for the
  paper-gap note recording the extra hypotheses beyond CPSV16 §II.

## Rate-quantified strengthening (non-dominant projection branch)

The two-layer per-block-projection lemmas
`fixed_*_sectorDecomp_twoLayer` in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/PerBlockProjection.lean`
and `fixed_*_paperFaithful_twoLayer` in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/HNoCancelDischarge.lean`
carry an abstract `hNoCancel` hypothesis whose **non-dominant** branch
is not dischargeable on the present `IsBNTCanonicalFormSD` surface
alone.  The obstruction analysis recorded in
`audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md` shows that an
additional rate-quantified cross-overlap decay hypothesis is required,
comparing the BNT spectral gap to the weight ratios `‖λ_j / λ_k‖`.
The structural predicate
`HasRateQuantifiedCrossOverlapDecay P lam` in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/RateQuantifiedDecay.lean`
captures this strengthened input; it is meant to be combined with
`IsBNTCanonicalFormSD P` by instantiating `lam` with
`h.spectralLevel`.  The paper-gap note
`docs/paper-gaps/cpsv16_bnt_rate_quantification.tex` records the
mathematical content of the strengthening.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Two-layer BNT canonical form on the `SectorDecomposition` surface
(`SD = Sector Decomposition`).**

A `SectorDecomposition` `P` satisfies this predicate — a project-specific
refinement of CPSV16 `eq:II_ABasicTensors` (§II, arXiv:1606.00608) via
equal-modulus sector grouping — when:

* there is a spectral level `λ : Fin P.basisCount → ℂ` with `λ_j ≠ 0`,
  `StrictAnti (fun j => ‖λ_j‖)`, and **dominant normalization**
  `‖λ_0‖ = 1` whenever `P.basisCount > 0`;
* the within-sector weight `P.sectors.weight j q` factors as `λ_j · ν_{j,q}`
  with `‖ν_{j,q}‖ = 1`, recorded as `‖P.sectors.weight j q / λ_j‖ = 1`;
* the basis of normal tensors is eventually linearly independent
  (`HasBNTSectorData`).

The three extra conditions (`StrictAnti`, `weight_factor`, dominant
normalization) are **not** present in CPSV16 `eq:II_ABasicTensors`, which
allows arbitrary complex `μ_{j,q}` without any modulus ordering or
factorization.  They are introduced by the project's `SectorDecomposition`
grouping and the `IsNormalCanonicalFormBNT` convention for `‖λ_0‖ = 1`
(cf. `IsNormalCanonicalFormBNT.mu_dom_norm_one`).  The eventual linear
independence `bnt_data` corresponds to CPSV21 Definition 4.3 (not Def. 4.2).

Combined with `StrictAnti`, the dominant normalization forces `‖λ_j‖ ≤ 1`
for every `j`, so per-length coefficients `coeff N j` are uniformly
controlled by the within-sector multiplicities.  This uniform bound powers
the analytic discharge of `HNoCancelDischarge` on the non-dominant `k₀`
branch (see the PR 1.5 amendment to the audit memo).

For the non-dominant branch of the two-layer per-block-projection
discharge, this predicate must be combined with the rate-quantified
cross-overlap decay predicate
`HasRateQuantifiedCrossOverlapDecay P h.spectralLevel`
(see `RateQuantifiedDecay.lean` and
`docs/paper-gaps/cpsv16_bnt_rate_quantification.tex`).

The spectral level is packaged inside an existential to keep the
predicate `Prop`-valued; the five layer projections are exposed via
the `spectralLevel`, `spectralLevel_ne_zero`, `spectralLevel_strict_anti`,
`weight_factor`, and `spectralLevel_dom_norm_one` accessors below. -/
structure IsBNTCanonicalFormSD (P : SectorDecomposition d) : Prop where
  /-- A spectral level `λ_j` exists with the four two-layer properties:
  nonvanishing, strictly-decreasing modulus, unit-modulus quotient by
  every within-sector weight `P.sectors.weight j q`, and dominant
  normalization `‖λ_0‖ = 1`.  The dominant normalization is vacuous
  when `P.basisCount = 0`. -/
  exists_spectralLevel :
    ∃ lam : Fin P.basisCount → ℂ,
      (∀ j, lam j ≠ 0) ∧
      StrictAnti (fun j : Fin P.basisCount => ‖lam j‖) ∧
      (∀ j q, ‖P.sectors.weight j q / lam j‖ = 1) ∧
      (∀ h : 0 < P.basisCount, ‖lam ⟨0, h⟩‖ = 1)
  /-- The basis of normal tensors is eventually linearly independent. -/
  bnt_data : HasBNTSectorData P

namespace IsBNTCanonicalFormSD

variable {P : SectorDecomposition d}

/-- **Spectral level** of the two-layer BNT canonical form.

One complex number `λ_j` per basis block, with `‖λ_j‖` strictly decreasing
in `j` and `‖λ_0‖ = 1`.  This is the equal-modulus grouping factor
introduced by the project's `SectorDecomposition` surface; it is not a
direct field of CPSV16 `eq:II_ABasicTensors`, which uses bare `μ_{j,q}`.
The dominant normalization mirrors `IsNormalCanonicalFormBNT.mu_dom_norm_one`. -/
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
  h.exists_spectralLevel.choose_spec.2.2.1 j q

/-- **Dominant normalization of the spectral level.**

When `P` has at least one basis block, the dominant spectral level has
unit modulus, `‖λ_0‖ = 1`.  This mirrors the convention
`IsNormalCanonicalFormBNT.mu_dom_norm_one` in
`TNLean/MPS/BNT/Construction.lean`; it is not asserted by CPSV16
`eq:II_ABasicTensors` (which imposes no normalization on `μ_{j,q}`).
Combined with `spectralLevel_strict_anti` this gives `‖λ_j‖ < 1` for
`j ≥ 1` and `‖λ_j‖ ≤ 1` for every `j`. -/
theorem spectralLevel_dom_norm_one (h : IsBNTCanonicalFormSD P)
    (hpos : 0 < P.basisCount) :
    ‖h.spectralLevel ⟨0, hpos⟩‖ = 1 :=
  h.exists_spectralLevel.choose_spec.2.2.2 hpos

/-- All spectral-level moduli are bounded by `1`.

Combines `spectralLevel_dom_norm_one` with `spectralLevel_strict_anti`:
the dominant block has unit modulus and every other block has strictly
smaller modulus, so all moduli are at most `1`.  Both inputs are
project-specific conditions not present in CPSV16 `eq:II_ABasicTensors`. -/
theorem spectralLevel_norm_le_one (h : IsBNTCanonicalFormSD P)
    (j : Fin P.basisCount) : ‖h.spectralLevel j‖ ≤ 1 := by
  have hpos : 0 < P.basisCount := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hdom : ‖h.spectralLevel ⟨0, hpos⟩‖ = 1 :=
    h.spectralLevel_dom_norm_one hpos
  have hle : (⟨0, hpos⟩ : Fin P.basisCount) ≤ j :=
    Fin.mk_le_of_le_val (Nat.zero_le _)
  have hanti : ‖h.spectralLevel j‖ ≤ ‖h.spectralLevel ⟨0, hpos⟩‖ :=
    h.spectralLevel_strict_anti.antitone hle
  rw [hdom] at hanti
  exact hanti

end IsBNTCanonicalFormSD

/-- **Adapter: `IsCanonicalFormBNT` produces a two-layer `IsBNTCanonicalFormSD`.**

The one-copy-per-sector BNT canonical form `IsCanonicalFormBNT μ A`
yields the two-layer `IsBNTCanonicalFormSD` on the trivial sector
decomposition (`copies j = 1`) after rescaling by the dominant-block
modulus `ρ = ‖μ_0‖` (or `ρ = 1` when there are no blocks).  The
spectral level is `λ_j = μ_j / ρ`, which satisfies the project's
dominant normalization `‖λ_0‖ = 1` (cf. `IsNormalCanonicalFormBNT.mu_dom_norm_one`).
This is the **Choice B** discharge: the rescaling is absorbed at the
adapter level so callers do not need to add a `‖μ ⟨0, _⟩‖ = 1`
hypothesis to existing `IsCanonicalFormBNT`-shaped lemmas.

The output structure refines CPSV16 `eq:II_ABasicTensors` (§II,
arXiv:1606.00608) by grouping the single copy per sector into the
trivial `SectorDecomposition` and imposing the project-specific
`StrictAnti` and `weight_factor` conditions.  The eventual linear
independence `bnt_data` corresponds to CPSV21 Definition 4.3.

Because the weights are rescaled, `P.toTensor` is no longer
`SameMPV₂`-equal to `toTensorFromBlocks μ A`; instead, the two assembled
tensors satisfy a uniform `NonzeroProportionalMPV₂` relation with
scalar `ρ^{-N}` (nonzero for every `N`).  Compose this with the
input `EventuallyNonzeroProportionalMPV₂` to transfer
proportionality to the `SectorDecomposition` surface. -/
theorem IsCanonicalFormBNT.toIsBNTCanonicalFormSD
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hCF : IsCanonicalFormBNT μ A) :
    ∃ P : SectorDecomposition d,
      IsBNTCanonicalFormSD P ∧
      NonzeroProportionalMPV₂ P.toTensor
        (toTensorFromBlocks (d := d) (μ := μ) A) := by
  classical
  have hμne : ∀ j, μ j ≠ 0 := hCF.toIsCanonicalForm.mu_ne_zero
  -- Rescaling factor: `‖μ_0‖` when `r > 0`, else `1` (vacuous).
  set ρ : ℝ := if h : 0 < r then ‖μ ⟨0, h⟩‖ else 1 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    split_ifs with hh
    · exact norm_pos_iff.mpr (hμne ⟨0, hh⟩)
    · exact one_pos
  have hρne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρpos.ne'
  have hρcomplex_norm : ‖(ρ : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hρpos.le]
  -- Rescaled weights.
  let lam : Fin r → ℂ := fun j => μ j / (ρ : ℂ)
  have hlamne : ∀ j, lam j ≠ 0 := fun j => div_ne_zero (hμne j) hρne
  refine ⟨trivialSectorDecomp lam A hlamne, ?_, ?_⟩
  · -- Two-layer predicate: build the existential layer-by-layer.
    refine
      { exists_spectralLevel := ⟨lam, hlamne, ?_, ?_, ?_⟩
        bnt_data := ?_ }
    · -- StrictAnti: dividing by a positive real preserves strict order.
      intro i j hij
      have hμij : ‖μ j‖ < ‖μ i‖ := hCF.mu_strict_anti hij
      simp only [lam, norm_div, hρcomplex_norm]
      exact div_lt_div_of_pos_right hμij hρpos
    · -- weight_factor: `(trivialSectorDecomp lam A).sectors.weight j q = lam j`
      -- and `lam j / lam j = 1`.
      intro j q
      simp [trivialSectorDecomp, div_self (hlamne j)]
    · -- Dominant normalization: `‖lam ⟨0, h⟩‖ = ‖μ_0‖ / ρ = 1`.
      intro hpos
      have hpos' : 0 < r := hpos
      have hρeq : ρ = ‖μ ⟨0, hpos'⟩‖ := by rw [hρdef]; exact dif_pos hpos'
      change ‖lam ⟨0, hpos'⟩‖ = 1
      simp only [lam, norm_div]
      rw [hρcomplex_norm, hρeq]
      exact div_self (norm_ne_zero_iff.mpr (hμne ⟨0, hpos'⟩))
    · -- `HasBNTSectorData (trivialSectorDecomp lam A hlamne)` unfolds to
      -- eventual linear independence of `mpvState (A j) N`, which is the
      -- `eventually_li` field of `IsCanonicalFormBNT.isBNT`.  The basis
      -- of `trivialSectorDecomp` is `A`, independent of the weight choice.
      simpa [HasBNTSectorData, trivialSectorDecomp] using hCF.isBNT.eventually_li
  · -- `NonzeroProportionalMPV₂ P.toTensor (toTensorFromBlocks μ A)`:
    -- `mpv P.toTensor σ = (ρ^N)⁻¹ · mpv (toTensorFromBlocks μ A) σ`.
    intro N
    refine ⟨((ρ : ℂ) ^ N)⁻¹, inv_ne_zero (pow_ne_zero _ hρne), ?_⟩
    intro σ
    -- Step 1: rewrite `mpv P.toTensor` using `sameMPV₂_trivialSectorDecomp`.
    have hP_mpv :
        mpv (trivialSectorDecomp lam A hlamne).toTensor σ
          = mpv (toTensorFromBlocks (d := d) (μ := lam) A) σ :=
      sameMPV₂_trivialSectorDecomp lam A hlamne N σ
    rw [hP_mpv]
    -- Step 2: expand both `toTensorFromBlocks` MPVs as sums over blocks.
    rw [mpv_toTensorFromBlocks_eq_sum lam A σ,
        mpv_toTensorFromBlocks_eq_sum μ A σ, Finset.mul_sum]
    -- Step 3: pointwise — `(μ_k / ρ)^N · mpv A_k = (ρ^N)⁻¹ · μ_k^N · mpv A_k`.
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [lam, smul_eq_mul, div_eq_mul_inv]
    ring

end MPSTensor
