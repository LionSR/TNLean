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

* a **spectral level** `λ : Fin P.basisCount → ℂ` with `λ_j ≠ 0`,
  strictly-decreasing modulus, and **dominant normalization**
  `‖λ_0‖ = 1`;
* **within-sector weights** factor as `P.sectors.weight j q = λ_j · ν_{j,q}`
  with `‖ν_{j,q}‖ = 1`, expressed as `‖P.sectors.weight j q / λ_j‖ = 1`;
* eventual linear independence of the basis blocks
  (`HasBNTSectorData`).

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
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.  Definition of the BNT
  canonical form, §II.
* CPSV21: Cirac--Pérez-García--Schuch--Verstraete, *Matrix product states
  and projected entangled pair states: Concepts, symmetries, theorems*,
  Rev. Mod. Phys. **93**, 045003 (2021); arXiv:2011.12127.
  Definition 4.2 (two-layer BNT canonical form).
* `audits/2026-05-13_cpsv16_ft_path_beta_scout.md`, §"PR 1.5 amendment".
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Two-layer BNT canonical form on the `SectorDecomposition` surface
(`SD = Sector Decomposition`).**

A `SectorDecomposition` `P` carries the two-layer BNT canonical form of
CPSV16 §II (arXiv:1606.00608; equivalently CPSV21 Definition 4.2,
arXiv:2011.12127) when:

* there is a spectral level `λ : Fin P.basisCount → ℂ` with `λ_j ≠ 0`,
  `StrictAnti (fun j => ‖λ_j‖)`, and **dominant normalization**
  `‖λ_0‖ = 1` whenever `P.basisCount > 0`;
* the within-sector weight `P.sectors.weight j q` factors as `λ_j · ν_{j,q}`
  with `‖ν_{j,q}‖ = 1`, recorded as `‖P.sectors.weight j q / λ_j‖ = 1`;
* the basis of normal tensors is eventually linearly independent
  (`HasBNTSectorData`).

The dominant normalization `‖λ_0‖ = 1` is the CPSV21 Definition 4.2
convention.  Combined with `StrictAnti`, it forces `‖λ_j‖ ≤ 1` for
every `j`, hence the per-length coefficients `coeff N j` are uniformly
controlled by the within-sector multiplicities.  This uniform bound is
what powers the analytic discharge of `HNoCancelDischarge` on the
non-dominant `k₀` branch (see the PR 1.5 amendment to the audit memo).

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
in `j` and `‖λ_0‖ = 1` (cf. arXiv:2011.12127 Definition 4.2). -/
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

/-- **Dominant normalization of the spectral level** (CPSV21 Definition 4.2).

When `P` has at least one basis block, the dominant spectral level has
unit modulus, `‖λ_0‖ = 1`.  Combined with `spectralLevel_strict_anti`
this gives `‖λ_j‖ < 1` for `j ≥ 1` and `‖λ_j‖ ≤ 1` for every `j`. -/
theorem spectralLevel_dom_norm_one (h : IsBNTCanonicalFormSD P)
    (hpos : 0 < P.basisCount) :
    ‖h.spectralLevel ⟨0, hpos⟩‖ = 1 :=
  h.exists_spectralLevel.choose_spec.2.2.2 hpos

/-- All spectral-level moduli are bounded by `1`.

Source: CPSV21 Definition 4.2.  Combines `spectralLevel_dom_norm_one`
with `spectralLevel_strict_anti`: the dominant block has unit modulus
and every other block has strictly smaller modulus, so all moduli are
at most `1`. -/
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
spectral level is `λ_j = μ_j / ρ`, which satisfies the CPSV21 Def 4.2
dominant normalization `‖λ_0‖ = 1`.  This is the **Choice B**
discharge: the rescaling is absorbed at the adapter level so callers
do not need to add a `‖μ ⟨0, _⟩‖ = 1` hypothesis to existing
`IsCanonicalFormBNT`-shaped lemmas.

Because the weights are rescaled, `P.toTensor` is no longer
`SameMPV₂`-equal to `toTensorFromBlocks μ A`; instead, the two assembled
tensors satisfy a uniform `NonzeroProportionalMPV₂` relation with
scalar `ρ^{-N}` (nonzero for every `N`).  Compose this with the
input `EventuallyNonzeroProportionalMPV₂` to transfer
proportionality to the `SectorDecomposition` surface.

(cf. arXiv:1606.00608 §II / arXiv:2011.12127 Definition 4.2.) -/
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
