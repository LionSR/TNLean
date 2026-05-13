/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap.FixedBlockDecay
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.RateQuantifiedDischarge

/-!
# Rate-quantified fixed-block decay contradictions on the `IsCanonicalFormBNT` surface

This module routes the rate-quantified two-layer discharge
(`fixed_*_..._sectorDecomp_twoLayer_rateQuantified` in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/RateQuantifiedDischarge.lean`)
through the Choice B adapter
`IsCanonicalFormBNT.toIsBNTCanonicalFormSD` (in
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/IsBNTCanonicalFormSD.lean`)
to the `_CFBNT` surface of
`Full/NondecayingOverlap/FixedBlockDecay.lean`.

The non-rate-quantified `_CFBNT` lemmas in
`Full/NondecayingOverlap/FixedBlockDecay.lean` (lines 107, 152) carry an
unconditional shape that — on the non-dominant projection branch — is
not dischargeable on the present `IsCanonicalFormBNT` surface alone
(see `audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md`).  Those
two lemmas remain `sorry`-marked here; the present module adds **sister
theorems with the rate-quantified hypotheses inlined as additional
inputs**, fully proven.

## Adapter shape

The existing `IsCanonicalFormBNT.toIsBNTCanonicalFormSD` returns a
sector decomposition existentially:

`∃ P : SectorDecomposition d, IsBNTCanonicalFormSD P ∧ NonzeroProportionalMPV₂ ...`

Rate hypotheses on the `IsBNTCanonicalFormSD` surface must be supplied
against the **specific** spectral level of the resulting `P`, so this
module exposes a **non-existential companion**
`IsCanonicalFormBNT.bntSectorDecomp` that returns a fixed
`SectorDecomposition d` (the same `trivialSectorDecomp` witness used
internally by the existential adapter), together with
`bntSectorDecomp_isBNTCanonicalFormSD` and
`bntSectorDecomp_proportional`.  The companion does not alter the
existing existential adapter; both coexist.

## Main statements

* `IsCanonicalFormBNT.bntSectorDecomp` — non-existential companion to
  `IsCanonicalFormBNT.toIsBNTCanonicalFormSD`, returning the
  `trivialSectorDecomp` carrying the rescaled spectral level
  `λ_j = μ_j / ‖μ_0‖`.
* `IsCanonicalFormBNT.bntSectorDecomp_isBNTCanonicalFormSD` — the
  two-layer BNT structural data on this fixed sector decomposition.
* `IsCanonicalFormBNT.bntSectorDecomp_proportional` — the
  `NonzeroProportionalMPV₂` between the sector-decomposition assembled
  tensor and the block-assembled tensor.
* `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_rateQuantified` —
  the right-block discharge for an arbitrary fixed block, given the
  rate-quantified within-family and cross-family overlap decay
  hypotheses on the rescaled spectral levels.
* `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_rateQuantified` —
  the symmetric left-block discharge.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  arXiv:1606.00608 (2017).  Theorem `thm1`, lines 1170--1192.
* `audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md` for the
  non-dominant projection obstruction analysis.
* `docs/paper-gaps/cpsv16_bnt_rate_quantification.tex` for the
  structural rate hypothesis paper-gap note.
-/

open scoped BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

section CFBNTSectorDecomp

-- Some structural facts below do not consume the `NeZero` instance on
-- `dim k`; suppress the unused-section-variable lint for the section.
set_option linter.unusedSectionVars false

variable {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
variable {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}

/-- **Dominant-block modulus** of a `IsCanonicalFormBNT` family, with a
unit value when the family is empty.  Used as the rescaling factor in
the Choice B adapter `IsCanonicalFormBNT.bntSectorDecomp`.  Always
strictly positive (cf. `dominantNorm_pos`). -/
noncomputable def IsCanonicalFormBNT.dominantNorm
    (_hCF : IsCanonicalFormBNT μ A) : ℝ :=
  if h : 0 < r then ‖μ ⟨0, h⟩‖ else 1

/-- The dominant-block modulus is positive: it is `‖μ_0‖ > 0` when the
family is nonempty, and `1` otherwise. -/
theorem IsCanonicalFormBNT.dominantNorm_pos
    (hCF : IsCanonicalFormBNT μ A) : 0 < hCF.dominantNorm := by
  unfold IsCanonicalFormBNT.dominantNorm
  split_ifs with hh
  · exact norm_pos_iff.mpr (hCF.toIsCanonicalForm.mu_ne_zero ⟨0, hh⟩)
  · exact one_pos

/-- The dominant-block modulus is nonzero (as a real number). -/
theorem IsCanonicalFormBNT.dominantNorm_ne_zero
    (hCF : IsCanonicalFormBNT μ A) : hCF.dominantNorm ≠ 0 :=
  hCF.dominantNorm_pos.ne'

/-- The dominant-block modulus cast to `ℂ` is nonzero. -/
theorem IsCanonicalFormBNT.complex_dominantNorm_ne_zero
    (hCF : IsCanonicalFormBNT μ A) : (hCF.dominantNorm : ℂ) ≠ 0 := by
  exact_mod_cast hCF.dominantNorm_ne_zero

/-- The complex norm of the dominant-block modulus equals the modulus itself. -/
theorem IsCanonicalFormBNT.complex_norm_dominantNorm
    (hCF : IsCanonicalFormBNT μ A) :
    ‖(hCF.dominantNorm : ℂ)‖ = hCF.dominantNorm := by
  rw [Complex.norm_real, Real.norm_of_nonneg hCF.dominantNorm_pos.le]

/-- On a nonempty family, the dominant-block modulus is `‖μ_0‖`. -/
theorem IsCanonicalFormBNT.dominantNorm_eq_of_pos
    (hCF : IsCanonicalFormBNT μ A) (hpos : 0 < r) :
    hCF.dominantNorm = ‖μ ⟨0, hpos⟩‖ := by
  unfold IsCanonicalFormBNT.dominantNorm
  exact dif_pos hpos

/-- Rescaled per-block spectral weight `λ_j = μ_j / ‖μ_0‖`. -/
noncomputable def IsCanonicalFormBNT.rescaledWeight
    (hCF : IsCanonicalFormBNT μ A) : Fin r → ℂ :=
  fun j => μ j / (hCF.dominantNorm : ℂ)

theorem IsCanonicalFormBNT.rescaledWeight_ne_zero
    (hCF : IsCanonicalFormBNT μ A) (j : Fin r) :
    hCF.rescaledWeight j ≠ 0 :=
  div_ne_zero (hCF.toIsCanonicalForm.mu_ne_zero j) hCF.complex_dominantNorm_ne_zero

/-- **Non-existential companion to `IsCanonicalFormBNT.toIsBNTCanonicalFormSD`.**

Returns a specific `SectorDecomposition d` — the `trivialSectorDecomp`
carrying the rescaled spectral weights `λ_j = μ_j / ‖μ_0‖` — instead
of an existential witness.  This shape lets callers attach rate-quantified
hypotheses
(`HasRateQuantifiedCrossOverlapDecay`, `HasCrossFamilyRateDecay`)
to the **fixed** `bntSectorDecomp_isBNTCanonicalFormSD.spectralLevel`,
which is required for the two-layer rate-quantified discharge in
`RateQuantifiedDischarge.lean`. -/
noncomputable def IsCanonicalFormBNT.bntSectorDecomp
    (hCF : IsCanonicalFormBNT μ A) : SectorDecomposition d :=
  trivialSectorDecomp (d := d) hCF.rescaledWeight A hCF.rescaledWeight_ne_zero

/-- The basis of `bntSectorDecomp` is the original block family. -/
@[simp]
theorem IsCanonicalFormBNT.bntSectorDecomp_basis
    (hCF : IsCanonicalFormBNT μ A) :
    hCF.bntSectorDecomp.basis = A := rfl

/-- The `basisCount` of `bntSectorDecomp` equals the original block count `r`. -/
@[simp]
theorem IsCanonicalFormBNT.bntSectorDecomp_basisCount
    (hCF : IsCanonicalFormBNT μ A) :
    hCF.bntSectorDecomp.basisCount = r := rfl

/-- The two-layer BNT structural data on the `bntSectorDecomp`. -/
theorem IsCanonicalFormBNT.bntSectorDecomp_isBNTCanonicalFormSD
    (hCF : IsCanonicalFormBNT μ A) :
    IsBNTCanonicalFormSD (d := d) hCF.bntSectorDecomp := by
  classical
  have hρpos : 0 < hCF.dominantNorm := hCF.dominantNorm_pos
  have hρne : (hCF.dominantNorm : ℂ) ≠ 0 := hCF.complex_dominantNorm_ne_zero
  have hρcomplex_norm : ‖(hCF.dominantNorm : ℂ)‖ = hCF.dominantNorm :=
    hCF.complex_norm_dominantNorm
  have hμne : ∀ j, μ j ≠ 0 := hCF.toIsCanonicalForm.mu_ne_zero
  refine
    { exists_spectralLevel :=
        ⟨hCF.rescaledWeight, hCF.rescaledWeight_ne_zero, ?_, ?_, ?_⟩
      bnt_data := ?_ }
  · -- StrictAnti
    intro i j hij
    have hμij : ‖μ j‖ < ‖μ i‖ := hCF.mu_strict_anti hij
    change ‖hCF.rescaledWeight i‖ > ‖hCF.rescaledWeight j‖
    simp only [IsCanonicalFormBNT.rescaledWeight, norm_div, hρcomplex_norm]
    exact div_lt_div_of_pos_right hμij hρpos
  · -- weight_factor
    intro j q
    have hweight :
        hCF.bntSectorDecomp.sectors.weight j q = hCF.rescaledWeight j := by
      simp [IsCanonicalFormBNT.bntSectorDecomp, trivialSectorDecomp]
    rw [hweight, div_self (hCF.rescaledWeight_ne_zero j)]
    exact norm_one
  · -- Dominant normalization
    intro hpos
    have hρeq : hCF.dominantNorm = ‖μ ⟨0, hpos⟩‖ :=
      hCF.dominantNorm_eq_of_pos hpos
    change ‖hCF.rescaledWeight ⟨0, hpos⟩‖ = 1
    simp only [IsCanonicalFormBNT.rescaledWeight, norm_div, hρcomplex_norm]
    rw [hρeq]
    exact div_self (norm_ne_zero_iff.mpr (hμne ⟨0, hpos⟩))
  · -- bnt_data
    simpa [HasBNTSectorData, IsCanonicalFormBNT.bntSectorDecomp,
      trivialSectorDecomp] using hCF.isBNT.eventually_li

/-- The `bntSectorDecomp` assembled tensor is `NonzeroProportionalMPV₂`
to the block-assembled tensor, with proportionality scalar `ρ⁻ᴺ`
(where `ρ = ‖μ_0‖`).  The scalar is nonzero because `ρ > 0`. -/
theorem IsCanonicalFormBNT.bntSectorDecomp_proportional
    (hCF : IsCanonicalFormBNT μ A) :
    NonzeroProportionalMPV₂ hCF.bntSectorDecomp.toTensor
      (toTensorFromBlocks (d := d) (μ := μ) A) := by
  classical
  have hρne : (hCF.dominantNorm : ℂ) ≠ 0 := hCF.complex_dominantNorm_ne_zero
  intro N
  refine ⟨((hCF.dominantNorm : ℂ) ^ N)⁻¹, inv_ne_zero (pow_ne_zero _ hρne), ?_⟩
  intro σ
  -- The sector-decomposition assembled MPV agrees with the rescaled block-assembled MPV.
  have hP_mpv :
      mpv hCF.bntSectorDecomp.toTensor σ
        = mpv (toTensorFromBlocks (d := d) (μ := hCF.rescaledWeight) A) σ :=
    sameMPV₂_trivialSectorDecomp (d := d) hCF.rescaledWeight A
      hCF.rescaledWeight_ne_zero N σ
  rw [hP_mpv]
  rw [mpv_toTensorFromBlocks_eq_sum hCF.rescaledWeight A σ,
      mpv_toTensorFromBlocks_eq_sum μ A σ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [IsCanonicalFormBNT.rescaledWeight, smul_eq_mul, div_eq_mul_inv]
  ring

end CFBNTSectorDecomp

section HeteroEqualCase

set_option linter.style.longLine false in
/-- **Rate-quantified right-block fixed-block decay contradiction on
the `IsCanonicalFormBNT` surface.**

Sister statement to
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
(in `Full/NondecayingOverlap/FixedBlockDecay.lean`) with the two
rate-quantified hypotheses
(`HasRateQuantifiedCrossOverlapDecay` on the `B`-side,
`HasCrossFamilyRateDecay` between the rescaled `A` and `B` spectral
levels) inlined as additional inputs and fully proven.  The unconditional
form is documented at
`Full/NondecayingOverlap/FixedBlockDecay.lean:107` and remains a paper-gap
(per Option~2 of
`audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md`); the rate
hypotheses correspond to the analytic obligation derivable from the
BNT transfer matrix spectral gap.

The cross-family qualitative decay
`Tendsto (fun N => mpvOverlap (A j) (B k₀) N) atTop (nhds 0)` is
automatically implied by the rate hypothesis `hRateCross`, so it does
**not** appear as an extra input in this signature (in contrast with
the non-rate-quantified form).

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. -/
theorem fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_rateQuantified
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (k₀ : Fin rB)
    (hRateB : HasRateQuantifiedCrossOverlapDecay
        hB.bntSectorDecomp
        hB.bntSectorDecomp_isBNTCanonicalFormSD.spectralLevel)
    (hRateCross : HasCrossFamilyRateDecay
        hA.bntSectorDecomp hB.bntSectorDecomp
        hA.bntSectorDecomp_isBNTCanonicalFormSD.spectralLevel
        hB.bntSectorDecomp_isBNTCanonicalFormSD.spectralLevel) :
    False := by
  classical
  -- Step 1: name the two sector decompositions and structural data.
  set P_sd : SectorDecomposition d := hA.bntSectorDecomp with hP_sd_def
  set Q_sd : SectorDecomposition d := hB.bntSectorDecomp with hQ_sd_def
  have hP_sd : IsBNTCanonicalFormSD P_sd :=
    hA.bntSectorDecomp_isBNTCanonicalFormSD
  have hQ_sd : IsBNTCanonicalFormSD Q_sd :=
    hB.bntSectorDecomp_isBNTCanonicalFormSD
  -- Step 2: adapter identities, written in `mpv σ` form.
  have hρA_pos : 0 < hA.dominantNorm := hA.dominantNorm_pos
  have hρB_pos : 0 < hB.dominantNorm := hB.dominantNorm_pos
  have hρA_ne : (hA.dominantNorm : ℂ) ≠ 0 := hA.complex_dominantNorm_ne_zero
  have hρB_ne : (hB.dominantNorm : ℂ) ≠ 0 := hB.complex_dominantNorm_ne_zero
  have hρA_norm : ‖(hA.dominantNorm : ℂ)‖ = hA.dominantNorm :=
    hA.complex_norm_dominantNorm
  have hρB_norm : ‖(hB.dominantNorm : ℂ)‖ = hB.dominantNorm :=
    hB.complex_norm_dominantNorm
  have hAdapter_A : ∀ N (σ : Fin N → Fin d),
      mpv P_sd.toTensor σ
        = ((hA.dominantNorm : ℂ) ^ N)⁻¹
            * mpv (toTensorFromBlocks (d := d) (μ := μA) A) σ := by
    intro N σ
    have hP_mpv :
        mpv P_sd.toTensor σ
          = mpv (toTensorFromBlocks (d := d) (μ := hA.rescaledWeight) A) σ :=
      sameMPV₂_trivialSectorDecomp (d := d) hA.rescaledWeight A
        hA.rescaledWeight_ne_zero N σ
    rw [hP_mpv,
        mpv_toTensorFromBlocks_eq_sum hA.rescaledWeight A σ,
        mpv_toTensorFromBlocks_eq_sum μA A σ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [IsCanonicalFormBNT.rescaledWeight, smul_eq_mul, div_eq_mul_inv]
    ring
  have hAdapter_B : ∀ N (σ : Fin N → Fin d),
      mpv Q_sd.toTensor σ
        = ((hB.dominantNorm : ℂ) ^ N)⁻¹
            * mpv (toTensorFromBlocks (d := d) (μ := μB) B) σ := by
    intro N σ
    have hP_mpv :
        mpv Q_sd.toTensor σ
          = mpv (toTensorFromBlocks (d := d) (μ := hB.rescaledWeight) B) σ :=
      sameMPV₂_trivialSectorDecomp (d := d) hB.rescaledWeight B
        hB.rescaledWeight_ne_zero N σ
    rw [hP_mpv,
        mpv_toTensorFromBlocks_eq_sum hB.rescaledWeight B σ,
        mpv_toTensorFromBlocks_eq_sum μB B σ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [IsCanonicalFormBNT.rescaledWeight, smul_eq_mul, div_eq_mul_inv]
    ring
  -- Step 3: dominant-adjusted scalar with norm tending to one.
  obtain ⟨c, _hc_ne, hState, hcAdj⟩ :=
    exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hProp
  set a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩ with ha0_def
  set b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩ with hb0_def
  have hμA_ne : μA a0 ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero a0
  have hμB_ne : μB b0 ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero b0
  have hρA_eq : hA.dominantNorm = ‖μA a0‖ :=
    hA.dominantNorm_eq_of_pos (Nat.pos_of_ne_zero hrA)
  have hρB_eq : hB.dominantNorm = ‖μB b0‖ :=
    hB.dominantNorm_eq_of_pos (Nat.pos_of_ne_zero hrB)
  -- Step 4: lift `hState` to `mpv σ`-level proportionality between block-assembled tensors.
  have hc_eq_blocks : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv (toTensorFromBlocks μA A) σ
        = c N * mpv (toTensorFromBlocks μB B) σ := by
    refine hState.mono ?_
    intro N hN σ
    have hAstate :
        mpvState (d := d) (toTensorFromBlocks μA A) N =
          ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N := by
      refine mpvState_eq_sum_of_decomp (d := d) (toTensorFromBlocks μA A) A
        (N := N) (fun j : Fin rA => (μA j) ^ N) ?_
      intro σ'
      simpa [smul_eq_mul] using
        mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μA) (A := A) σ'
    have hBstate :
        mpvState (d := d) (toTensorFromBlocks μB B) N =
          ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N := by
      refine mpvState_eq_sum_of_decomp (d := d) (toTensorFromBlocks μB B) B
        (N := N) (fun k : Fin rB => (μB k) ^ N) ?_
      intro σ'
      simpa [smul_eq_mul] using
        mpv_toTensorFromBlocks_eq_sum (d := d) (μ := μB) (A := B) σ'
    have hTotal :
        mpvState (d := d) (toTensorFromBlocks μA A) N =
          c N • mpvState (d := d) (toTensorFromBlocks μB B) N := by
      rw [hAstate, hN, hBstate]
    have hσ := congr_arg (fun v => v σ) hTotal
    simpa [mpvState_apply, mpv, smul_eq_mul] using hσ
  -- Step 5: SD-side proportionality with rescaled scalar
  -- `c_sd N := c N * ((ρB : ℂ) / (ρA : ℂ))^N`.
  set c_sd : ℕ → ℂ := fun N =>
    c N * ((hB.dominantNorm : ℂ) / (hA.dominantNorm : ℂ)) ^ N with hc_sd_def
  have hc_eq_sd : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv P_sd.toTensor σ = c_sd N * mpv Q_sd.toTensor σ := by
    refine hc_eq_blocks.mono ?_
    intro N hN σ
    rw [hAdapter_A N σ, hAdapter_B N σ, hN σ]
    have hρA_pow_ne : ((hA.dominantNorm : ℂ) ^ N) ≠ 0 := pow_ne_zero N hρA_ne
    have hρB_pow_ne : ((hB.dominantNorm : ℂ) ^ N) ≠ 0 := pow_ne_zero N hρB_ne
    simp only [c_sd, div_pow]
    field_simp
  -- Step 6: norm of `c_sd` tends to one.  Use the dominant-adjusted scalar
  -- limit and the identity `‖(μB b0 / μA a0)^N‖ = (ρB / ρA)^N`.
  have hcsd_eq_pow : ∀ N : ℕ,
      ‖c N * (μB b0 / μA a0) ^ N‖ = ‖c_sd N‖ := by
    intro N
    have h1 : ‖(μB b0 / μA a0) ^ N‖
        = ‖((hB.dominantNorm : ℂ) / (hA.dominantNorm : ℂ)) ^ N‖ := by
      rw [norm_pow, norm_pow, norm_div, norm_div, hρA_norm, hρB_norm,
          hρA_eq, hρB_eq]
    rw [norm_mul, norm_mul, h1]
  have hc_sd_norm : Tendsto (fun N => ‖c_sd N‖) atTop (nhds (1 : ℝ)) := by
    refine hcAdj.congr ?_
    intro N
    exact hcsd_eq_pow N
  -- Eventually `‖c_sd N‖ ≥ 1/2`.
  have hc_sd_lower : ∀ᶠ N in atTop, (1 / 2 : ℝ) ≤ ‖c_sd N‖ := by
    have hOpen : IsOpen (Set.Ioi (1 / 2 : ℝ)) := isOpen_Ioi
    have hmem : (1 : ℝ) ∈ Set.Ioi (1 / 2 : ℝ) := by norm_num
    have := hc_sd_norm (hOpen.mem_nhds hmem)
    filter_upwards [this] with N hN
    exact le_of_lt hN
  -- Step 7: self-overlap limit on `Q_sd.basis k₀ = B k₀`.
  have hQ_self_limit :
      ∃ ℓ : ℂ, ℓ ≠ 0 ∧
        Tendsto
          (fun N => mpvOverlap (d := d) (Q_sd.basis k₀) (Q_sd.basis k₀) N)
          atTop (nhds ℓ) :=
    ⟨1, one_ne_zero,
      hB.toHasNormalizedSelfOverlap.overlap_tendsto_one k₀⟩
  -- Step 8: apply the single-sequence renormalised non-cancellation.
  refine hNoCancel_renorm_single_seq (d := d) P_sd Q_sd hP_sd hQ_sd
    hRateB hRateCross k₀ hQ_self_limit c_sd ?_ hc_eq_sd
  exact ⟨(1 / 2 : ℝ), by norm_num, hc_sd_lower⟩

set_option linter.style.longLine false in
/-- **Rate-quantified left-block fixed-block decay contradiction on
the `IsCanonicalFormBNT` surface.**

Symmetric counterpart of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_rateQuantified`
fixing an `A`-block `j₀ : Fin rA` instead of a `B`-block.  Reduces to
the right-block version after swapping the two families via
`EventuallyNonzeroProportionalMPV₂.symm`.  The rate hypotheses likewise
swap: the within-family rate is taken on the `A`-side, and the
cross-family rate is from `B` to `A`.

The unconditional sister statement is at
`Full/NondecayingOverlap/FixedBlockDecay.lean:152` and remains
paper-gap material per Option~2 of
`audits/2026-05-13_cpsv16_ft_path_beta_pr2_5_design.md`.

Source: arXiv:1606.00608, Theorem `thm1`, lines 1182--1185. -/
theorem fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_rateQuantified
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (j₀ : Fin rA)
    (hRateA : HasRateQuantifiedCrossOverlapDecay
        hA.bntSectorDecomp
        hA.bntSectorDecomp_isBNTCanonicalFormSD.spectralLevel)
    (hRateCross : HasCrossFamilyRateDecay
        hB.bntSectorDecomp hA.bntSectorDecomp
        hB.bntSectorDecomp_isBNTCanonicalFormSD.spectralLevel
        hA.bntSectorDecomp_isBNTCanonicalFormSD.spectralLevel) :
    False :=
  fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT_rateQuantified
    B A hB hA hrB hrA hProp.symm j₀ hRateA hRateCross

end HeteroEqualCase

end MPSTensor
