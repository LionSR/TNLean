/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexPhasePositivity
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.Core.TransferChannel
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain
import TNLean.MPS.BNT.Construction
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.Symmetry.StringOrderAux

/-!
# Perron gauges for normal tensors

This file connects the spectral normal-tensor condition of
Cirac--Pérez-García--Schuch--Verstraete with eventual block injectivity.

For a normal tensor, irreducible Perron--Frobenius theory gives positive-definite
right and left eigenvectors of the transfer map.  The spectral-radius-one
normalization forces both Perron eigenvalues to be one.  Gauging with the left
eigenvector therefore gives a trace-preserving tensor without any scalar
rescaling.  Peripheral primitivity and irreducibility survive this gauge, so
the trace-preserving primitive normality theorem gives eventual injectivity.
Gauge invariance then transports eventual injectivity back to the original
tensor.

## Main statements

* `exists_tpGauge_of_irreducible_spectralRadius_one`: an irreducible
  spectral-radius-one tensor admits a pure trace-preserving Perron gauge.
* `IsNormalTensor.exists_tpGauge`: a normal tensor admits a pure
  trace-preserving Perron gauge.
* `IsNormalTensor.isNormal`: spectral normality implies eventual block
  injectivity.
* `isNormalTensor_of_isNormal_leftCanonical`: an algebraically normal
  left-canonical tensor is a spectrally normalized normal tensor.
* `MPVBlockPhaseEquiv.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor`: exact MPV
  phase equivalence between normal tensors is realized by an invertible gauge.
* `IsCPSVBasisOfNormalTensors.blocks_not_gaugePhaseEquiv`: distinct members of
  a basis of normal tensors are not gauge-phase equivalent.
* `exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv`:
  a separated finite family of normal tensors is eventually linearly
  independent.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, lines 231--235
  and the proof of Lemma `equalMPS`, lines 1093--1117.
* Wolf, *Quantum Channels & Operations*, Theorem 6.3.
-/

open scoped Matrix BigOperators ComplexOrder
open Filter

namespace MPSTensor

variable {d D : ℕ}

/-- An irreducible tensor of spectral radius one admits a trace-preserving Perron gauge with no
scalar rescaling.

The positive-definite right and left Perron eigenvectors have the same positive eigenvalue.  The
spectral-radius-one hypothesis forces this eigenvalue to be one, so the left Perron eigenvector is
an adjoint fixed point of the original transfer map.  Gauging by its positive square root is
therefore a pure similarity, is left-canonical, and preserves irreducibility.

Source: arXiv:1708.00029, lines 313--332; Wolf, *Quantum Channels & Operations*, Theorem 6.3. -/
theorem exists_tpGauge_of_irreducible_spectralRadius_one
    {A : MPSTensor d D}
    (hIrr : IsIrreducibleTensor A)
    (hRadius :
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (transferMap (d := d) (D := D) A)) = 1) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosDef ∧
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ = σ ∧
      IsLeftCanonical (tpGauge (d := d) (D := D) A σ) ∧
      GaugeEquiv A (tpGauge (d := d) (D := D) A σ) ∧
      IsIrreducibleTensor (tpGauge (d := d) (D := D) A σ) := by
  have hD : D ≠ 0 :=
    matrix_dim_ne_zero_of_spectralRadius_eq_one
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (transferMap (d := d) (D := D) A))
      hRadius
  letI : NeZero D := ⟨hD⟩
  have hA : ∃ i, A i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hmap : transferMap (d := d) (D := D) A = 0 := by
      ext X a b
      simp [transferMap_apply, hzero]
    have hspectral := hRadius
    rw [hmap] at hspectral
    simp at hspectral
  have hIrrMap : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor A hIrr
  obtain ⟨ρ, r, hρ, hr, hρeig⟩ :=
    exists_posDef_transferMap_eigenvector_of_irreducible A hIrr hA
  have hradius :
      (spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (transferMap (d := d) (D := D) A))).toReal = r :=
    spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp
      (transferMap (d := d) (D := D) A) (transferMap_isCPMap A) hIrrMap
      ρ r hρ hr hρeig
  have hradius_one :
      (spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
          (transferMap (d := d) (D := D) A))).toReal = 1 := by
    rw [hRadius]
    simp
  have hr_one : r = 1 := hradius.symm.trans hradius_one
  obtain ⟨σ, t, hσ, ht, hσeig⟩ :=
    exists_posDef_adjoint_eigenvector A hIrr hA
  have htrace : Matrix.trace (σ * transferMap (d := d) (D := D) A ρ) =
      Matrix.trace
        (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ * ρ) :=
    trace_mul_transferMap_adjoint A rfl σ ρ
  have htr_ne : Matrix.trace (σ * ρ) ≠ 0 := by
    intro htr
    exact (Matrix.PosDef.isUnit hρ).ne_zero
      (Kraus.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero
        hρ.posSemidef hσ htr)
  have hscalar : (r : ℂ) * Matrix.trace (σ * ρ) =
      (t : ℂ) * Matrix.trace (σ * ρ) := by
    calc
      (r : ℂ) * Matrix.trace (σ * ρ) =
          Matrix.trace (σ * ((r : ℂ) • ρ)) := by
            rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      _ = Matrix.trace (σ * transferMap (d := d) (D := D) A ρ) := by rw [hρeig]
      _ = Matrix.trace
          (transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ * ρ) := htrace
      _ = Matrix.trace (((t : ℂ) • σ) * ρ) := by rw [hσeig]
      _ = (t : ℂ) * Matrix.trace (σ * ρ) := by
            rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hrt : r = t := by
    have hc : (r : ℂ) = (t : ℂ) := mul_right_cancel₀ htr_ne hscalar
    exact_mod_cast hc
  have ht_one : t = 1 := hrt ▸ hr_one
  have hσfix : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ = σ := by
    simpa [ht_one] using hσeig
  have hTP : IsLeftCanonical (tpGauge (d := d) (D := D) A σ) :=
    tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint A σ hσ hσfix
  have hGauge : GaugeEquiv A (tpGauge (d := d) (D := D) A σ) :=
    gaugeEquiv_tpGauge A σ hσ
  have hGaugeIrr : IsIrreducibleTensor (tpGauge (d := d) (D := D) A σ) :=
    isIrreducibleTensor_tpGauge_of_isIrreducibleMap A σ hσ hIrrMap
  exact ⟨σ, hσ, hσfix, hTP, hGauge, hGaugeIrr⟩

/-- A normal tensor admits a trace-preserving gauge with no scalar rescaling.

The tensor is normal in the sense of arXiv:1606.00608, lines 231--235: its
transfer map has spectral radius one and unique peripheral eigenvalue one.
The spectral-radius normalization forces positive bond dimension. The
positive-definite left Perron eigenvector consequently has eigenvalue one, so
the usual Perron gauge is a pure similarity of the original tensor. -/
theorem IsNormalTensor.exists_tpGauge
    {A : MPSTensor d D} (h : IsNormalTensor A) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosDef ∧
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ = σ ∧
      IsLeftCanonical (tpGauge (d := d) (D := D) A σ) ∧
      GaugeEquiv A (tpGauge (d := d) (D := D) A σ) ∧
      _root_.IsPrimitive
        (transferMap (d := d) (D := D) (tpGauge (d := d) (D := D) A σ)) ∧
      IsIrreducibleTensor (tpGauge (d := d) (D := D) A σ) := by
  obtain ⟨σ, hσ, hσfix, hTP, hGauge, hIrr⟩ :=
    exists_tpGauge_of_irreducible_spectralRadius_one
      h.no_invariant_proj h.spectral_radius_one
  have hPrim : _root_.IsPrimitive
      (transferMap (d := d) (D := D) (tpGauge (d := d) (D := D) A σ)) :=
    (isPrimitive_transferMap_tpGauge_iff A σ hσ).2 h.primitive_transfer
  exact ⟨σ, hσ, hσfix, hTP, hGauge, hPrim, hIrr⟩

/-- A normal tensor in the spectral sense of arXiv:1606.00608 is eventually
block-injective. -/
theorem IsNormalTensor.isNormal
    {A : MPSTensor d D} (h : IsNormalTensor A) : IsNormal A := by
  letI : NeZero D := ⟨h.bondDim_ne_zero⟩
  obtain ⟨σ, _hσ, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := h.exists_tpGauge
  have hNormalGauge : IsNormal (tpGauge (d := d) (D := D) A σ) :=
    isNormal_of_tp_primitive_irreducible _ hTP hPrim hIrr
  exact isNormal_of_gaugeEquiv hNormalGauge hGauge.symm

/-- An algebraically normal left-canonical tensor is a spectrally normalized normal tensor.

Algebraic normality and left-canonical normalization imply strong irreducibility by
arXiv:0909.5347, Proposition 3. Thus the transfer map has a positive-definite fixed point and
has no unit-modulus eigenvalue other than one. The spectral normalization of
arXiv:1606.00608, lines 224--235, then has Perron value one and does not rescale the tensor.
This conversion is an input to the BNT identification invoked at arXiv:1606.00608, line 1307.
-/
theorem isNormalTensor_of_isNormal_leftCanonical [NeZero D]
    (A : MPSTensor d D) (hNormal : IsNormal A) (hLeft : IsLeftCanonical A) :
    IsNormalTensor A := by
  have hStrong : IsStronglyIrreduciblePaper A :=
    isNormal_implies_stronglyIrreducible A hLeft hNormal
  obtain ⟨ρ, hρ, hρfix⟩ := hStrong.posDef_fixedPoint
  have hIrr : IsIrreducibleTensor A :=
    isIrreducibleTensor_of_isIrreducibleMap A hStrong.isIrreducibleMap
  have huniq : ∀ μ : ℂ, Module.End.HasEigenvalue (transferMap A) μ →
      ‖μ‖ = (1 : ℝ) → μ = (1 : ℂ) := by
    intro μ hμ hμnorm
    have hmem : μ ∈ peripheralEigenvalues (transferMap A) := ⟨hμ, hμnorm⟩
    rw [hStrong.peripheralEigenvalues_eq] at hmem
    simpa using hmem
  have hScaled : IsNormalTensor (fun i =>
      (((Real.sqrt (1 : ℝ) : ℝ) : ℂ))⁻¹ • A i) :=
    isNormalTensor_invSqrt_smul_of_unique_peripheral A hIrr ρ 1 hρ (by norm_num)
      (by simpa using hρfix) huniq
  simpa using hScaled

/-- A normal tensor has a nonzero letter.

Indeed, if every letter vanished, then its transfer map and hence its spectral
radius would vanish, contradicting the spectral-radius-one normalization of
arXiv:1606.00608, lines 231--235. -/
theorem IsNormalTensor.exists_apply_ne_zero [NeZero D]
    {A : MPSTensor d D} (h : IsNormalTensor A) : ∃ i, A i ≠ 0 := by
  by_contra hzero
  push Not at hzero
  have hmap : transferMap (d := d) (D := D) A = 0 := by
    ext X a b
    simp [transferMap_apply, hzero]
  have hspectral := h.spectral_radius_one
  rw [hmap] at hspectral
  simp at hspectral

/-- The self-overlap of a normal tensor tends to one.

The trace-preserving Perron gauge is a pure similarity, so it leaves every
matrix product vector unchanged.  The assertion therefore follows from the
primitive trace-preserving overlap limit.  This is the normalization used in
the proof of Lemma `equalMPS` of arXiv:1606.00608, lines 1080--1097. -/
theorem IsNormalTensor.selfOverlap_tendsto_one [NeZero D]
    {A : MPSTensor d D} (hA : IsNormalTensor A) :
    Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ)) := by
  obtain ⟨σ, _hσ, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := hA.exists_tpGauge
  let A' := tpGauge (d := d) (D := D) A σ
  have hPrepared : Tendsto (fun N => mpvOverlap (d := d) A' A' N)
      atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible A' hIrr hTP hPrim
  apply hPrepared.congr'
  filter_upwards with N
  apply Finset.sum_congr rfl
  intro w _
  rw [GaugeEquiv.sameMPV hGauge N w]

/-- Identifying equal bond dimensions does not change normality. -/
theorem isNormalTensor_cast_iff {D₁ D₂ : ℕ} (hdim : D₁ = D₂)
    (A : MPSTensor d D₁) :
    IsNormalTensor (cast (congr_arg (MPSTensor d) hdim) A) ↔ IsNormalTensor A := by
  subst D₂
  rfl

/-- The scalar in an explicit gauge-phase relation between normal tensors has
unit norm.

After identifying the bond dimensions, the gauge relation multiplies the
self-overlap by powers of $\zeta\overline\zeta$.  Since both normalized
self-overlaps tend to one, $\lVert\zeta\rVert=1$.  This is the phase
normalization following Lemma `equalMPS` of arXiv:1606.00608, lines
1080--1097. -/
theorem norm_eq_one_of_gaugePhase_cast_of_isNormalTensor
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNormalTensor A) (hB : IsNormalTensor B)
    (hdim : D₁ = D₂) {X : GL (Fin D₂) ℂ} {ζ : ℂ}
    (hrel : ∀ i, B i = ζ • ((X : Matrix (Fin D₂) (Fin D₂) ℂ) *
      (cast (congr_arg (MPSTensor d) hdim) A) i *
      (↑(X⁻¹) : Matrix (Fin D₂) (Fin D₂) ℂ))) :
    ‖ζ‖ = 1 := by
  subst D₂
  have hAA : Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖)
      atTop (nhds (1 : ℝ)) := by
    simpa using hA.selfOverlap_tendsto_one.norm
  have hBB : Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖)
      atTop (nhds (1 : ℝ)) := by
    simpa using hB.selfOverlap_tendsto_one.norm
  exact norm_eq_one_of_selfOverlap_scale hAA hBB
    (mpvOverlap_self_scale_of_mpv_eq_pow_mul
      (mpv_eq_pow_mul_of_gaugePhase A B X ζ hrel))

/-- MPV phase equivalence between normal tensors is realized letterwise by a
gauge and a nonzero scalar, after identifying their bond dimensions.

This is the grouping implication in arXiv:1606.00608, Lemma `equalMPS`
(lines 1080--1117) and Proposition `prop:char-BNT` (lines 1135--1148).
Each tensor is first put into its trace-preserving Perron gauge.  The gauges
are pure similarities because both tensors have spectral radius one.  The
rectangular overlap-decay theorem gives equality of the bond dimensions from
the positive-length overlaps, without using the empty word.  The
trace-preserving equal-overlap theorem then supplies the gauge-phase relation,
which is transported back to the original tensors. -/
theorem MPVBlockPhaseEquiv.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
    {DX DY : ℕ} [NeZero DX] [NeZero DY]
    {X : MPSTensor d DX} {Y : MPSTensor d DY}
    (hX : IsNormalTensor X) (hY : IsNormalTensor Y)
    (h : MPVBlockPhaseEquiv X Y) :
    ∃ hdim : DX = DY,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hdim) X) Y := by
  classical
  obtain ⟨σX, _hσX, _hσXfix, hTPX, hGaugeX, hPrimX, hIrrX⟩ := hX.exists_tpGauge
  obtain ⟨σY, _hσY, _hσYfix, hTPY, hGaugeY, hPrimY, hIrrY⟩ := hY.exists_tpGauge
  let X' := tpGauge (d := d) (D := DX) X σX
  let Y' := tpGauge (d := d) (D := DY) Y σY
  have hPhase : MPVBlockPhaseEquiv X' Y' := by
    obtain ⟨ζ, hζ, hmpv⟩ := h
    refine ⟨ζ, hζ, ?_⟩
    intro N hN w
    calc
      mpv Y' w = mpv Y w := (GaugeEquiv.sameMPV hGaugeY N w).symm
      _ = ζ ^ N * mpv X w := hmpv N hN w
      _ = ζ ^ N * mpv X' w := by rw [GaugeEquiv.sameMPV hGaugeX N w]
  have hSelf : Tendsto
      (fun N => mpvOverlap (d := d) X' X' N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      X' hIrrX hTPX hPrimX
  have hSelfY : Tendsto
      (fun N => mpvOverlap (d := d) Y' Y' N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      Y' hIrrY hTPY hPrimY
  have hSelfNorm : Tendsto
      (fun N => ‖mpvOverlap (d := d) X' X' N‖) atTop (nhds (1 : ℝ)) := by
    simpa using hSelf.norm
  have hSelfYNorm : Tendsto
      (fun N => ‖mpvOverlap (d := d) Y' Y' N‖) atTop (nhds (1 : ℝ)) := by
    simpa using hSelfY.norm
  have hζ : ‖hPhase.choose‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale_pos hSelfNorm hSelfYNorm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul_pos hPhase.choose_spec.2)
  have hCrossEq : ∀ N, 0 < N →
      mpvOverlap (d := d) X' Y' N =
        (star hPhase.choose) ^ N * mpvOverlap (d := d) X' X' N :=
    mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul_pos hPhase.choose_spec.2
  have hCrossNormEq : ∀ N, 0 < N →
      ‖mpvOverlap (d := d) X' Y' N‖ = ‖mpvOverlap (d := d) X' X' N‖ := by
    intro N hN
    rw [hCrossEq N hN, norm_mul, norm_pow]
    calc
      ‖star hPhase.choose‖ ^ N * ‖mpvOverlap (d := d) X' X' N‖ =
          ‖hPhase.choose‖ ^ N * ‖mpvOverlap (d := d) X' X' N‖ := by
            rw [norm_star]
      _ = ‖mpvOverlap (d := d) X' X' N‖ := by rw [hζ, one_pow, one_mul]
  have hCrossNorm : Tendsto
      (fun N => ‖mpvOverlap (d := d) X' Y' N‖) atTop (nhds (1 : ℝ)) :=
    hSelfNorm.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hCrossNormEq N hN).symm)
  have hdim : DX = DY :=
    dim_eq_of_mpvOverlap_norm_tendsto_one_of_irreducible_TP
      X' Y' hIrrX hIrrY hTPX hTPY hCrossNorm
  subst DY
  have hGaugePhase : GaugePhaseEquiv X' Y' :=
    gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP
      X' Y' hIrrX hIrrY hTPX hTPY hCrossNorm
  refine ⟨rfl, ?_⟩
  exact gaugePhaseEquiv_of_gaugeEquiv_left_right hGaugeX hGaugePhase hGaugeY

/-- Eventual linear independence excludes gauge-phase-equivalent duplicate
members of a basis of normal tensors.

This is condition (ii) in the characterization of arXiv:1606.00608,
Proposition 2.7 (`prop:char-BNT`, lines 278--280 and 1137--1142). -/
theorem IsCPSVBasisOfNormalTensors.blocks_not_gaugePhaseEquiv
    {g : ℕ} {dim : Fin g → ℕ}
    {A : MPSTensor d D} {B : (j : Fin g) → MPSTensor d (dim j)}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    BlocksNotGaugePhaseEquiv (d := d) B := by
  intro j k hjk hdim hGPE
  obtain ⟨N₀, hLI⟩ := hBNT.eventually_li
  have hN := hLI (N₀ + 1) (by omega)
  obtain ⟨X, ζ, _hζ, hConj⟩ := hGPE
  have hState : ζ ^ (N₀ + 1) • mpvState (d := d) (B j) (N₀ + 1) =
      mpvState (d := d) (B k) (N₀ + 1) := by
    apply PiLp.ext
    intro σ
    simp only [PiLp.smul_apply, mpvState_apply, smul_eq_mul]
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (MPSTensor d) hdim) (B j))
      (B := B k) X ζ hConj (N₀ + 1) σ,
      mpv_cast_dim hdim (B j) (N₀ + 1) σ]
  have hPair : LinearIndepOn ℂ
      (fun l : Fin g => mpvState (d := d) (B l) (N₀ + 1)) {j, k} :=
    hN.linearIndepOn {j, k}
  have hNot := (linearIndepOn_pair_iff _ hjk (hN.ne_zero j)).mp hPair
  exact hNot (ζ ^ (N₀ + 1)) hState

/-- A finite gauge-phase-separated family of normal tensors is eventually
linearly independent at the level of matrix product vectors.

This is the corollary to Lemma `equalMPS` at arXiv:1606.00608, lines
1121--1132.  The proof puts each tensor into its trace-preserving Perron gauge,
applies the overlap orthogonality criterion there, and uses gauge invariance of
the matrix product vectors. -/
theorem exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hNormal : ∀ k, IsNormalTensor (A k))
    (hDistinct : BlocksNotGaugePhaseEquiv (d := d) A) :
    ∃ N₀ : ℕ, ∀ N > N₀,
      LinearIndependent ℂ (fun k : Fin r => mpvState (d := d) (A k) N) := by
  classical
  choose σ hσ hσfix hTP hGauge hPrim hIrr using
    fun k => (hNormal k).exists_tpGauge
  let prepared : (k : Fin r) → MPSTensor d (dim k) :=
    fun k => tpGauge (d := d) (D := dim k) (A k) (σ k)
  have hPreparedDistinct : BlocksNotGaugePhaseEquiv (d := d) prepared := by
    intro j k hjk hdim hGPE
    apply hDistinct j k hjk hdim
    exact gaugePhaseEquiv_of_gaugeEquiv_left_right_cast hdim
      (hGauge j) (by simpa [prepared] using hGPE) (hGauge k)
  obtain ⟨N₀, hLI⟩ :=
    exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal prepared
      (fun k => overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
        (prepared k) (hIrr k) (hTP k) (hPrim k))
      (fun j k hjk =>
        cross_overlap_tendsto_zero_of_separated_normal_bnt_data prepared
          (HasIrreducibleBlocks.ofForall hIrr)
          (IsLeftCanonicalBlockFamily.ofForall hTP)
          hPreparedDistinct j k hjk)
  refine ⟨N₀, fun N hN => ?_⟩
  have hFamily :
      (fun k : Fin r => mpvState (d := d) (prepared k) N) =
        fun k : Fin r => mpvState (d := d) (A k) N := by
    funext k
    ext w
    exact (GaugeEquiv.sameMPV (hGauge k) N w).symm
  rw [← hFamily]
  exact hLI N hN

end MPSTensor
