/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.Definitions
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

* `IsNormalTensor.exists_tpGauge`: a normal tensor admits a pure
  trace-preserving Perron gauge.
* `IsNormalTensor.isNormal`: spectral normality implies eventual block
  injectivity.
* `MPVBlockPhaseEquiv.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor`: exact MPV
  phase equivalence between normal tensors is realized by an invertible gauge.
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

/-- A positive-bond-dimension normal tensor admits a trace-preserving gauge
with no scalar rescaling.

The tensor is normal in the sense of arXiv:1606.00608, lines 231--235: its
transfer map has spectral radius one and unique peripheral eigenvalue one.
The positive-definite left Perron eigenvector consequently has eigenvalue one,
so the usual Perron gauge is a pure similarity of the original tensor. -/
theorem IsNormalTensor.exists_tpGauge [NeZero D]
    {A : MPSTensor d D} (h : IsNormalTensor A) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosDef ∧
      transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ = σ ∧
      IsLeftCanonical (tpGauge (d := d) (D := D) A σ) ∧
      GaugeEquiv A (tpGauge (d := d) (D := D) A σ) ∧
      _root_.IsPrimitive
        (transferMap (d := d) (D := D) (tpGauge (d := d) (D := D) A σ)) ∧
      IsIrreducibleTensor (tpGauge (d := d) (D := D) A σ) := by
  have hA : ∃ i, A i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hmap : transferMap (d := d) (D := D) A = 0 := by
      ext X a b
      simp [transferMap_apply, hzero]
    have hspectral := h.spectral_radius_one
    rw [hmap] at hspectral
    simp at hspectral
  have hIrrMap : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor A h.no_invariant_proj
  obtain ⟨ρ, r, hρ, hr, hρeig⟩ :=
    exists_posDef_transferMap_eigenvector_of_irreducible A h.no_invariant_proj hA
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
    rw [h.spectral_radius_one]
    simp
  have hr_one : r = 1 := hradius.symm.trans hradius_one
  obtain ⟨σ, t, hσ, ht, hσeig⟩ :=
    exists_posDef_adjoint_eigenvector A h.no_invariant_proj hA
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
  have hPrim : _root_.IsPrimitive
      (transferMap (d := d) (D := D) (tpGauge (d := d) (D := D) A σ)) :=
    (isPrimitive_transferMap_tpGauge_iff A σ hσ).2 h.primitive_transfer
  have hIrr : IsIrreducibleTensor (tpGauge (d := d) (D := D) A σ) :=
    isIrreducibleTensor_tpGauge_of_isIrreducibleMap A σ hσ hIrrMap
  exact ⟨σ, hσ, hσfix, hTP, hGauge, hPrim, hIrr⟩

/-- A normal tensor in the spectral sense of arXiv:1606.00608 is eventually
block-injective. -/
theorem IsNormalTensor.isNormal [NeZero D]
    {A : MPSTensor d D} (h : IsNormalTensor A) : IsNormal A := by
  obtain ⟨σ, _hσ, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := h.exists_tpGauge
  have hNormalGauge : IsNormal (tpGauge (d := d) (D := D) A σ) :=
    isNormal_of_tp_primitive_irreducible _ hTP hPrim hIrr
  exact isNormal_of_gaugeEquiv hNormalGauge hGauge.symm

/-- MPV phase equivalence between normal tensors is realized letterwise by a
gauge and a nonzero scalar, after identifying their bond dimensions.

This is the grouping implication in arXiv:1606.00608, Lemma `equalMPS`
(lines 1080--1117) and Proposition `prop:char-BNT` (lines 1135--1148).
Each tensor is first put into its trace-preserving Perron gauge.  The gauges
are pure similarities because both tensors have spectral radius one.  The
trace-preserving equal-overlap theorem supplies the gauge-phase relation, which
is then transported back to the original tensors. -/
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
    intro N w
    calc
      mpv Y' w = mpv Y w := (GaugeEquiv.sameMPV hGaugeY N w).symm
      _ = ζ ^ N * mpv X w := hmpv N w
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
    norm_eq_one_of_selfOverlap_scale hSelfNorm hSelfYNorm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul hPhase.choose_spec.2)
  have hCrossEq : ∀ N,
      mpvOverlap (d := d) X' Y' N =
        (star hPhase.choose) ^ N * mpvOverlap (d := d) X' X' N :=
    mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul hPhase.choose_spec.2
  have hCrossNormEq : ∀ N,
      ‖mpvOverlap (d := d) X' Y' N‖ = ‖mpvOverlap (d := d) X' X' N‖ := by
    intro N
    rw [hCrossEq N, norm_mul, norm_pow]
    calc
      ‖star hPhase.choose‖ ^ N * ‖mpvOverlap (d := d) X' X' N‖ =
          ‖hPhase.choose‖ ^ N * ‖mpvOverlap (d := d) X' X' N‖ := by
            rw [norm_star]
      _ = ‖mpvOverlap (d := d) X' X' N‖ := by rw [hζ, one_pow, one_mul]
  have hCrossNorm : Tendsto
      (fun N => ‖mpvOverlap (d := d) X' Y' N‖) atTop (nhds (1 : ℝ)) :=
    hSelfNorm.congr fun N => (hCrossNormEq N).symm
  have hdim : DX = DY :=
    dim_eq_of_mpvOverlap_norm_tendsto_one_of_irreducible_TP
      X' Y' hIrrX hIrrY hTPX hTPY hCrossNorm
  subst DY
  have hGaugePhase : GaugePhaseEquiv X' Y' :=
    gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP
      X' Y' hIrrX hIrrY hTPX hTPY hCrossNorm
  refine ⟨rfl, ?_⟩
  exact gaugePhaseEquiv_of_gaugeEquiv_left_right hGaugeX hGaugePhase hGaugeY

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
