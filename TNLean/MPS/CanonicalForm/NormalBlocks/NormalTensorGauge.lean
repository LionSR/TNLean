/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Order.ComplexPhasePositivity
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Channel.Irreducible.SpectralRadius
import TNLean.MPS.CanonicalForm.Definitions
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Kraus.Transfer
import TNLean.MPS.Transfer.Irreducible.PerronGauge
import TNLean.MPS.CanonicalForm.BNT.PhaseCover
import TNLean.MPS.CanonicalForm.NormalBlocks.ProjectorClosureSpectral
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalityChain
import TNLean.MPS.CanonicalForm.BNT.Construction
import TNLean.MPS.Transfer.Spectrum.GaugePhase
import QICLean.Channel.Irreducible.KrausGauge
import TNLean.MPS.Tensor.Words.ScaledNormality
import TNLean.MPS.Tensor.Gauge.GaugeUniqueness
import TNLean.MPS.Tensor.GroundSpace.ChainGroundSpace
import TNLean.MPS.Tensor.GroundSpace.ParentHamiltonianBasic
import TNLean.MPS.Transfer.Primitivity.Equivalence
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorTPGauge
import QICLean.Channel.Peripheral.Spectrum.Conjugation

/-!
# Normal tensors: eventual injectivity and separation

This file connects the spectral normal-tensor condition of
Cirac--Pérez-García--Schuch--Verstraete with eventual block injectivity.

The trace-preserving Perron gauge of a normal tensor
(`IsNormalTensor.exists_tpGauge`, in `NormalTensorTPGauge`) is a pure similarity
that keeps peripheral primitivity and irreducibility, so the trace-preserving
primitive normality theorem gives eventual injectivity.  Gauge invariance then
transports eventual injectivity back to the original tensor.

## Main statements

* `IsNormalTensor.isNormal`: spectral normality implies eventual block
  injectivity.
* `isNormalTensor_of_isNormal_leftCanonical`: an algebraically normal
  left-canonical tensor is a spectrally normalized normal tensor.
* `isNormalTensor_of_isIrreducibleFamily_leftCanonical`: an irreducible left-canonical tensor
  whose transfer map has `1` as its only unit-modulus eigenvalue is a normal tensor.
* `MPVBlockPhaseEquiv.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor`: exact MPV
  phase equivalence between normal tensors is realized by an invertible gauge.
* `IsCPSVBasisOfNormalTensors.blocks_not_gaugePhaseEquiv`: distinct members of
  a basis of normal tensors are not gauge-phase equivalent.
* `exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv`:
  a separated finite family of normal tensors is eventually linearly
  independent.
* `MPSTensor.exists_hasComplementaryFixedPointGap_gauge_of_isNormal`: the normalized primitive gauge
  of a normal tensor.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, lines 231--235
  and the proof of Lemma `equalMPS`, lines 1093--1117.
* Wolf, *Quantum Channels & Operations*, Theorem 6.3.

## Common physical blocking for normal tensors

The quantum Wielandt bound gives an injective blocking length depending only
on a bound for the bond dimension. A trace-preserving gauge permits the bound
to be applied to every normalized normal tensor, and injectivity is preserved
by transport through this gauge.

Source context: arXiv:1606.00608, lines 318–344, and quantum Wielandt theory.
-/

open MPTensor

section NormalTensorGauge

section

open scoped Matrix BigOperators ComplexOrder Kraus
open Filter

namespace MPSTensor

variable {d D : ℕ}

/-- A normal tensor in the spectral sense of arXiv:1606.00608 is eventually
block-injective. -/
theorem _root_.MPTensor.IsNormalTensor.isNormal {α : Type*} [Fintype α]
    {A : MPTensor α (Fin D)} (h : IsNormalTensor A) : Kraus.IsNormal A := by
  classical
  let : NeZero D := ⟨h.bondDim_ne_zero⟩
  let e := (Fintype.equivFin α).symm
  obtain ⟨σ, _hσ, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := (h.reindexPhysical e).exists_tpGauge
  have hNormalGauge : Kraus.IsNormal (Kraus.tpGauge (Kraus.reindexPhysical e A) σ) :=
    isNormal_of_tp_primitive_irreducible _ hTP hPrim hIrr
  exact (isNormal_reindexPhysical_equiv e A).1 (isNormal_of_gaugeEquiv hNormalGauge hGauge.symm)

/-- An algebraically normal left-canonical tensor is a spectrally normalized normal tensor.

Algebraic normality and left-canonical normalization imply strong irreducibility by
arXiv:0909.5347, Proposition 3. Thus the transfer map has a positive-definite fixed point and
has no unit-modulus eigenvalue other than one. The spectral normalization of
arXiv:1606.00608, lines 224--235, then has Perron value one and does not rescale the tensor.
This conversion is an input to the BNT identification invoked at arXiv:1606.00608, line 1307.
The physical alphabet is relabelled along `Fintype.equivFin`, where the strong-irreducibility
consequences of normality are stated.
-/
theorem isNormalTensor_of_isNormal_leftCanonical [NeZero D] {α : Type*} [Fintype α]
    (A : MPTensor α (Fin D)) (hNormal : Kraus.IsNormal A) (hLeft : IsLeftCanonical A) :
    IsNormalTensor A := by
  classical
  let e := (Fintype.equivFin α).symm
  suffices h : IsNormalTensor (Kraus.reindexPhysical e A) by
    have hA : Kraus.reindexPhysical e.symm (Kraus.reindexPhysical e A) = A := by
      funext i
      simp [Kraus.reindexPhysical]
    simpa only [hA] using h.reindexPhysical e.symm
  have hNormal' := (isNormal_reindexPhysical_equiv e A).2 hNormal
  have hLeft' : IsLeftCanonical (Kraus.reindexPhysical e A) :=
    (Kraus.isTP_reindexPhysical_iff e A).2 hLeft
  clear hNormal hLeft
  generalize Kraus.reindexPhysical e A = A at hNormal' hLeft' ⊢
  obtain ⟨ρ, hρ, hρfix⟩ := exists_posDef_fixedPoint_of_isNormal A hLeft' hNormal'
  have hPrim : IsPrimitive (Kraus.transferMap A) :=
    isPrimitive_transferMap_of_isNormal A hLeft' hNormal'
  have hIrr : Kraus.IsIrreducibleFamily A := isIrreducibleFamily_of_isNormal A hNormal'
  have huniq : ∀ μ : ℂ, Module.End.HasEigenvalue (Kraus.transferMap A) μ →
      ‖μ‖ = (1 : ℝ) → μ = (1 : ℂ) := by
    intro μ hμ hμnorm
    have hmem : μ ∈ peripheralEigenvalues (Kraus.transferMap A) := ⟨hμ, hμnorm⟩
    rw [hPrim] at hmem
    simpa using hmem
  have hScaled : IsNormalTensor (fun i =>
      (((Real.sqrt (1 : ℝ) : ℝ) : ℂ))⁻¹ • A i) :=
    isNormalTensor_invSqrt_smul_of_unique_peripheral A hIrr ρ 1 hρ (by norm_num)
      (by simpa using hρfix) huniq
  simpa using hScaled

/-- A left-canonical tensor whose letters have no nontrivial common invariant subspace and whose
transfer map has `1` as its only eigenvalue of modulus one is a normal tensor.

This is the definition of normality after arXiv:2307.01696, eq. `eq:transfer_matrix`, in the
left-canonical gauge. The spectral-radius-one field of `IsNormalTensor` is automatic there:
the transfer map of a left-canonical tensor is a channel, so its spectral radius is one
(Wolf Proposition 6.1). -/
theorem isNormalTensor_of_isIrreducibleFamily_leftCanonical {α : Type*} [Fintype α] [NeZero D]
    (A : MPTensor α (Fin D)) (hIrr : Kraus.IsIrreducibleFamily A)
    (hPrim : _root_.IsPrimitive (Kraus.transferMap (ι := α) (n := Fin D) A))
    (hLeft : IsLeftCanonical A) : IsNormalTensor A where
  no_invariant_proj := hIrr
  spectral_radius_one :=
    have hC := Kraus.isChannel_mapLM A hLeft
    hC.pos.spectralRadius_eq_one_of_tracePreserving hC.tp
  primitive_transfer := hPrim

/-- **Normal tensors are the normal families with spectral radius one.**
Definition NT of arXiv:1606.00608 (`Papers/1606.00608/MPDO-22-12-17-2.tex:233-235`) asks
for no nontrivial invariant projection, transfer-map spectral radius one, and `1` as the only
eigenvalue of modulus one. With no further hypothesis this is algebraic normality
(arXiv:0909.5347, property (b), `main.tex:416-421`) together with spectral radius one:
irreducibility follows from normality, and so does the peripheral condition after the
trace-preserving gauge. -/
theorem isNormalTensor_iff_isNormal_and_spectralRadius_eq_one (A : MPSTensor d D) :
    IsNormalTensor A ↔ Kraus.IsNormal A ∧
      spectralRadius ℂ ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap (ι := Fin d) (n := Fin D) A)) = 1 := by
  refine ⟨fun h => ⟨h.isNormal, h.spectral_radius_one⟩, fun ⟨hN, hr⟩ => ?_⟩
  have : NeZero D := ⟨matrix_dim_ne_zero_of_spectralRadius_eq_one _ hr⟩
  obtain ⟨σ, _, _, hLeft, hGauge, _⟩ :=
    exists_tpGauge_of_irreducible_spectralRadius_one (isIrreducibleFamily_of_isNormal A hN) hr
  exact IsNormalTensor.of_gaugeEquiv
    (isNormalTensor_of_isNormal_leftCanonical _ (isNormal_of_gaugeEquiv hN hGauge) hLeft) hGauge
/-- The self-overlap of a normal tensor tends to one.

The trace-preserving Perron gauge is a pure similarity, so it leaves every
matrix product vector unchanged.  The assertion therefore follows from the
primitive trace-preserving overlap limit.  This is the normalization used in
the proof of Lemma `equalMPS` of arXiv:1606.00608, lines 1080--1097.  The physical alphabet is
relabelled along `Fintype.equivFin`, where the trace-preserving overlap limit is stated. -/
theorem _root_.MPTensor.IsNormalTensor.selfOverlap_tendsto_one {α : Type*} [Fintype α]
    {A : MPTensor α (Fin D)} (hA : IsNormalTensor A) :
    Tendsto (fun N => mpvOverlap A A N) atTop (nhds (1 : ℂ)) := by
  classical
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  let e := (Fintype.equivFin α).symm
  obtain ⟨σ, _hσ, _hσfix, hTP, hGauge, hPrim, hIrr⟩ := (hA.reindexPhysical e).exists_tpGauge
  let A' := Kraus.tpGauge (Kraus.reindexPhysical e A) σ
  have hPrepared : Tendsto (fun N => mpvOverlap A' A' N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible A' hIrr hTP hPrim
  apply hPrepared.congr'
  filter_upwards with N
  rw [← mpvOverlap_reindexPhysical_equiv e A A]
  apply Finset.sum_congr rfl
  intro w _
  rw [GaugeEquiv.sameMPV hGauge N w]

/-- Identifying equal bond dimensions does not change normality. -/
theorem isNormalTensor_cast_iff {α : Type*} [Fintype α] {D₁ D₂ : ℕ} (hdim : D₁ = D₂)
    (A : MPTensor α (Fin D₁)) :
    IsNormalTensor (cast (congr_arg (fun n ↦ MPTensor α (Fin n)) hdim) A) ↔
      IsNormalTensor A := by
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
    {α : Type*} [Fintype α] {D₁ D₂ : ℕ}
    {A : MPTensor α (Fin D₁)} {B : MPTensor α (Fin D₂)}
    (hA : IsNormalTensor A) (hB : IsNormalTensor B)
    (hdim : D₁ = D₂) {X : GL (Fin D₂) ℂ} {ζ : ℂ}
    (hrel : ∀ i, B i = ζ • ((X : Matrix (Fin D₂) (Fin D₂) ℂ) *
      (cast (congr_arg (fun n ↦ MPTensor α (Fin n)) hdim) A) i *
      (↑(X⁻¹) : Matrix (Fin D₂) (Fin D₂) ℂ))) :
    ‖ζ‖ = 1 := by
  have : NeZero D₁ := ⟨hA.bondDim_ne_zero⟩
  have : NeZero D₂ := ⟨hB.bondDim_ne_zero⟩
  subst D₂
  have hAA : Tendsto (fun N => ‖mpvOverlap A A N‖)
      atTop (nhds (1 : ℝ)) := by
    simpa using hA.selfOverlap_tendsto_one.norm
  have hBB : Tendsto (fun N => ‖mpvOverlap B B N‖)
      atTop (nhds (1 : ℝ)) := by
    simpa using hB.selfOverlap_tendsto_one.norm
  exact norm_eq_one_of_selfOverlap_scale hAA hBB
    (mpvOverlap_self_scale_of_mpv_eq_pow_mul
      (mpv_eq_pow_mul_of_gaugePhase A B X ζ hrel))

private theorem dim_eq_and_gaugePhaseEquiv_of_isNormalTensor_fin
    {DX DY : ℕ}
    {X : MPSTensor d DX} {Y : MPSTensor d DY}
    (hX : IsNormalTensor X) (hY : IsNormalTensor Y)
    (h : MPVBlockPhaseEquiv X Y) :
    ∃ hdim : DX = DY,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hdim) X) Y := by
  have : NeZero DX := ⟨hX.bondDim_ne_zero⟩
  have : NeZero DY := ⟨hY.bondDim_ne_zero⟩
  classical
  obtain ⟨σX, _hσX, _hσXfix, hTPX, hGaugeX, hPrimX, hIrrX⟩ := hX.exists_tpGauge
  obtain ⟨σY, _hσY, _hσYfix, hTPY, hGaugeY, hPrimY, hIrrY⟩ := hY.exists_tpGauge
  let X' := Kraus.tpGauge (ι := Fin d) (D := DX) X σX
  let Y' := Kraus.tpGauge (ι := Fin d) (D := DY) Y σY
  have hPhase : MPVBlockPhaseEquiv X' Y' := by
    obtain ⟨ζ, hζ, hmpv⟩ := h
    refine ⟨ζ, hζ, ?_⟩
    intro N hN w
    calc
      mpv Y' w = mpv Y w := (GaugeEquiv.sameMPV hGaugeY N w).symm
      _ = ζ ^ N * mpv X w := hmpv N hN w
      _ = ζ ^ N * mpv X' w := by rw [GaugeEquiv.sameMPV hGaugeX N w]
  have hSelf : Tendsto
      (fun N => mpvOverlap (α := Fin d) X' X' N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      X' hIrrX hTPX hPrimX
  have hSelfY : Tendsto
      (fun N => mpvOverlap (α := Fin d) Y' Y' N) atTop (nhds (1 : ℂ)) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      Y' hIrrY hTPY hPrimY
  have hSelfNorm : Tendsto
      (fun N => ‖mpvOverlap (α := Fin d) X' X' N‖) atTop (nhds (1 : ℝ)) := by
    simpa using hSelf.norm
  have hSelfYNorm : Tendsto
      (fun N => ‖mpvOverlap (α := Fin d) Y' Y' N‖) atTop (nhds (1 : ℝ)) := by
    simpa using hSelfY.norm
  have hζ : ‖hPhase.choose‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale_pos hSelfNorm hSelfYNorm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul_pos hPhase.choose_spec.2)
  have hCrossEq : ∀ N, 0 < N →
      mpvOverlap (α := Fin d) X' Y' N =
        (star hPhase.choose) ^ N * mpvOverlap (α := Fin d) X' X' N :=
    mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul_pos hPhase.choose_spec.2
  have hCrossNormEq : ∀ N, 0 < N →
      ‖mpvOverlap (α := Fin d) X' Y' N‖ = ‖mpvOverlap (α := Fin d) X' X' N‖ := by
    intro N hN
    rw [hCrossEq N hN, norm_mul, norm_pow]
    calc
      ‖star hPhase.choose‖ ^ N * ‖mpvOverlap (α := Fin d) X' X' N‖ =
          ‖hPhase.choose‖ ^ N * ‖mpvOverlap (α := Fin d) X' X' N‖ := by
            rw [norm_star]
      _ = ‖mpvOverlap (α := Fin d) X' X' N‖ := by rw [hζ, one_pow, one_mul]
  have hCrossNorm : Tendsto
      (fun N => ‖mpvOverlap (α := Fin d) X' Y' N‖) atTop (nhds (1 : ℝ)) :=
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
    {α : Type*} [Fintype α] {DX DY : ℕ}
    {X : MPTensor α (Fin DX)} {Y : MPTensor α (Fin DY)}
    (hX : IsNormalTensor X) (hY : IsNormalTensor Y)
    (h : MPVBlockPhaseEquiv X Y) :
    ∃ hdim : DX = DY,
      GaugePhaseEquiv
        (cast (congr_arg (fun n ↦ MPTensor α (Fin n)) hdim) X) Y := by
  classical
  -- The proof runs on the `Fin` alphabet obtained by relabelling along `Fintype.equivFin`.
  let e := (Fintype.equivFin α).symm
  obtain ⟨hdim, hG⟩ := dim_eq_and_gaugePhaseEquiv_of_isNormalTensor_fin
    (hX.reindexPhysical e) (hY.reindexPhysical e) (h.reindexPhysical e)
  subst hdim
  exact ⟨rfl, (gaugePhaseEquiv_reindexPhysical_equiv e X Y).1 hG⟩

/-- Eventual linear independence excludes gauge-phase-equivalent duplicate
members of a basis of normal tensors.

This is condition (ii) in the characterization of arXiv:1606.00608,
Proposition 2.7 (`prop:char-BNT`, lines 278--280 and 1137--1142). -/
theorem IsCPSVBasisOfNormalTensors.blocks_not_gaugePhaseEquiv
    {α : Type*} [Fintype α] {g : ℕ} {dim : Fin g → ℕ}
    {A : MPTensor α (Fin D)} {B : (j : Fin g) → MPTensor α (Fin (dim j))}
    (hBNT : IsCPSVBasisOfNormalTensors A (fun j => ⟨dim j, B j⟩)) :
    BlocksNotGaugePhaseEquiv B := by
  intro j k hjk hdim hGPE
  obtain ⟨N₀, hLI⟩ := hBNT.eventually_li
  have hN := hLI (N₀ + 1) (by omega)
  obtain ⟨X, ζ, _hζ, hConj⟩ := hGPE
  have hState : ζ ^ (N₀ + 1) • mpvState (B j) (N₀ + 1) =
      mpvState (B k) (N₀ + 1) := by
    apply PiLp.ext
    intro σ
    simp only [PiLp.smul_apply, mpvState_apply, smul_eq_mul]
    rw [mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congr_arg (fun n ↦ MPTensor α (Fin n)) hdim) (B j))
      (B := B k) X ζ hConj (N₀ + 1) σ,
      mpv_cast_dim hdim (B j) (N₀ + 1) σ]
  have hPair : LinearIndepOn ℂ
      (fun l : Fin g => mpvState (B l) (N₀ + 1)) {j, k} :=
    hN.linearIndepOn {j, k}
  have hNot := (linearIndepOn_pair_iff _ hjk (hN.ne_zero j)).mp hPair
  exact hNot (ζ ^ (N₀ + 1)) hState

/-- A finite gauge-phase-separated family of normal tensors is eventually
linearly independent at the level of matrix product vectors.

This is the corollary to Lemma `equalMPS` at arXiv:1606.00608, lines
1121--1132.  The proof puts each tensor into its trace-preserving Perron gauge,
applies the overlap orthogonality criterion there, and uses gauge invariance of
the matrix product vectors. -/
private theorem exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv_fin
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hNormal : ∀ k, IsNormalTensor (A k))
    (hDistinct : BlocksNotGaugePhaseEquiv (α := Fin d) A) :
    ∃ N₀ : ℕ, ∀ N > N₀,
      LinearIndependent ℂ (fun k : Fin r => mpvState (α := Fin d) (A k) N) := by
  classical
  choose σ hσ hσfix hTP hGauge hPrim hIrr using
    fun k => (hNormal k).exists_tpGauge
  let prepared : (k : Fin r) → MPSTensor d (dim k) :=
    fun k => Kraus.tpGauge (ι := Fin d) (D := dim k) (A k) (σ k)
  have hPreparedDistinct : BlocksNotGaugePhaseEquiv (α := Fin d) prepared := by
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
          hIrr
          hTP
          hPreparedDistinct j k hjk)
  refine ⟨N₀, fun N hN => ?_⟩
  have hFamily :
      (fun k : Fin r => mpvState (α := Fin d) (prepared k) N) =
        fun k : Fin r => mpvState (α := Fin d) (A k) N := by
    funext k
    ext w
    exact (GaugeEquiv.sameMPV (hGauge k) N w).symm
  rw [← hFamily]
  exact hLI N hN

/-- **Eventual linear independence of separated normal blocks**, over any finite physical
alphabet: the statement above, transported along `Fintype.equivFin`. -/
theorem exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv
    {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPTensor α (Fin (dim k)))
    (hNormal : ∀ k, IsNormalTensor (A k))
    (hDistinct : BlocksNotGaugePhaseEquiv A) :
    ∃ N₀ : ℕ, ∀ N > N₀, LinearIndependent ℂ (fun k : Fin r => mpvState (A k) N) := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  obtain ⟨N₀, hLI⟩ :=
    exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv_fin
      (fun k ↦ Kraus.reindexPhysical e (A k)) (fun k ↦ (hNormal k).reindexPhysical e)
      (hDistinct.reindexPhysical e)
  refine ⟨N₀, fun N hN ↦ ?_⟩
  exact linearIndependent_mpvState_of_configEquiv (Equiv.arrowCongr (Equiv.refl _) e.symm) A
    (fun k ↦ Kraus.reindexPhysical e (A k))
    (fun k σ ↦ by rw [mpv_reindexPhysical]; rfl) (hLI N hN)

/-- **Bases of normal tensors of a weighted direct sum.** A finite family of normal tensors is a
basis of normal tensors of the weighted direct sum `⊕_k μ_k A_k` exactly when distinct members
are not gauge-phase equivalent; the weights are arbitrary.

The spanning clause is the block expansion `V^{(N)}(⊕_k μ_k A_k) = ∑_k μ_k^N V^{(N)}(A_k)`;
eventual linear independence is equivalent to gauge-phase separation by the corollary to
Lemma `equalMPS` and by condition (ii) of Proposition 2.7 of arXiv:1606.00608
(`prop:char-BNT`, lines 271--280 and 1121--1142). -/
theorem isCPSVBasisOfNormalTensors_toTensorFromBlocks_iff
    {r : ℕ} {dim : Fin r → ℕ} (μ : Fin r → ℂ)
    {A : (k : Fin r) → MPSTensor d (dim k)} (hNormal : ∀ k, IsNormalTensor (A k)) :
    IsCPSVBasisOfNormalTensors (toTensorFromBlocks μ A) (fun k => ⟨dim k, A k⟩) ↔
      BlocksNotGaugePhaseEquiv (α := Fin d) A := by
  refine ⟨fun h => h.blocks_not_gaugePhaseEquiv, fun hDistinct => ?_⟩
  have : ∀ k, NeZero (dim k) := fun k => ⟨(hNormal k).bondDim_ne_zero⟩
  refine ⟨hNormal, fun N _ => ⟨fun k => μ k ^ N, fun σ => ?_⟩,
    exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv A hNormal
      hDistinct⟩
  simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ A σ

end MPSTensor

end

end NormalTensorGauge

section NormalPrimitiveGauge

/-!
## The normalized primitive gauge of a normal tensor

A normal tensor need not be trace preserving, and its transfer map need not have
spectral radius one.  Both normalizations are taken "without loss of generality"
by the sources: Nachtergaele, arXiv:cond-mat/9410110, rewrites the generalized
valence-bond construction so that equations (3.2a) and (3.2b) hold (lines
1394--1435), and Pérez-García, Verstraete, Wolf, and Cirac, arXiv:quant-ph/0608197,
open the proof of Theorem 4, the translation-invariant canonical form
(statement lines 742--761, proof lines 765--770), by assuming that the spectral
radius of the transfer map is one and gauging by the square root of a positive
fixed point.

This file performs that step. From a normal tensor \(A\) it produces a positive
scalar \(\zeta\), a virtual gauge \(X\), and the rescaled gauged tensor
\(B^i=\zeta\,XA^iX^{-1}\) which carries the trace-preserving normalization
\(\sum_i (B^i)^\dagger B^i=\mathbb 1\) together with a positive definite fixed
point of its transfer map: exactly the data bundled by the complementary
transfer-map gap predicate.  Rescaling and gauging leave the local MPS spaces,
the parent interaction, and the periodic chain ground spaces untouched.

### Main results

* `MPSTensor.exists_hasComplementaryFixedPointGap_gauge_of_isNormal`: the normalized primitive
  gauge of a normal tensor.

### References

* B. Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines
  1394--1435.
* D. Pérez-García, F. Verstraete, M. Wolf, J. I. Cirac, arXiv:quant-ph/0608197,
  Theorem 4, lines 742--770.
* M. Sanz, D. Pérez-García, M. Wolf, J. I. Cirac, arXiv:0909.5347,
  Proposition 3.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **The normalized primitive gauge of a normal tensor.**

For a normal tensor \(A\) there are a nonzero scalar \(\zeta\), a virtual gauge,
and a matrix \(\rho>0\) such that the rescaled gauged tensor \(B\) satisfies
\(\sum_i (B^i)^\dagger B^i=\mathbb 1\) and has \(\rho\) as the distinguished
fixed point of a complementary transfer-map gap.  The matrix product vectors of
\(B\) are those of \(A\) rescaled by \(\zeta^N\), and the local MPS spaces, the
parent interactions, and the periodic chain ground spaces of \(A\) and \(B\)
coincide.

This is the step taken without loss of generality at
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435, and at
arXiv:quant-ph/0608197, Theorem 4, proof lines 765--770: rescale
so that the transfer map has spectral radius one and gauge by the square root of
a positive fixed point.  The gauge here is built from the Perron eigenvector of
the adjoint transfer map, giving the trace-preserving orientation, which is what
conditions 1 and 2 of that theorem (statement lines 752--758) become after the
further gauge by the square root of the matrix \(\Lambda\) appearing in
condition 2.

Normality supplies the irreducibility that the Perron--Frobenius eigenvector
requires, through the direction of arXiv:0909.5347, Proposition 3, that imposes
no normalization on the tensor, and it survives both the rescaling and the
gauge; the trace-preserving representative is therefore normal as well, and the
full equivalence of Proposition 3, which does assume the trace-preserving
normalization, returns the complementary transfer-map gap with a positive
definite fixed point. -/
theorem exists_hasComplementaryFixedPointGap_gauge_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) :
    ∃ (B : MPSTensor d D) (ζ : ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      ζ ≠ 0 ∧
      GaugeEquiv (ζ • A) B ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) ∧
      Kraus.HasComplementaryFixedPointGap B ρ ∧ ρ.PosDef ∧
      (∀ L : ℕ, groundSpace A L = groundSpace B L) ∧
      (∀ L : ℕ, parentInteraction A L = parentInteraction B L) ∧
      (∀ L N : ℕ, chainGroundSpace A L N = chainGroundSpace B L N) := by
  classical
  have hIrr : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) A :=
    isIrreducibleFamily_of_isNormal A hA
  obtain ⟨B, r, σ, _hσ, hr, _hBdef, hBnorm, hBgauge⟩ :=
    exists_tp_data_of_irreducible A hIrr (exists_apply_ne_zero_of_isNormal hA)
  set ζ : ℂ := (↑((Real.sqrt r)⁻¹) : ℂ) with hζ_def
  have hζ : ζ ≠ 0 := by
    have hsqrt : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
    simpa [hζ_def] using inv_ne_zero hsqrt
  have hgauge : GaugeEquiv (ζ • A) B := hBgauge
  have hNormalScaled : Kraus.IsNormal (ζ • A) := (isNormal_smul_iff hζ A).2 hA
  have hNormalB : Kraus.IsNormal B := isNormal_of_gaugeEquiv hNormalScaled hgauge
  obtain ⟨ρ, hPrim, hρ⟩ :=
    exists_hasComplementaryFixedPointGap_posDef_of_isNormal B hBnorm hNormalB
  have hGS : ∀ L : ℕ, groundSpace A L = groundSpace B L := by
    intro L
    rw [← groundSpace_smul_eq A ζ hζ L]
    exact hgauge.groundSpace_eq L
  refine ⟨B, ζ, ρ, hζ, hgauge, ?_, hPrim, hρ, hGS, ?_, ?_⟩
  · intro N τ
    rw [← hgauge.sameMPV N τ]
    simp only [mpv, coeff]
    change Matrix.trace (Kraus.evalWord (fun i => ζ • A i) (List.ofFn τ)) = _
    rw [Kraus.evalWord_smul]
    simp [List.length_ofFn, Matrix.trace_smul]
  · exact fun L => parentInteraction_eq_of_groundSpace_eq (hGS L)
  · exact fun L N => chainGroundSpace_eq_of_groundSpace_eq (hGS L)

/-- A normal tensor of bond dimension \(D>0\) is injective at length
\(D^4\), without assuming a trace-preserving normalization. A nonzero
rescaling and a virtual gauge reduce to the normalized quantum Wielandt
bound, and injectivity is invariant under both operations. Source:
arXiv:0909.5347, Theorem 1; arXiv:1606.00608, line 332. -/
theorem isNBlkInjective_pow_four_of_isNormal [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    Kraus.IsNBlkInjective A (D ^ 4) := by
  obtain ⟨B, ζ, ρ, hζ, hGauge, _hMPV, hP, _hρ, _hGS, _hPI, _hChain⟩ :=
    exists_hasComplementaryFixedPointGap_gauge_of_isNormal hA
  have hNormalB : Kraus.IsNormal B :=
    isNormal_of_gaugeEquiv ((isNormal_smul_iff hζ A).2 hA) hGauge
  have hInjB : Kraus.IsNBlkInjective B (D ^ 4) :=
    isNBlkInjective_pow_four_of_isNormal_leftCanonical B hP.norm hNormalB
  exact (isNBlkInjective_smul_iff hζ A (D ^ 4)).1
    (isNBlkInjective_of_gaugeEquiv hInjB hGauge.symm)

/-- A bound \(K\) on the bond dimension of a normalized normal tensor gives
the common injective length \(K^4\): products of length \(K^4\) span the full
matrix algebra. Source: arXiv:1606.00608, lines 318–344, bounded common
physical blocking; arXiv:0909.5347, Theorem 1. -/
theorem _root_.MPTensor.IsNormalTensor.isNBlkInjective_of_bondDim_le
    {K : ℕ} {A : MPSTensor d D} (hA : IsNormalTensor A) (hDK : D ≤ K) :
    Kraus.IsNBlkInjective A (K ^ 4) := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  exact Kraus.isNBlkInjective_of_le (pow_pos (NeZero.pos D) 4)
    (isNBlkInjective_pow_four_of_isNormal A hA.isNormal) (Nat.pow_le_pow_left hDK 4)

/-- **Normality, four equivalent forms.** For bond dimension `D > 0`, with no
normalization:
1. `Kraus.IsNormal A`: some positive length has full word span (arXiv:0909.5347,
   property (b), `Papers/0909.5347/main.tex:416-421`);
2. all sufficiently long word spans are full;
3. the word span of length `D ^ 4` is full (arXiv:0909.5347, Theorem 1;
   arXiv:1606.00608, line 332);
4. the tensor blocked over some positive number of sites is injective
   (arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex:1815-1830`). -/
theorem normality_tfae [NeZero D] (A : MPSTensor d D) :
    List.TFAE
      [Kraus.IsNormal A,
       ∀ᶠ N in Filter.atTop, Kraus.wordSpan A N = ⊤,
       Kraus.IsNBlkInjective A (D ^ 4),
       ∃ L, 0 < L ∧ Kraus.IsInjective (Kraus.blockTensor A L)] := by
  have hD4 : 0 < D ^ 4 := pow_pos (NeZero.pos D) 4
  tfae_have 1 → 3 := fun h => isNBlkInjective_pow_four_of_isNormal A h
  tfae_have 3 → 2 := fun h =>
    Filter.eventually_atTop.mpr ⟨D ^ 4, fun m hm => Kraus.isNBlkInjective_of_le hD4 h hm⟩
  tfae_have 2 → 1 := fun h => by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
    exact ⟨max N 1, by omega, hN _ (le_max_left _ _)⟩
  tfae_have 1 → 4 := fun ⟨N, hN, h⟩ =>
    ⟨N, hN, (Kraus.isNBlkInjective_iff_blockTensor_isInjective A N).1 h⟩
  tfae_have 4 → 1 := fun ⟨N, hN, h⟩ =>
    ⟨N, hN, (Kraus.isNBlkInjective_iff_blockTensor_isInjective A N).2 h⟩
  tfae_finish

end MPSTensor

end NormalPrimitiveGauge
