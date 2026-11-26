/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ContinuousFamily.CompactMinimalClassStability
import TNLean.MPS.Symmetry.GroundPath.VaryingBondPhysicalCharacter
import TNLean.MPS.Symmetry.GappedPath.PolarVirtualCohomology
import TNLean.MPS.Symmetry.GappedPath.ExactMPSPhaseGaugeInvariance
import TNLean.MPS.Symmetry.ContinuousFamily.StationarySupportedDensityPhaseInvariance
import QICLean.Algebra.Unitary.IsometricFrameEmbedding
import TNLean.MPS.Symmetry.PeriodicRay.PositiveRayVirtualCohomology
import TNLean.MPS.Symmetry.GroundPath.ExactGroundPathWindowClustering
import TNLean.MPS.CanonicalForm.Correlation.FiniteRingCorrelationLimit
import TNLean.MPS.Symmetry.GroundPath.InjectiveTracePreservingGauge

/-!
# Virtual classes of exact ground-state paths under a transfer bound

The finite-chain ground lines determine a common physical character.
After removing this character, injective representatives of the periodic
rays have unitary virtual projective actions. Compactness and a supplied
uniform transfer bound imply local constancy of their classes; connectedness
of the interval then gives one class along the whole path.

Source context: arXiv:1010.3732, Appendix B, lines 2614–2632, and Appendix C,
lines 2653–2717. The uniform transfer bound is an explicit auxiliary
hypothesis. Its derivation from the Hamiltonian gap is separate; see
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

## Virtual class invariance from the actual physical ground-state gap

The physical gap gives ordinary connected clustering, then a common
transfer spectral bound for every unital injective representative of the
periodic rays. The existing compact-limit argument now applies without
its auxiliary transfer-bound premise. The minimal bond dimension may
change along the path; no continuous minimal gauge or virtual action is
chosen. This is the converse obstruction for the exact MPS path domain.

Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953,
Appendix B, lines 2614–2632, and Appendix C, lines 2653–2717.

## Prescribed endpoint classes of an exact physical gapped MPS path

The constant virtual class derived from the physical Hamiltonian gap agrees
with every prescribed virtual action of either endpoint ray. Minimal bond
dimensions, tensor normalizations, bond gauges, and the physical characters
at the two endpoints need not be identified in advance.

Source: arXiv:1010.3732, Section II.F.2, lines 929–993, and Appendix C.

It also contains the following results.

* `MPSTensor.ExactMPSGroundPath.exists_uniform_tracePreserving_transfer_bound`,
  `MPSTensor.ExactMPSGroundPath.exists_uniform_unital_transfer_bound`: a common transfer spectral
  bound from the actual physical gap.
-/

section ExactGroundPathTransferBound

/-!
## A common transfer spectral bound from the actual physical gap

The physical path supplies a common finite-ring correlation rate. Actual
window geometry and equality of the periodic rays transfer it to each
trace-preserving representative. Pointwise primitivity proves the
finite-to-limiting correlation passage, so no common transfer gap or
limiting-correlation bound is assumed. The actual eigenvalue observers
then force the same bound below one on the nonunit transfer spectrum.

The faithful-fixed-point data and trace-preserving gauge are then derived
for every unital injective representative. Gauge invariance of the actual
periodic rays and transfer spectrum removes these auxiliary choices from
the common unital transfer bound.

Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953, and
Hastings–Koma, arXiv:math-ph/0507008, Section 3.
-/

noncomputable section

open Filter
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSTensor

variable {G : Type} [Group G] {d : ℕ}
  {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
  {h₀ h₁ : MPOTensor.ChainOperator d 2}
  {P : SymmetricGappedInteractionPath U h₀ h₁}

/-- The actual physical gap gives a common bound below one on the
nonunit transfer spectrum of every trace-preserving block-injective
representative of the periodic rays with a faithful trace-one fixed
density. Its finite-ring convergence is derived pointwise; no uniform
transfer-gap or correlation conclusion is an extra premise.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_tracePreserving_transfer_bound
    (Q : ExactMPSGroundPath P) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ D : ℕ, ∀ _ : NeZero D,
      ∀ A : MPSTensor d D, SamePositiveMpvRay (Q.tensor γ) A →
      ∀ L : ℕ, 0 < L → Kraus.IsNBlkInjective A L →
      (∑ i, (A i)ᴴ * A i = 1) →
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosDef →
      Kraus.transferMap A ρ = ρ → Matrix.trace ρ = 1 →
      ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ r := by
  obtain ⟨K, κ, hK, hκ, hEst⟩ := Q.exists_uniform_ray_window_correlation_bound
  refine ⟨Real.exp (-κ), Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hκ)
  intro γ hγ D hD A hRay L hL hInj hTP ρ hρ hfix htr z hz hzne
  let : NeZero D := hD
  apply norm_transfer_spectrum_le_of_finite_mpvConnectedCorrelator_bound
    hL hInj hTP hρ hfix htr (Real.exp_pos _) ?_ hz hzne
  intro X Y
  refine ⟨K * ((L : ℝ) + 1) * ‖X‖ * ‖Y‖, 1, fun t ht ↦ ?_⟩
  filter_upwards [eventually_ge_atTop t] with n hn
  have h := hEst γ hγ D A hRay L hL X Y t ht n hn
  simpa only [← Real.exp_nat_mul, mul_comm (t : ℝ) (-κ)] using h

/-- The actual physical gap gives one common bound below one for all
unital injective representatives of its periodic rays. Trace-preserving
normalization, the faithful stationary density, finite-ring convergence
and the spectral comparison are all derived. No transfer-bound or
continuous minimal-gauge choice is assumed.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953. -/
theorem ExactMPSGroundPath.exists_uniform_unital_transfer_bound
    (Q : ExactMPSGroundPath P) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ D : ℕ, 0 < D →
      ∀ A : MPSTensor d D, Kraus.IsInjective A → Kraus.IsUnital A →
      SamePositiveMpvRay (Q.tensor γ) A →
      ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ r := by
  obtain ⟨r, hr, hrOne, hEst⟩ := Q.exists_uniform_tracePreserving_transfer_bound
  refine ⟨r, hr, hrOne, ?_⟩
  intro γ hγ D hD A hA hUnital hRay z hz hzne
  let : NeZero D := ⟨hD.ne'⟩
  obtain ⟨B, ρ, _, hB, hTP, hρ, hfix, htr, hAB, hSpec⟩ :=
    exists_tpGauge_of_isInjective_unital hA hUnital
  rw [hSpec] at hz
  exact hEst γ hγ D inferInstance B (hRay.trans hAB) 1 zero_lt_one
    (Kraus.isNBlkInjective_one_of_isInjective hB) hTP ρ hρ hfix htr z hz hzne

end MPSTensor

end

end ExactGroundPathTransferBound

section ExactGroundPathTransferClass

section

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.Frobenius Topology ScalarCohomology
open Filter TNLean.Algebra ScalarCohomology

namespace MPSTensor

private theorem isOnSiteSymmetric_of_samePositiveMpvRay
    {G : Type} [Group G] {d D E : ℕ} {A : MPSTensor d D} {B : MPSTensor d E}
    (hRay : SamePositiveMpvRay A B)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (hA : IsOnSiteSymmetric A U) :
    IsOnSiteSymmetric B U := by
  intro g N s
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [mpv, coeff]
  · simpa only [one_mul] using (hRay.symmetry_eigenvalue U g 1 hN
      (fun s => by simpa only [one_mul] using (hA g N s).symm) s).symm

private theorem exists_unitary_projective_covariance_of_unital_symmetry
    {G : Type} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hAU : Kraus.IsUnital A)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)) :
    ∃ ω : ScalarCocycle G, ∃ ρ : ProjectiveRepresentation (D := D) ω,
      (∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      ∀ g, rotatePhysical (U g) A = fun i =>
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
          (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨ω, ρ, hρ, hCov⟩ := exists_unitary_virtualRep_polarDeformation
    A hA (Kraus.map_one_of_isUnital A hAU) U hSym
  refine ⟨ω, ρ, hρ, ?_⟩
  intro g
  funext i
  have h := hCov 1 g i
  simp only [polarDeformation_one] at h
  rw [Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hρ _)] at h
  exact h

/-- A continuous exact ground-state path has one virtual cohomology class
under a supplied uniform bound below one on the nonunit transfer spectra
of its unital injective representatives. The common physical character,
representatives, and unitary virtual actions are derived. Source context:
arXiv:1010.3732, Appendix B, lines 2614–2632, and Appendix C, lines 2653–2717.
This is a transfer-bound conditional result, not a Hamiltonian-gap theorem. -/
theorem ExactMPSGroundPath.exists_constant_virtual_class_of_uniform_transfer_bound
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hTransfer : ∀ t : unitInterval, ∀ D : ℕ, 0 < D → ∀ A : MPSTensor d D,
      Kraus.IsInjective A → Kraus.IsUnital A → SamePositiveMpvRay (Q.tensor t) A →
      ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q) :
    ∃ χ : G →* ℂ, ∃ hχ : ∀ g, ‖χ g‖ = 1,
    ∃ D : unitInterval → ℕ, ∃ A : ∀ t, MPSTensor d (D t),
    ∃ ω : unitInterval → ScalarCocycle G,
    ∃ ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t),
    ∃ hω : ∀ t, groupCohomology.IsMulCocycle₂ (ω t),
      (∀ t, 0 < D t ∧ D t ≤ Q.bondDimension) ∧
      (∀ t, Kraus.IsInjective (A t) ∧ Kraus.IsUnital (A t)) ∧
      (∀ t : unitInterval, SamePositiveMpvRay (Q.tensor t) (A t)) ∧
      (∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
        Matrix.unitaryGroup _ ℂ) ∧
      (∀ t g, rotatePhysical (physicalCharacterUntwist χ hχ U g) (A t) = fun i =>
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
          ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ) ∧
      ∀ s t, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
          (groupCohomology.cocyclesOfIsMulCocycle₂ (hω t)) =
        groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
          (groupCohomology.cocyclesOfIsMulCocycle₂ (hω s)) := by
  classical
  obtain ⟨χ, hχ, hSym⟩ := Q.exists_exact_symmetry
  let V := physicalCharacterUntwist χ hχ U
  have hData : ∀ t : unitInterval, ∃ D : ℕ, 0 < D ∧ D ≤ Q.bondDimension ∧
      ∃ A : MPSTensor d D, Kraus.IsInjective A ∧ Kraus.IsUnital A ∧
        SamePositiveMpvRay (Q.tensor t) A := by
    intro t
    obtain ⟨D, hD, hBound, A, hA, hRay⟩ := Q.injective_representative t t.property
    let : NeZero D := ⟨hD.ne'⟩
    obtain ⟨B, c, hc, hGauge, hB, hBU, _⟩ :=
      exists_unital_parent_representative_of_isInjective A hA
    refine ⟨D, hD, hBound, B, hB, ?_,
      hRay.trans (samePositiveMpvRay_of_smul_gaugeEquiv c hc hGauge)⟩
    change ∑ i, B i * (B i)ᴴ = 1
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using hBU
  choose D hD hBound A hA hAU hRay using hData
  have hVirtual : ∀ t, ∃ ω : ScalarCocycle G,
      ∃ ρ : ProjectiveRepresentation (D := D t) ω,
        (∀ g, (ρ.X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
          Matrix.unitaryGroup _ ℂ) ∧
        ∀ g, rotatePhysical (V g) (A t) = fun i =>
          (ρ.X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
            (ρ.X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ := by
    intro t
    let : NeZero (D t) := ⟨(hD t).ne'⟩
    exact exists_unitary_projective_covariance_of_unital_symmetry (A t) (hA t) (hAU t)
      V (isOnSiteSymmetric_of_samePositiveMpvRay (hRay t) _ (hSym t))
  choose ω ρ hρ hCov using hVirtual
  let hω : ∀ t, groupCohomology.IsMulCocycle₂ (ω t) :=
    fun t ↦ ScalarCocycle.isMulCocycle₂_of_projRep (ρ t) (hD t)
  refine ⟨χ, hχ, D, A, ω, ρ, hω, fun t => ⟨hD t, hBound t⟩,
    fun t => ⟨hA t, hAU t⟩, hRay, hρ, hCov, ?_⟩
  intro s t
  apply (H2π_eq_iff_isMulCoboundary₂_div (hω t) (hω s)).mpr
  refine isMulCoboundary₂_div_of_eventually_at_all_points ω ?_ t s
  intro t₀
  have hQ : Continuous (fun t : unitInterval => Q.tensor t) := Q.continuous.domRestrict
  apply (eventually_H2π_eq_iff_isMulCoboundary₂_div _ _).mp
  exact eventually_cohomologousTo_of_continuousAt_bounded_unital_periodic_rays
    D hD hBound A
    (fun t => Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM (A t)
      (Kraus.injective_implies_irreducibleCP (A t) (hA t))) hAU t₀ (hA t₀)
    (fun t => Q.tensor t) hQ.continuousAt hRay q hq hqOne
    (fun t => hTransfer t (D t) (hD t) (A t) (hA t) (hAU t) (hRay t))
    V ω ρ hρ hCov

end MPSTensor

end

section

noncomputable section

open scoped Matrix ScalarCohomology
open TNLean.Algebra

namespace MPSTensor

/-- An exact physical gapped MPS path has a common virtual cohomology
class, including when its minimal injective bond dimension changes.
The common physical character, injective unital representatives and
unitary virtual actions are derived. There is no transfer-bound,
clustering, limiting-correlation or continuous minimal-gauge premise.
Source: SPC11, arXiv:1010.3732, Section II.F, lines 929–953,
Appendix B, lines 2614–2632, and Appendix C, lines 2653–2717. -/
theorem ExactMPSGroundPath.exists_constant_virtual_class
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P) :
    ∃ χ : G →* ℂ, ∃ hχ : ∀ g, ‖χ g‖ = 1,
    ∃ D : unitInterval → ℕ, ∃ A : ∀ t, MPSTensor d (D t),
    ∃ ω : unitInterval → ScalarCocycle G,
    ∃ ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t),
    ∃ hω : ∀ t, groupCohomology.IsMulCocycle₂ (ω t),
      (∀ t, 0 < D t ∧ D t ≤ Q.bondDimension) ∧
      (∀ t, Kraus.IsInjective (A t) ∧ Kraus.IsUnital (A t)) ∧
      (∀ t : unitInterval, SamePositiveMpvRay (Q.tensor t) (A t)) ∧
      (∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
        Matrix.unitaryGroup _ ℂ) ∧
      (∀ t g, rotatePhysical (physicalCharacterUntwist χ hχ U g) (A t) = fun i ↦
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
          ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ) ∧
      ∀ s t, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
          (groupCohomology.cocyclesOfIsMulCocycle₂ (hω t)) =
        groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
          (groupCohomology.cocyclesOfIsMulCocycle₂ (hω s)) := by
  obtain ⟨r, hr, hrOne, hTransfer⟩ := Q.exists_uniform_unital_transfer_bound
  apply Q.exists_constant_virtual_class_of_uniform_transfer_bound r hr.le hrOne
  intro t D hD A hA hUnital hRay z hz hzne
  exact hTransfer t t.property D hD A hA hUnital hRay z hz hzne

end MPSTensor
end

end

section

open scoped Matrix ScalarCohomology
open TNLean.Algebra

namespace MPSTensor

/-- A physical gapped path in the exact MPS regime identifies the classes
of prescribed injective endpoint representations. Both endpoint character
changes are permitted independently. Their compatibility with the path is
derived from periodic ray equality. Source: arXiv:1010.3732, Section II.F.2
and Appendix C; physical character changes are allowed in Section II.C.2. -/
theorem ExactMPSGroundPath.cohomologousTo_endpoints
    {G : Type} [Group G] {d D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    {A₀ : MPSTensor d D₀} {A₁ : MPSTensor d D₁}
    (hA₀ : Kraus.IsInjective A₀) (hA₁ : Kraus.IsInjective A₁)
    (hRay₀ : SamePositiveMpvRay (Q.tensor 0) A₀)
    (hRay₁ : SamePositiveMpvRay (Q.tensor 1) A₁)
    (χ₀ χ₁ : G →* ℂ) (hχ₀ : ∀ g, ‖χ₀ g‖ = 1) (hχ₁ : ∀ g, ‖χ₁ g‖ = 1)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (hρ₀ : ∀ g i, twistedTensor A₀ ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₀ hχ₀ U)) g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D₀) (Fin D₀) ℂ) * A₀ i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D₀) ℂ) : Matrix (Fin D₀) (Fin D₀) ℂ))
    (hρ₁ : ∀ g i, twistedTensor A₁ ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ₁ hχ₁ U)) g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D₁) (Fin D₁) ℂ) * A₁ i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D₁) ℂ) : Matrix (Fin D₁) (Fin D₁) ℂ)) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₁ (NeZero.pos D₁))) =
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂
      (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀ (NeZero.pos D₀))) := by
  obtain ⟨χ, hχ, D, A, ω, ρ, hω, hD, hA, hRay, hUnitary, hCov, hClass⟩ :=
    Q.exists_constant_virtual_class
  have : NeZero (D 0) := ⟨(hD 0).1.ne'⟩
  have : NeZero (D 1) := ⟨(hD 1).1.ne'⟩
  have hInvCov : ∀ (t : unitInterval) g i,
      twistedTensor (A t) ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
        (physicalCharacterUntwist χ hχ U)) g i =
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((((ρ t).X (g⁻¹))⁻¹ : GL (Fin (D t)) ℂ) :
          Matrix (Fin (D t)) (Fin (D t)) ℂ) := by
    intro t g i
    rw [Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hUnitary t g⁻¹)]
    exact congrFun (hCov t g) i
  have hEnd₀ := cohomologousTo_of_samePositiveMpvRay_character_covariance
    hA₀ (hA 0).1 (hRay₀.symm.trans (hRay 0)) U χ₀ χ hχ₀ hχ
    ρ₀ (ρ 0) hρ₀ (hInvCov 0)
  have hEnd₁ := cohomologousTo_of_samePositiveMpvRay_character_covariance
    hA₁ (hA 1).1 (hRay₁.symm.trans (hRay 1)) U χ₁ χ hχ₁ hχ
    ρ₁ (ρ 1) hρ₁ (hInvCov 1)
  exact hEnd₁.symm.trans ((hClass 0 1).trans hEnd₀)

end MPSTensor

end

end ExactGroundPathTransferClass
