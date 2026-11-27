/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Periodic.Overlap.FixedLineLimitSimplicity
import TNLean.MPS.Symmetry.PeriodicRay.MpvRayLimit
import TNLean.MPS.Symmetry.ContinuousFamily.ContinuousStationaryDensity
import TNLean.MPS.Symmetry.OnSite.BlockingVirtualCovariance
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.Tensor.Physical.BlockingTransfer
import TNLean.MPS.FundamentalTheorem.InjectivePhase
import QICLean.Algebra.Hermitian.OrthogonalProjection
import QICLean.Channel.FixedPoint.Algebra.Algebra
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import TNLean.MPS.Symmetry.ContinuousFamily.StationarySupportedDensityPhaseInvariance
import TNLean.MPS.Symmetry.ContinuousFamily.SupportPeriodicDecomposition
import TNLean.MPS.Symmetry.OnSite.CompactSupportVirtualTransport
import TNLean.MPS.Symmetry.OnSite.UnitaryVirtualGauge
import TNLean.MPS.CanonicalForm.Periodic.Overlap.PeriodicRayUnitOverlap
import Mathlib.Topology.Compactification.OnePoint.Basic
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import TNLean.MPS.Tensor.Defs
import QICLean.Channel.Schwarz.Basic
import QICLean.Channel.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Compactness and virtual class stability for periodic-ray sequences

The tensors realizing the periodic rays are chosen pointwise and need not
converge. Compactness supplies a convergent subsequence in fixed dimensions.
A supplied uniform bound on their nonunit transfer spectra prevents an
additional fixed line from appearing in the limit. Its stationary support
then identifies the limiting minimal tensor with the injective reference.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. The uniform
transfer bound and exact unitary virtual covariance are explicit auxiliary
hypotheses. No physical-gap conclusion is asserted here.

It also contains the following results.

* `MPSTensor.eventually_cohomologousTo_of_tendsto_unital_periodic_lines`: virtual class stability
  along a convergent unital sequence.
* `MPSTensor.isCompact_setOf_isUnital`, `MPSTensor.exists_subsequence_unital_stationary_limit`:
  compactness of unital tensors and stationary densities.
-/

open MPTensor

section CompactSupportedSequenceClass

/-!
## Virtual class stability along a convergent unital sequence

The one-point compactification of the natural numbers turns a convergent
sequence of ambient tensors into a continuous family. At the finite points,
the stationary support may be the entire bond space; at infinity it may have
smaller dimension. The supported-family theorem requires no convergence of
virtual representatives or support frames.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. The transfer
spectral bound remains an explicit hypothesis in the eventual application.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder Topology OnePoint
open Filter TNLean.Algebra

open scoped ScalarCohomology

namespace MPSTensor

private theorem eventually_class_of_unital_sequence_supported_limit
    {G : Type} [Group G] {d k E : ℕ}
    (B : ℕ → MPSTensor d k) (b : MPSTensor d k)
    (hB : Tendsto B atTop (𝓝 b)) (hUnital : ∀ n, Kraus.IsUnital (B n))
    (hbUnital : Kraus.IsUnital b)
    (σ : ℕ → Matrix (Fin k) (Fin k) ℂ) (hσ : ∀ n, (σ n).PosDef)
    (hTrace : ∀ n, (σ n).trace = 1)
    (hFix : ∀ n, Kraus.adjointMap (B n) (σ n) = σ n)
    (τ : Matrix (Fin k) (Fin k) ℂ) (hτ : τ.PosSemidef)
    (hτTrace : τ.trace = 1) (hτFix : Kraus.adjointMap b τ = τ)
    (K : Matrix (Fin k) (Fin E) ℂ) (hK : K.IsIsometry)
    (hSupport : K * Kᴴ = hτ.supportProj)
    (C : MPSTensor d E) (hC : ∀ i, C i = Kᴴ * b i * K)
    (hCInj : Kraus.IsInjective C)
    (hDim : Module.finrank ℂ (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM b)) = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ω : ℕ → ScalarCocycle G) (ω₀ : ScalarCocycle G)
    (ρ : ∀ n, ProjectiveRepresentation (D := k) (ω n))
    (ρ₀ : ProjectiveRepresentation (D := E) ω₀)
    (hρ : ∀ n g, ((ρ n).X g : Matrix (Fin k) (Fin k) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hρ₀ : ∀ g, (ρ₀.X g : Matrix (Fin E) (Fin E) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ n g, rotatePhysical (U g) (B n) = fun i =>
      ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ) * B n i *
        ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ)ᴴ)
    (hCov₀ : ∀ g, rotatePhysical (U g) C = fun i =>
      (ρ₀.X (g⁻¹) : Matrix (Fin E) (Fin E) ℂ) * C i *
        (ρ₀.X (g⁻¹) : Matrix (Fin E) (Fin E) ℂ)ᴴ) :
    ∀ᶠ n in atTop, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ n) (by
            apply Nat.pos_of_ne_zero
            intro hk
            subst k
            simp only [Matrix.trace_fin_zero, zero_ne_one] at hτTrace))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep ρ₀
            (Matrix.supportFrame_dimension_pos_of_trace_one K τ hτ hSupport hτTrace))) := by
  let ambient := OnePoint.continuousMapMkNat B b hB
  let dim : OnePoint ℕ → ℕ := OnePoint.rec E (fun _ => k)
  let factor : OnePoint ℕ → ScalarCocycle G := OnePoint.rec ω₀ ω
  let action : ∀ t, ProjectiveRepresentation (D := dim t) (factor t) :=
    OnePoint.rec ρ₀ ρ
  let density : OnePoint ℕ → Matrix (Fin k) (Fin k) ℂ := OnePoint.rec τ σ
  let frame : ∀ t : OnePoint ℕ, Matrix (Fin k) (Fin (dim t)) ℂ :=
    OnePoint.rec K (fun _ => (1 : Matrix (Fin k) (Fin k) ℂ))
  let tensor : ∀ t, MPSTensor d (dim t) := OnePoint.rec C B
  have hClass := eventually_cohomologousTo_of_continuousAt_unital_supported_family
    dim factor action ambient ∞ ambient.continuous.continuousAt
    (OnePoint.rec hbUnital hUnital) density
    (OnePoint.rec hτ (fun n => (hσ n).posSemidef))
    (OnePoint.rec hτTrace hTrace) (OnePoint.rec hτFix hFix) frame
    (OnePoint.rec hK (fun _ => by
      change (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ *
        (1 : Matrix (Fin k) (Fin k) ℂ) = (1 : Matrix (Fin k) (Fin k) ℂ)
      simp only [Matrix.conjTranspose_one, Matrix.one_mul]))
    (OnePoint.rec hSupport (fun n => by
      change (1 : Matrix (Fin k) (Fin k) ℂ) *
        (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ = (hσ n).posSemidef.supportProj
      rw [Matrix.conjTranspose_one, Matrix.one_mul, (hσ n).supportProj_eq_one]))
    tensor (OnePoint.rec hC (fun n i => by
      change B n i = (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ * B n i *
        (1 : Matrix (Fin k) (Fin k) ℂ)
      simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]))
    (OnePoint.rec hρ₀ hρ) U (OnePoint.rec hCov₀ hCov) hDim hCInj
  have hTendsto : Tendsto ((↑) : ℕ → OnePoint ℕ) atTop (𝓝 ∞) := by
    simpa only [coclosedCompact_eq_cocompact, cocompact_eq_cofinite,
      Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))
  exact hTendsto.eventually hClass

/-- A convergent sequence of unital tensors eventually has the base virtual class
when its limiting periodic lines agree eventually with those of a unital
injective reference. The limiting transfer spectral bound is supplied. The
normality and the limiting virtual action are derived inside the argument;
no continuity of virtual representatives is assumed. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem eventually_cohomologousTo_of_tendsto_unital_periodic_lines
    {G : Type} [Group G] {d D k E : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hAU : Kraus.IsUnital A)
    (B : ℕ → MPSTensor d k) (b : MPSTensor d k)
    (hB : Tendsto B atTop (𝓝 b)) (hBU : ∀ n, Kraus.IsUnital (B n))
    (hbU : Kraus.IsUnital b)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap b) 1) = 1)
    (σ : ℕ → Matrix (Fin k) (Fin k) ℂ) (hσ : ∀ n, (σ n).PosDef)
    (hσTrace : ∀ n, (σ n).trace = 1)
    (hσFix : ∀ n, Kraus.adjointMap (B n) (σ n) = σ n)
    (τ : Matrix (Fin k) (Fin k) ℂ) (hτ : τ.PosSemidef)
    (hτTrace : τ.trace = 1) (hτFix : Kraus.adjointMap b τ = τ)
    (K : Matrix (Fin k) (Fin E) ℂ) (hK : K.IsIsometry)
    (hSupport : K * Kᴴ = hτ.supportProj)
    (C : MPSTensor d E) (hC : ∀ i, C i = Kᴴ * b i * K)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hSpecA : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q)
    (hSpecb : ∀ z ∈ spectrum ℂ (Kraus.transferMap b), z ≠ 1 → ‖z‖ ≤ q)
    (hSpan : ∀ᶠ N in atTop,
      Submodule.span ℂ {(mpv A : (Fin N → Fin d) → ℂ)} =
        Submodule.span ℂ {(mpv b : (Fin N → Fin d) → ℂ)})
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ω : ℕ → ScalarCocycle G) (ω₀ : ScalarCocycle G)
    (ρ : ∀ n, ProjectiveRepresentation (D := k) (ω n))
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (hρ : ∀ n g, ((ρ n).X g : Matrix (Fin k) (Fin k) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hρ₀ : ∀ g, (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ n g, rotatePhysical (U g) (B n) = fun i =>
      ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ) * B n i *
        ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ)ᴴ)
    (hCov₀ : ∀ g, rotatePhysical (U g) A = fun i =>
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    ∀ᶠ n in atTop, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ n) (by
            apply Nat.pos_of_ne_zero
            intro hk
            subst k
            simp only [Matrix.trace_fin_zero, zero_ne_one] at hτTrace))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ₀) (NeZero.pos D))) := by
  have hk : k ≠ 0 := by
    intro hzero
    subst k
    simp only [Matrix.trace_fin_zero, zero_ne_one] at hτTrace
  let : NeZero k := ⟨hk⟩
  have hAirr := Kraus.injective_implies_irreducibleCP A hA
  have hAdim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1 :=
    finrank_eigenspace_eq_one_of_irreducible_positive
      (Kraus.mapLM A) (Kraus.isPositiveMap_mapLM A) hAirr (r := 1) zero_le_one
      Matrix.PosDef.one (by simpa only [Kraus.mapLM_apply, Complex.ofReal_one, one_smul]
        using Kraus.map_one_of_isUnital A hAU)
  have hAnorm := norm_mpvState_tendsto_one_of_transfer_spectrum
    A hAU hAdim q hq hqOne hSpecA
  have hbnorm := norm_mpvState_tendsto_one_of_transfer_spectrum
    b hbU hDim q hq hqOne hSpecb
  have hBound : ∀ᶠ N in atTop, ‖mpvState A N‖ ≤ (2 : ℝ) :=
    ((tendsto_order.mp hAnorm).2 2 (by norm_num)).mono fun _ h => h.le
  have hOverlap := norm_mpvOverlap_tendsto_one_of_eventual_span_eq A b hSpan hAnorm hbnorm
  obtain ⟨Λ, hΛ, hΛfix⟩ := exists_posDef_adjoint_fixedPoint_of_isInjective_unital
    hA (Kraus.map_one_of_isUnital A hAU)
  have hΛfix' : Kraus.adjointMap A Λ = Λ := by
    simpa only [Kraus.transferMap, Kraus.mapLM_apply, Kraus.map_apply,
      Matrix.conjTranspose_conjTranspose, Kraus.adjointMap_apply] using hΛfix
  obtain ⟨_, hEq, hGauge⟩ := exists_dim_eq_gaugePhase_of_unital_stationary_support_overlap
    A b C (Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A hAirr)
    Λ hΛ hΛfix' hbU hDim τ hτ hτFix hτTrace K hK hSupport hC
    q hq hqOne hSpecb 2 hBound hOverlap
  subst E
  have hGauge' : GaugePhaseEquiv A C := by simpa using hGauge
  have hUniq := normalized_adjoint_fixed_unique_of_transfer_fixed_finrank_one
    b hDim τ hτFix hτTrace
  have hCU := (prepare_stationary_support_compression
    b C K hK hC hbU τ hτ hSupport hτFix hτTrace hUniq).1
  obtain ⟨ρLimit, hρLimit, hCovLimit⟩ := exists_unitary_virtualRep_of_unital_gaugePhaseEquiv
    hA hAU hCU hGauge' U ρ₀ hρ₀ hCov₀
  obtain ⟨X, c, hc, hX⟩ := hGauge'
  have hCInj : Kraus.IsInjective C := isInjective_of_gaugeEquiv (hA.smul hc)
    ⟨X, fun i => by simpa only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul] using hX i⟩
  exact eventually_class_of_unital_sequence_supported_limit
    B b hB hBU hbU σ hσ hσTrace hσFix τ hτ hτTrace hτFix K hK hSupport C hC hCInj
    ((finrank_adjointFixedSpace_eq_transferFixedSpace b).trans hDim)
    U ω ω₀ ρ ρLimit hρ hρLimit hCov hCovLimit

end MPSTensor

end CompactSupportedSequenceClass

section CompactUnitalTensors

/-!
## Compactness of unital tensors and stationary densities

In fixed physical and bond dimensions, each entry of a unital tensor has
modulus at most one. Unitality is a closed condition, so these tensors form
a compact set. Pairing this set with the compact set of density matrices
gives a common convergent subsequence of tensors and stationary densities.
Stationarity passes to the limit by continuity. The limiting density is
allowed to have smaller rank.

These are finite-dimensional compactness results for the exact MPS families
of arXiv:1010.3732, Section II.F.2 and Appendix C, lines 2653–2717. They do not
identify the limiting stationary support with a prescribed minimal tensor.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix

private theorem norm_entry_le_one_of_isUnital {d D : ℕ}
    (A : MPSTensor d D) (hA : Kraus.IsUnital A) (i : Fin d) (a b : Fin D) :
    ‖A i a b‖ ≤ 1 := by
  have hdiag := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => (M a a).re) hA
  have hsum : ∑ j : Fin d, ∑ c : Fin D, ‖A j a c‖ ^ 2 = 1 := by
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      map_sum, Complex.mul_re, Complex.norm_mul_self_eq_normSq,
      Complex.normSq_apply, pow_two] using hdiag
  have hle : ‖A i a b‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    apply (Finset.single_le_sum (fun c _ => sq_nonneg ‖A i a c‖)
      (Finset.mem_univ b)).trans
    exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg
      (fun c _ => sq_nonneg ‖A j a c‖)) (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i a b)]

/-- In fixed physical and bond dimensions the unital tensors form a compact
set, irrespective of injectivity or the rank of a stationary density. -/
theorem MPSTensor.isCompact_setOf_isUnital (d D : ℕ) :
    IsCompact {A : MPSTensor d D | Kraus.IsUnital A} := by
  have hclosed : IsClosed {A : MPSTensor d D | Kraus.IsUnital A} := by
    apply isClosed_eq ?_ continuous_const
    fun_prop
  have hcompact : IsCompact {A : MPSTensor d D |
      ∀ i a b, A i a b ∈ Metric.closedBall (0 : ℂ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite
      (fun _ => isCompact_pi_infinite (fun _ => isCompact_closedBall 0 1)))
  apply hcompact.of_isClosed_subset hclosed
  intro A hA i a b
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_entry_le_one_of_isUnital A hA i a b

/-- Unital tensors and stationary density matrices admit a common convergent
subsequence in fixed dimensions. The limiting density may have smaller rank. -/
theorem MPSTensor.exists_subsequence_unital_stationary_limit {d D : ℕ}
    (A : ℕ → MPSTensor d D) (σ : ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ n, Kraus.IsUnital (A n))
    (hσ : ∀ n, σ n ∈ densityMatrices D)
    (hfixed : ∀ n, Kraus.adjointMap (A n) (σ n) = σ n) :
    ∃ B : MPSTensor d D, ∃ τ : Matrix (Fin D) (Fin D) ℂ,
      Kraus.IsUnital B ∧ τ ∈ densityMatrices D ∧ Kraus.adjointMap B τ = τ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (A ∘ φ) Filter.atTop (nhds B) ∧
        Filter.Tendsto (σ ∘ φ) Filter.atTop (nhds τ) := by
  let : FirstCountableTopology (Fin D → ℂ) := inferInstance
  let : FirstCountableTopology (Matrix (Fin D) (Fin D) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin D → Fin D → ℂ))
  let : FirstCountableTopology (MPSTensor d D) :=
    inferInstanceAs (FirstCountableTopology (Fin d → Matrix (Fin D) (Fin D) ℂ))
  obtain ⟨p, hp, φ, hφ, hconv⟩ :=
    ((MPSTensor.isCompact_setOf_isUnital d D).prod
      (densityMatrices_isCompact (D := D))).tendsto_subseq
        (fun n => show (A n, σ n) ∈
          {B : MPSTensor d D | Kraus.IsUnital B} ×ˢ densityMatrices D from ⟨hA n, hσ n⟩)
  have hadj : Continuous (fun p : MPSTensor d D × Matrix (Fin D) (Fin D) ℂ =>
      Kraus.adjointMap p.1 p.2) := by
    unfold Kraus.adjointMap
    fun_prop
  have hAc : Filter.Tendsto (A ∘ φ) Filter.atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hconv
  have hσc : Filter.Tendsto (σ ∘ φ) Filter.atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hconv
  refine ⟨p.1, p.2, hp.1, hp.2, ?_, φ, hφ, hAc, hσc⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hadj.tendsto p).comp hconv) hσc
    (Filter.Eventually.of_forall (fun n => hfixed (φ n)))

end CompactUnitalTensors

section CompactMinimalClassStability

open Kraus (blockPhysDim wordOfBlock blockTensor evalWord_blockTensor)

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Matrix.Norms.Frobenius ComplexOrder Topology
open Filter TNLean.Algebra ScalarCohomology

open scoped ScalarCohomology

namespace MPSTensor

private theorem fixedSpace_finrank_of_irreducible_unital
    {d D : ℕ} [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsIrreducibleFamily A) (hAU : Kraus.IsUnital A) :
    Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1 :=
  finrank_eigenspace_eq_one_of_irreducible_positive
    (Kraus.mapLM A) (Kraus.isPositiveMap_mapLM A)
    (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA) (r := 1) zero_le_one
    Matrix.PosDef.one (by simpa only [Kraus.mapLM_apply, Complex.ofReal_one, one_smul]
      using Kraus.map_one_of_isUnital A hAU)

private theorem exists_faithful_adjoint_density_of_irreducible_unital
    {d D : ℕ} [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsIrreducibleFamily A) (hAU : Kraus.IsUnital A) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosDef ∧ σ.trace = 1 ∧ Kraus.adjointMap A σ = σ := by
  have hLetter : ∃ i, A i ≠ 0 := by
    by_contra! hZero
    have hOne := Kraus.map_one_of_isUnital A hAU
    simp only [Kraus.map_apply, hZero,
      Matrix.zero_mul, Finset.sum_const_zero] at hOne
    exact one_ne_zero hOne.symm
  obtain ⟨Λ, r, hΛ, _, hEig⟩ := Kraus.exists_posDef_adjoint_eigenvector A
    (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily A hA) hLetter
  have hTrace := Kraus.trace_mul_mapLM_adjoint A rfl Λ 1
  have hNorm : Kraus.transferMap A 1 = 1 := Kraus.map_one_of_isUnital A hAU
  have hPos : 0 < Λ.trace := hΛ.trace_pos
  have hr : (r : ℂ) = 1 := mul_right_cancel₀ hPos.ne' (by
    simpa [hNorm, hEig, Matrix.trace_smul, smul_eq_mul] using hTrace.symm)
  have hFix : Kraus.adjointMap A Λ = Λ := by
    simpa only [Kraus.mapLM_apply, Kraus.map_apply, Kraus.adjointMap_apply,
      Matrix.conjTranspose_conjTranspose, hr, one_smul] using hEig
  refine ⟨(Λ.trace)⁻¹ • Λ, hΛ.smul (inv_pos.mpr hPos), ?_, ?_⟩
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hPos.ne']
  · rw [Kraus.adjointMap_smul, hFix]

private theorem continuous_transferCLM {d D : ℕ} :
    Continuous (fun A : MPSTensor d D => (Kraus.transferMap A).toContinuousLinearMap) := by
  refine continuous_clm_apply.mpr (fun X => ?_)
  change Continuous (fun A : MPSTensor d D => ∑ i : Fin d, A i * X * (A i)ᴴ)
  fun_prop

/-- Pointwise unital irreducible realizations of convergent periodic rays have
an eventually constant virtual class in fixed bond dimensions, provided a
uniform nonunit transfer bound and exact unitary covariance are supplied. -/
theorem eventually_cohomologousTo_of_tendsto_periodic_ray_sequence
    {G : Type} [Group G] {d D k r : ℕ} [NeZero D] [NeZero k]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hAU : Kraus.IsUnital A)
    (B : ℕ → MPSTensor d k) (hB : ∀ n, Kraus.IsIrreducibleFamily (B n))
    (hBU : ∀ n, Kraus.IsUnital (B n))
    (Q : ℕ → MPSTensor d r) (a : MPSTensor d r) (hQ : Tendsto Q atTop (𝓝 a))
    (hRay : ∀ n, SamePositiveMpvRay (Q n) (B n)) (hRay₀ : SamePositiveMpvRay a A)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hSpecA : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q)
    (hSpecB : ∀ n z, z ∈ spectrum ℂ (Kraus.transferMap (B n)) → z ≠ 1 → ‖z‖ ≤ q)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ω : ℕ → ScalarCocycle G) (ω₀ : ScalarCocycle G)
    (ρ : ∀ n, ProjectiveRepresentation (D := k) (ω n))
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (hρ : ∀ n g, ((ρ n).X g : Matrix (Fin k) (Fin k) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hρ₀ : ∀ g, (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ n g, rotatePhysical (U g) (B n) = fun i =>
      ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ) * B n i *
        ((ρ n).X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ)ᴴ)
    (hCov₀ : ∀ g, rotatePhysical (U g) A = fun i =>
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    ∀ᶠ n in atTop, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ n) (NeZero.pos k))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ₀) (NeZero.pos D))) := by
  apply (eventually_H2π_eq_iff_isMulCoboundary₂_div _ _).mpr
  classical
  by_contra hClass
  obtain ⟨ψ, hψ, hBad⟩ := exists_seq_forall_of_frequently
    (show ∃ᶠ n in atTop, ¬ groupCohomology.IsMulCoboundary₂ (ω n / ω₀) from
      not_eventually.mp hClass)
  choose σ hσ hσTrace hσFix using
    (fun n => exists_faithful_adjoint_density_of_irreducible_unital (hB n) (hBU n))
  obtain ⟨b, τ, hbU, hτ, hτFix, φ, hφ, hConv, _⟩ :=
    exists_subsequence_unital_stationary_limit (B ∘ ψ) (σ ∘ ψ)
      (fun n => hBU (ψ n)) (fun n => ⟨(hσ (ψ n)).posSemidef, hσTrace (ψ n)⟩)
      (fun n => hσFix (ψ n))
  let η := ψ ∘ φ
  have hη : Tendsto η atTop atTop := hψ.comp hφ.tendsto_atTop
  let f : ℕ → Matrix (Fin k) (Fin k) ℂ →L[ℂ] Matrix (Fin k) (Fin k) ℂ :=
    fun n => (Kraus.transferMap (B (η n))).toContinuousLinearMap
  let f₀ : Matrix (Fin k) (Fin k) ℂ →L[ℂ] Matrix (Fin k) (Fin k) ℂ :=
    (Kraus.transferMap b).toContinuousLinearMap
  have hf : Tendsto f atTop (𝓝 f₀) := continuous_transferCLM.continuousAt.tendsto.comp hConv
  have hSimple : ∀ n, (f n : Module.End ℂ (Matrix (Fin k) (Fin k) ℂ)).charpoly.rootMultiplicity
      1 = 1 := fun n => simple_fixedEigenvalue_of_unital_positive _
    (Kraus.isPositiveMap_mapLM _) (Kraus.map_one_of_isUnital _ (hBU (η n)))
    (fixedSpace_finrank_of_irreducible_unital (hB (η n)) (hBU (η n)))
  have hFix : ∀ n, f n 1 = 1 := fun n => Kraus.map_one_of_isUnital _ (hBU (η n))
  have hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap b) 1) = 1 := by
    have hEq := ContinuousLinearMap.eigenspace_one_limit_eq_span_of_uniform_spectrum_bound
      f f₀ hf (1 : Matrix (Fin k) (Fin k) ℂ) one_ne_zero hFix hSimple q hqOne
        (fun n => hSpecB (η n))
    change Module.End.eigenspace (Kraus.transferMap b) 1 =
      Submodule.span ℂ {(1 : Matrix (Fin k) (Fin k) ℂ)} at hEq
    rw [hEq]
    exact finrank_span_singleton one_ne_zero
  have hSpecb := ContinuousLinearMap.spectrum_limit_norm_le_of_uniform_nontrivial_bound
    f f₀ hf 1 one_ne_zero hFix hSimple q (fun n => hSpecB (η n))
  obtain ⟨E, K, hK, hSupport⟩ := hτ.1.isOrthogonalProjection_supportProj.exists_range_isometry
  let C : MPSTensor d E := fun i => Kᴴ * b i * K
  have hbnorm := norm_mpvState_tendsto_one_of_transfer_spectrum b hbU hDim q hq hqOne hSpecb
  have hbnz : ∀ᶠ N in atTop, (mpv b : (Fin N → Fin d) → ℂ) ≠ 0 := by
    filter_upwards [(tendsto_order.mp hbnorm).1 0 zero_lt_one] with N hN
    intro hzero
    have hs : mpvState b N = 0 := by
      ext s
      simp only [mpvState_apply, hzero, Pi.zero_apply, PiLp.zero_apply]
    simp only [hs, norm_zero, lt_self_iff_false] at hN
  have hSpan : ∀ᶠ N in atTop, Submodule.span ℂ {(mpv A : (Fin N → Fin d) → ℂ)} =
      Submodule.span ℂ {(mpv b : (Fin N → Fin d) → ℂ)} := by
    filter_upwards [hbnz, eventually_gt_atTop 0] with N hbN hN
    obtain ⟨s, hs⟩ := exists_mpv_ne_zero_of_isInjective hA hN
    have haN : (mpv a : (Fin N → Fin d) → ℂ) ≠ 0 := by
      intro hzero
      have hMem : (mpv A : (Fin N → Fin d) → ℂ) ∈
          Submodule.span ℂ {(mpv a : (Fin N → Fin d) → ℂ)} := by
        rw [hRay₀ N hN]
        exact Submodule.mem_span_singleton_self _
      have hz : (mpv A : (Fin N → Fin d) → ℂ) = 0 := by
        simpa only [hzero, Submodule.span_zero_singleton, Submodule.mem_bot] using hMem
      exact hs (congrFun hz s)
    exact (hRay₀ N hN).symm.trans (mpv_span_eq_of_tendsto
      (Q ∘ η) (B ∘ η) a b (hQ.comp hη) hConv
      (Eventually.of_forall fun n => hRay (η n) N hN) haN hbN)
  have hGood := eventually_cohomologousTo_of_tendsto_unital_periodic_lines
    A hA hAU (B ∘ η) b hConv (fun n => hBU (η n)) hbU hDim
    (σ ∘ η) (fun n => hσ (η n)) (fun n => hσTrace (η n)) (fun n => hσFix (η n))
    τ hτ.1 hτ.2 hτFix K hK hSupport C (fun _ => rfl) q hq hqOne hSpecA hSpecb hSpan
    U (ω ∘ η) ω₀ (fun n => ρ (η n)) ρ₀ (fun n => hρ (η n)) hρ₀
    (fun n => hCov (η n)) hCov₀
  obtain ⟨n, hn⟩ := hGood.exists
  exact hBad (φ n) ((H2π_eq_iff_isMulCoboundary₂_div _ _).mp hn)

end MPSTensor

namespace MPSTensor

private theorem exists_reindexed_unital_symmetry_tensor
    {G : Type} [Group G] {d D E r : ℕ} {ω : ScalarCocycle G}
    (hDim : D = E) (A : MPSTensor d D) (hA : Kraus.IsIrreducibleFamily A)
    (hAU : Kraus.IsUnital A) (Q : MPSTensor d r) (hRay : SamePositiveMpvRay Q A)
    (q : ℝ) (hSpec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ g, rotatePhysical (U g) A = fun i =>
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    ∃ B : MPSTensor d E, ∃ V : ProjectiveRepresentation (D := E) ω,
      Kraus.IsUnital B ∧ Kraus.IsIrreducibleFamily B ∧ SamePositiveMpvRay Q B ∧
      (∀ z ∈ spectrum ℂ (Kraus.transferMap B), z ≠ 1 → ‖z‖ ≤ q) ∧
      (∀ g, (V.X g : Matrix (Fin E) (Fin E) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      (∀ g, rotatePhysical (U g) B = fun i =>
        (V.X (g⁻¹) : Matrix (Fin E) (Fin E) ℂ) * B i *
          (V.X (g⁻¹) : Matrix (Fin E) (Fin E) ℂ)ᴴ) := by
  subst E
  exact ⟨A, ρ, hAU, hA, hRay, hSpec, hρ, hCov⟩

/-- On a first-countable parameter space, bounded pointwise unital irreducible
realizations of continuous periodic rays have locally constant virtual class
at an injective base tensor. The transfer bound and exact unitary covariance
are supplied; no continuous choice of minimal tensors or densities is made. -/
theorem eventually_cohomologousTo_of_continuousAt_bounded_unital_periodic_rays
    {T G : Type} [TopologicalSpace T] [FirstCountableTopology T] [Group G]
    {d r M : ℕ} (D : T → ℕ) (hDPos : ∀ t, 0 < D t) (hDBound : ∀ t, D t ≤ M)
    (A : ∀ t, MPSTensor d (D t)) (hA : ∀ t, Kraus.IsIrreducibleFamily (A t))
    (hAU : ∀ t, Kraus.IsUnital (A t)) (t₀ : T) (hA₀ : Kraus.IsInjective (A t₀))
    (Q : T → MPSTensor d r) (hQ : ContinuousAt Q t₀)
    (hRay : ∀ t, SamePositiveMpvRay (Q t) (A t))
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hSpec : ∀ t z, z ∈ spectrum ℂ (Kraus.transferMap (A t)) → z ≠ 1 → ‖z‖ ≤ q)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ω : T → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (hρ : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ t g, rotatePhysical (U g) (A t) = fun i =>
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ) :
    ∀ᶠ t in 𝓝 t₀, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t) (hDPos t))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t₀) (hDPos t₀))) := by
  apply (eventually_H2π_eq_iff_isMulCoboundary₂_div _ _).mpr
  classical
  by_contra hClass
  obtain ⟨x, hx, hBad⟩ := exists_seq_forall_of_frequently
    (show ∃ᶠ t in 𝓝 t₀, ¬ groupCohomology.IsMulCoboundary₂ (ω t / ω t₀) from
      not_eventually.mp hClass)
  let dim : ℕ → Fin (M + 1) := fun n => ⟨D (x n), Nat.lt_succ_of_le (hDBound (x n))⟩
  obtain ⟨⟨k, hkBound⟩, hInfinite⟩ := Finite.exists_infinite_fiber dim
  have hInfinite' : {n | dim n = ⟨k, hkBound⟩}.Infinite :=
    Set.infinite_coe_iff.mp hInfinite
  let φ : ℕ → ℕ := Nat.nth (fun n => dim n = ⟨k, hkBound⟩)
  have hφ : StrictMono φ := Nat.nth_strictMono hInfinite'
  let t := x ∘ φ
  have ht : Tendsto t atTop (𝓝 t₀) := hx.comp hφ.tendsto_atTop
  have hDim : ∀ n, D (t n) = k := fun n =>
    congrArg Fin.val (Nat.nth_mem_of_infinite hInfinite' n)
  have hkPos : 0 < k := by
    rw [← hDim 0]
    exact hDPos (t 0)
  let : NeZero k := ⟨hkPos.ne'⟩
  let : NeZero (D t₀) := ⟨(hDPos t₀).ne'⟩
  have hData : ∀ n, ∃ B : MPSTensor d k,
      ∃ V : ProjectiveRepresentation (D := k) (ω (t n)),
      Kraus.IsUnital B ∧ Kraus.IsIrreducibleFamily B ∧
      SamePositiveMpvRay (Q (t n)) B ∧
      (∀ z ∈ spectrum ℂ (Kraus.transferMap B), z ≠ 1 → ‖z‖ ≤ q) ∧
      (∀ g, (V.X g : Matrix (Fin k) (Fin k) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      (∀ g, rotatePhysical (U g) B = fun i =>
        (V.X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ) * B i *
          (V.X (g⁻¹) : Matrix (Fin k) (Fin k) ℂ)ᴴ) := by
    intro n
    exact exists_reindexed_unital_symmetry_tensor (hDim n) (A (t n)) (hA (t n))
      (hAU (t n)) (Q (t n)) (hRay (t n)) q (hSpec (t n)) U (ρ (t n)) (hρ (t n))
      (hCov (t n))
  choose B V hBU hBIrr hBRay hBSpec hV hBCov using hData
  have hGood := eventually_cohomologousTo_of_tendsto_periodic_ray_sequence
    (A t₀) hA₀ (hAU t₀) B hBIrr hBU (Q ∘ t) (Q t₀) (hQ.tendsto.comp ht)
    hBRay (hRay t₀) q hq hqOne (hSpec t₀) hBSpec U (ω ∘ t) (ω t₀)
    V (ρ t₀) hV (hρ t₀) hBCov (hCov t₀)
  obtain ⟨n, hn⟩ := hGood.exists
  exact hBad (φ n) ((H2π_eq_iff_isMulCoboundary₂_div _ _).mp hn)

end MPSTensor

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

namespace MPSTensor

/-- Common positive-length physical blocking preserves every positive-length
periodic ray. Source: arXiv:1606.00608, lines 318–344. -/
theorem SamePositiveMpvRay.blockTensor {d D E : ℕ}
    {A : MPSTensor d D} {B : MPSTensor d E} (hRay : SamePositiveMpvRay A B)
    (L : ℕ) (hL : 0 < L) :
    SamePositiveMpvRay (Kraus.blockTensor A L) (Kraus.blockTensor B L) := by
  intro N hN
  let f := LinearMap.funLeft ℂ ℂ (blockedConfigEquiv d N L)
  have hMap : ∀ {k : ℕ} (C : MPSTensor d k),
      f (mpv C : (Fin (N * L) → Fin d) → ℂ) =
        (mpv (Kraus.blockTensor C L) : (Fin N → Fin (blockPhysDim d L)) → ℂ) := by
    intro k C
    funext s
    simp only [f, LinearMap.funLeft_apply, mpv, coeff,
      ofFn_blockedConfigEquiv, evalWord_blockTensor]
  have h := congrArg (fun S : Submodule ℂ (((Fin (N * L) → Fin d) → ℂ)) => S.map f)
    (hRay (N * L) (Nat.mul_pos hN hL))
  simpa only [Submodule.map_span, Set.image_singleton, hMap] using h

end MPSTensor

namespace MPSTensor

private theorem isUnital_blockTensor_of_isUnital {d D : ℕ}
    (A : MPSTensor d D) (hA : Kraus.IsUnital A) (L : ℕ) :
    Kraus.IsUnital (blockTensor A L) := by
  have h := transferMap_blockTensor_fixedPoint A L 1 (Kraus.map_one_of_isUnital A hA)
  change ∑ i, blockTensor A L i * (blockTensor A L i)ᴴ = 1
  simpa only [Kraus.transferMap_apply, Matrix.mul_one] using h

private theorem spectrum_blockTensor_norm_le {d D L : ℕ}
    (A : MPSTensor d D) (hL : 0 < L) (q : ℝ)
    (hSpec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q) :
    ∀ z ∈ spectrum ℂ (Kraus.transferMap (blockTensor A L)), z ≠ 1 → ‖z‖ ≤ q ^ L := by
  intro z hz hzOne
  rw [transferMap_blockTensor, spectrum.map_pow_of_pos _ hL] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwOne : w ≠ 1 := by
    intro hwOne
    exact hzOne (by simp only [hwOne, one_pow])
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg w) (hSpec w hw hwOne) L

private theorem continuous_mps_blockTensor {d D : ℕ} (L : ℕ) :
    Continuous (fun A : MPSTensor d D => blockTensor A L) := by
  refine continuous_pi fun i => ?_
  exact continuous_evalWord_family id continuous_id (wordOfBlock d L i)

/-- Bounded pointwise normal unital realizations of continuous periodic rays
have locally constant virtual class on a first-countable parameter space,
under a supplied uniform transfer bound and exact unitary covariance.
Common blocking is derived, and neither minimal tensors nor stationary
matrices are assumed to vary continuously. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717; arXiv:1606.00608, lines 318–344. -/
theorem eventually_cohomologousTo_of_continuousAt_bounded_normal_periodic_rays
    {T G : Type} [TopologicalSpace T] [FirstCountableTopology T] [Group G]
    {d r M : ℕ} (D : T → ℕ) (hDBound : ∀ t, D t ≤ M)
    (A : ∀ t, MPSTensor d (D t)) (hA : ∀ t, IsNormalTensor (A t))
    (hAU : ∀ t, Kraus.IsUnital (A t)) (t₀ : T)
    (Q : T → MPSTensor d r) (hQ : ContinuousAt Q t₀)
    (hRay : ∀ t, SamePositiveMpvRay (Q t) (A t))
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hSpec : ∀ t z, z ∈ spectrum ℂ (Kraus.transferMap (A t)) → z ≠ 1 → ‖z‖ ≤ q)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (ω : T → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (hρ : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ t g, rotatePhysical (U g) (A t) = fun i =>
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ) :
    ∀ᶠ t in 𝓝 t₀, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t)
            (Nat.pos_of_ne_zero (hA t).bondDim_ne_zero))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t₀)
            (Nat.pos_of_ne_zero (hA t₀).bondDim_ne_zero))) := by
  let L := M ^ 4
  have hDPos : ∀ t, 0 < D t := fun t => Nat.pos_of_ne_zero (hA t).bondDim_ne_zero
  have hMPos : 0 < M := (hDPos t₀).trans_le (hDBound t₀)
  have hL : 0 < L := Nat.pow_pos hMPos
  have hBlock : ∀ t, Kraus.IsInjective (blockTensor (A t) L) :=
    fun t => (hA t).blockTensor_isInjective_of_bondDim_le (hDBound t)
  have hIrred : ∀ t, Kraus.IsIrreducibleFamily (blockTensor (A t) L) := fun t =>
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (Kraus.injective_implies_irreducibleCP _ (hBlock t))
  have hBlockedQ : ContinuousAt (fun t => blockTensor (Q t) L) t₀ :=
    (continuous_mps_blockTensor L).continuousAt.comp hQ
  exact eventually_cohomologousTo_of_continuousAt_bounded_unital_periodic_rays
    D hDPos hDBound (fun t => blockTensor (A t) L) hIrred
    (fun t => isUnital_blockTensor_of_isUnital _ (hAU t) L) t₀ (hBlock t₀)
    (fun t => blockTensor (Q t) L) hBlockedQ (fun t => (hRay t).blockTensor L hL)
    (q ^ L) (pow_nonneg hq _) (pow_lt_one₀ hq hqOne hL.ne')
    (fun t => spectrum_blockTensor_norm_le (A t) hL q (hSpec t))
    (blockUnitaryPhysicalAction U L) ω ρ hρ
    (fun t => rotatePhysical_blockTensor_of_unitary_virtual_covariance
      (A t) U (ρ t) (hρ t) (hCov t) L)

end MPSTensor

end CompactMinimalClassStability
