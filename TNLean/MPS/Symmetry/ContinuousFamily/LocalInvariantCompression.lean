/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ContinuousFamily.PointwiseInvariantCompression
import TNLean.MPS.Symmetry.GappedPath.PolarDeformation
import Mathlib.Analysis.Normed.Ring.Units
import QICLean.Analysis.Isometry.SupportedIsometricCompression
import TNLean.MPS.Symmetry.ContinuousFamily.LocalSpectralSupport

/-!
# Local constancy under invariant bond compression

Injectivity is open in a continuous tensor family. Consequently, a compressed
tensor that is injective at one parameter remains injective along sufficiently
short subintervals. Restriction of the actual pointwise virtual actions then
shows that their factor systems have the same cohomology class near that
parameter, without continuity of those actions or of their ambient dimensions.

The statements are auxiliary restriction results in the context of
arXiv:1010.3732, Appendix C, lines 2712–2717. A continuous compressed tensor
family is supplied explicitly; it is not inferred from a physical gap.
See `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

## Local cohomology for continuous supported bond data

A continuous tensor family and a continuous positive trace-one bond density
have a locally constant virtual cohomology class on their injective minimal
supports, provided the actual unitary virtual actions commute with the
compressed densities. The minimal dimensions and chosen support frames may
vary without being continuous. No projective action on a complementary bond
space is assumed.

This is an auxiliary form of the restriction in arXiv:1010.3732, Appendix C,
lines 2653–2717. Continuity of the ambient tensor and density is supplied here.
Their construction from a physical gap remains open, as recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

section

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open Filter Topology

open scoped ScalarCohomology

namespace MPSTensor

/-- Injectivity persists near a parameter at which a one-site tensor
family is continuous and injective.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem eventually_isInjective_of_continuousAt
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (C : T → MPSTensor d r) (t₀ : T) (hC : ContinuousAt C t₀)
    (hInj : Kraus.IsInjective (C t₀)) :
    ∀ᶠ t in 𝓝 t₀, Kraus.IsInjective (C t) := by
  let M := fun t => physicalMatrix (C t)
  have hM : ContinuousAt M t₀ := by
    exact continuousAt_pi.2 fun i => continuousAt_pi.2 fun p =>
      (continuous_apply p.2).continuousAt.comp ((continuous_apply p.1).continuousAt.comp
        ((continuous_apply i).continuousAt.comp hC))
  have hGram : ContinuousAt (fun t => (M t)ᴴ * M t) t₀ :=
    ((continuous_id : Continuous fun X : Matrix (Fin d) (Fin r × Fin r) ℂ => X).matrix_conjTranspose
      |>.matrix_mul continuous_id).continuousAt.comp hM
  have hunit : IsUnit ((M t₀)ᴴ * M t₀) :=
    (Matrix.PosDef.conjTranspose_mul_self (M t₀)
      (injective_physicalMatrix_mulVec_of_isInjective hInj)).isUnit
  have hunitEvent : ∀ᶠ X in 𝓝 ((M t₀)ᴴ * M t₀), IsUnit X :=
    (Units.isOpen : IsOpen {X : Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ |
      IsUnit X}).mem_nhds hunit
  have hevent := hGram.eventually hunitEvent
  filter_upwards [hevent] with t ht
  apply isInjective_of_leftInverse_physicalMatrix (C t)
    (((M t)ᴴ * M t)⁻¹ * (M t)ᴴ)
  simpa only [Matrix.mul_assoc] using
    Matrix.nonsing_inv_mul ((M t)ᴴ * M t) ((Matrix.isUnit_iff_isUnit_det _).mp ht)

end MPSTensor

namespace Set.Icc

/-- A property holding near a point of the unit interval holds along every
sufficiently short affine subinterval issuing from that point. -/
theorem eventually_forall_convexComb {p : unitInterval → Prop}
    (t₀ : unitInterval) (hp : ∀ᶠ t in 𝓝 t₀, p t) :
    ∀ᶠ t in 𝓝 t₀, ∀ s : unitInterval, p (Set.Icc.convexComb t₀ t s) := by
  obtain ⟨ε, hε, hpε⟩ := Metric.eventually_nhds_iff.mp hp
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  intro s
  apply hpε
  have hdist : dist (Set.Icc.convexComb t₀ t s) t₀ ≤ dist t t₀ := by
    change |(1 - (s : ℝ)) * (t₀ : ℝ) + s * t - t₀| ≤ |(t : ℝ) - t₀|
    rw [show (1 - (s : ℝ)) * (t₀ : ℝ) + s * t - t₀ =
      (s : ℝ) * (t - t₀) by ring, abs_mul, abs_of_nonneg s.2.1]
    exact mul_le_of_le_one_left (abs_nonneg _) s.2.2
  exact hdist.trans_lt ht

end Set.Icc

namespace MPSTensor

open ScalarCohomology

/-- Pointwise invariant single-bond compressions have locally constant
factor-system classes when the compressed tensors are continuous and
injective at the base parameter. The original dimensions, frames and
virtual actions need not be continuous. Auxiliary context:
arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem eventually_cohomologousTo_of_continuousOn_pointwise_compression
    {G : Type} [Group G] {d r : ℕ} (hr : 0 < r)
    (D : unitInterval → ℕ) (ω : unitInterval → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (A : ∀ t, MPSTensor d (D t))
    (J : ∀ t, Matrix (Fin (D t)) (Fin r) ℂ)
    (S : Set unitInterval)
    (hJ : ∀ t ∈ S, (J t).IsIsometry)
    (hUnitary : ∀ t ∈ S, ∀ g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hComm : ∀ t ∈ S, ∀ g, Commute ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ)
      (J t * (J t)ᴴ))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hCov : ∀ t ∈ S, ∀ g i, twistedTensor (A t) U g i =
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (C : unitInterval → MPSTensor d r) (hC : ContinuousOn C S)
    (t₀ : unitInterval) (hS : S ∈ 𝓝 t₀)
    (hInj : Kraus.IsInjective (C t₀))
    (hCompress : ∀ t ∈ S, ∀ i, C t i = (J t)ᴴ * A t i * J t) :
    ∀ᶠ t in 𝓝 t₀, groupCohomology.IsMulCoboundary₂ (ω t / ω t₀) := by
  have hlocal := Set.Icc.eventually_forall_convexComb t₀
    (eventually_isInjective_of_continuousAt C t₀ (hC.continuousAt hS) hInj)
  have hlocalS := Set.Icc.eventually_forall_convexComb t₀ hS
  filter_upwards [hlocal, hlocalS] with t ht hts
  apply (H2π_eq_iff_isMulCoboundary₂_div _ _).mp
  simpa only [Set.Icc.convexComb_zero, Set.Icc.convexComb_one] using
    cohomologousTo_of_continuous_injective_pointwise_compression hr
      (fun s => D (Set.Icc.convexComb t₀ t s))
      (fun s => ω (Set.Icc.convexComb t₀ t s))
      (fun s => ρ (Set.Icc.convexComb t₀ t s))
      (fun s => A (Set.Icc.convexComb t₀ t s))
      (fun s => J (Set.Icc.convexComb t₀ t s))
      (fun s => hJ (Set.Icc.convexComb t₀ t s) (hts s))
      (fun s => hUnitary (Set.Icc.convexComb t₀ t s) (hts s))
      (fun s => hComm (Set.Icc.convexComb t₀ t s) (hts s)) U
      (fun s => hCov (Set.Icc.convexComb t₀ t s) (hts s))
      (fun s => C (Set.Icc.convexComb t₀ t s))
      (hC.comp_continuous (Set.Icc.continuous_convexComb t₀ t) hts) ht
      (fun s => hCompress (Set.Icc.convexComb t₀ t s) (hts s))

/-- Pointwise invariant single-bond compressions have locally constant
factor-system classes when the compressed tensors are continuous and
injective at the base parameter. The original dimensions, frames and
virtual actions need not be continuous. Auxiliary context:
arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem eventually_cohomologousTo_of_continuous_pointwise_compression
    {G : Type} [Group G] {d r : ℕ} (hr : 0 < r)
    (D : unitInterval → ℕ) (ω : unitInterval → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (A : ∀ t, MPSTensor d (D t))
    (J : ∀ t, Matrix (Fin (D t)) (Fin r) ℂ)
    (hJ : ∀ t, (J t).IsIsometry)
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hComm : ∀ t g, Commute ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ)
      (J t * (J t)ᴴ))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hCov : ∀ t g i, twistedTensor (A t) U g i =
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (C : unitInterval → MPSTensor d r) (hC : Continuous C)
    (t₀ : unitInterval) (hInj : Kraus.IsInjective (C t₀))
    (hCompress : ∀ t i, C t i = (J t)ᴴ * A t i * J t) :
    ∀ᶠ t in 𝓝 t₀, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t)
            (hr.trans_le (by
              simpa only [Fintype.card_fin] using Matrix.IsIsometry.card_le (J t) (hJ t))))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t₀)
            (hr.trans_le (by
              simpa only [Fintype.card_fin] using Matrix.IsIsometry.card_le (J t₀) (hJ t₀))))) := by
  apply (eventually_H2π_eq_iff_isMulCoboundary₂_div _ _).mpr
  exact eventually_cohomologousTo_of_continuousOn_pointwise_compression
    hr D ω ρ A J Set.univ (fun t _ => hJ t) (fun t _ => hUnitary t)
    (fun t _ => hComm t) U (fun t _ => hCov t) C hC.continuousOn t₀
    Filter.univ_mem hInj (fun t _ => hCompress t)

/-- Continuous ambient tensors and continuous invariant isometric frames
give locally constant factor-system classes if their single-bond
compression is injective at the base parameter. The pointwise virtual
actions and their factor systems need not be continuous. Auxiliary context:
arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem eventually_cohomologousTo_of_continuousOn_invariant_compression
    {G : Type} [Group G] {d D r : ℕ} (hr : 0 < r)
    (ω : unitInterval → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D) (ω t))
    (A : unitInterval → MPSTensor d D)
    (J : unitInterval → Matrix (Fin D) (Fin r) ℂ)
    (S : Set unitInterval) (hA : ContinuousOn A S) (hJcont : ContinuousOn J S)
    (hJ : ∀ t ∈ S, (J t).IsIsometry)
    (hUnitary : ∀ t ∈ S, ∀ g, ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hComm : ∀ t ∈ S, ∀ g, Commute ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ)
      (J t * (J t)ᴴ))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hCov : ∀ t ∈ S, ∀ g i, twistedTensor (A t) U g i =
      ((ρ t).X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ)
    (t₀ : unitInterval) (hS : S ∈ 𝓝 t₀)
    (hInj : Kraus.IsInjective (fun i => (J t₀)ᴴ * A t₀ i * J t₀)) :
    ∀ᶠ t in 𝓝 t₀, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t)
            (hr.trans_le (by
              simpa only [Fintype.card_fin] using
                Matrix.IsIsometry.card_le (J t₀) (hJ t₀ (mem_of_mem_nhds hS)))))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t₀)
            (hr.trans_le (by
              simpa only [Fintype.card_fin] using
                Matrix.IsIsometry.card_le (J t₀) (hJ t₀ (mem_of_mem_nhds hS)))))) := by
  apply (eventually_H2π_eq_iff_isMulCoboundary₂_div _ _).mpr
  let C : unitInterval → MPSTensor d r := fun t i => (J t)ᴴ * A t i * J t
  have hC : ContinuousOn C S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_pi fun i =>
      hJcont.domRestrict.matrix_conjTranspose.matrix_mul
        ((continuous_apply i).comp hA.domRestrict) |>.matrix_mul
          hJcont.domRestrict
  exact eventually_cohomologousTo_of_continuousOn_pointwise_compression
    hr (fun _ => D) ω ρ A J S hJ hUnitary hComm U hCov C hC t₀ hS hInj
    (fun _ _ _ => rfl)

end MPSTensor

end

section

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix ComplexOrder Topology
open Filter ScalarCohomology

open scoped ScalarCohomology

namespace MPSTensor

/-- Continuous ambient tensors and positive bond densities determine a
locally constant virtual class when their pointwise minimal support
compression is injective at the base parameter and the unitary virtual
actions commute with the compressed densities. No continuity of the minimal frames or virtual
actions is assumed, and no projective action on an augmented complement
is required. This is conditional on the supplied continuous bond data;
it does not derive those data from a physical gap. Auxiliary context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem eventually_cohomologousTo_of_continuous_supported_density
    {G : Type} [Group G] {d k : ℕ}
    (D : unitInterval → ℕ) (ω : unitInterval → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (B : unitInterval → MPSTensor d k) (hB : Continuous B)
    (σ : unitInterval → Matrix (Fin k) (Fin k) ℂ) (hσcont : Continuous σ)
    (hσ : ∀ t, (σ t).PosSemidef) (htrace : ∀ t, (σ t).trace = 1)
    (K : ∀ t, Matrix (Fin k) (Fin (D t)) ℂ)
    (hK : ∀ t, (K t).IsIsometry)
    (hsupport : ∀ t, K t * (K t)ᴴ = (hσ t).supportProj)
    (A : ∀ t, MPSTensor d (D t))
    (hA : ∀ t i, A t i = (K t)ᴴ * B t i * K t)
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hComm : ∀ t g, Commute ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ)
      ((K t)ᴴ * σ t * K t))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hCov : ∀ t g i, twistedTensor (A t) U g i =
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (t₀ : unitInterval) (hInj : Kraus.IsInjective (A t₀)) :
    ∀ᶠ t in 𝓝 t₀, groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t)
            (Matrix.supportFrame_dimension_pos_of_trace_one
              (K t) (σ t) (hσ t) (hsupport t) (htrace t)))) =
      groupCohomology.H2π (Rep.ofMulDistribMulAction G ℂˣ)
        (groupCohomology.cocyclesOfIsMulCocycle₂
          (ScalarCocycle.isMulCocycle₂_of_projRep (ρ t₀)
            (Matrix.supportFrame_dimension_pos_of_trace_one
              (K t₀) (σ t₀) (hσ t₀) (hsupport t₀) (htrace t₀)))) := by
  apply (eventually_H2π_eq_iff_isMulCoboundary₂_div _ _).mpr
  have hD : 0 < D t₀ := Matrix.supportFrame_dimension_pos_of_trace_one
    (K t₀) (σ t₀) (hσ t₀) (hsupport t₀) (htrace t₀)
  obtain ⟨a, b, S, ha, hab, hSopen, ht₀, hJcont, hJ₀, hJ⟩ :=
    Matrix.exists_local_continuous_spectral_frame σ hσcont (fun t => (hσ t).isHermitian)
      t₀ (hσ t₀) (K t₀) (hK t₀) (hsupport t₀).symm
  let J := fun t => Matrix.polarIso (Matrix.spectralCorner a b (σ t) * K t₀)
  have hsub : ∀ t ∈ S, (K t * (K t)ᴴ) * J t = J t := by
    intro t ht
    apply Matrix.isometry_absorption_of_projector_absorption (J t) (hJ t ht).1
    rw [hsupport t, (hJ t ht).2]
    exact Matrix.supportProj_mul_spectralCorner (hσ t) ha hab
  let C : unitInterval → MPSTensor d (D t₀) := fun t i => (J t)ᴴ * B t i * J t
  have hCcont : ContinuousOn C S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_pi fun i =>
      hJcont.domRestrict.matrix_conjTranspose.matrix_mul
        ((continuous_apply i).comp (hB.comp continuous_subtype_val)) |>.matrix_mul
          hJcont.domRestrict
  have hC₀ : C t₀ = A t₀ := by
    funext i
    simpa only [C, J, hJ₀] using (hA t₀ i).symm
  let J' := fun t => (K t)ᴴ * J t
  have hJ' : ∀ t ∈ S, (J' t).IsIsometry := fun t ht =>
    Matrix.isIsometry_conjTranspose_mul_of_absorption (K t) (J t) (hJ t ht).1 (hsub t ht)
  have hComm' : ∀ t ∈ S, ∀ g,
      Commute ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ)
        (J' t * (J' t)ᴴ) := by
    intro t ht g
    have hL := Matrix.commute_isometryExtendByIdentity_of_commute_compression
      (K t) (hK t) (σ t) (hσ t) (hsupport t) ((ρ t).X g) (hComm t g)
    have hP := Matrix.commute_spectralCorner_of_commute a b _ (σ t) hL
    have hQ := Matrix.commute_compression_of_commute_isometryExtendByIdentity
      (K t) (hK t) ((ρ t).X g) _ hP
    rw [← (hJ t ht).2] at hQ
    simpa only [J', J, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hQ
  have hCompress : ∀ t ∈ S, ∀ i, C t i = (J' t)ᴴ * A t i * J' t := by
    intro t ht i
    simpa only [C, J', hA t i] using
      (Matrix.isometry_double_compression_eq_of_absorption
        (K t) (J t) (B t i) (hsub t ht)).symm
  exact eventually_cohomologousTo_of_continuousOn_pointwise_compression
    hD D ω ρ A J' S hJ' (fun t _ => hUnitary t) hComm' U
    (fun t _ => hCov t) C hCcont t₀ (hSopen.mem_nhds ht₀)
    (by simpa only [hC₀] using hInj) hCompress

end MPSTensor

end
