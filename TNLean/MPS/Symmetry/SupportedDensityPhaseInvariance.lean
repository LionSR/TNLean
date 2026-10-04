/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SupportedIsometricCompression
import TNLean.MPS.Symmetry.LocalSpectralSupport
import TNLean.MPS.Symmetry.LocalInvariantCompression

/-!
# Local cohomology for continuous supported bond data

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

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix ComplexOrder Topology
open Filter TNLean.Algebra

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
    ∀ᶠ t in 𝓝 t₀, (ω t).CohomologousTo (ω t₀) := by
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
