/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausCornerCompression
import QICLean.Channel.FixedPoint.SupportInvariance
import TNLean.Algebra.SupportedIsometricCompression
import TNLean.MPS.Symmetry.LocalInvariantCompression
import TNLean.MPS.Symmetry.LocalProjectiveClassStability
import TNLean.MPS.Symmetry.LocalSpectralSupport
import TNLean.MPS.Symmetry.ContinuousStationaryDensity
import TNLean.MPS.Symmetry.StationaryDensitySymmetry

/-!
# Local virtual class invariance from stationary support data

Continuous ambient bond tensors with uniquely determined normalized stationary
densities yield locally constant virtual cohomology on their minimal supports.
The density may change rank, and neither the minimal support frames nor their
virtual actions are assumed continuous. The arguments require no projective
action on the complementary ambient bond space.

The final unital-family theorem derives local continuity and uniqueness of the
stationary density from a one-dimensional adjoint fixed space at the base
parameter. It assumes injectivity only at that parameter. The parameter space is arbitrary;
the final local theorem requires continuity only at the base point.

These are conditional auxiliary results in the setting of arXiv:1010.3732,
Appendix C, lines 2653–2717. Continuous ambient canonical tensors, stationary
support realizations, and exact unitary covariance are supplied. Their
construction from a gapped physical path remains open; see
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix ComplexOrder Topology
open Filter TNLean.Algebra

namespace MPSTensor

/-- Stationary support invariance makes the adjoint transfer map intertwine
expansion from support coordinates. Source: Wolf, Lemma 6.4. -/
private theorem adjointMap_compression_lift
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ)
    (Z : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.adjointMap B (K * Z * Kᴴ) = K * Kraus.adjointMap A Z * Kᴴ := by
  have hfix' : Kraus.map (fun i => (B i)ᴴ) σ = σ := by
    simpa only [Kraus.map_apply, Matrix.conjTranspose_conjTranspose,
      Kraus.adjointMap_apply] using hfix
  have hInv := Kraus.lowerZero_of_posSemidef_fixedPoint
    (fun i => (B i)ᴴ) σ hσ hfix'
  have hP : IsOrthogonalProjection (K * Kᴴ) := by
    simpa only [Kraus.stationaryProj, ← hsupport] using hInv.1
  have hLower : ∀ i, (1 - K * Kᴴ) * (B i)ᴴ * (K * Kᴴ) = 0 := by
    simpa only [Kraus.stationaryProj, ← hsupport] using hInv.2
  have hCorner := Kraus.lowerZero_implies_invariance
    (fun i => (B i)ᴴ) (K * Kᴴ) hP hLower (K * Z * Kᴴ)
  have hC : Kraus.adjointMap A Z = Kᴴ * Kraus.adjointMap B (K * Z * Kᴴ) * K := by
    simpa only [Kraus.map_apply, Matrix.conjTranspose_conjTranspose,
      Kraus.adjointMap_apply] using
        Kraus.map_compressed_eq_conj (fun i => (B i)ᴴ) (fun i => (A i)ᴴ) K
          (fun i => by simp only [hA i, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]) Z
  have hCorner' :
      (K * Kᴴ) * Kraus.adjointMap B (K * Z * Kᴴ) * (K * Kᴴ) =
        Kraus.adjointMap B (K * Z * Kᴴ) := by
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ K,
      show Kᴴ * K = 1 from hK, Matrix.one_mul, Matrix.mul_one,
      Kraus.map_apply, Matrix.conjTranspose_conjTranspose, Kraus.adjointMap_apply]
      using hCorner
  rw [hC]
  simpa only [Matrix.mul_assoc] using hCorner'.symm

/-- Compression to the support of a unique stationary density preserves
trace-one stationarity and its uniqueness. Unitality is not required for
this algebraic implication. Source context: arXiv:1010.3732, Appendix C,
lines 2653–2717; stationary support invariance is Wolf, Lemma 6.4. -/
theorem stationaryMatrix_compression_unique
    {d k D : ℕ} (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (huniq : ∀ Z : Matrix (Fin k) (Fin k) ℂ,
      Kraus.adjointMap B Z = Z → Z.trace = 1 → Z = σ) :
    Kraus.adjointMap A (Kᴴ * σ * K) = Kᴴ * σ * K ∧
      (Kᴴ * σ * K).trace = 1 ∧
      ∀ Z : Matrix (Fin D) (Fin D) ℂ,
        Kraus.adjointMap A Z = Z → Z.trace = 1 → Z = Kᴴ * σ * K := by
  have hfix' : Kraus.adjointMap A (Kᴴ * σ * K) = Kᴴ * σ * K := by
    simpa only [Kraus.map_apply, Matrix.conjTranspose_conjTranspose,
      Kraus.adjointMap_apply] using
        Kraus.map_compressed_fixedPoint (fun i => (B i)ᴴ) (fun i => (A i)ᴴ)
          K (hσ.supportProj) σ
          (fun i => by simp only [hA i, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]) hsupport
          (by rw [hσ.supportProj_mul_self, hσ.mul_supportProj_self])
          (by simpa only [Kraus.map_apply, Matrix.conjTranspose_conjTranspose,
            Kraus.adjointMap_apply] using hfix)
  refine ⟨hfix', ?_, ?_⟩
  · rw [Matrix.trace_mul_cycle, hsupport,
      hσ.supportProj_mul_self, htrace]
  · intro Z hZ hZtrace
    have hlift : K * Z * Kᴴ = σ := huniq _
      (by rw [adjointMap_compression_lift B A K hK hA σ hσ hsupport hfix, hZ])
      (by rw [Matrix.trace_mul_cycle, show Kᴴ * K = 1 from hK,
        Matrix.one_mul, hZtrace])
    have h := congrArg (fun X => Kᴴ * X * K) hlift
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Kᴴ K,
      show Kᴴ * K = 1 from hK, Matrix.one_mul, Matrix.mul_one] using h

private theorem eventually_class_of_continuousAt_pointwise_compression
    {T : Type*} [TopologicalSpace T] {G : Type} [Group G] {d r : ℕ} (hr : 0 < r)
    (D : T → ℕ) (ω : T → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (A : ∀ t, MPSTensor d (D t))
    (J : ∀ t, Matrix (Fin (D t)) (Fin r) ℂ)
    (S : Set T) (hSopen : IsOpen S)
    (hJ : ∀ t ∈ S, (J t).IsIsometry)
    (hUnitary : ∀ t ∈ S, ∀ g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (hComm : ∀ t ∈ S, ∀ g, Commute ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ)
      (J t * (J t)ᴴ))
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : ∀ t ∈ S, ∀ g i, ∑ j, (U g : Matrix (Fin d) (Fin d) ℂ) i j • A t j =
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (C : T → MPSTensor d r) (hC : ContinuousOn C S)
    (t₀ : T) (ht₀ : t₀ ∈ S) (hInj : Kraus.IsInjective (C t₀))
    (hCompress : ∀ t ∈ S, ∀ i, C t i = (J t)ᴴ * A t i * J t) :
    ∀ᶠ t in 𝓝 t₀, (ω t).CohomologousTo (ω t₀) := by
  let : NeZero r := ⟨Nat.ne_of_gt hr⟩
  choose σ hσ hσUnitary using fun t : S =>
    (ρ t).exists_unitary_compression (J t) (hJ t t.property)
      (hUnitary t t.property) (hComm t t.property)
  have hCovC : ∀ t : S, ∀ g i,
      ∑ j, (U g : Matrix (Fin d) (Fin d) ℂ) i j • C t j =
        ((σ t).X g⁻¹ : Matrix (Fin r) (Fin r) ℂ) * C t i *
          ((σ t).X g⁻¹ : Matrix (Fin r) (Fin r) ℂ)ᴴ := by
    intro t g i
    have hrot : ∑ j, (U g : Matrix (Fin d) (Fin d) ℂ) i j • C t j =
        (J t)ᴴ * (∑ j, (U g : Matrix (Fin d) (Fin d) ℂ) i j • A t j) * J t := by
      simp only [hCompress t t.property, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [hrot, hCov t t.property, hσ, hCompress t t.property]
    exact Matrix.isometry_compression_conj_of_commute (J t) (hJ t t.property)
      _ _ (hComm t t.property g⁻¹)
  have hClass := eventually_cohomologousTo_of_continuousAt_exact_unitary_covariance
    (fun t : S => C t) ⟨t₀, ht₀⟩ hC.domRestrict.continuousAt hInj
    (fun g => U g) (fun t : S => ω t) σ hσUnitary hCovC
  have hNhds : Filter.map ((↑) : S → T) (𝓝 (⟨t₀, ht₀⟩ : S)) = 𝓝 t₀ :=
    map_nhds_subtype_coe_eq_nhds ht₀ (hSopen.mem_nhds ht₀)
  rw [← hNhds]
  exact hClass


end MPSTensor

namespace Matrix

/-- Restrict the spectral frame construction to an open neighborhood.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
private theorem exists_local_continuousOn_spectral_frame
    {T m n : Type*} [TopologicalSpace T]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : T → Matrix m m ℂ) (S : Set T) (hS : IsOpen S)
    (hA : ContinuousOn A S) (hHerm : ∀ t, (A t).IsHermitian)
    (t₀ : T) (ht₀ : t₀ ∈ S) (hbase : (A t₀).PosSemidef)
    (J₀ : Matrix m n ℂ) (hJ₀ : J₀.IsIsometry)
    (hsupport : hbase.supportProj = J₀ * J₀ᴴ) :
    ∃ a b : ℝ, ∃ R : Set T, 0 < a ∧ a < b ∧ IsOpen R ∧ t₀ ∈ R ∧ R ⊆ S ∧
      ContinuousOn (fun t => polarIso (spectralCorner a b (A t) * J₀)) R ∧
      polarIso (spectralCorner a b (A t₀) * J₀) = J₀ ∧
      ∀ t ∈ R, (polarIso (spectralCorner a b (A t) * J₀)).IsIsometry ∧
        polarIso (spectralCorner a b (A t) * J₀) *
          (polarIso (spectralCorner a b (A t) * J₀))ᴴ = spectralCorner a b (A t) := by
  obtain ⟨a, b, R, ha, hab, hR, ht₀R, hcont, hbaseFrame, hFrame⟩ :=
    exists_local_continuous_spectral_frame (fun t : S => A t) hA.domRestrict
      (fun t => hHerm t) ⟨t₀, ht₀⟩ hbase J₀ hJ₀ hsupport
  refine ⟨a, b, Subtype.val '' R, ha, hab,
    hS.isOpenMap_subtype_val R hR, ⟨⟨t₀, ht₀⟩, ht₀R, rfl⟩, ?_, ?_, hbaseFrame, ?_⟩
  · rintro t ⟨s, hs, rfl⟩
    exact s.property
  · exact Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr hcont
  · rintro t ⟨s, hs, rfl⟩
    exact hFrame s hs

end Matrix

namespace MPSTensor

/-- On an open neighborhood, continuous ambient tensors and unique stationary
densities give local constancy of the minimal virtual class. Only the density
is required continuous on that neighborhood, and injectivity is required
only at the base parameter. Continuous canonical bond data are supplied;
no implication from a physical gap is asserted. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem eventually_cohomologousTo_of_continuousOn_unique_stationary_density
    {T : Type*} [TopologicalSpace T] {G : Type} [Group G] {d k : ℕ}
    (D : T → ℕ) (ω : T → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (B : T → MPSTensor d k) (hB : Continuous B)
    (σ : T → Matrix (Fin k) (Fin k) ℂ)
    (S : Set T) (hS : IsOpen S) (hσcont : ContinuousOn σ S)
    (hσ : ∀ t, (σ t).PosSemidef) (htrace : ∀ t, (σ t).trace = 1)
    (hfix : ∀ t, Kraus.adjointMap (B t) (σ t) = σ t)
    (huniq : ∀ t ∈ S, ∀ Z, Kraus.adjointMap (B t) Z = Z → Z.trace = 1 → Z = σ t)
    (K : ∀ t, Matrix (Fin k) (Fin (D t)) ℂ)
    (hK : ∀ t, (K t).IsIsometry)
    (hsupport : ∀ t, K t * (K t)ᴴ = (hσ t).supportProj)
    (A : ∀ t, MPSTensor d (D t))
    (hA : ∀ t i, A t i = (K t)ᴴ * B t i * K t)
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : ∀ t g, rotatePhysical (U g) (A t) = fun i =>
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (t₀ : T) (ht₀S : t₀ ∈ S) (hInj : Kraus.IsInjective (A t₀)) :
    ∀ᶠ t in 𝓝 t₀, (ω t).CohomologousTo (ω t₀) := by
  have hD : 0 < D t₀ := Matrix.supportFrame_dimension_pos_of_trace_one
    (K t₀) (σ t₀) (hσ t₀) (hsupport t₀) (htrace t₀)
  obtain ⟨a, b, R, ha, hab, hRopen, ht₀, hRS, hJcont, hJ₀, hJ⟩ :=
    Matrix.exists_local_continuousOn_spectral_frame σ S hS hσcont
      (fun t => (hσ t).isHermitian) t₀ ht₀S (hσ t₀) (K t₀) (hK t₀) (hsupport t₀).symm
  have hComm : ∀ t ∈ R, ∀ g,
      Commute ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ)
        ((K t)ᴴ * σ t * K t) := by
    intro t ht
    obtain ⟨hfixed, htr, hunique⟩ := stationaryMatrix_compression_unique
      (B t) (A t) (K t) (hK t) (hA t) (σ t) (hσ t)
        (hsupport t) (hfix t) (htrace t) (huniq t (hRS ht))
    exact virtualAction_commute_stationaryMatrix_of_unique (ρ t) (hUnitary t)
      U (A t) (hCov t) _ hfixed htr hunique
  let J := fun t => Matrix.polarIso (Matrix.spectralCorner a b (σ t) * K t₀)
  have hsub : ∀ t ∈ R, (K t * (K t)ᴴ) * J t = J t := by
    intro t ht
    apply Matrix.isometry_absorption_of_projector_absorption (J t) (hJ t ht).1
    rw [hsupport t, (hJ t ht).2]
    exact Matrix.supportProj_mul_spectralCorner (hσ t) ha hab
  let C : T → MPSTensor d (D t₀) := fun t i => (J t)ᴴ * B t i * J t
  have hCcont : ContinuousOn C R := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_pi fun i =>
      hJcont.domRestrict.matrix_conjTranspose.matrix_mul
        ((continuous_apply i).comp (hB.comp continuous_subtype_val)) |>.matrix_mul
          hJcont.domRestrict
  have hC₀ : C t₀ = A t₀ := by
    funext i
    simpa only [C, J, hJ₀] using (hA t₀ i).symm
  let J' := fun t => (K t)ᴴ * J t
  have hJ' : ∀ t ∈ R, (J' t).IsIsometry := fun t ht =>
    Matrix.isIsometry_conjTranspose_mul_of_absorption (K t) (J t) (hJ t ht).1 (hsub t ht)
  have hComm' : ∀ t ∈ R, ∀ g,
      Commute ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ)
        (J' t * (J' t)ᴴ) := by
    intro t ht g
    have hL := Matrix.commute_isometryExtendByIdentity_of_commute_compression
      (K t) (hK t) (σ t) (hσ t) (hsupport t) ((ρ t).X g) (hComm t ht g)
    have hP := Matrix.commute_spectralCorner_of_commute a b _ (σ t) hL
    have hQ := Matrix.commute_compression_of_commute_isometryExtendByIdentity
      (K t) (hK t) ((ρ t).X g) _ hP
    rw [← (hJ t ht).2] at hQ
    simpa only [J', J, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hQ
  have hCompress : ∀ t ∈ R, ∀ i, C t i = (J' t)ᴴ * A t i * J' t := by
    intro t ht i
    simpa only [C, J', hA t i] using
      (Matrix.isometry_double_compression_eq_of_absorption
        (K t) (J t) (B t i) (hsub t ht)).symm
  exact eventually_class_of_continuousAt_pointwise_compression
    hD D ω ρ A J' R hRopen hJ' (fun t _ => hUnitary t) hComm' U
    (fun t _ g i => congrFun (hCov t g) i) C hCcont t₀ ht₀
    (by simpa only [hC₀] using hInj) hCompress

/-- The global continuous-density specialization of the neighborhood
stationary-support theorem. Source context: arXiv:1010.3732, Appendix C,
lines 2653–2717. -/
theorem eventually_cohomologousTo_of_continuous_unique_stationary_density
    {T : Type*} [TopologicalSpace T] {G : Type} [Group G] {d k : ℕ}
    (D : T → ℕ) (ω : T → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (B : T → MPSTensor d k) (hB : Continuous B)
    (σ : T → Matrix (Fin k) (Fin k) ℂ) (hσcont : Continuous σ)
    (hσ : ∀ t, (σ t).PosSemidef) (htrace : ∀ t, (σ t).trace = 1)
    (hfix : ∀ t, Kraus.adjointMap (B t) (σ t) = σ t)
    (huniq : ∀ t Z, Kraus.adjointMap (B t) Z = Z → Z.trace = 1 → Z = σ t)
    (K : ∀ t, Matrix (Fin k) (Fin (D t)) ℂ)
    (hK : ∀ t, (K t).IsIsometry)
    (hsupport : ∀ t, K t * (K t)ᴴ = (hσ t).supportProj)
    (A : ∀ t, MPSTensor d (D t))
    (hA : ∀ t i, A t i = (K t)ᴴ * B t i * K t)
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : ∀ t g, rotatePhysical (U g) (A t) = fun i =>
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (t₀ : T) (hInj : Kraus.IsInjective (A t₀)) :
    ∀ᶠ t in 𝓝 t₀, (ω t).CohomologousTo (ω t₀) := by
  exact eventually_cohomologousTo_of_continuousOn_unique_stationary_density
    D ω ρ B hB σ Set.univ isOpen_univ hσcont.continuousOn hσ htrace hfix
    (fun t _ => huniq t) K hK hsupport A hA hUnitary U hCov t₀ (Set.mem_univ t₀) hInj

/-- A continuous unital ambient tensor family with one-dimensional adjoint
fixed space at the base has locally constant minimal virtual class. The
pointwise normalized positive stationary density need not be assumed
continuous, nor must the minimal support frames or virtual actions be
continuous. Injectivity is required only at the base. Continuous ambient
canonical tensors and supported exact covariance remain hypotheses; this
does not construct them from a physical gap. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem eventually_cohomologousTo_of_continuous_unital_supported_family
    {T : Type*} [TopologicalSpace T] {G : Type} [Group G] {d k : ℕ}
    (D : T → ℕ) (ω : T → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (B : T → MPSTensor d k) (hB : Continuous B)
    (hUnital : ∀ t, Kraus.IsUnital (B t))
    (σ : T → Matrix (Fin k) (Fin k) ℂ)
    (hσ : ∀ t, (σ t).PosSemidef) (htrace : ∀ t, (σ t).trace = 1)
    (hfix : ∀ t, Kraus.adjointMap (B t) (σ t) = σ t)
    (K : ∀ t, Matrix (Fin k) (Fin (D t)) ℂ)
    (hK : ∀ t, (K t).IsIsometry)
    (hsupport : ∀ t, K t * (K t)ᴴ = (hσ t).supportProj)
    (A : ∀ t, MPSTensor d (D t))
    (hA : ∀ t i, A t i = (K t)ᴴ * B t i * K t)
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : ∀ t g, rotatePhysical (U g) (A t) = fun i =>
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (t₀ : T)
    (hdim : Module.finrank ℂ
      (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM (B t₀))) = 1)
    (hInj : Kraus.IsInjective (A t₀)) :
    ∀ᶠ t in 𝓝 t₀, (ω t).CohomologousTo (ω t₀) := by
  let : NeZero k := ⟨by
    intro hk
    subst k
    simpa [Matrix.trace] using htrace t₀⟩
  obtain ⟨S, hS, ht₀, hcont, huniq⟩ :=
    exists_open_continuousOn_stationaryDensity_of_unital
      B hB hUnital σ htrace hfix t₀ hdim
  exact eventually_cohomologousTo_of_continuousOn_unique_stationary_density
    D ω ρ B hB σ S hS hcont hσ htrace hfix (fun t ht => (huniq t ht).2)
    K hK hsupport A hA hUnitary U hCov t₀ ht₀ hInj


/-- A unital ambient tensor family continuous at one parameter has locally constant
virtual class on its stationary support, for an arbitrary topological parameter space.
The adjoint fixed space must be one-dimensional at the base, and only the supported
base tensor is required injective. The positive trace-one stationary matrices, full
support frames and virtual representatives need not be continuous. The exact supported
unitary covariance is supplied; no construction from a physical gap is asserted.
Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem eventually_cohomologousTo_of_continuousAt_unital_supported_family
    {T : Type*} [τ : TopologicalSpace T] {G : Type} [Group G] {d k : ℕ}
    (D : T → ℕ) (ω : T → ScalarCocycle G)
    (ρ : ∀ t, ProjectiveRepresentation (D := D t) (ω t))
    (B : T → MPSTensor d k) (t₀ : T) (hB : ContinuousAt B t₀)
    (hUnital : ∀ t, Kraus.IsUnital (B t))
    (σ : T → Matrix (Fin k) (Fin k) ℂ)
    (hσ : ∀ t, (σ t).PosSemidef) (htrace : ∀ t, (σ t).trace = 1)
    (hfix : ∀ t, Kraus.adjointMap (B t) (σ t) = σ t)
    (K : ∀ t, Matrix (Fin k) (Fin (D t)) ℂ)
    (hK : ∀ t, (K t).IsIsometry)
    (hsupport : ∀ t, K t * (K t)ᴴ = (hσ t).supportProj)
    (A : ∀ t, MPSTensor d (D t))
    (hA : ∀ t i, A t i = (K t)ᴴ * B t i * K t)
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin (D t)) (Fin (D t)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hCov : ∀ t g, rotatePhysical (U g) (A t) = fun i =>
      ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ) * A t i *
        ((ρ t).X (g⁻¹) : Matrix (Fin (D t)) (Fin (D t)) ℂ)ᴴ)
    (hdim : Module.finrank ℂ
      (LinearMap.ker (LinearMap.id - Kraus.adjointMapLM (B t₀))) = 1)
    (hInj : Kraus.IsInjective (A t₀)) :
    ∀ᶠ t in 𝓝 t₀, (ω t).CohomologousTo (ω t₀) := by
  have hNhds : @nhds T (τ ⊓ TopologicalSpace.induced B inferInstance) t₀ =
      @nhds T τ t₀ := by
    rw [nhds_inf, nhds_induced, inf_eq_left]
    exact tendsto_iff_comap.mp hB
  let : TopologicalSpace T := τ ⊓ TopologicalSpace.induced B inferInstance
  have hCont : Continuous B := continuous_iff_le_induced.mpr inf_le_right
  have hClass := eventually_cohomologousTo_of_continuous_unital_supported_family
    D ω ρ B hCont hUnital σ hσ htrace hfix K hK hsupport A hA hUnitary U hCov t₀ hdim hInj
  rw [hNhds] at hClass
  exact hClass

end MPSTensor
