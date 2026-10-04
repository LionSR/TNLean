/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicShortGapContinuity
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Symmetry.PositiveLengthSymmetryCharacter
import TNLean.MPS.Symmetry.PhysicalCharacterTwist
import TNLean.MPS.Symmetry.GlobalVirtualGauge
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Symmetry characters derived from physical ground lines

Finite-chain ground lines of a continuous exact MPS family inherit a constant
symmetry character from the physical Hamiltonian symmetry. The proof uses
the nonzero continuous MPS vectors and the finite spectrum of each fixed
physical symmetry operator.

Source context: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
lines 930–954, and Appendix B, lines 2614–2632. No continuous virtual
representation is assumed. The varying-support canonical step of Appendix C
remains separate; see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

**Scope restriction (fixed injective bond dimension):** The single-character,
exact-rephasing, virtual-existence, and endpoint-cohomology results require the ambient tensors
of the independent ground-state realization to be one-site injective in
their fixed dimension. They do not prove Appendix C's varying-support step;
see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`. The preceding
finite-chain character results do not carry this restriction.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

namespace Matrix

/-- A nonzero invariant line admits an eigenvalue which is extracted by a
quadratic quotient. Source context: arXiv:1010.3732, Section II.F.2,
lines 930–954. -/
theorem eigenvector_of_mem_span_singleton
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (v : EuclideanSpace ℂ n) (hv : v ≠ 0)
    (hline : toEuclideanLin U v ∈ Submodule.span ℂ {v}) :
    toEuclideanLin U v =
      (inner ℂ v (toEuclideanLin U v) / inner ℂ v v) • v := by
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hline
  rw [← hz, inner_smul_right]
  simp only [mul_div_cancel_right₀ z (inner_self_ne_zero.mpr hv)]

/-- The eigenvalue on a continuous nonzero invariant line is constant on a
connected parameter space, since the fixed physical operator has finite
spectrum. Source context: arXiv:1010.3732, Section II.F.2, lines 930–954. -/
theorem eigenvalue_constant_of_continuous_invariant_line
    {T n : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (v : T → EuclideanSpace ℂ n) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0)
    (hline : ∀ t, toEuclideanLin U (v t) ∈ Submodule.span ℂ {v t})
    (t t₀ : T) :
    inner ℂ (v t) (toEuclideanLin U (v t)) / inner ℂ (v t) (v t) =
      inner ℂ (v t₀) (toEuclideanLin U (v t₀)) / inner ℂ (v t₀) (v t₀) := by
  let c : T → ℂ := fun t => inner ℂ (v t) (toEuclideanLin U (v t)) / inner ℂ (v t) (v t)
  have hcov (t : T) : toEuclideanLin U (v t) = c t • v t :=
    eigenvector_of_mem_span_singleton U (v t) (hne t) (hline t)
  have hspec (t : T) : c t ∈ spectrum ℂ U := by
    rw [← spectrum_toLpLin (A := U) 2]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hcov t), hne t⟩).mem_spectrum
  have hc : Continuous c :=
    (hv.inner ((toEuclideanLin U).continuous_of_finiteDimensional.comp hv)).div
      (hv.inner hv) (fun t => inner_self_ne_zero.mpr (hne t))
  let cs : T → spectrum ℂ U := fun t => ⟨c t, hspec t⟩
  exact congrArg Subtype.val (TotallyDisconnectedSpace.eq_of_continuous cs
    (hc.subtype_mk _) t t₀)

/-- A continuous nonzero invariant vector family carries a constant unitary
character of the physical representation. Source context:
arXiv:1010.3732, Section II.F.2, lines 930–954. -/
theorem exists_constant_character_of_continuous_invariant_line
    {T G n : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ unitaryGroup n ℂ)
    (v : T → EuclideanSpace ℂ n) (hv : Continuous v) (hne : ∀ t, v t ≠ 0)
    (hline : ∀ t g, toEuclideanLin (U g) (v t) ∈ Submodule.span ℂ {v t})
    (t₀ : T) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      ∀ t g, toEuclideanLin (U g) (v t) = χ g • v t := by
  let c : G → ℂ := fun g =>
    inner ℂ (v t₀) (toEuclideanLin (U g) (v t₀)) / inner ℂ (v t₀) (v t₀)
  have hcov (t : T) (g : G) : toEuclideanLin (U g) (v t) = c g • v t := by
    rw [eigenvector_of_mem_span_singleton (U g) (v t) (hne t) (hline t g),
      eigenvalue_constant_of_continuous_invariant_line (U g) v hv hne
        (fun t => hline t g) t t₀]
  let χ : G →* ℂ :=
    { toFun := c
      map_one' := by
        apply smul_left_injective ℂ (hne t₀)
        simpa only [map_one, toLpLin_one, LinearMap.id_apply, one_smul] using (hcov t₀ 1).symm
      map_mul' := by
        intro g h
        apply smul_left_injective ℂ (hne t₀)
        calc
          c (g * h) • v t₀ = toEuclideanLin (U (g * h)) (v t₀) := (hcov t₀ (g * h)).symm
          _ = toEuclideanLin (U g) (toEuclideanLin (U h) (v t₀)) := by
            simp only [map_mul, toLpLin_mul_same, LinearMap.comp_apply]
          _ = c h • (c g • v t₀) := by rw [hcov t₀ h, map_smul, hcov t₀ g]
          _ = (c g * c h) • v t₀ := by rw [smul_smul, mul_comm] }
  refine ⟨χ, ?_, hcov⟩
  intro g
  have hspec : c g ∈ spectrum ℂ (U g) := by
    rw [← spectrum_toLpLin (A := U g) 2]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hcov t₀ g), hne t₀⟩).mem_spectrum
  exact spectrum.norm_eq_one_of_unitary (hU g) hspec

end Matrix

namespace MPSTensor

/-- A commuting physical operator preserves a one-dimensional eigenspace.
Source context: arXiv:1010.3732, Section II.F.2, lines 930–954. -/
theorem mem_span_mpv_of_commute_ground_line
    {d D N : ℕ} (A : MPSTensor d D)
    (H W : MPOTensor.ChainOperator d N) (E : ℝ)
    (hComm : Commute H W)
    (hline : LinearMap.ker (Matrix.toEuclideanLin (H - (E : ℂ) • 1)) =
      Submodule.span ℂ
        {(WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv A)}) :
    Matrix.toEuclideanLin W
        ((WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv A)) ∈
      Submodule.span ℂ
        {(WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv A)} := by
  let v := (WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv A)
  have hv : Matrix.toEuclideanLin (H - (E : ℂ) • 1) v = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hline]
    exact Submodule.mem_span_singleton_self v
  have hCommE : Commute (H - (E : ℂ) • 1) W :=
    hComm.sub_left (by
      change ((E : ℂ) • 1) * W = W * ((E : ℂ) • 1)
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
  rw [← hline, LinearMap.mem_ker]
  have h := congrArg (fun M => Matrix.toEuclideanLin M v) hCommE.eq
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply, hv, map_zero] using h

/-- The unique finite-chain ground lines of an independent exact MPS path
carry a constant unitary character of the on-site symmetry. This conclusion
uses the physical symmetry field, rather than an assumed tensor symmetry.
Source context: arXiv:1010.3732, Section II.F.2, lines 930–954. -/
theorem ExactMPSGroundPath.exists_chain_character
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      ∀ t : unitInterval, ∀ g,
        Matrix.toEuclideanLin
            (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ))
            ((WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv (Q.tensor t))) =
          χ g • ((WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv (Q.tensor t))) := by
  let V : G →* Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ :=
    { toFun := fun g => Matrix.finKronecker fun _ : Fin N =>
        (U g : Matrix (Fin d) (Fin d) ℂ)
      map_one' := by simp
      map_mul' := by
        intro g h
        simp only [map_mul, Submonoid.coe_mul, ← Matrix.finKronecker_mul] }
  have hV : ∀ g, V g ∈ Matrix.unitaryGroup (Fin N → Fin d) ℂ := by
    intro g
    rw [Matrix.mem_unitaryGroup_iff']
    exact Matrix.finKronecker_conjTranspose_mul_self
      (Matrix.mem_unitaryGroup_iff'.mp (SetLike.coe_mem (U g)))
  let v : unitInterval → EuclideanSpace ℂ (Fin N → Fin d) := fun t =>
    (WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm (mpv (Q.tensor t))
  have hv : Continuous v := continuous_mpvES_family (fun t : unitInterval => Q.tensor t)
    (Q.continuous.comp_continuous continuous_subtype_val (fun t => t.property)) N
  have hne : ∀ t, v t ≠ 0 := by
    intro t hzero
    apply Q.nonzero t t.property N (by omega)
    simpa only [v, map_zero, LinearEquiv.apply_symm_apply] using
      congrArg (WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)) hzero
  apply Matrix.exists_constant_character_of_continuous_invariant_line V hV v hv hne
    (t₀ := 0)
  intro t g
  obtain ⟨E, _, _, hline⟩ := Q.ground_line t t.property N hN
  exact mem_span_mpv_of_commute_ground_line (Q.tensor t)
    (interactionHamiltonian (P.interaction t) hN) (V g) E
    (P.symmetric t t.property g N hN) hline

/-- The constant finite-chain character acts on periodic MPS coefficients.
Source context: arXiv:1010.3732, Appendix B, lines 2614–2632. -/
theorem ExactMPSGroundPath.exists_chain_character_mpv
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    {N : ℕ} (hN : 2 ≤ N) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      ∀ t : unitInterval, ∀ g, ∀ σ : Fin N → Fin d,
        mpv (twistedTensor (Q.tensor t) ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g) σ =
          χ g * mpv (Q.tensor t) σ := by
  obtain ⟨χ, hχ, hcov⟩ := Q.exists_chain_character hN
  refine ⟨χ, hχ, ?_⟩
  intro t g σ
  have h := congrArg (fun v : EuclideanSpace ℂ (Fin N → Fin d) => v σ) (hcov t g)
  change ((Matrix.finKronecker fun _ : Fin N =>
    (U g : Matrix (Fin d) (Fin d) ℂ)) *ᵥ mpv (Q.tensor t)) σ =
      χ g * mpv (Q.tensor t) σ at h
  change mpv (rotatePhysical (U g : Matrix (Fin d) (Fin d) ℂ) (Q.tensor t)) σ = _
  rw [mpv_rotatePhysical]
  simpa only [Matrix.mulVec, dotProduct, Matrix.finKronecker_apply] using h

/-- When the continuous ambient tensors themselves are one-site injective,
one character accounts for the scalar physical symmetry at every parameter
and every chain length.
Source context: arXiv:1010.3732, Section II.F.2, lines 930–954,
and Appendix B, lines 2614–2632. -/
theorem ExactMPSGroundPath.exists_single_character_of_isInjective
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    (hInj : ∀ t : unitInterval, Kraus.IsInjective (Q.tensor t)) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      ∀ t : unitInterval, ∀ g, SameMPV (χ g • Q.tensor t)
        (twistedTensor (Q.tensor t) ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g) := by
  classical
  let : NeZero Q.bondDimension := ⟨Nat.ne_of_gt Q.bondDimension_pos⟩
  have hchars : ∀ N, 2 ≤ N → ∃ c : G →* ℂ, (∀ g, ‖c g‖ = 1) ∧
      ∀ t : unitInterval, ∀ g, ∀ σ : Fin N → Fin d,
        mpv (twistedTensor (Q.tensor t) ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g) σ =
          c g * mpv (Q.tensor t) σ := fun _ hN => Q.exists_chain_character_mpv hN
  choose! c hnorm hC using hchars
  obtain ⟨χ, hχnorm, hχ, _⟩ := exists_character_sameMPV_smul_of_mpv_eq_smul_from_two
    (fun g => twistedTensor (Q.tensor 0) ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g)
    (hInj 0) c (fun g N hN => hC N hN 0 g) hnorm
  refine ⟨χ, hχnorm, ?_⟩
  intro t
  obtain ⟨χt, _, hχt, hSame⟩ := exists_character_sameMPV_smul_of_mpv_eq_smul_from_two
    (fun g => twistedTensor (Q.tensor t) ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g)
    (hInj t) c (fun g N hN => hC N hN t g) hnorm
  have heq : χt = χ := MonoidHom.ext (fun g => (hχt g).trans (hχ g).symm)
  simpa only [heq] using hSame

/-- A single physical character change makes every tensor in a fixed
injective ambient realization exactly on-site symmetric. The character
is derived from the physical ground lines. Source context:
arXiv:1010.3732, Section II.F.2, lines 930–1063, and Appendix B,
lines 2614–2632. -/
theorem ExactMPSGroundPath.exists_exact_symmetry_of_isInjective
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    (hInj : ∀ t : unitInterval, Kraus.IsInjective (Q.tensor t)) :
    ∃ χ : G →* ℂ, ∃ hχ : ∀ g, ‖χ g‖ = 1,
      ∀ t : unitInterval, IsOnSiteSymmetric (Q.tensor t)
        ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp (physicalCharacterUntwist χ hχ U)) := by
  obtain ⟨χ, hχ, hSame⟩ := Q.exists_single_character_of_isInjective hInj
  exact ⟨χ, hχ, fun t => isOnSiteSymmetric_physicalCharacterUntwist χ hχ U (Q.tensor t)
    (hSame t)⟩

open TNLean.Algebra

/-- Continuous virtual projective data and endpoint cohomology can be
derived from the independent physical ground-state realization when its
ambient tensors are one-site injective. Source context:
arXiv:1010.3732, Section II.F.2, lines 930–1063, and Appendix B,
lines 2614–2632. -/
theorem ExactMPSGroundPath.exists_continuous_virtual_data_of_isInjective
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    (hInj : ∀ t : unitInterval, Kraus.IsInjective (Q.tensor t)) :
    ∃ χ : G →* ℂ, ∃ hχ : ∀ g, ‖χ g‖ = 1,
    ∃ ω : unitInterval → ScalarCocycle G,
    ∃ ρ : ∀ t, ProjectiveRepresentation (D := Q.bondDimension) (ω t),
      (∀ g, Continuous fun t =>
        ((ρ t).X g : Matrix (Fin Q.bondDimension) (Fin Q.bondDimension) ℂ)) ∧
      (∀ g h, Continuous fun t => (ω t g h : ℂ)) ∧
      (∀ (t : unitInterval) g i, twistedTensor (Q.tensor t)
        ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp (physicalCharacterUntwist χ hχ U)) g i =
        ((ρ t).X (g⁻¹) : Matrix (Fin Q.bondDimension) (Fin Q.bondDimension) ℂ) * Q.tensor t i *
          ((((ρ t).X (g⁻¹))⁻¹ : GL (Fin Q.bondDimension) ℂ) :
            Matrix (Fin Q.bondDimension) (Fin Q.bondDimension) ℂ)) ∧
      (ω 1).CohomologousTo (ω 0) := by
  obtain ⟨χ, hχ, hSym⟩ := Q.exists_exact_symmetry_of_isInjective hInj
  obtain ⟨ω, ρ, hcont, hfactor, hCov⟩ :=
    exists_continuous_projectiveRepresentation_of_isOnSiteSymmetric Q.bondDimension_pos
      (fun t : unitInterval => Q.tensor t)
      (Q.continuous.comp_continuous continuous_subtype_val (fun t => t.property)) hInj
      ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp (physicalCharacterUntwist χ hχ U)) hSym
  refine ⟨χ, hχ, ω, ρ, hcont, hfactor, hCov, ?_⟩
  exact invertible_projectivePath_factor_endpoints_cohomologous Q.bondDimension_pos
    (fun t g => ((ρ t).X g : Matrix (Fin Q.bondDimension) (Fin Q.bondDimension) ℂ)) ω hcont
    (fun t g => ((ρ t).X g).det_ne_zero) (fun t => (ρ t).map_mul)

/-- Endpoint virtual classes are equal for a physical exact MPS path whose
continuous ambient tensors are one-site injective. No continuous virtual
family is supplied. The endpoint representations are arbitrary choices for
the derived common character rephasing and are compared by gauge uniqueness.
Source context: arXiv:1010.3732, Section II.F.2, lines 930–1063,
and Appendix B, lines 2614–2632. -/
theorem ExactMPSGroundPath.exists_rephasing_endpoint_cohomology_of_isInjective
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P)
    (hInj : ∀ t : unitInterval, Kraus.IsInjective (Q.tensor t)) :
    ∃ χ : G →* ℂ, ∃ hχ : ∀ g, ‖χ g‖ = 1,
      ∀ {ω₀ ω₁ : ScalarCocycle G},
        ∀ (ρ₀ : ProjectiveRepresentation (D := Q.bondDimension) ω₀)
          (ρ₁ : ProjectiveRepresentation (D := Q.bondDimension) ω₁),
        (∀ g i, twistedTensor (Q.tensor 0)
          ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp (physicalCharacterUntwist χ hχ U)) g i =
          (ρ₀.X (g⁻¹) : Matrix (Fin Q.bondDimension) (Fin Q.bondDimension) ℂ) * Q.tensor 0 i *
            (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin Q.bondDimension) ℂ) :
              Matrix (Fin Q.bondDimension) (Fin Q.bondDimension) ℂ)) →
        (∀ g i, twistedTensor (Q.tensor 1)
          ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp (physicalCharacterUntwist χ hχ U)) g i =
          (ρ₁.X (g⁻¹) : Matrix (Fin Q.bondDimension) (Fin Q.bondDimension) ℂ) * Q.tensor 1 i *
            (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin Q.bondDimension) ℂ) :
              Matrix (Fin Q.bondDimension) (Fin Q.bondDimension) ℂ)) →
        ω₁.CohomologousTo ω₀ := by
  obtain ⟨χ, hχ, hSym⟩ := Q.exists_exact_symmetry_of_isInjective hInj
  refine ⟨χ, hχ, ?_⟩
  intro ω₀ ω₁ ρ₀ ρ₁ hρ₀ hρ₁
  exact cohomologousTo_of_continuous_isOnSiteSymmetric_tensorPath Q.bondDimension_pos
    (fun t : unitInterval => Q.tensor t)
    (Q.continuous.comp_continuous continuous_subtype_val (fun t => t.property)) hInj
    ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp (physicalCharacterUntwist χ hχ U))
    hSym ρ₀ ρ₁ hρ₀ hρ₁

end MPSTensor
