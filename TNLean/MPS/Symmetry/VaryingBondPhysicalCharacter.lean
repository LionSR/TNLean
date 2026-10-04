/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.FixedBondPhysicalPathInvariance

/-!
# A common physical character when the minimal bond dimension varies

Equality of nonzero periodic MPS rays transfers the physical symmetry
eigenvalue from an ambient tensor to any minimal injective representative.
The coefficients at lengths two and three therefore determine one common
character without requiring the ambient tensor to be injective.

Source context: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Appendix B,
lines 2614–2632, and Appendix C, lines 2653–2717. This removes the scalar
physical character from the independent exact MPS path. It does not
construct continuous canonical virtual supports across changing dimension;
see `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix

namespace LinearMap

/-- Equality of vector spans transfers a scalar eigenvalue. Source context:
arXiv:1010.3732, Appendix B, lines 2614–2632. -/
theorem map_eq_smul_of_span_singleton_eq
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : M →ₗ[ℂ] M) (x y : M) (c : ℂ)
    (hspan : Submodule.span ℂ {x} = Submodule.span ℂ {y}) (hx : f x = c • x) :
    f y = c • y := by
  have hy : y ∈ Submodule.span ℂ {x} := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self y
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
  rw [← ha, map_smul, hx, smul_comm]

end LinearMap

namespace MPSTensor

/-- Twisting the physical tensor applies the sitewise symmetry matrix to
its periodic MPS vector. Source context: arXiv:1010.3732, Appendix B,
lines 2614–2632. -/
theorem mpv_twistedTensor_eq_finKronecker_mulVec
    {G : Type} [Group G] {d D N : ℕ}
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    (mpv (twistedTensor A U g) : (Fin N → Fin d) → ℂ) =
      (Matrix.finKronecker fun _ : Fin N => U g) *ᵥ mpv A := by
  funext σ
  change mpv (rotatePhysical (U g) A) σ = _
  rw [mpv_rotatePhysical]
  rfl

/-- Positive-length ray equality preserves each physical symmetry
eigenvalue, even when the tensor bond dimensions differ. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem SamePositiveMpvRay.symmetry_eigenvalue
    {G : Type} [Group G] {d D₀ D₁ N : ℕ}
    {A : MPSTensor d D₀} {B : MPSTensor d D₁} (hAB : SamePositiveMpvRay A B)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) (c : ℂ) (hN : 0 < N)
    (hA : ∀ σ : Fin N → Fin d, mpv (twistedTensor A U g) σ = c * mpv A σ) :
    ∀ σ : Fin N → Fin d, mpv (twistedTensor B U g) σ = c * mpv B σ := by
  have hcov : (Matrix.finKronecker fun _ : Fin N => U g) *ᵥ mpv A = c • mpv A := by
    rw [← mpv_twistedTensor_eq_finKronecker_mulVec]
    exact funext hA
  have h := LinearMap.map_eq_smul_of_span_singleton_eq
    (Matrix.toLin' (Matrix.finKronecker fun _ : Fin N => U g))
    (mpv A) (mpv B) c (hAB N hN) hcov
  intro σ
  rw [mpv_twistedTensor_eq_finKronecker_mulVec]
  exact congrFun h σ

/-- An independent exact MPS ground-state path has one common scalar
physical character, even when its minimal injective bond dimension changes.
The character is derived from the finite-chain ground lines and does not
occur as a field of the path. Source context: arXiv:1010.3732, Appendix B,
lines 2614–2632, and Appendix C, lines 2653–2717. -/
theorem ExactMPSGroundPath.exists_single_character
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      ∀ t : unitInterval, ∀ g, SameMPV (χ g • Q.tensor t)
        (twistedTensor (Q.tensor t) ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g) := by
  classical
  let V := (Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U
  have hchars : ∀ N, 2 ≤ N → ∃ c : G →* ℂ, (∀ g, ‖c g‖ = 1) ∧
      ∀ t : unitInterval, ∀ g, ∀ σ : Fin N → Fin d,
        mpv (twistedTensor (Q.tensor t) V g) σ = c g * mpv (Q.tensor t) σ :=
    fun _ hN => Q.exists_chain_character_mpv hN
  choose! c hnorm hC using hchars
  obtain ⟨D₀, hD₀, _, A₀, hInj₀, hRay₀⟩ := Q.injective_representative 0 (by simp)
  let : NeZero D₀ := ⟨Nat.ne_of_gt hD₀⟩
  obtain ⟨χ, hχnorm, hχ, _⟩ := exists_character_sameMPV_smul_of_mpv_eq_smul_from_two
    (fun g => twistedTensor A₀ V g) hInj₀ c
    (fun g N hN => hRay₀.symmetry_eigenvalue V g (c N g) (by omega) (hC N hN 0 g)) hnorm
  refine ⟨χ, hχnorm, ?_⟩
  intro t
  obtain ⟨D, hD, _, A, hInj, hRay⟩ := Q.injective_representative t t.property
  let : NeZero D := ⟨Nat.ne_of_gt hD⟩
  obtain ⟨χt, _, hχt, hSame⟩ := exists_character_sameMPV_smul_of_mpv_eq_smul_from_two
    (fun g => twistedTensor A V g) hInj c
    (fun g N hN => hRay.symmetry_eigenvalue V g (c N g) (by omega) (hC N hN t g)) hnorm
  have heq : χt = χ := MonoidHom.ext (fun g => (hχt g).trans (hχ g).symm)
  simp only [heq] at hSame
  intro g N σ
  simp only [Pi.smul_def, mpv_smul]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [mpv, coeff]
  · have hmin : ∀ σ : Fin N → Fin d,
        mpv (twistedTensor A V g) σ = χ g ^ N * mpv A σ := by
      intro σ
      simpa only [Pi.smul_def, mpv_smul] using (hSame g N σ).symm
    exact (hRay.symm.symmetry_eigenvalue V g (χ g ^ N) hN hmin σ).symm

/-- One common physical character rephasing makes the ambient tensors
exactly symmetric, without fixing their minimal injective dimension.
Source context: arXiv:1010.3732, Appendix B, lines 2614–2632,
and Appendix C, lines 2653–2717. -/
theorem ExactMPSGroundPath.exists_exact_symmetry
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁} (Q : ExactMPSGroundPath P) :
    ∃ χ : G →* ℂ, ∃ hχ : ∀ g, ‖χ g‖ = 1,
      ∀ t : unitInterval, IsOnSiteSymmetric (Q.tensor t)
        ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp (physicalCharacterUntwist χ hχ U)) := by
  obtain ⟨χ, hχ, hSame⟩ := Q.exists_single_character
  exact ⟨χ, hχ, fun t => isOnSiteSymmetric_physicalCharacterUntwist χ hχ U (Q.tensor t)
    (hSame t)⟩

end MPSTensor
