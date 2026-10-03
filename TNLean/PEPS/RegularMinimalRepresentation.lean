/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularFourier
import TNLean.PEPS.TorusBlockMultiplicityState
import TNLean.Algebra.SemiRegularGroupAlgebra

/-!
# A multiplicity-one semi-regular representation derived from the finite group

The regular Fourier decomposition supplies actual irreducible unitary matrix
representations with multiplicities equal to their dimensions. Retaining one copy
of every sector gives a unitary semi-regular representation, and each of its sectors
has character multiplicity one. No irreducible enumeration or Fourier decomposition
is assumed: both are chosen from the preceding finite-group existence theorem.

Source: SCP10, Definition 4.5 and Section 7, lines 2947–3019. The universal comparison
with the dimension of every semi-regular representation is a separate consequence.
-/

open scoped Matrix Kronecker
namespace TNLean.PEPS
open Representation
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private theorem minimal_isSemiRegular_of_fourier
    {K : ℕ} (d : Fin K → ℕ)
    (b : OrthonormalBasis ((k : Fin K) × (Fin (d k) × Fin (d k))) ℂ
      (EuclideanSpace ℂ G))
    (D : ∀ k, G →* Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (hfourier : ∀ g, LinearMap.toMatrix b.toBasis b.toBasis
      (euclideanMatrixRepresentation (leftRegularMatrix G) g) =
      multiplicityRestoredRepresentation d D g) :
    IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) := by
  classical
  let ρ := euclideanMatrixRepresentation (leftRegularMatrix G)
  have hLI : LinearIndependent ℂ (fun g => ρ g) :=
    linearIndependent_of_isSemiRegular ρ
      (isSemiRegular_leftRegular.of_equiv (leftRegularEuclideanMatrixEquiv (G := G)))
  apply isSemiRegular_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have hmin : ∑ x : G, c x • blockMatrixRepresentation d D x = 0 := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [map_sum, map_zero]
    simp only [map_smul]
    exact hc
  have hD : ∀ k, ∑ x : G, c x • D k x = 0 := by
    intro k
    ext i j
    have h := congrArg (fun M => M ⟨k, i⟩ ⟨k, j⟩) hmin
    change (∑ x : G, c x • Matrix.blockDiagonal' (fun k => D k x)) ⟨k, i⟩ ⟨k, j⟩ = 0 at h
    simpa only [Matrix.sum_apply, Matrix.smul_apply,
      Matrix.blockDiagonal'_apply_eq, Matrix.zero_apply] using h
  have hrep : ∑ x : G, c x • multiplicityRestoredRepresentation d D x = 0 := by
    ext ⟨k, i, j⟩ ⟨k', i', j'⟩
    change (∑ x : G, c x • Matrix.blockDiagonal'
      (fun k => D k x ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)))
      ⟨k, (i, j)⟩ ⟨k', (i', j')⟩ = 0
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    by_cases hk : k = k'
    · subst k'
      have h := congrArg (fun M => M i i') (hD k)
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply] at h
      simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, smul_eq_mul]
      simp only [smul_eq_mul] at h
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, h, zero_mul]
    · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hk, smul_zero, Finset.sum_const_zero]
  have hρ : ∑ x : G, c x • ρ x = 0 := by
    apply (LinearMap.toMatrixAlgEquiv b.toBasis).injective
    rw [map_sum, map_zero]
    simp only [map_smul]
    change ∑ x : G, c x • LinearMap.toMatrix b.toBasis b.toBasis
      (euclideanMatrixRepresentation (leftRegularMatrix G) x) = 0
    simpa only [hfourier] using hrep
  exact (Fintype.linearIndependent_iff.mp hLI) c hρ g

omit [DecidableEq G] in
private theorem minimal_characterMultiplicity_eq_one
    {K : ℕ} (d : Fin K → ℕ)
    (D : ∀ k, G →* Matrix (Fin (d k)) (Fin (d k)) ℂ)
    (hirr : ∀ k, IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k)))
    (hcross : ∀ k k', k ≠ k' →
      character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k)) ≠
        character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k'))) (k : Fin K) :
    characterMultiplicity
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))
      (character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k))) = 1 := by
  classical
  let ρ : Representation ℂ G ((Σ k, Fin (d k)) → ℂ) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)
  let σ : ∀ k, Representation ℂ G (Fin (d k) → ℂ) :=
    fun k => Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k)
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (natCard_ne_zero_complex (G := G))
  have hchar : ∀ g, ρ.character g = ∑ i, (σ i).character g := by
    intro g
    change LinearMap.trace ℂ _ (Matrix.toLin' (blockMatrixRepresentation d D g)) = _
    rw [Matrix.trace_toLin'_eq]
    change (Matrix.blockDiagonal' (fun i => D i g)).trace = _
    rw [Matrix.trace_blockDiagonal']
    apply Finset.sum_congr rfl
    intro i hi
    exact (Matrix.trace_toLin'_eq (D i g)).symm
  change characterMultiplicity ρ (σ k).character = 1
  unfold characterMultiplicity
  simp_rw [hchar, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  have hterm : ∀ i, (Nat.card G : ℂ)⁻¹ * ∑ g : G,
      (σ i).character g * (σ k).character g⁻¹ = if i = k then 1 else 0 := by
    intro i
    have := hirr i
    have := hirr k
    rw [char_orthonormal]
    by_cases hik : i = k
    · subst i
      rw [ite_eq_left ⟨Representation.Equiv.refl (σ k)⟩, ite_eq_left rfl]
    · rw [ite_eq_right ?_, ite_eq_right hik]
      rintro ⟨e⟩
      exact hcross i k hik (char_iso e).symm
  simp only [hterm]
  simp

/-- The finite group determines a unitary regular Fourier decomposition and a
unitary semi-regular direct sum containing each of its inequivalent irreducible sectors
with multiplicity one. Source: SCP10, Section 7, lines 2947–3019. -/
theorem exists_minimalSemiRegular_leftRegular_fourier :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (b : OrthonormalBasis ((k : Fin K) × (Fin (d k) × Fin (d k))) ℂ
        (EuclideanSpace ℂ G))
      (D : ∀ k, G →* Matrix (Fin (d k)) (Fin (d k)) ℂ),
      (∀ k, 0 < d k) ∧
      (∀ k g, D k g ∈ Matrix.unitaryGroup (Fin (d k)) ℂ) ∧
      (∀ k, IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k))) ∧
      (∀ k k', k ≠ k' →
        character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k)) ≠
          character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k'))) ∧
      (∀ g, LinearMap.toMatrix b.toBasis b.toBasis
        (euclideanMatrixRepresentation (leftRegularMatrix G) g) =
        multiplicityRestoredRepresentation d D g) ∧
      (∀ g, blockMatrixRepresentation d D g ∈
        Matrix.unitaryGroup (Σ k, Fin (d k)) ℂ) ∧
      IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) ∧
      ∀ k, characterMultiplicity
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))
        (character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D k))) = 1 := by
  classical
  obtain ⟨K, d, b, D, hd, hunit, hirr, hcross, hfourier⟩ :=
    exists_unitary_leftRegular_fourier (G := G)
  refine ⟨K, d, b, D, hd, hunit, hirr, hcross, hfourier, ?_,
    minimal_isSemiRegular_of_fourier d b D hfourier,
    minimal_characterMultiplicity_eq_one d D hirr hcross⟩
  intro g
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  change Matrix.blockDiagonal' (fun k => D k g) *
    (Matrix.blockDiagonal' (fun k => D k g))ᴴ = 1
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  convert Matrix.blockDiagonal'_one (m' := fun k : Fin K => Fin (d k)) using 1
  congr 1
  funext k
  exact Matrix.mem_unitaryGroup_iff.mp (hunit k g)
end TNLean.PEPS
