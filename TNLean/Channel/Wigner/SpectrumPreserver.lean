/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianSpectrumPreserver
import TNLean.Channel.Wigner.PureStateCharpoly
import TNLean.Channel.Wigner.Rigidity
import TNLean.Channel.Wigner.TwoPureStateCharpoly

/-!
# Classification of Hermitian spectrum preservers

A complex-linear map on square complex matrices that commutes with the adjoint and preserves the
spectrum as a set on Hermitian matrices is either unitary conjugation or unitary conjugation after
transposition. The proof identifies the images of normalized pure-state matrices, applies Wigner
rigidity to the induced map on projective rays, and extends the resulting equality by complex
linearity.

## Main declaration

* `Projectivization.exists_unitary_conj_or_transpose_of_preserves_hermitian_spectrum`
-/

open scoped LinearAlgebra.Projectivization Matrix

namespace Projectivization

variable {d : ℕ}

/-- A complex-linear adjoint-preserving map that preserves the complex spectrum as a set on every
Hermitian matrix is either unitary conjugation or unitary conjugation after transposition.

This is the corollary "Spectrum preserving maps" in Wolf, Chapter 1, lines 289--296. The
hypothesis `hstar` is Wolf's definition of a Hermitian map at line 290. -/
theorem exists_unitary_conj_or_transpose_of_preserves_hermitian_spectrum
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hstar : ∀ X : Matrix (Fin d) (Fin d) ℂ, T (Xᴴ) = (T X)ᴴ)
    (hSpectrum : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.IsHermitian → spectrum ℂ (T A) = spectrum ℂ A) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      (∀ X, T X = (U : Matrix (Fin d) (Fin d) ℂ) * X *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) ∨
      (∀ X, T X = (U : Matrix (Fin d) (Fin d) ℂ) * Xᵀ *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  have hHermitian : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.IsHermitian → (T A).IsHermitian := by
    intro A hA
    rw [Matrix.IsHermitian, ← hstar A, hA]
  have hcharpoly : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.IsHermitian → (T A).charpoly = A.charpoly :=
    Matrix.charpoly_map_eq_of_preserves_hermitian_spectrum T hHermitian hSpectrum
  have himage : ∀ p : ℙ ℂ (Fin d → ℂ),
      ∃ q : ℙ ℂ (Fin d → ℂ), pureStateMatrix q = T (pureStateMatrix p) := by
    intro p
    have hp : (pureStateMatrix p).IsHermitian :=
      (isOrthogonalProjection_pureStateMatrix p).1
    exact exists_pureStateMatrix_eq_of_isHermitian_charpoly_eq
      (T (pureStateMatrix p)) p (hHermitian _ hp) (hcharpoly _ hp)
  let f : ℙ ℂ (Fin d → ℂ) → ℙ ℂ (Fin d → ℂ) := fun p ↦
    Classical.choose (himage p)
  have hfimage : ∀ p, pureStateMatrix (f p) = T (pureStateMatrix p) := fun p ↦
    Classical.choose_spec (himage p)
  have hftransition : ∀ p q, transitionProbability (f p) (f q) =
      transitionProbability p q := by
    intro p q
    rw [← trace_pureStateMatrix_mul_pureStateMatrix,
      ← trace_pureStateMatrix_mul_pureStateMatrix]
    apply trace_pureStateMatrix_mul_eq_of_charpoly_add_eq
    rw [hfimage, hfimage, ← T.map_add]
    exact hcharpoly _ ((isOrthogonalProjection_pureStateMatrix p).1.add
      (isOrthogonalProjection_pureStateMatrix q).1)
  rcases wigner_rigidity_fin hftransition with ⟨U, hU⟩ | ⟨U, hU⟩
  · let S : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
      { toFun X := (U : Matrix (Fin d) (Fin d) ℂ) * X *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ
        map_add' X Y := by rw [mul_add, add_mul]
        map_smul' c X := by
          simp only [RingHom.id_apply]
          rw [mul_smul_comm, smul_mul_assoc] }
    have hTS : T = S := linearMap_eq_of_eq_on_pureStateMatrix T S fun p ↦ by
      calc
        T (pureStateMatrix p) = pureStateMatrix (f p) := (hfimage p).symm
        _ = pureStateMatrix (unitaryAction U p) := congrArg pureStateMatrix (hU p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * pureStateMatrix p *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := pureStateMatrix_unitaryAction U p
        _ = S (pureStateMatrix p) := rfl
    exact ⟨U, Or.inl (fun X ↦ by rw [hTS]; rfl)⟩
  · let S : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
      { toFun X := (U : Matrix (Fin d) (Fin d) ℂ) * Xᵀ *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ
        map_add' X Y := by rw [Matrix.transpose_add, mul_add, add_mul]
        map_smul' c X := by
          simp only [RingHom.id_apply, Matrix.transpose_smul]
          rw [mul_smul_comm, smul_mul_assoc] }
    have hTS : T = S := linearMap_eq_of_eq_on_pureStateMatrix T S fun p ↦ by
      calc
        T (pureStateMatrix p) = pureStateMatrix (f p) := (hfimage p).symm
        _ = pureStateMatrix (unitaryAction U (coordinateConjugation p)) :=
          congrArg pureStateMatrix (hU p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) *
            pureStateMatrix (coordinateConjugation p) *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ :=
          pureStateMatrix_unitaryAction U (coordinateConjugation p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * (pureStateMatrix p)ᵀ *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
          rw [pureStateMatrix_coordinateConjugation]
        _ = S (pureStateMatrix p) := rfl
    exact ⟨U, Or.inr (fun X ↦ by rw [hTS]; rfl)⟩

end Projectivization
