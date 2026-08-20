/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.TransferMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Singular value decompositions for (transfer) matrices

This file records singular value decomposition (SVD) existence results for
general complex square matrices and transfer matrices.  They are elementary
linear-algebraic results used in the normal-form development.

Wolf Section 2.4 uses a real SVD only for the `3 × 3` block of a qubit
transfer matrix.  The arbitrary-dimensional complex SVD proved here is more
general and is not attributed to that passage.

* **SVD for PSD matrices.** Every positive semi-definite complex square matrix
  admits a decomposition `M = U * diagonal σ * Uᴴ` with `U` unitary and `σ`
  non-negative; this is the spectral theorem formulated in SVD form.
* **SVD for invertible matrices.** Every invertible complex square matrix
  admits a decomposition `M = U * diagonal σ * Vᴴ` with `U, V` unitary and
  `σ : n → ℝ` strictly positive.

The full Lorentz normal form of Wolf Section 2.4 (Propositions 2.9 and 2.11 for
qubit channels) also requires a compactness argument showing that the infimum
of `tr τ'` over `SL(2, ℂ)` filterings is attained.  That argument is developed
in `TNLean.Channel.LorentzNormalForm`.

The singular values produced here are not sorted and not proven unique;
the applications in Wolf Section 2.4 that require ordered or unique singular
values need corresponding refinements.

## Main results

* `Matrix.svd_of_posSemidef` — SVD existence for positive-semidefinite
  matrices.
* `Matrix.svd_of_isUnit` — SVD existence for invertible complex matrices.
* `transferMatrix_svd_of_isUnit` — SVD existence specialised to invertible
  transfer matrices of linear channel super-operators.

-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace Matrix

section SVD

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **SVD for positive semi-definite matrices** (spectral theorem, formulated).
If `M` is positive semi-definite, then `M = U * diagonal σ * Uᴴ` for a unitary
`U` and some non-negative real sequence `σ`. -/
theorem svd_of_posSemidef {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (σ : n → ℝ),
      (∀ i, 0 ≤ σ i) ∧
      M = (U : Matrix n n ℂ) *
        Matrix.diagonal (fun i => (σ i : ℂ)) *
        (U : Matrix n n ℂ)ᴴ :=
  ⟨hM.isHermitian.eigenvectorUnitary, hM.isHermitian.eigenvalues,
    hM.eigenvalues_nonneg, by
      simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Function.comp_def] using hM.isHermitian.spectral_theorem⟩

/-- **Singular Value Decomposition (invertible case).** Every invertible
complex square matrix admits an SVD
`M = U * diagonal σ * Vᴴ` with `U, V` unitary and `σ` strictly positive. -/
theorem svd_of_isUnit {M : Matrix n n ℂ} (hM : IsUnit M) :
    ∃ (U V : Matrix.unitaryGroup n ℂ) (σ : n → ℝ),
      (∀ i, 0 < σ i) ∧
      M = (U : Matrix n n ℂ) *
        Matrix.diagonal (fun i => (σ i : ℂ)) *
        (V : Matrix n n ℂ)ᴴ := by
  classical
  -- `N := Mᴴ * M` is positive semi-definite; since `M` is invertible, it is
  -- positive definite.
  have hN_psd : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hMh_unit : IsUnit Mᴴ := by
    rw [← Matrix.star_eq_conjTranspose]; exact hM.star
  have hN_unit : IsUnit (Mᴴ * M) := hMh_unit.mul hM
  have hN_pd : (Mᴴ * M).PosDef := hN_psd.posDef_iff_isUnit.mpr hN_unit
  -- Extract spectral data.
  set V : Matrix.unitaryGroup n ℂ := hN_psd.isHermitian.eigenvectorUnitary
  set lam : n → ℝ := hN_psd.isHermitian.eigenvalues
  have hlam_pos : ∀ i, 0 < lam i := fun i => hN_pd.eigenvalues_pos i
  -- Singular values `σ_i = sqrt λ_i`.
  let sig : n → ℝ := fun i => Real.sqrt (lam i)
  have hsig_pos : ∀ i, 0 < sig i := fun i => Real.sqrt_pos.mpr (hlam_pos i)
  have hsig_ne : ∀ i, sig i ≠ 0 := fun i => (hsig_pos i).ne'
  have hsig_sq : ∀ i, (sig i) * (sig i) = lam i := fun i =>
    Real.mul_self_sqrt (hlam_pos i).le
  have hsigC_ne : ∀ i, (sig i : ℂ) ≠ 0 := fun i => by
    exact_mod_cast hsig_ne i
  -- Diagonal factors.
  let Sdiag : Matrix n n ℂ := Matrix.diagonal (fun i => (sig i : ℂ))
  let Sinv : Matrix n n ℂ :=
    Matrix.diagonal (fun i => ((sig i : ℂ))⁻¹)
  have hS_mul_Sinv : Sdiag * Sinv = 1 := by
    simp only [Sdiag, Sinv, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (sig i : ℂ) * ((sig i : ℂ))⁻¹) = fun _ => (1 : ℂ) from ?_]
    · exact Matrix.diagonal_one
    · funext i; field_simp [hsigC_ne i]
  have hSinv_mul_S : Sinv * Sdiag = 1 := by
    simp only [Sdiag, Sinv, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => ((sig i : ℂ))⁻¹ * (sig i : ℂ)) = fun _ => (1 : ℂ) from ?_]
    · exact Matrix.diagonal_one
    · funext i; field_simp [hsigC_ne i]
  have hSinv_herm : Sinvᴴ = Sinv := by
    simp only [Sinv, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  -- Spectral decomposition of `Mᴴ * M`.
  have hSpectral :
      Mᴴ * M = (V : Matrix n n ℂ) *
        Matrix.diagonal (fun i => (lam i : ℂ)) *
        (V : Matrix n n ℂ)ᴴ :=
    by
      simpa [V, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Function.comp_def] using hN_psd.isHermitian.spectral_theorem
  -- Unitarity of V.
  have hVhV : (V : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp V.prop
    simpa [Matrix.star_eq_conjTranspose] using this
  have hVVh : (V : Matrix n n ℂ) * (V : Matrix n n ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp V.prop
    simpa [Matrix.star_eq_conjTranspose] using this
  -- Σ² = diagonal lam as complex matrices.
  have hSsq : Sdiag * Sdiag = Matrix.diagonal (fun i => (lam i : ℂ)) := by
    simp only [Sdiag, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    have : (sig i : ℂ) * (sig i : ℂ) = ((sig i * sig i : ℝ) : ℂ) := by push_cast; ring
    rw [this, hsig_sq]
  -- Define U := M * V * Sinv.
  let Um : Matrix n n ℂ := M * (V : Matrix n n ℂ) * Sinv
  -- Key computation: Umᴴ * Um = 1.
  have hUhU : Umᴴ * Um = 1 := by
    have step_conj : Umᴴ = Sinv * (V : Matrix n n ℂ)ᴴ * Mᴴ := by
      simp only [Um, Matrix.conjTranspose_mul, hSinv_herm]
      noncomm_ring
    rw [step_conj]
    have key :
        Sinv * (V : Matrix n n ℂ)ᴴ * Mᴴ *
          (M * (V : Matrix n n ℂ) * Sinv) =
        Sinv *
          ((V : Matrix n n ℂ)ᴴ * (Mᴴ * M) * (V : Matrix n n ℂ)) *
          Sinv := by noncomm_ring
    rw [key, hSpectral]
    have collapse :
        (V : Matrix n n ℂ)ᴴ *
          ((V : Matrix n n ℂ) *
            Matrix.diagonal (fun i => (lam i : ℂ)) *
            (V : Matrix n n ℂ)ᴴ) *
          (V : Matrix n n ℂ) =
        Matrix.diagonal (fun i => (lam i : ℂ)) := by
      calc (V : Matrix n n ℂ)ᴴ *
            ((V : Matrix n n ℂ) *
              Matrix.diagonal (fun i => (lam i : ℂ)) *
              (V : Matrix n n ℂ)ᴴ) *
            (V : Matrix n n ℂ)
          = ((V : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ)) *
              Matrix.diagonal (fun i => (lam i : ℂ)) *
              ((V : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ)) := by noncomm_ring
        _ = 1 * Matrix.diagonal (fun i => (lam i : ℂ)) * 1 := by rw [hVhV]
        _ = Matrix.diagonal (fun i => (lam i : ℂ)) := by simp
    rw [collapse, ← hSsq]
    calc Sinv * (Sdiag * Sdiag) * Sinv
        = (Sinv * Sdiag) * (Sdiag * Sinv) := by noncomm_ring
      _ = 1 * 1 := by rw [hSinv_mul_S, hS_mul_Sinv]
      _ = 1 := by simp
  -- State U as a unitary group element.
  refine ⟨⟨Um, Matrix.mem_unitaryGroup_iff'.mpr
    (by simpa [Matrix.star_eq_conjTranspose] using hUhU)⟩, V, sig, hsig_pos, ?_⟩
  -- Verify M = Um * Sdiag * Vᴴ.
  change M = Um * Sdiag * (V : Matrix n n ℂ)ᴴ
  have expand :
      Um * Sdiag * (V : Matrix n n ℂ)ᴴ =
        M * ((V : Matrix n n ℂ) * (Sinv * Sdiag) *
          (V : Matrix n n ℂ)ᴴ) := by
    simp only [Um]; noncomm_ring
  rw [expand, hSinv_mul_S]
  calc M = M * 1 := by rw [mul_one]
    _ = M * ((V : Matrix n n ℂ) * (V : Matrix n n ℂ)ᴴ) := by rw [hVVh]
    _ = M * ((V : Matrix n n ℂ) * 1 * (V : Matrix n n ℂ)ᴴ) := by rw [mul_one]

end SVD

end Matrix

/-! ### Transfer-matrix specialisation -/

section TransferMatrixSVD

variable {D : ℕ}

/-- **SVD representation of a transfer matrix.**
Every invertible transfer matrix admits a singular value decomposition
`T̂ = U * diagonal σ * Vᴴ` with `U, V` unitary and `σ` strictly positive.

This is a direct specialisation of `Matrix.svd_of_isUnit` to the
`(Fin D × Fin D)` index type used by `transferMatrix`. -/
theorem transferMatrix_svd_of_isUnit
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsUnit (transferMatrix T)) :
    ∃ (U V : Matrix.unitaryGroup (Fin D × Fin D) ℂ)
      (σ : (Fin D × Fin D) → ℝ),
      (∀ i, 0 < σ i) ∧
      transferMatrix T =
        (U : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) *
          Matrix.diagonal (fun i => (σ i : ℂ)) *
          (V : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)ᴴ :=
  Matrix.svd_of_isUnit (n := Fin D × Fin D) hT

end TransferMatrixSVD
