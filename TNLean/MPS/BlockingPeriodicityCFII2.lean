/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.MPS.IrreducibleFormII
import TNLean.MPS.BlockingTransfer
import TNLean.MPS.FixedPointInvariantProjection
import TNLean.Channel.PeripheralClosureFixedPoint
import TNLean.Channel.PeriodicityRemoval
import TNLean.Channel.ConjugationSpectrum

import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas



/-!
# Blocking periodicity removal in the CFII setting (diagonal √-gauge)

This file implements the Appendix-A periodicity-removal argument in the *CFII* situation:
starting from a trace-preserving (TP) irreducible tensor `A`, we:

1. use `exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor` to obtain
   a unitary conjugate `B` with a diagonal positive-definite fixed point `Λ` of its transfer map;
2. unitalize via the diagonal similarity transform `C i = Λ^{-1/2} B i Λ^{1/2}`;
3. apply the channel-level root-of-unity lemma for irreducible unital maps with an adjoint
   fixed point;
4. choose a common power killing all peripheral eigenvalues, and conclude primitivity after
   physical blocking.

The main theorem is
`MPSTensor.exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor_CFII`.

## Status

This file is retained as a fully compiling archival Appendix-A route. The
stable library surface now keeps only
`TNLean.MPS.BlockingPeriodicityCFII_viaAdjoint` as the live blocking module,
so this file remains intentionally excluded from `TNLean.lean`.

No stable in-repo module currently depends on this older CFII development
exactly, but we keep the full file as a checked alternate proof instead of
collapsing it to a thinner compatibility wrapper.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace MPSTensor

open Matrix Finset Complex

variable {d D : ℕ}

/-! ## Diagonal square roots -/

section DiagonalSqrt

/-- `diagSqrt Λ` is the diagonal matrix whose diagonal entries are `√(re (Λ i i))`.

This is intended for diagonal positive definite `Λ`, where `Λ i i` is a positive real number
(viewed in `ℂ`). -/
noncomputable def diagSqrt (Λ : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal (fun i => ((Real.sqrt (Λ i i).re : ℝ) : ℂ))

/-- `diagInvSqrt Λ` is the diagonal matrix whose diagonal entries are `1 / √(re (Λ i i))`.

This is intended as the inverse of `diagSqrt Λ` for diagonal positive definite `Λ`. -/
noncomputable def diagInvSqrt (Λ : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal (fun i => ((1 / Real.sqrt (Λ i i).re : ℝ) : ℂ))

@[simp] lemma diagSqrt_conjTranspose (Λ : Matrix (Fin D) (Fin D) ℂ) :
    (diagSqrt (D := D) Λ)ᴴ = diagSqrt (D := D) Λ := by
  classical
  simp [diagSqrt, Matrix.diagonal_conjTranspose]

@[simp] lemma diagInvSqrt_conjTranspose (Λ : Matrix (Fin D) (Fin D) ℂ) :
    (diagInvSqrt (D := D) Λ)ᴴ = diagInvSqrt (D := D) Λ := by
  classical
  simp [diagInvSqrt, Matrix.diagonal_conjTranspose]

private lemma diag_eq_of_lt_zero_lt {z : ℂ} (hz : 0 < z) : ((z.re : ℝ) : ℂ) = z := by
  have h := (Complex.lt_def).1 hz
  -- `h : 0 < z.re ∧ (0:ℂ).im = z.im`
  have hz_im : z.im = 0 := by simpa using h.2.symm
  refine Complex.ext ?_ ?_
  · simp
  · -- imaginary parts
    simp [hz_im]

/-- For a positive definite matrix, the diagonal entries are real and positive. -/
private lemma re_pos_of_posDef_diag (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛ : Λ.PosDef) (i : Fin D) :
    0 < (Λ i i).re := by
  have hpos : (0 : ℂ) < Λ i i := Matrix.PosDef.diag_pos hΛ
  exact (Complex.lt_def).1 hpos |>.1

/-- `diagSqrt Λ * diagSqrt Λ = Λ` for diagonal positive definite `Λ`. -/
lemma diagSqrt_mul_self_of_posDef_of_isDiag
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛ : Λ.PosDef) (hDiag : Λ.IsDiag) :
    diagSqrt (D := D) Λ * diagSqrt (D := D) Λ = Λ := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    have hre_pos : 0 < (Λ i i).re := re_pos_of_posDef_diag (D := D) Λ hΛ i
    have hre_nonneg : 0 ≤ (Λ i i).re := le_of_lt hre_pos
    have hs : Real.sqrt (Λ i i).re * Real.sqrt (Λ i i).re = (Λ i i).re :=
      Real.mul_self_sqrt hre_nonneg
    have hcast : ((Real.sqrt (Λ i i).re : ℝ) : ℂ) * ((Real.sqrt (Λ i i).re : ℝ) : ℂ) =
        ((Λ i i).re : ℂ) := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hs
      simpa [Complex.ofReal_mul] using this
    have hΛii : ((Λ i i).re : ℂ) = Λ i i :=
      diag_eq_of_lt_zero_lt (z := Λ i i) (Matrix.PosDef.diag_pos hΛ)
    have hscalar :
        ((Real.sqrt (Λ i i).re : ℝ) : ℂ) * ((Real.sqrt (Λ i i).re : ℝ) : ℂ) = Λ i i := by
      simpa [hΛii] using hcast
    simpa [diagSqrt] using hscalar
  · have hΛij : Λ i j = 0 := hDiag hij
    simp [diagSqrt, hij, hΛij]

/-- `diagSqrt Λ * diagInvSqrt Λ = 1` for positive definite `Λ`. -/
lemma diagSqrt_mul_diagInvSqrt_of_posDef
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛ : Λ.PosDef) :
    diagSqrt (D := D) Λ * diagInvSqrt (D := D) Λ = 1 := by
  classical
  rw [diagSqrt, diagInvSqrt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  have hre_pos : 0 < (Λ i i).re := re_pos_of_posDef_diag (D := D) Λ hΛ i
  have hsqrt_ne : Real.sqrt (Λ i i).re ≠ 0 := (Real.sqrt_ne_zero'.2 hre_pos)
  have hs : Real.sqrt (Λ i i).re * (1 / Real.sqrt (Λ i i).re) = (1 : ℝ) := by
    simpa using (mul_one_div_cancel hsqrt_ne)
  have := congrArg (fun r : ℝ => (r : ℂ)) hs
  simpa [Complex.ofReal_mul, Complex.ofReal_div] using this

/-- `diagInvSqrt Λ * diagSqrt Λ = 1` for positive definite `Λ`. -/
lemma diagInvSqrt_mul_diagSqrt_of_posDef
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛ : Λ.PosDef) :
    diagInvSqrt (D := D) Λ * diagSqrt (D := D) Λ = 1 := by
  classical
  rw [diagInvSqrt, diagSqrt, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  have hre_pos : 0 < (Λ i i).re := re_pos_of_posDef_diag (D := D) Λ hΛ i
  have hsqrt_ne : Real.sqrt (Λ i i).re ≠ 0 := (Real.sqrt_ne_zero'.2 hre_pos)
  have hs : (1 / Real.sqrt (Λ i i).re) * Real.sqrt (Λ i i).re = (1 : ℝ) := by
    simpa using (one_div_mul_cancel hsqrt_ne)
  have := congrArg (fun r : ℝ => (r : ℂ)) hs
  simpa [Complex.ofReal_mul, Complex.ofReal_div] using this

end DiagonalSqrt

/-! ## Unitalization by a diagonal fixed point -/

section Unitalize

/-- Similarity-transformed tensor `C i = Λ^{-1/2} B i Λ^{1/2}` (diagonal version). -/
noncomputable def unitalize (B : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ) : MPSTensor d D :=
  fun i => diagInvSqrt (D := D) Λ * B i * diagSqrt (D := D) Λ

/-- If `Λ` is a positive definite fixed point of `transferMap B`, then `unitalize B Λ` is unital. -/
lemma unitalize_isUnitalKraus_of_fixedPoint
    (B : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛ : Λ.PosDef) (hDiag : Λ.IsDiag)
    (hfix : transferMap (d := d) (D := D) B Λ = Λ) :
    KadisonSchwarz.IsUnitalKraus (d := d) (D := D) (unitalize (d := d) (D := D) B Λ) := by
  classical
  let S : Matrix (Fin D) (Fin D) ℂ := diagSqrt (D := D) Λ
  let Sinv : Matrix (Fin D) (Fin D) ℂ := diagInvSqrt (D := D) Λ
  have hS_mul : S * S = Λ := by
    simpa [S] using diagSqrt_mul_self_of_posDef_of_isDiag (D := D) (Λ := Λ) hΛ hDiag
  have hS_herm : Sᴴ = S := by simp [S]
  have hSinv_herm : Sinvᴴ = Sinv := by simp [Sinv]
  have hSSinv : S * Sinv = 1 := by
    simpa [S, Sinv] using diagSqrt_mul_diagInvSqrt_of_posDef (D := D) (Λ := Λ) hΛ
  have hSinvS : Sinv * S = 1 := by
    simpa [S, Sinv] using diagInvSqrt_mul_diagSqrt_of_posDef (D := D) (Λ := Λ) hΛ
  have hInvΛ : Sinv * Λ * Sinv = 1 := by
    calc
      Sinv * Λ * Sinv = Sinv * (S * S) * Sinv := by simp [hS_mul]
      _ = (Sinv * S) * (S * Sinv) := by simp [Matrix.mul_assoc]
      _ = 1 := by simp [hSinvS, hSSinv]
  -- Unfold unitality.
  -- (This is just the defining equation.)
  simpa [KadisonSchwarz.IsUnitalKraus, unitalize, S, Sinv] using (show
      (∑ i : Fin d, (Sinv * B i * S) * (Sinv * B i * S)ᴴ = (1 : Matrix (Fin D) (Fin D) ℂ)) from by
    calc
      ∑ i : Fin d, (Sinv * B i * S) * (Sinv * B i * S)ᴴ
        = ∑ i : Fin d, Sinv * (B i * Λ * (B i)ᴴ) * Sinv := by
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              (Sinv * B i * S) * (Sinv * B i * S)ᴴ
                  = Sinv * B i * (S * S) * (B i)ᴴ * Sinv := by
                        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, hS_herm, hSinv_herm]
              _ = Sinv * (B i * Λ * (B i)ᴴ) * Sinv := by
                        simp [Matrix.mul_assoc, hS_mul]
    _ = Sinv * (∑ i : Fin d, B i * Λ * (B i)ᴴ) * Sinv := by
          simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    _ = Sinv * transferMap (d := d) (D := D) B Λ * Sinv := by
          simp [MPSTensor.transferMap_apply, Matrix.mul_assoc]
    _ = Sinv * Λ * Sinv := by simp [hfix]
    _ = 1 := by simp [hInvΛ]
  )

/-- If `B` is trace-preserving and `Λ` is positive definite diagonal, then the adjoint map of the
unitalized tensor fixes `Λ`. -/
lemma unitalize_adjoint_fixedPoint_of_TP
    (B : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛ : Λ.PosDef) (hDiag : Λ.IsDiag)
    (hTP : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    Kraus.adjointMap (unitalize (d := d) (D := D) B Λ) Λ = Λ := by
  classical
  let S : Matrix (Fin D) (Fin D) ℂ := diagSqrt (D := D) Λ
  let Sinv : Matrix (Fin D) (Fin D) ℂ := diagInvSqrt (D := D) Λ
  have hS_mul : S * S = Λ := by
    simpa [S] using diagSqrt_mul_self_of_posDef_of_isDiag (D := D) (Λ := Λ) hΛ hDiag
  have hS_herm : Sᴴ = S := by simp [S]
  have hSinv_herm : Sinvᴴ = Sinv := by simp [Sinv]
  have hSSinv : S * Sinv = 1 := by
    simpa [S, Sinv] using diagSqrt_mul_diagInvSqrt_of_posDef (D := D) (Λ := Λ) hΛ
  have hSinvS : Sinv * S = 1 := by
    simpa [S, Sinv] using diagInvSqrt_mul_diagSqrt_of_posDef (D := D) (Λ := Λ) hΛ
  have hInvΛ : Sinv * Λ * Sinv = 1 := by
    calc
      Sinv * Λ * Sinv = Sinv * (S * S) * Sinv := by simp [hS_mul]
      _ = (Sinv * S) * (S * Sinv) := by simp [Matrix.mul_assoc]
      _ = 1 := by simp [hSinvS, hSSinv]
  -- Expand `Kraus.adjointMap`.
  change ∑ i : Fin d,
        (unitalize (d := d) (D := D) B Λ i)ᴴ * Λ * (unitalize (d := d) (D := D) B Λ i) = Λ
  calc
    ∑ i : Fin d,
        (unitalize (d := d) (D := D) B Λ i)ᴴ * Λ * (unitalize (d := d) (D := D) B Λ i)
        = ∑ i : Fin d, (S * (B i)ᴴ * Sinv) * Λ * (Sinv * B i * S) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [unitalize, S, Sinv, Matrix.conjTranspose_mul, Matrix.mul_assoc,
              hS_herm, hSinv_herm]
    _ = ∑ i : Fin d, S * ((B i)ᴴ * (Sinv * Λ * Sinv) * B i) * S := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [Matrix.mul_assoc]
    _ = ∑ i : Fin d, S * ((B i)ᴴ * B i) * S := by
          simp [hInvΛ, Matrix.mul_assoc]
    _ = S * (∑ i : Fin d, (B i)ᴴ * B i) * S := by
          simp [Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
    _ = S * 1 * S := by simp [hTP]
    _ = Λ := by simp [hS_mul]

end Unitalize

/-! ## Similarity on `Matrix` as a vector space -/

section Similarity

/-- The linear equivalence `X ↦ L * X * R` with inverse `X ↦ Linv * X * Rinv`. -/
noncomputable def mulLeftRightLinearEquiv
    (L R Linv Rinv : Matrix (Fin D) (Fin D) ℂ)
    (hLL : L * Linv = 1) (hL : Linv * L = 1)
    (hRR : R * Rinv = 1) (hR : Rinv * R = 1) :
    Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  LinearEquiv.ofLinear
    (LinearMap.mulLeftRight ℂ (L, R))
    (LinearMap.mulLeftRight ℂ (Linv, Rinv))
    (by
      ext X i j
      have hmat : L * (Linv * X * Rinv) * R = X := by
        calc
          L * (Linv * X * Rinv) * R
              = ((L * (Linv * X)) * Rinv) * R := by
                    rw [← Matrix.mul_assoc L (Linv * X) Rinv]
          _ = (((L * Linv) * X) * Rinv) * R := by
                rw [← Matrix.mul_assoc L Linv X]
          _ = ((L * Linv) * X) * (Rinv * R) := by
                simp [Matrix.mul_assoc]
          _ = X := by
                simp [hLL, hR]
      simpa [LinearMap.mulLeftRight_apply, Matrix.mul_assoc] using congrArg (fun M => M i j) hmat)
    (by
      ext X i j
      have hmat : Linv * (L * X * R) * Rinv = X := by
        calc
          Linv * (L * X * R) * Rinv
              = ((Linv * (L * X)) * R) * Rinv := by
                    rw [← Matrix.mul_assoc Linv (L * X) R]
          _ = (((Linv * L) * X) * R) * Rinv := by
                rw [← Matrix.mul_assoc Linv L X]
          _ = ((Linv * L) * X) * (R * Rinv) := by
                simp [Matrix.mul_assoc]
          _ = X := by
                simp [hL, hRR]
      simpa [LinearMap.mulLeftRight_apply, Matrix.mul_assoc] using congrArg (fun M => M i j) hmat)

@[simp] lemma mulLeftRightLinearEquiv_apply
    (L R Linv Rinv : Matrix (Fin D) (Fin D) ℂ)
    (hLL : L * Linv = 1) (hL : Linv * L = 1)
    (hRR : R * Rinv = 1) (hR : Rinv * R = 1)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    mulLeftRightLinearEquiv (D := D) L R Linv Rinv hLL hL hRR hR X = L * X * R := by
  simp [mulLeftRightLinearEquiv, LinearEquiv.ofLinear_apply, LinearMap.mulLeftRight_apply]

@[simp] lemma mulLeftRightLinearEquiv_symm_apply
    (L R Linv Rinv : Matrix (Fin D) (Fin D) ℂ)
    (hLL : L * Linv = 1) (hL : Linv * L = 1)
    (hRR : R * Rinv = 1) (hR : Rinv * R = 1)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (mulLeftRightLinearEquiv (D := D) L R Linv Rinv hLL hL hRR hR).symm X = Linv * X * Rinv := by
  simp [mulLeftRightLinearEquiv, LinearEquiv.ofLinear_symm_apply, LinearMap.mulLeftRight_apply]

end Similarity

/-! ## Support projector: kernel inclusion and range equality -/

section SupportProj

/-- If `ρ` is PSD and `ρ *ᵥ v = 0`, then the support projector also kills `v`.

This is the key kernel inclusion `ker(ρ) ≤ ker(supportProj ρ)`. -/
lemma supportProj_mulVec_eq_zero_of_mulVec_eq_zero
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef)
    (v : Fin D → ℂ) (hv : ρ *ᵥ v = 0) :
    supportProj (D := D) ρ hρ *ᵥ v = 0 := by
  classical
  let hH : ρ.IsHermitian := hρ.isHermitian
  -- Work with the unitary diagonalization `ρ = U * diag(λ) * Uᴴ`.
  let U : Matrix (Fin D) (Fin D) ℂ := ↑hH.eigenvectorUnitary
  let s : Fin D → ℂ := fun i => if 0 < hH.eigenvalues i then 1 else 0
  have hUU : Uᴴ * U = 1 := by
    -- direct from unitarity
    simpa [U] using eig_conj_mul (D := D) (M := ρ) hH
  -- Work in the eigenbasis: `w := Uᴴ *ᵥ v`.
  let w : Fin D → ℂ := Uᴴ *ᵥ v
  have hΛw : Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w = 0 := by
    have hρ_spec : ρ = U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ := by
      simpa [U] using (spectral_decomp_eq (D := D) (M := ρ) hH)
    have hρv : (U * Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) * Uᴴ) *ᵥ v = 0 := by
      -- Rewrite `ρ` using its spectral decomposition.
      have hv' := hv
      -- After rewriting, `hv'` has exactly the desired type.
      -- (We use `rw` rather than `simp` to avoid recursion-depth issues.)
      rw [hρ_spec] at hv'
      exact hv'
    have hUΛw : U *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w) = 0 := by
      simpa [w, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hρv
    have hUΛw' : Uᴴ *ᵥ (U *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w)) = 0 := by
      simp [hUΛw]
    -- Cancel `Uᴴ * U = 1`.
    have : (Uᴴ * U) *ᵥ (Matrix.diagonal (fun j => (↑(hH.eigenvalues j) : ℂ)) *ᵥ w) = 0 := by
      simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hUΛw'
    simpa [Matrix.mulVec_mulVec, hUU] using this
  have h_comp : ∀ j, (↑(hH.eigenvalues j) : ℂ) * w j = 0 := fun j => by
    have := congrFun hΛw j
    simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply] using this
  have hSw : Matrix.diagonal s *ᵥ w = 0 := by
    ext j
    rw [Matrix.mulVec_diagonal]
    by_cases hjpos : 0 < hH.eigenvalues j
    · have : w j = 0 := by
        have hEig_ne : (↑(hH.eigenvalues j) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt hjpos)
        exact (mul_eq_zero.mp (h_comp j)).resolve_left hEig_ne
      simp [s, hjpos, this]
    · simp [s, hjpos]
  have hP_def : supportProj (D := D) ρ hρ = U * Matrix.diagonal s * Uᴴ := by
    -- Unfolding `supportProj` matches exactly our `U` and `s` definitions.
    rfl
  have : (U * Matrix.diagonal s * Uᴴ) *ᵥ v = U *ᵥ (Matrix.diagonal s *ᵥ w) := by
    simp [w, U, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp [hP_def, this, hSw]

-- Blank lines between `have` groups aid readability; tolerated here.
set_option linter.style.emptyLine false in
/-- The support projector has the same range as the original PSD matrix. -/
lemma range_mulVecLin_supportProj_eq
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosSemidef) :
    LinearMap.range (Matrix.mulVecLin (supportProj (D := D) ρ hρ)) =
      LinearMap.range (Matrix.mulVecLin ρ) := by
  classical
  let Q : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ
  have hQρ : Q * ρ = ρ := supportProj_mul (D := D) (ρ := ρ) hρ
  -- Range inclusion `range ρ ≤ range Q` from `Q * ρ = ρ`.
  have hrange : LinearMap.range (Matrix.mulVecLin ρ) ≤ LinearMap.range (Matrix.mulVecLin Q) := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨ρ *ᵥ x, ?_⟩
    simp [Q, Matrix.mulVec_mulVec, hQρ]
  -- Kernel inclusion `ker ρ ≤ ker Q` from the kernel lemma.
  have hker : LinearMap.ker (Matrix.mulVecLin ρ) ≤ LinearMap.ker (Matrix.mulVecLin Q) := by
    intro x hx
    exact supportProj_mulVec_eq_zero_of_mulVec_eq_zero (D := D) ρ hρ x hx

  have hker_fin :
      Module.finrank ℂ ↥(LinearMap.ker (Matrix.mulVecLin ρ)) ≤
        Module.finrank ℂ ↥(LinearMap.ker (Matrix.mulVecLin Q)) :=
    Submodule.finrank_mono hker

  have frange (M : Matrix (Fin D) (Fin D) ℂ) :
      Module.finrank ℂ ↥(LinearMap.range (Matrix.mulVecLin M)) =
        Module.finrank ℂ (Fin D → ℂ) - Module.finrank ℂ ↥(LinearMap.ker (Matrix.mulVecLin M)) := by
    have hdim := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    have := congrArg (fun n => n - Module.finrank ℂ ↥(LinearMap.ker (Matrix.mulVecLin M))) hdim
    simpa [Nat.add_sub_cancel, Nat.add_sub_cancel_left] using this

  have hfin_le :
      Module.finrank ℂ ↥(LinearMap.range (Matrix.mulVecLin Q)) ≤
        Module.finrank ℂ ↥(LinearMap.range (Matrix.mulVecLin ρ)) := by
    have := Nat.sub_le_sub_left hker_fin (Module.finrank ℂ (Fin D → ℂ))
    simpa [frange, Q] using this

  have hfin_ge :
      Module.finrank ℂ ↥(LinearMap.range (Matrix.mulVecLin ρ)) ≤
        Module.finrank ℂ ↥(LinearMap.range (Matrix.mulVecLin Q)) :=
    Submodule.finrank_mono hrange

  have hfin_eq :
      Module.finrank ℂ ↥(LinearMap.range (Matrix.mulVecLin ρ)) =
        Module.finrank ℂ ↥(LinearMap.range (Matrix.mulVecLin Q)) :=
    le_antisymm hfin_ge hfin_le

  have := Submodule.eq_of_le_of_finrank_eq (K := ℂ)
    (V := Fin D → ℂ)
    (S₁ := LinearMap.range (Matrix.mulVecLin ρ))
    (S₂ := LinearMap.range (Matrix.mulVecLin Q))
    hrange hfin_eq
  simpa [Q] using this.symm

end SupportProj

/-! ## Irreducibility under unitary conjugation and unitalization -/

section Irreducibility

-- Blank lines between `have` groups aid readability; tolerated here.
set_option linter.style.emptyLine false in
/-- Unitary conjugation preserves tensor irreducibility. -/
lemma isIrreducibleTensor_unitaryConj
    (A : MPSTensor d D) (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) A) :
    IsIrreducibleTensor (d := d) (D := D)
      (fun i => (↑U : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (↑U : Matrix (Fin D) (Fin D) ℂ)) := by
  classical
  intro hHas
  rcases hHas with ⟨P, hPproj, hP0, hP1, hLower⟩
  let V : Matrix (Fin D) (Fin D) ℂ := (↑U : Matrix (Fin D) (Fin D) ℂ)
  have hVV : V * Vᴴ = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using (Unitary.mul_star_self_of_mem U.prop)
  have hVV' : Vᴴ * V = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using (Matrix.UnitaryGroup.star_mul_self U)

  -- Conjugate the invariant projection back.
  let P' : Matrix (Fin D) (Fin D) ℂ := V * P * Vᴴ

  have hP'proj : IsOrthogonalProjection P' := by
    refine ⟨?_, ?_⟩
    · -- Hermitian
      have hHermP : P.IsHermitian := hPproj.1
      calc
        P'ᴴ = V * P * Vᴴ := by
          simp [P', Matrix.conjTranspose_mul, Matrix.mul_assoc, hHermP.eq]
        _ = P' := rfl
    · -- Idempotent
      have hPP : P * P = P := hPproj.2
      calc
        P' * P' = V * P * (Vᴴ * V) * P * Vᴴ := by
          simp [P', Matrix.mul_assoc]
        _ = V * (P * P) * Vᴴ := by
              simp [Matrix.mul_assoc, hVV']
        _ = P' := by simp [P', Matrix.mul_assoc, hPP]

  have hP'0 : P' ≠ 0 := by
    intro h0
    have h0' : Vᴴ * P' * V = (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa using congrArg (fun M => Vᴴ * M * V) h0
    have hVP : Vᴴ * P' * V = P := by
      calc
        Vᴴ * P' * V = Vᴴ * (V * P * Vᴴ) * V := by rfl
        _ = Vᴴ * (V * P) := by
              simp [Matrix.mul_assoc, hVV']
        _ = (Vᴴ * V) * P := by
              rw [← Matrix.mul_assoc]
        _ = P := by simp [hVV']
    have : P = 0 := by
      simpa [hVP] using h0'
    exact hP0 this

  have hP'1 : P' ≠ 1 := by
    intro h1
    have h1' : Vᴴ * P' * V = (1 : Matrix (Fin D) (Fin D) ℂ) := by
      -- `Vᴴ * 1 * V = Vᴴ * V = 1`.
      simpa [hVV'] using congrArg (fun M => Vᴴ * M * V) h1
    have hVP : Vᴴ * P' * V = P := by
      calc
        Vᴴ * P' * V = Vᴴ * (V * P * Vᴴ) * V := by rfl
        _ = Vᴴ * (V * P) := by
              simp [Matrix.mul_assoc, hVV']
        _ = (Vᴴ * V) * P := by
              rw [← Matrix.mul_assoc]
        _ = P := by simp [hVV']
    have : P = 1 := by
      simpa [hVP] using h1'
    exact hP1 this

  have hLower' : ∀ i : Fin d, (1 - P') * A i * P' = 0 := by
    intro i
    -- Conjugate the lower-zero relation.
    have hconj : V * ((1 - P) * (Vᴴ * A i * V) * P) * Vᴴ = 0 := by
      simpa [Matrix.mul_assoc] using congrArg (fun M => V * M * Vᴴ) (hLower i)

    -- Rewrite `(1 - P')` as a conjugate of `(1 - P)`.
    have h1P' : V * (1 - P) * Vᴴ = (1 - P') := by
      calc
        V * (1 - P) * Vᴴ
            = (V * (1 - P)) * Vᴴ := by simp [Matrix.mul_assoc]
        _ = (V * 1 - V * P) * Vᴴ := by simp [mul_sub]
        _ = (V * 1) * Vᴴ - (V * P) * Vᴴ := by simp [sub_mul]
        _ = V * Vᴴ - V * P * Vᴴ := by simp [Matrix.mul_assoc]
        _ = 1 - P' := by simp [P', hVV, Matrix.mul_assoc]

    have h1P'_symm : (1 - P') = V * (1 - P) * Vᴴ := by
      simpa using h1P'.symm

    calc
      (1 - P') * A i * P'
          = (V * (1 - P) * Vᴴ) * A i * (V * P * Vᴴ) := by
                simp [P', h1P'_symm]
      _ = V * ((1 - P) * (Vᴴ * A i * V) * P) * Vᴴ := by
                simp [Matrix.mul_assoc]
      _ = 0 := hconj

  exact hIrr ⟨P', hP'proj, hP'0, hP'1, hLower'⟩

-- Blank lines between `have` groups aid readability; tolerated here.
set_option linter.style.emptyLine false in
/-- If the unitalized tensor has an invariant projection, so does the original tensor.

This is the key irreducibility-preservation step for the CFII unitalization. -/
lemma hasInvariantProj_of_hasInvariantProj_unitalize
    (B : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛ : Λ.PosDef) (_hDiag : Λ.IsDiag) :
    HasInvariantProj (d := d) (D := D) (unitalize (d := d) (D := D) B Λ) →
      HasInvariantProj (d := d) (D := D) B := by
  classical
  rintro ⟨P, hPproj, hP0, hP1, hLower⟩

  -- Similarity matrices.
  let S : Matrix (Fin D) (Fin D) ℂ := diagSqrt (D := D) Λ
  let Sinv : Matrix (Fin D) (Fin D) ℂ := diagInvSqrt (D := D) Λ
  have hSSinv : S * Sinv = 1 := by
    simpa [S, Sinv] using diagSqrt_mul_diagInvSqrt_of_posDef (D := D) (Λ := Λ) hΛ
  have hSinvS : Sinv * S = 1 := by
    simpa [S, Sinv] using diagInvSqrt_mul_diagSqrt_of_posDef (D := D) (Λ := Λ) hΛ
  have hS_herm : Sᴴ = S := by simp [S]

  let C : MPSTensor d D := unitalize (d := d) (D := D) B Λ

  -- A PSD matrix whose range is `S (range(P))`.
  let ρ : Matrix (Fin D) (Fin D) ℂ := S * P * S
  have hρ_psd : ρ.PosSemidef := by
    have hHermP : P.IsHermitian := hPproj.1
    have hPP : P * P = P := hPproj.2
    have hSP : (S * P) * (S * P)ᴴ = ρ := by
      calc
        (S * P) * (S * P)ᴴ
            = (S * P) * (Pᴴ * Sᴴ) := by
                simp [Matrix.conjTranspose_mul]
        _ = S * (P * P) * S := by
              simp [Matrix.mul_assoc, hHermP.eq, hS_herm]
        _ = S * P * S := by
              simp [Matrix.mul_assoc, hPP]
        _ = ρ := by rfl
    have hρ_eq : ρ = (S * P) * (S * P)ᴴ := by
      simpa using hSP.symm
    simpa [hρ_eq] using Matrix.posSemidef_self_mul_conjTranspose (S * P)

  let Q : Matrix (Fin D) (Fin D) ℂ := supportProj (D := D) ρ hρ_psd
  have hQproj : IsOrthogonalProjection Q :=
    isOrthogonalProjection_supportProj (D := D) (ρ := ρ) (hρ := hρ_psd)

  -- Nontriviality of `Q`.
  have hρ_ne : ρ ≠ 0 := by
    intro h0
    have h0' : Sinv * ρ * Sinv = (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa using congrArg (fun M => Sinv * M * Sinv) h0

    have hSPS : Sinv * ρ * Sinv = P := by
      calc
        Sinv * ρ * Sinv = Sinv * (S * P * S) * Sinv := by rfl
        _ = (Sinv * S) * P * (S * Sinv) := by
              simp [Matrix.mul_assoc]
        _ = P := by
              simp [hSinvS, hSSinv]

    have : P = 0 := by
      simpa [hSPS] using h0'
    exact hP0 this

  have hQ0 : Q ≠ 0 := supportProj_ne_zero_of_ne_zero (D := D) ρ hρ_psd hρ_ne

  have hnotPD : ¬ ρ.PosDef := by
    intro hρPD
    have hρunit : IsUnit ρ := Matrix.PosDef.isUnit hρPD

    have hSinv_unit : IsUnit Sinv := by
      refine ⟨⟨Sinv, S, hSinvS, hSSinv⟩, rfl⟩

    have hP_unit : IsUnit P := by
      -- `P = Sinv * ρ * Sinv`.
      have hP_eq : (P : Matrix (Fin D) (Fin D) ℂ) = Sinv * ρ * Sinv := by
        calc
          (P : Matrix (Fin D) (Fin D) ℂ)
              = (Sinv * S) * P * (S * Sinv) := by
                    simp [hSinvS, hSSinv]
          _ = Sinv * (S * P * S) * Sinv := by
                    simp [Matrix.mul_assoc]
          _ = Sinv * ρ * Sinv := by rfl

      have : IsUnit (Sinv * ρ * Sinv) :=
        IsUnit.mul (IsUnit.mul hSinv_unit hρunit) hSinv_unit
      simpa [hP_eq] using this

    -- Idempotent + unit ⇒ `P = 1`.
    have hPP : P * P = P := hPproj.2
    rcases hP_unit.exists_right_inv with ⟨Pinv, hPinv⟩
    have : (P : Matrix (Fin D) (Fin D) ℂ) = 1 := by
      have := congrArg (fun M => M * Pinv) hPP
      simpa [Matrix.mul_assoc, hPinv] using this
    exact hP1 this

  have hQ1 : Q ≠ 1 := supportProj_ne_one_of_not_posDef (D := D) ρ hρ_psd hnotPD

  -- Range equality: `range(Q) = range(ρ)`.
  have hRange : LinearMap.range (Matrix.mulVecLin Q) = LinearMap.range (Matrix.mulVecLin ρ) := by
    simpa [Q] using (range_mulVecLin_supportProj_eq (D := D) ρ hρ_psd)

  -- Invariance: show `(1 - Q) * B i * Q = 0`.
  have hLowerB : ∀ i : Fin d, (1 - Q) * B i * Q = 0 := by
    intro i
    apply (Matrix.ext_iff_mulVec).2
    intro v

    let w : Fin D → ℂ := Q *ᵥ v
    have hw_memQ : w ∈ LinearMap.range (Matrix.mulVecLin Q) := ⟨v, by simp [w]⟩
    have hw_memρ : w ∈ LinearMap.range (Matrix.mulVecLin ρ) := by
      simpa [hRange] using hw_memQ
    rcases (LinearMap.mem_range).1 hw_memρ with ⟨u, hu⟩

    -- Use the lower-zero condition to rewrite `C i * P` as `P * C i * P`.
    have hCiP : C i * P = P * C i * P := by
      have h : (1 - P) * C i * P = 0 := hLower i
      have h' : (1 - P) * (C i * P) = 0 := by
        simpa [Matrix.mul_assoc] using h
      have hdecomp : (P + (1 - P) : Matrix (Fin D) (Fin D) ℂ) = 1 := by
        -- `P + (1 - P) = P + 1 - P = 1`.
        simp [sub_eq_add_neg]
      calc
        C i * P = (P + (1 - P)) * (C i * P) := by
          simp [hdecomp]
        _ = P * (C i * P) + (1 - P) * (C i * P) := by
          exact add_mul P (1 - P) (C i * P)
        _ = P * (C i * P) := by
          simp [h']
        _ = P * C i * P := by
          simp [Matrix.mul_assoc]

    have hBS : B i * S = S * C i := by
      have hSC : S * C i = B i * S := by
        calc
          S * C i = S * (Sinv * B i * S) := by rfl
          _ = (S * Sinv) * B i * S := by
                simp [Matrix.mul_assoc]
          _ = B i * S := by
                simp [hSSinv]
      simpa using hSC.symm

    have hBρ : B i * ρ = ρ * (Sinv * C i * P * S) := by
      calc
        B i * ρ = (B i * S) * P * S := by
          simp [ρ, Matrix.mul_assoc]
        _ = (S * C i) * P * S := by
          simp [hBS]
        _ = S * (C i * P) * S := by
              simp [Matrix.mul_assoc]
        _ = S * (P * C i * P) * S := by
              simp [hCiP]
        _ = ρ * (Sinv * C i * P * S) := by
          -- Expand `ρ` and cancel `S * Sinv = 1`.
          dsimp [ρ]
          have : (S * P * S) * (Sinv * C i * P * S) = S * (P * C i * P) * S := by
            calc
              (S * P * S) * (Sinv * C i * P * S)
                  = S * P * (S * Sinv) * C i * P * S := by
                        noncomm_ring
              _ = S * P * C i * P * S := by
                        simp [hSSinv]
              _ = S * (P * C i * P) * S := by
                        noncomm_ring
          simpa using this.symm

    have hBi_w_memρ : B i *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin ρ) := by
      refine ⟨(Sinv * C i * P * S) *ᵥ u, ?_⟩
      -- Rewrite `mulVecLin` as `mulVec`.
      change ρ *ᵥ ((Sinv * C i * P * S) *ᵥ u) = B i *ᵥ w
      have hw : w = ρ *ᵥ u := by
        simpa [Matrix.mulVecLin_apply] using hu.symm
      -- Now transport along `B i * ρ = ρ * (...)`.
      calc
        ρ *ᵥ ((Sinv * C i * P * S) *ᵥ u)
            = (ρ * (Sinv * C i * P * S)) *ᵥ u := by
                simp [Matrix.mulVec_mulVec]
        _ = (B i * ρ) *ᵥ u := by
                simp [hBρ.symm]
        _ = B i *ᵥ w := by
                have : (B i * ρ) *ᵥ u = B i *ᵥ (ρ *ᵥ u) := by
                  simp [Matrix.mulVec_mulVec]
                -- Rewrite the goal using `w = ρ *ᵥ u`.
                rw [hw]
                exact this

    have hBi_w_memQ : B i *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin Q) := by
      -- Rewrite the goal using `range(Q) = range(ρ)`.
      rw [hRange]
      exact hBi_w_memρ
    rcases (LinearMap.mem_range).1 hBi_w_memQ with ⟨z, hz⟩

    have hkill : (1 - Q) *ᵥ (B i *ᵥ w) = 0 := by
      have : B i *ᵥ w = Q *ᵥ z := by
        simpa [Matrix.mulVecLin_apply] using hz.symm
      -- `(1-Q)*Q = 0`.
      simp [this, Matrix.mulVec_mulVec, sub_mul, hQproj.2]

    -- Reassociate the matrix product to match the goal.
    simpa [w, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hkill

  exact ⟨Q, hQproj, hQ0, hQ1, hLowerB⟩

/-- Similarity unitalization preserves tensor irreducibility. -/
lemma isIrreducibleTensor_unitalize
    (B : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛ : Λ.PosDef) (hDiag : Λ.IsDiag)
    (hIrr : IsIrreducibleTensor (d := d) (D := D) B) :
    IsIrreducibleTensor (d := d) (D := D) (unitalize (d := d) (D := D) B Λ) := by
  intro hHas
  exact hIrr (hasInvariantProj_of_hasInvariantProj_unitalize (d := d) (D := D)
    (B := B) (Λ := Λ) hΛ hDiag hHas)

end Irreducibility

/-! ## Periodicity removal for CFII blocks -/

section PeriodicityRemoval

-- Blank lines between `have` groups aid readability; tolerated here.
set_option linter.style.emptyLine false in
/-- Appendix A periodicity removal in the CFII setting.

If `A` is trace-preserving and irreducible (tensor sense), then some physical blocking makes the
blocked transfer map primitive (peripheral eigenvalues = `{1}`). -/
theorem exists_blockTensor_isPrimitive_of_TP_of_isIrreducibleTensor_CFII
    {d D : ℕ} [NeZero D]
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hIrrT : IsIrreducibleTensor (d := d) (D := D) A) :
    ∃ p : ℕ, 0 < p ∧
      _root_.IsPrimitive
        (transferMap (d := blockPhysDim d p) (D := D)
          (blockTensor (d := d) (D := D) A p)) := by
  classical
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)

  -- CFII data: a unitary conjugate with a diagonal positive-definite fixed point.
  obtain ⟨U, Λ, hΛ_pd, hΛ_diag, hTPB, hfixB⟩ :=
    exists_unitary_diag_posDef_fixedPoint_of_TP_of_isIrreducibleTensor
      (d := d) (D := D) A (by simpa using hTP) hIrrT hDpos

  let V : Matrix (Fin D) (Fin D) ℂ := (↑U : Matrix (Fin D) (Fin D) ℂ)
  let B : MPSTensor d D := fun i => Vᴴ * A i * V

  -- Unitalize using the diagonal fixed point.
  let C : MPSTensor d D := unitalize (d := d) (D := D) B Λ

  have h_unital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) C :=
    unitalize_isUnitalKraus_of_fixedPoint (d := d) (D := D)
      (B := B) (Λ := Λ) hΛ_pd hΛ_diag hfixB

  have h_adjfix : Kraus.adjointMap C Λ = Λ :=
    unitalize_adjoint_fixedPoint_of_TP (d := d) (D := D)
      (B := B) (Λ := Λ) hΛ_pd hΛ_diag (by simpa [B] using hTPB)

  -- Irreducibility: preserved by unitary conjugation and by similarity unitalization.
  have hIrrB : IsIrreducibleTensor (d := d) (D := D) B :=
    isIrreducibleTensor_unitaryConj (d := d) (D := D) (A := A) U hIrrT

  have hIrrC_tensor : IsIrreducibleTensor (d := d) (D := D) C :=
    isIrreducibleTensor_unitalize (d := d) (D := D) (B := B) (Λ := Λ) hΛ_pd hΛ_diag hIrrB

  have hIrrC : IsIrreducibleMap (transferMap (d := d) (D := D) C) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor (d := d) (D := D) C hIrrC_tensor

  -- Root-of-unity peripheral eigenvalues for the unitalized map.
  let E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    transferMap (d := d) (D := D) C

  have hfin : (peripheralEigenvalues E).Finite := peripheralEigenvalues_finite (f := E)

  have hroot : ∀ μ ∈ hfin.toFinset, ∃ q : ℕ, 0 < q ∧ μ ^ q = 1 := by
    intro μ hμ
    have hμ' : μ ∈ peripheralEigenvalues E := hfin.mem_toFinset.mp hμ
    simpa [E] using
      (peripheral_isRootOfUnity_of_irreducible_unital_of_adjoint_fixedPoint
        (K := C) h_unital Λ hΛ_pd h_adjfix hIrrC μ (by simpa [E] using hμ'))

  obtain ⟨p, hp_pos, hp_all⟩ :=
    exists_common_power_eq_one_of_finite (s := hfin.toFinset) hroot

  have hperE : ∀ μ : ℂ, μ ∈ peripheralEigenvalues E → μ ^ p = 1 := by
    intro μ hμ
    have hμ_fin : μ ∈ hfin.toFinset := hfin.mem_toFinset.mpr hμ
    exact hp_all μ hμ_fin

  -- Transport `μ ^ p = 1` back to `transferMap A` using conjugation invariance.
  have hVV : V * Vᴴ = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using (Unitary.mul_star_self_of_mem U.prop)
  have hVV' : Vᴴ * V = 1 := by
    simpa [V, Matrix.star_eq_conjTranspose] using (Matrix.UnitaryGroup.star_mul_self U)

  -- Similarity between `transferMap C` and `transferMap B`.
  let S : Matrix (Fin D) (Fin D) ℂ := diagSqrt (D := D) Λ
  let Sinv : Matrix (Fin D) (Fin D) ℂ := diagInvSqrt (D := D) Λ
  have hSSinv : S * Sinv = 1 := by
    simpa [S, Sinv] using diagSqrt_mul_diagInvSqrt_of_posDef (D := D) (Λ := Λ) hΛ_pd
  have hSinvS : Sinv * S = 1 := by
    simpa [S, Sinv] using diagInvSqrt_mul_diagSqrt_of_posDef (D := D) (Λ := Λ) hΛ_pd

  let Φ : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    mulLeftRightLinearEquiv (D := D) S S Sinv Sinv hSSinv hSinvS hSSinv hSinvS

  have hEC_conj : E = Φ.symm.conj (transferMap (d := d) (D := D) B) := by
    ext X
    simp [E, C, unitalize, Φ, S, Sinv, MPSTensor.transferMap_apply, Matrix.mul_assoc,
      LinearEquiv.conj_apply_apply]

  -- Similarity between `transferMap B` and `transferMap A` (unitary conjugation).
  let Ψ : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    mulLeftRightLinearEquiv (D := D) V Vᴴ Vᴴ V hVV hVV' hVV' hVV

  have hEB_conj : transferMap (d := d) (D := D) B =
      Ψ.symm.conj (transferMap (d := d) (D := D) A) := by
    ext X
    simp [B, Ψ, MPSTensor.transferMap_apply, Matrix.mul_assoc,
      LinearEquiv.conj_apply_apply]

  have hperA : ∀ μ : ℂ,
      μ ∈ peripheralEigenvalues (transferMap (d := d) (D := D) A) → μ ^ p = 1 := by
    intro μ hμA

    have hμB : μ ∈ peripheralEigenvalues (transferMap (d := d) (D := D) B) := by
      have : peripheralEigenvalues (transferMap (d := d) (D := D) B) =
          peripheralEigenvalues (transferMap (d := d) (D := D) A) := by
        simpa [hEB_conj] using
          (peripheralEigenvalues_conj (S := Ψ.symm) (E := transferMap (d := d) (D := D) A))
      simpa [this] using hμA

    have hμC : μ ∈ peripheralEigenvalues E := by
      have : peripheralEigenvalues E =
          peripheralEigenvalues (transferMap (d := d) (D := D) B) := by
        simpa [hEC_conj] using
          (peripheralEigenvalues_conj (S := Φ.symm) (E := transferMap (d := d) (D := D) B))
      simpa [this] using hμB

    exact hperE μ hμC

  -- Fixed point for `transferMap A`: transport `Λ` back by the unitary.
  let ρA : Matrix (Fin D) (Fin D) ℂ := V * Λ * Vᴴ

  have hfixA : transferMap (d := d) (D := D) A ρA = ρA := by
    -- Rewrite the fixed-point equation for `B` using the conjugation identity
    -- `transferMap B = Ψ.symm.conj (transferMap A)`, then apply `Ψ` to transport the equation.
    have hfixB' : transferMap (d := d) (D := D) B Λ = Λ := by
      simpa [B, V] using hfixB
    have hfixB_conj : (Ψ.symm.conj (transferMap (d := d) (D := D) A)) Λ = Λ := by
      simpa [hEB_conj] using hfixB'
    have hfixA' := congrArg (fun X => Ψ X) hfixB_conj
    -- Simplify the conjugation expression.
    have hfixA'' :
        transferMap (d := d) (D := D) A (Ψ Λ) = Ψ Λ := by
      simpa [LinearEquiv.conj_apply_apply] using hfixA'
    -- Finally identify `Ψ Λ` with `ρA = V * Λ * Vᴴ`.
    simpa [ρA, Ψ] using hfixA''

  have hρA_ne : ρA ≠ 0 := by
    intro h0
    have hρA_eq : Ψ Λ = ρA := by simp [ρA, Ψ]
    have h0' : Ψ Λ = 0 := by simpa [hρA_eq] using h0
    have hΛ0 : Λ = 0 := by
      have := congrArg (fun M => Ψ.symm M) h0'
      simpa using this
    -- Positive definite matrices are nonzero.
    exact (Matrix.PosDef.isUnit hΛ_pd).ne_zero hΛ0

  have hprim_pow : peripheralEigenvalues ((transferMap (d := d) (D := D) A) ^ p) = {1} :=
    peripheralEigenvalues_pow_eq_singleton
      (E := transferMap (d := d) (D := D) A)
      (p := p)
      hp_pos
      hperA
      ρA
      hfixA
      hρA_ne

  refine ⟨p, hp_pos, ?_⟩
  unfold _root_.IsPrimitive
  -- Convert from a power to blocking.
  rw [MPSTensor.transferMap_blockTensor (A := A) (L := p)]
  simpa using hprim_pow

end PeriodicityRemoval

end MPSTensor
