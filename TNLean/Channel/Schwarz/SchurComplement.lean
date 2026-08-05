/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.Douglas
import TNLean.Analysis.MatrixSqrt
import Mathlib.Data.Matrix.Block

/-!
# Block Schur complements

Working towards Wolf's Theorem 5.2: for a self-adjoint 2×2 block matrix
`M = [[P, Q], [Q†, R]]` with `P, R` PSD, the following are equivalent:

1. `M` is PSD
2. `ker(R) ⊆ ker(Q)` and the pseudoinverse Schur complement `P − Q·R⁺·Q†` is PSD
3. `ker(R) ⊆ ker(Q)` and `‖P^{-1/2}·Q·R^{-1/2}‖ ≤ 1` (contraction form)

## Main results

* `ker_subset_of_block_psd` : the kernel-inclusion half of (1) ⟹ (2)
* `block_quadratic_form` : the quadratic-form expansion of the block matrix
* `R_mul_pinv_eq_supportProj`, `pinv_mul_self_eq_supportProj`,
  `supportProj_mul_pinv_eq_pinv`, `pinv_isHermitian` : pseudoinverse algebra for
  PSD `R`, building on the general `Matrix.PosSemidef.supportProj_sq_eq_supportProj`

## Remaining gap towards Wolf Thm 5.2

The Schur-complement-PSD half of (1) ⟹ (2) (quadratic-form minimisation with
`y = -R⁺Q†x`), the converse (2) ⟹ (1) (completing the square), and the
contraction equivalence (2) ⇔ (3) are not formalized here; see
`docs/paper-gaps/schur_complement_tfae.tex`.

## Implementation notes

`pinv_isHermitian` expands `(Douglas.pinv R)ᴴ` via the definition
`Douglas.pinv R = Rᴴ * supportInv(R Rᴴ)`, reducing it to `supportInv(R Rᴴ) * R`
using that `supportInv(R Rᴴ)` is Hermitian, then shows `supportInv(R Rᴴ)` commutes
with `R` via continuous-function calculus (`IsSelfAdjoint.commute_cfc`), since it
is a cfc element of `R Rᴴ`, which commutes with `R`.

`pinv_mul_self_eq_supportProj` is proved by conjugate-transposing
`R * pinv R = supportProj R` (`R_mul_pinv_eq_supportProj`) using `pinv_isHermitian`.

`supportProj_mul_pinv_eq_pinv` avoids rewriting `Rᴴ = R` inside dependent positions
(which breaks the `rw` motive because `hR : R.PosSemidef` mentions `R`): all
conversions are done in term mode via `congrArg` transitivity chains, factoring `R`
as `√R * √R` and using the support absorption `supportProj R * √R = √R`.

## References

* [M. Wolf, *Quantum Channels & Operations*, Theorem 5.2][Wolf2012QChannels]
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace SchurComplement

variable {D₁ D₂ : ℕ}

/-- A 2×2 block matrix: [[P, Q], [Q†, R]]. -/
def blockMatrix (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) :
    Matrix ((Fin D₁) ⊕ (Fin D₂)) ((Fin D₁) ⊕ (Fin D₂)) ℂ :=
  Matrix.fromBlocks P Q (Qᴴ) R

/-- The block matrix `[[P, Q], [Q†, R]]` is Hermitian when its diagonal
blocks `P` and `R` are Hermitian. -/
theorem blockMatrix_isHermitian (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hP : P.IsHermitian) (hR : R.IsHermitian) : (blockMatrix P Q R).IsHermitian := by
  rw [Matrix.IsHermitian, blockMatrix]
  simp [Matrix.fromBlocks_conjTranspose, hP.eq, hR.eq]

/-- Pseudoinverse Schur complement: `P − Q·R⁺·Q†`. -/
noncomputable def schurComplement (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ) :
    Matrix (Fin D₁) (Fin D₁) ℂ :=
  P - Q * (Douglas.pinv R) * (Qᴴ)

/-- The quadratic form of the block matrix `[[P, Q], [Q†, R]]` splits into the four
block contributions `⟨x,Px⟩ + ⟨x,Qy⟩ + ⟨y,Q†x⟩ + ⟨y,Ry⟩`. -/
theorem block_quadratic_form (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (x : Fin D₁ → ℂ) (y : Fin D₂ → ℂ) :
    dotProduct (star (Sum.elim x y)) (mulVec (blockMatrix P Q R) (Sum.elim x y)) =
    dotProduct (star x) (mulVec P x) + dotProduct (star x) (mulVec Q y) +
    dotProduct (star y) (mulVec (Qᴴ) x) + dotProduct (star y) (mulVec R y) := by
  rw [blockMatrix, Matrix.fromBlocks_mulVec P Q (Qᴴ) R (Sum.elim x y)]
  calc
    star (Sum.elim x y) ⬝ᵥ (Sum.elim (P *ᵥ x + Q *ᵥ y) (Qᴴ *ᵥ x + R *ᵥ y)) =
      star x ⬝ᵥ (P *ᵥ x + Q *ᵥ y) + star y ⬝ᵥ (Qᴴ *ᵥ x + R *ᵥ y) := by
      simp [dotProduct]
    _ = (star x ⬝ᵥ (P *ᵥ x) + star x ⬝ᵥ (Q *ᵥ y)) +
        (star y ⬝ᵥ (Qᴴ *ᵥ x) + star y ⬝ᵥ (R *ᵥ y)) := by simp [dotProduct_add]
    _ = star x ⬝ᵥ (P *ᵥ x) + star x ⬝ᵥ (Q *ᵥ y) +
        star y ⬝ᵥ (Qᴴ *ᵥ x) + star y ⬝ᵥ (R *ᵥ y) := by ring

/-! ### Forward: block PSD → ker inclusion -/

/-- If the block matrix `[[P, Q], [Q†, R]]` is PSD, then `ker(R) ⊆ ker(Q)`. -/
theorem ker_subset_of_block_psd (P : Matrix (Fin D₁) (Fin D₁) ℂ)
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hM : (blockMatrix P Q R).PosSemidef) (y : Fin D₂ → ℂ) (hRy : mulVec R y = 0) :
    mulVec Q y = 0 := by
  have h_quad : star (Sum.elim (0 : Fin D₁ → ℂ) y) ⬝ᵥ
      ((blockMatrix P Q R) *ᵥ Sum.elim (0 : Fin D₁ → ℂ) y) = 0 := by
    rw [block_quadratic_form P Q R 0 y]
    simp [hRy]
  have hMv_zero : (blockMatrix P Q R) *ᵥ Sum.elim (0 : Fin D₁ → ℂ) y = 0 :=
    ((Matrix.PosSemidef.dotProduct_mulVec_zero_iff hM _).mp h_quad)
  have h_comp : (blockMatrix P Q R) *ᵥ Sum.elim (0 : Fin D₁ → ℂ) y =
      Sum.elim (mulVec Q y) (mulVec R y) := by
    rw [blockMatrix, Matrix.fromBlocks_mulVec P Q (Qᴴ) R]
    simp [hRy]
  rw [h_comp] at hMv_zero
  ext i
  have := congrFun hMv_zero (Sum.inl i)
  simpa using this

/-! ### Algebraic identities for `Douglas.pinv` on PSD `R` -/

/-- For PSD `R`, `R * pinv R = supportProj R`: the pseudoinverse is a right
support-inverse. -/
theorem R_mul_pinv_eq_supportProj (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hR : R.PosSemidef) :
    R * (Douglas.pinv R) = hR.supportProj := by
  rw [Douglas.mul_pinv_eq_supportProj R]
  exact hR.supportProj_sq_eq_supportProj

/-- The Moore–Penrose pseudoinverse of a PSD matrix is Hermitian. -/
theorem pinv_isHermitian (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hR : R.PosSemidef) :
    (Douglas.pinv R).IsHermitian := by
  classical
  have hS : (R * Rᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose R
  have hInvHerm : hS.supportInvᴴ = hS.supportInv := by
    rw [Matrix.PosSemidef.supportInv, Matrix.conjTranspose_mul,
        hS.supportInvSqrt_isHermitian.eq]
  have hcomm1 : Commute R (R * Rᴴ) := by
    simp only [Commute, SemiconjBy, hR.isHermitian.eq]
    exact (Matrix.mul_assoc R R R).symm
  have hcomm2 : Commute R hS.supportInvSqrt := by
    rw [Matrix.PosSemidef.supportInvSqrt, ← hS.isHermitian.cfc_eq]
    exact (IsSelfAdjoint.commute_cfc
      (Matrix.isHermitian_iff_isSelfAdjoint.mp hS.isHermitian) hcomm1.symm
      (fun x : ℝ => if x ≠ 0 then (Real.sqrt x)⁻¹ else 0)).symm
  have hcommInv : hS.supportInv * R = R * hS.supportInv := by
    calc hS.supportInvSqrt * hS.supportInvSqrt * R
        = hS.supportInvSqrt * (hS.supportInvSqrt * R) := Matrix.mul_assoc _ _ _
      _ = hS.supportInvSqrt * (R * hS.supportInvSqrt) := by rw [hcomm2.symm.eq]
      _ = (hS.supportInvSqrt * R) * hS.supportInvSqrt := (Matrix.mul_assoc _ _ _).symm
      _ = (R * hS.supportInvSqrt) * hS.supportInvSqrt := by rw [hcomm2.symm.eq]
      _ = R * (hS.supportInvSqrt * hS.supportInvSqrt) := Matrix.mul_assoc _ _ _
  have hcommInv' : hS.supportInv * R = R * hS.supportInv := by
    rw [Matrix.PosSemidef.supportInv]
    exact hcommInv
  calc (Douglas.pinv R)ᴴ = hS.supportInvᴴ * Rᴴᴴ := by
        rw [Douglas.pinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    _ = hS.supportInv * R := by rw [hInvHerm, Matrix.conjTranspose_conjTranspose]
    _ = R * hS.supportInv := hcommInv'
    _ = Rᴴ * hS.supportInv := by
        exact (congrArg (HMul.hMul · hS.supportInv) hR.isHermitian.eq).symm
    _ = Douglas.pinv R := rfl

/-- For PSD `R`, `pinv R * R = supportProj R`: the pseudoinverse is a left
support-inverse. -/
theorem pinv_mul_self_eq_supportProj (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hR : R.PosSemidef) :
    Douglas.pinv R * R = hR.supportProj := by
  classical
  have h2 : Rᴴ * (Douglas.pinv R)ᴴ = hR.supportProj := by
    rw [(pinv_isHermitian R hR).eq,
        show Rᴴ * Douglas.pinv R = R * Douglas.pinv R from
          congrArg (· * Douglas.pinv R) hR.isHermitian.eq]
    exact R_mul_pinv_eq_supportProj R hR
  calc Douglas.pinv R * R = (Rᴴ * (Douglas.pinv R)ᴴ)ᴴ := by
        rw [← Matrix.conjTranspose_conjTranspose (Douglas.pinv R * R),
            Matrix.conjTranspose_mul]
    _ = hR.supportProjᴴ := by rw [h2]
    _ = hR.supportProj := hR.supportProj_isHermitian.eq

/-- Support-projection absorption on the pseudoinverse of a PSD matrix:
`supportProj R * pinv R = pinv R`. -/
theorem supportProj_mul_pinv_eq_pinv (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hR : R.PosSemidef) :
    hR.supportProj * Douglas.pinv R = Douglas.pinv R := by
  have hsqrt : hR.supportProj * hR.isHermitian.cfc Real.sqrt =
      hR.isHermitian.cfc Real.sqrt := hR.supportProj_mul_cfc_sqrt
  have hRR : hR.isHermitian.cfc Real.sqrt * hR.isHermitian.cfc Real.sqrt = R :=
    hR.cfc_sqrt_mul_self
  have e2 : hR.supportProj * (hR.isHermitian.cfc Real.sqrt * hR.isHermitian.cfc Real.sqrt) =
      hR.isHermitian.cfc Real.sqrt * hR.isHermitian.cfc Real.sqrt := by
    rw [← Matrix.mul_assoc, hsqrt]
  have e1 : hR.supportProj * R = R :=
    (congrArg (fun X => hR.supportProj * X) hRR).symm.trans (e2.trans hRR)
  have key : hR.supportProj * Rᴴ = Rᴴ :=
    (congrArg (HMul.hMul hR.supportProj) hR.isHermitian.eq).trans
      (e1.trans hR.isHermitian.eq.symm)
  calc hR.supportProj * Douglas.pinv R
      = (hR.supportProj * Rᴴ) * (Matrix.posSemidef_self_mul_conjTranspose R).supportInv := by
        rw [Douglas.pinv, Matrix.mul_assoc]
    _ = Rᴴ * (Matrix.posSemidef_self_mul_conjTranspose R).supportInv := by rw [key]
    _ = Douglas.pinv R := by rw [Douglas.pinv]

end SchurComplement
