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
3. `ker(R) ⊆ ker(Q)`, `ker(P) ⊆ ker(Q†)`, and
   `‖P^{-1/2}·Q·R^{-1/2}‖ ≤ 1` (corrected contraction form)

Wolf's printed condition (3) omits the left-support condition. The omission is
substantive when `P` is singular: `P = 0`, `Q = R = 1` is a counterexample.

## Main results

* `ker_subset_of_block_psd` : the kernel-inclusion half of (1) ⟹ (2)
* `block_quadratic_form` : the quadratic-form expansion of the block matrix
* `blockMatrix_posSemidef_iff` : the equivalence of the block positivity and
  pseudoinverse Schur-complement conditions in Wolf's Theorem 5.2
* `R_mul_pinv_eq_supportProj`, `pinv_mul_self_eq_supportProj`,
  `supportProj_mul_pinv_eq_pinv`, `pinv_isHermitian` : pseudoinverse algebra for
  PSD `R`, building on the general `Matrix.PosSemidef.supportProj_sq_eq_supportProj`

## Remaining gap towards Wolf Thm 5.2

The corrected contraction equivalence (2) ⇔ (3), with both support conditions,
is not yet formalized; see `docs/paper-gaps/schur_complement_tfae.tex`.

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
theorem R_mul_pinv_eq_supportProj {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℂ) (hR : R.PosSemidef) :
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

/-! ### Pseudoinverse Schur-complement equivalence -/

/-- Completing the square for a block quadratic form using the pseudoinverse
of its lower-right block.

This is the quadratic identity underlying conditions (1) and (2) of Wolf,
*Quantum Channels & Operations*, Theorem 5.2; see
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 103--118. -/
theorem schur_complement_quadratic_form
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hR : R.PosSemidef)
    (hker : ∀ v : Fin D₂ → ℂ, R *ᵥ v = 0 → Q *ᵥ v = 0)
    (x : Fin D₁ → ℂ) (y : Fin D₂ → ℂ) :
    (star (Sum.elim x y)) ᵥ* (blockMatrix P Q R) ⬝ᵥ (Sum.elim x y) =
      (star ((Douglas.pinv R * Qᴴ) *ᵥ x + y)) ᵥ* R ⬝ᵥ
        ((Douglas.pinv R * Qᴴ) *ᵥ x + y) +
      (star x) ᵥ* (schurComplement P Q R) ⬝ᵥ x := by
  classical
  have hQ : Q * hR.supportProj = Q :=
    hR.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
  have hQH : hR.supportProj * Qᴴ = Qᴴ := by
    have h := congrArg Matrix.conjTranspose hQ
    simpa [Matrix.conjTranspose_mul, hR.supportProj_isHermitian.eq] using h
  have hKR : Douglas.pinv R * R = hR.supportProj :=
    pinv_mul_self_eq_supportProj R hR
  have hRK : R * Douglas.pinv R = hR.supportProj :=
    R_mul_pinv_eq_supportProj R hR
  have hRQ : R * (Douglas.pinv R * Qᴴ) = Qᴴ := by
    calc
      R * (Douglas.pinv R * Qᴴ) = (R * Douglas.pinv R) * Qᴴ :=
        (Matrix.mul_assoc _ _ _).symm
      _ = hR.supportProj * Qᴴ := by rw [hRK]
      _ = Qᴴ := hQH
  simp [blockMatrix, schurComplement, Function.star_sumElim, vecMul_fromBlocks,
    add_vecMul, dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc,
    (pinv_isHermitian R hR).eq, star_mulVec, hQ, hKR, hRQ]
  abel

/-- Positivity of a block matrix implies positivity of its pseudoinverse Schur
complement.

This is the Schur-complement part of (1) implies (2) in Wolf, *Quantum
Channels & Operations*, Theorem 5.2; see
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 103--118. -/
theorem schurComplement_posSemidef_of_blockMatrix_posSemidef
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hP : P.PosSemidef) (hR : R.PosSemidef)
    (hM : (blockMatrix P Q R).PosSemidef) :
    (schurComplement P Q R).PosSemidef := by
  have hker := ker_subset_of_block_psd P Q R hM
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · exact hP.isHermitian.sub
      (Matrix.isHermitian_mul_mul_conjTranspose Q (pinv_isHermitian R hR))
  have hnonneg := hM.dotProduct_mulVec_nonneg
    (Sum.elim x (-((Douglas.pinv R * Qᴴ) *ᵥ x)))
  rw [dotProduct_mulVec, schur_complement_quadratic_form P Q R hR hker] at hnonneg
  simpa [← dotProduct_mulVec] using hnonneg

/-- The kernel and pseudoinverse Schur-complement conditions imply positivity
of the block matrix.

This is (2) implies (1) in Wolf, *Quantum Channels & Operations*, Theorem 5.2;
see `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 103--118. -/
theorem blockMatrix_posSemidef_of_schurComplement_posSemidef
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hP : P.PosSemidef) (hR : R.PosSemidef)
    (hker : ∀ v : Fin D₂ → ℂ, R *ᵥ v = 0 → Q *ᵥ v = 0)
    (hS : (schurComplement P Q R).PosSemidef) :
    (blockMatrix P Q R).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (blockMatrix_isHermitian P Q R hP.isHermitian hR.isHermitian) fun z => ?_
  rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr z,
    schur_complement_quadratic_form P Q R hR hker]
  exact add_nonneg
    (by simpa only [dotProduct_mulVec] using (hR.dotProduct_mulVec_nonneg
      ((Douglas.pinv R * Qᴴ) *ᵥ (z ∘ Sum.inl) + z ∘ Sum.inr)))
    (by simpa only [dotProduct_mulVec] using
      (hS.dotProduct_mulVec_nonneg (z ∘ Sum.inl)))

/-- A block matrix is positive semidefinite if and only if the kernel of its
lower-right block is contained in the kernel of the off-diagonal block and its
pseudoinverse Schur complement is positive semidefinite.

This is the equivalence of conditions (1) and (2) in Wolf, *Quantum Channels &
Operations*, Theorem 5.2; see
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 103--118. -/
theorem blockMatrix_posSemidef_iff
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hP : P.PosSemidef) (hR : R.PosSemidef) :
    (blockMatrix P Q R).PosSemidef ↔
      (∀ v : Fin D₂ → ℂ, R *ᵥ v = 0 → Q *ᵥ v = 0) ∧
        (schurComplement P Q R).PosSemidef := by
  constructor
  · intro hM
    exact ⟨ker_subset_of_block_psd P Q R hM,
      schurComplement_posSemidef_of_blockMatrix_posSemidef P Q R hP hR hM⟩
  · rintro ⟨hker, hS⟩
    exact blockMatrix_posSemidef_of_schurComplement_posSemidef
      P Q R hP hR hker hS

end SchurComplement
