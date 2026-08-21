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
* `blockMatrix_posSemidef_iff_contraction` : the corrected contraction
  criterion with both support conditions
* `wolf_condition_three_not_sufficient` : a scalar counterexample to the
  contraction criterion as printed
* `R_mul_pinv_eq_supportProj`, `pinv_mul_self_eq_supportProj`,
  `supportProj_mul_pinv_eq_pinv`, `pinv_isHermitian` : pseudoinverse algebra for
  PSD `R`, building on the general `Matrix.PosSemidef.supportProj_sq_eq_supportProj`

## Source correction for Wolf Thm 5.2

Conditions (1) and (2) are equivalent as printed. Condition (3) becomes
equivalent to them after adding `ker(P) ⊆ ker(Q†)`. The printed version is
false; see `docs/paper-gaps/schur_complement_tfae.tex`.

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

/-- On a positive-semidefinite matrix, the Moore--Penrose pseudoinverse agrees
with the generalized inverse obtained by inverting on the support.

This identifies the two inverse-on-the-support conventions in Wolf,
*Quantum Channels & Operations*, Theorem 5.2; see
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 114--116. -/
theorem pinv_eq_supportInv (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hR : R.PosSemidef) :
    Douglas.pinv R = hR.supportInv := by
  have hInvR : hR.supportInv * R = hR.supportProj := hR.supportInv_mul_self
  calc
    Douglas.pinv R = hR.supportProj * Douglas.pinv R :=
      (supportProj_mul_pinv_eq_pinv R hR).symm
    _ = (hR.supportInv * R) * Douglas.pinv R :=
      (congrArg (· * Douglas.pinv R) hInvR).symm
    _ = hR.supportInv * (R * Douglas.pinv R) := Matrix.mul_assoc _ _ _
    _ = hR.supportInv * hR.supportProj := by rw [R_mul_pinv_eq_supportProj R hR]
    _ = hR.supportInv := hR.supportInv_mul_supportProj

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

/-! ### Corrected contraction criterion -/

/-- The support-normalized off-diagonal block in the corrected contraction
criterion for a positive block matrix.

Wolf, *Quantum Channels & Operations*, Theorem 5.2, condition (3), uses this
matrix; see `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, line 116. -/
noncomputable def schurContraction
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hP : P.PosSemidef) (hR : R.PosSemidef) :
    Matrix (Fin D₁) (Fin D₂) ℂ :=
  hP.supportInvSqrt * Q * hR.supportInvSqrt

/-- The product of the support-normalized off-diagonal block with its adjoint
is the support-normalized pseudoinverse Schur term.

This is the algebraic identity used in Wolf, *Quantum Channels & Operations*,
Theorem 5.2, conditions (2) and (3); see
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 114--116. -/
theorem schurContraction_mul_conjTranspose
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hP : P.PosSemidef) (hR : R.PosSemidef) :
    schurContraction P Q R hP hR * (schurContraction P Q R hP hR)ᴴ =
      hP.supportInvSqrt * (Q * Douglas.pinv R * Qᴴ) * hP.supportInvSqrt := by
  rw [pinv_eq_supportInv R hR]
  simp only [schurContraction, Matrix.conjTranspose_mul,
    hP.supportInvSqrt_isHermitian.eq, hR.supportInvSqrt_isHermitian.eq,
    Matrix.PosSemidef.supportInv]
  simp only [Matrix.mul_assoc]

/-- The pseudoinverse term in the Schur complement is positive semidefinite.

This is the positive term compared with `P` in Wolf, *Quantum Channels &
Operations*, Theorem 5.2, condition (2); see
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 114--115. -/
theorem schurTerm_posSemidef
    (Q : Matrix (Fin D₁) (Fin D₂) ℂ) (R : Matrix (Fin D₂) (Fin D₂) ℂ)
    (hR : R.PosSemidef) :
    (Q * Douglas.pinv R * Qᴴ).PosSemidef := by
  rw [pinv_eq_supportInv R hR]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    hR.supportInv_posSemidef.conjTranspose_mul_mul_same Qᴴ

/-- Schur-complement positivity forces the missing left-support condition on
the off-diagonal block.

This condition is implicit in condition (2) of Wolf, *Quantum Channels &
Operations*, Theorem 5.2, but is absent from the printed condition (3); see
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 114--116. -/
theorem ker_conjTranspose_subset_of_schurComplement_posSemidef
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (_hP : P.PosSemidef) (hR : R.PosSemidef)
    (hkerR : ∀ v : Fin D₂ → ℂ, R *ᵥ v = 0 → Q *ᵥ v = 0)
    (hS : (schurComplement P Q R).PosSemidef) :
    ∀ v : Fin D₁ → ℂ, P *ᵥ v = 0 → Qᴴ *ᵥ v = 0 := by
  let B := Q * Douglas.pinv R * Qᴴ
  have hB : B.PosSemidef := schurTerm_posSemidef Q R hR
  have hBS : B + schurComplement P Q R = P := by
    simp only [B, schurComplement]
    abel
  have hQ : Q * hR.supportProj = Q :=
    hR.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hkerR
  have hQH : hR.supportProj * Qᴴ = Qᴴ := by
    have h := congrArg Matrix.conjTranspose hQ
    simpa [Matrix.conjTranspose_mul, hR.supportProj_isHermitian.eq] using h
  intro v hv
  have hvB : B *ᵥ v = 0 := by
    apply hB.mulVec_eq_zero_left hS v
    rw [hBS, hv]
  let A := hR.supportInvSqrt * Qᴴ
  have hBA : B = Aᴴ * A := by
    dsimp only [B, A]
    rw [pinv_eq_supportInv R hR]
    simp only [Matrix.PosSemidef.supportInv, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hR.supportInvSqrt_isHermitian.eq,
      Matrix.mul_assoc]
  have hvA : A *ᵥ v = 0 := by
    rw [hBA] at hvB
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero A v).mp hvB
  have hz := congrArg
    (fun w : Fin D₂ → ℂ ↦ hR.isHermitian.cfc Real.sqrt *ᵥ w) hvA
  simpa only [A, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    hR.cfc_sqrt_mul_supportInvSqrt, hQH, Matrix.mulVec_zero] using hz

/-- The pseudoinverse Schur complement is positive semidefinite exactly when
the off-diagonal block obeys the left-support condition and its support
normalization is a contraction.

**Local fix (Wolf Theorem 5.2, condition (3)):** The printed condition (3) at
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, line 116 omits
`ker(P) ⊆ ker(Q†)`. Without this condition the implication to block positivity
is false. The deviation and the scalar counterexample are recorded in
`docs/paper-gaps/schur_complement_tfae.tex`. -/
theorem schurComplement_posSemidef_iff_contraction
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hP : P.PosSemidef) (hR : R.PosSemidef)
    (hkerR : ∀ v : Fin D₂ → ℂ, R *ᵥ v = 0 → Q *ᵥ v = 0) :
    (schurComplement P Q R).PosSemidef ↔
      (∀ v : Fin D₁ → ℂ, P *ᵥ v = 0 → Qᴴ *ᵥ v = 0) ∧
        ‖schurContraction P Q R hP hR‖ ≤ 1 := by
  let B := Q * Douglas.pinv R * Qᴴ
  let K := schurContraction P Q R hP hR
  have hB : B.PosSemidef := schurTerm_posSemidef Q R hR
  have hnorm :
      ‖hP.supportInvSqrt * B * hP.supportInvSqrt‖ = ‖K‖ * ‖K‖ := by
    calc
      ‖hP.supportInvSqrt * B * hP.supportInvSqrt‖ = ‖K * Kᴴ‖ := by
        apply congrArg norm
        exact (schurContraction_mul_conjTranspose P Q R hP hR).symm
      _ = ‖Kᴴᴴ * Kᴴ‖ := by rw [Matrix.conjTranspose_conjTranspose]
      _ = ‖Kᴴ‖ * ‖Kᴴ‖ := Matrix.l2_opNorm_conjTranspose_mul_self Kᴴ
      _ = ‖K‖ * ‖K‖ := by rw [Matrix.l2_opNorm_conjTranspose]
  constructor
  · intro hS
    have hkerP := ker_conjTranspose_subset_of_schurComplement_posSemidef
      P Q R hP hR hkerR hS
    have hkerB : ∀ v : Fin D₁ → ℂ, P *ᵥ v = 0 → B *ᵥ v = 0 := by
      intro v hv
      dsimp only [B]
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hkerP v hv, Matrix.mulVec_zero, Matrix.mulVec_zero]
    have hbound :=
      (hP.sub_smul_posSemidef_iff hB one_pos hkerB).mp (by
        simpa only [schurComplement, B, one_smul] using hS)
    rw [one_mul, hnorm] at hbound
    exact ⟨hkerP, by nlinarith [norm_nonneg K]⟩
  · rintro ⟨hkerP, hK⟩
    have hkerB : ∀ v : Fin D₁ → ℂ, P *ᵥ v = 0 → B *ᵥ v = 0 := by
      intro v hv
      dsimp only [B]
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hkerP v hv, Matrix.mulVec_zero, Matrix.mulVec_zero]
    have hbound : 1 * ‖hP.supportInvSqrt * B * hP.supportInvSqrt‖ ≤ 1 := by
      rw [one_mul, hnorm]
      nlinarith [norm_nonneg K]
    have hS := (hP.sub_smul_posSemidef_iff hB one_pos hkerB).mpr hbound
    simpa only [schurComplement, B, one_smul] using hS

/-- A positive block matrix is equivalent to the corrected singular
contraction criterion, with support conditions on both sides of the
off-diagonal block.

**Local fix (Wolf Theorem 5.2, condition (3)):** The printed condition (3) at
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, line 116 contains only
the right-support condition. The left-support condition displayed here is
necessary, as documented in `docs/paper-gaps/schur_complement_tfae.tex`. -/
theorem blockMatrix_posSemidef_iff_contraction
    (P : Matrix (Fin D₁) (Fin D₁) ℂ) (Q : Matrix (Fin D₁) (Fin D₂) ℂ)
    (R : Matrix (Fin D₂) (Fin D₂) ℂ) (hP : P.PosSemidef) (hR : R.PosSemidef) :
    (blockMatrix P Q R).PosSemidef ↔
      (∀ v : Fin D₂ → ℂ, R *ᵥ v = 0 → Q *ᵥ v = 0) ∧
      (∀ v : Fin D₁ → ℂ, P *ᵥ v = 0 → Qᴴ *ᵥ v = 0) ∧
        ‖schurContraction P Q R hP hR‖ ≤ 1 := by
  constructor
  · intro hM
    have hkerR := ker_subset_of_block_psd P Q R hM
    have hS := schurComplement_posSemidef_of_blockMatrix_posSemidef
      P Q R hP hR hM
    exact ⟨hkerR, (schurComplement_posSemidef_iff_contraction
      P Q R hP hR hkerR).mp hS⟩
  · rintro ⟨hkerR, hkerP, hK⟩
    have hS := (schurComplement_posSemidef_iff_contraction
      P Q R hP hR hkerR).mpr ⟨hkerP, hK⟩
    exact blockMatrix_posSemidef_of_schurComplement_posSemidef
      P Q R hP hR hkerR hS

/-- The contraction condition printed in Wolf's Theorem 5.2 does not imply
block positivity in the singular case: take the scalar blocks
`P = 0`, `Q = 1`, and `R = 1`.

**Local fix (Wolf Theorem 5.2, condition (3)):** At
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, line 116, the printed
condition lacks `ker(P) ⊆ ker(Q†)`. The normalized matrix is zero in this
example, whereas the block quadratic form at `(1, -1)` equals `-1`. See
`docs/paper-gaps/schur_complement_tfae.tex`. -/
theorem wolf_condition_three_not_sufficient :
    let P : Matrix (Fin 1) (Fin 1) ℂ := 0
    let Q : Matrix (Fin 1) (Fin 1) ℂ := 1
    let R : Matrix (Fin 1) (Fin 1) ℂ := 1
    let hP : P.PosSemidef := Matrix.PosSemidef.zero
    let hR : R.PosSemidef := Matrix.PosSemidef.one
    (∀ v : Fin 1 → ℂ, R *ᵥ v = 0 → Q *ᵥ v = 0) ∧
      ‖schurContraction P Q R hP hR‖ ≤ 1 ∧
      ¬ (blockMatrix P Q R).PosSemidef := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    simpa using hv
  · rw [schurContraction,
      show (Matrix.PosSemidef.zero (n := Fin 1)).supportInvSqrt = 0 by
      rw [Matrix.PosSemidef.supportInvSqrt,
        ← Matrix.PosSemidef.zero.isHermitian.cfc_eq]
      simp]
    simp
  · intro hM
    have hnonneg := hM.dotProduct_mulVec_nonneg
      (Sum.elim (1 : Fin 1 → ℂ) (-1 : Fin 1 → ℂ))
    rw [block_quadratic_form] at hnonneg
    norm_num [dotProduct, Matrix.mulVec, blockMatrix] at hnonneg

end SchurComplement
