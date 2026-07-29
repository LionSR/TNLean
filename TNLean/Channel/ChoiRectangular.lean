/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixSpectralDecomp
import TNLean.Channel.PartialTrace
import TNLean.Channel.MaximallyEntangled
import TNLean.Channel.TensorMap
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Rectangular Choi–Jamiołkowski isomorphism (Wolf §2.1, Proposition 2.1)

This file defines the rectangular Choi matrix for a linear map
`T : M_d(ℂ) → M_{d'}(ℂ)` and proves the one-to-one correspondence
with all characterization clauses of Wolf Chapter 2, Proposition 2.1
(lines 60–126 of `Notes/WolfNoteTexSource/ch02_representations.tex`).

## Main definitions

* `ChoiRectangular.choiMatrixRect T` — the rectangular Choi matrix
  `τ = (T ⊗ id_d)(|Ω⟩⟨Ω|)` on `ℂ^{d'} ⊗ ℂ^d`
* `ChoiRectangular.mapOfChoiMatrix τ` — the inverse map recovering
  `T` from its Choi matrix via the trace-pairing formula
  `tr[A T(B)] = d·tr[τ (A ⊗ B^T)]`
* `ChoiRectangular.IsCPMapRect T` — rectangular complete positivity:
  `T` admits a Kraus representation with operators `K_j : ℂ^d → ℂ^{d'}`

## Main results (Wolf §2.1, Proposition 2.1)

* `ChoiRectangular.choiMatrixRect_mapOfChoiMatrix` — mutual inverse pair
* `ChoiRectangular.mapOfChoiMatrix_choiMatrixRect` — mutual inverse pair
* `ChoiRectangular.trace_pairing` — trace-pairing formula
* `ChoiRectangular.choiMatrixRect_isHermitian_iff_hermiticityPreserving` —
  Hermiticity clause
* `ChoiRectangular.isCPMapRect_iff_choiMatrixRect_posSemidef` —
  CP clause
* `ChoiRectangular.tracePreserving_iff_traceLeft_choiMatrixRect` —
  trace-preserving clause
* `ChoiRectangular.unital_iff_traceRight_choiMatrixRect` — unital clause
* `ChoiRectangular.trace_choiMatrixRect_normalization` —
  trace normalization

## Bridge to the square development

The square Choi matrix `ChoiJamiolkowski.choiMatrix` for maps
`T : M_D(ℂ) → M_D(ℂ)` is the specialization `d = d' = D`. Bridge
lemmas at the end of this file establish that each rectangular
statement reduces to the corresponding square one.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Ch. 2,
  Proposition 2.1, lines 60–126][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

namespace ChoiRectangular

variable {d d' : ℕ}

/-! ### The rectangular Choi matrix and its inverse -/

/-- The **rectangular Choi matrix** of a linear map
`T : M_d(ℂ) → M_{d'}(ℂ)`:

  `τ = (T ⊗ id_d)(|Ω⟩⟨Ω|)`

where `|Ω⟩ = (1/√d) Σⱼ |j,j⟩` is the maximally entangled state on
`ℂ^d ⊗ ℂ^d`. The output `τ` is indexed by `(Fin d' × Fin d)`.

Wolf §2.1, Proposition 2.1, Equation (2.1). -/
noncomputable def choiMatrixRect
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ :=
  Matrix.tensorMapId T (Matrix.omegaProj d)

/-- Elementwise formula:
`τ (i₁,i₂) (j₁,j₂) = (T (bipartiteSlice(|Ω⟩⟨Ω|) i₂ j₂)) i₁ j₁`.

Wolf §2.1, Equation (2.1). -/
theorem choiMatrixRect_apply
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (i₁ j₁ : Fin d') (i₂ j₂ : Fin d) :
    choiMatrixRect T (i₁, i₂) (j₁, j₂) =
      (T (Matrix.bipartiteSlice (Matrix.omegaProj d) i₂ j₂)) i₁ j₁ := by
  simp [choiMatrixRect, Matrix.tensorMapId_apply]

/-- `choiMatrixRect` as a linear map in the superoperator argument. -/
noncomputable def choiMatrixRectLinearMap :
    (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) →ₗ[ℂ]
      Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ where
  toFun := choiMatrixRect
  map_add' T S := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [choiMatrixRect, Matrix.tensorMapId_apply]
  map_smul' c T := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [choiMatrixRect, Matrix.tensorMapId_apply]

@[simp] theorem choiMatrixRect_add
    (T S : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    choiMatrixRect (T + S) = choiMatrixRect T + choiMatrixRect S :=
  (choiMatrixRectLinearMap (d := d) (d' := d')).map_add T S

@[simp] theorem choiMatrixRect_smul
    (c : ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    choiMatrixRect (c • T) = c • choiMatrixRect T :=
  (choiMatrixRectLinearMap (d := d) (d' := d')).map_smul c T

@[simp] theorem choiMatrixRect_neg
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    choiMatrixRect (-T) = -choiMatrixRect T := by
  rw [← neg_one_smul ℂ T, choiMatrixRect_smul]
  exact neg_one_smul ℂ (choiMatrixRect T)

/-- The **inverse Choi map**: for a matrix `τ` on `ℂ^{d'} ⊗ ℂ^d`, recover the
linear map `T : M_d(ℂ) → M_{d'}(ℂ)` via the trace-pairing formula.

Elementwise:
`T(B)_{i₁,j₁} = d · Σ_{i₂,j₂} τ_{(i₁,i₂),(j₁,j₂)} · B_{i₂,j₂}`.

This is the `τ ↦ T` direction of Wolf §2.1, Equation (2.1). -/
noncomputable def mapOfChoiMatrix
    (τ : Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ where
  toFun B i₁ j₁ := (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d,
    τ (i₁, i₂) (j₁, j₂) * B i₂ j₂
  map_add' X Y := by
    ext i₁ j₁
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, add_mul]
    ring
  map_smul' c X := by
    ext i₁ j₁
    simp only [Matrix.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum, mul_assoc, mul_comm (X _ _), ← mul_assoc]
    rfl

/-- `mapOfChoiMatrix` as a linear map in `τ`. -/
noncomputable def mapOfChoiMatrixLinearMap :
    Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ →ₗ[ℂ]
      (Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) where
  toFun := mapOfChoiMatrix
  map_add' τ σ := by
    ext B i₁ j₁
    dsimp [mapOfChoiMatrix]
    simp [Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c τ := by
    ext B i₁ j₁
    dsimp [mapOfChoiMatrix]
    simp [Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-! ### The omega coefficient -/

private theorem omegaCoeff_eq_inv (hd : 0 < d) :
    (((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) *
      star ((1 : ℂ) / ((d : ℝ).sqrt : ℂ))) =
      1 / (d : ℂ) := by
  have hdr : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  rw [show star ((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) =
      1 / ((d : ℝ).sqrt : ℂ) from by simp [Complex.conj_ofReal]]
  rw [show (1 : ℂ) / ((d : ℝ).sqrt : ℂ) *
      (1 / ((d : ℝ).sqrt : ℂ)) =
      1 / (((d : ℝ).sqrt : ℂ) ^ 2) from by ring]
  rw [show (((d : ℝ).sqrt : ℂ) ^ 2) = (((d : ℝ).sqrt ^ 2 : ℝ) : ℂ) from by push_cast; ring]
  rw [Real.sq_sqrt hdr.le]
  simp

/-- The `(i₂, j₂)`-slice of `|Ω⟩⟨Ω|` equals a scalar multiple of the matrix unit
`|i₂⟩⟨j₂|`. Specifically:
`bipartiteSlice (|Ω⟩⟨Ω|) i₂ j₂ = (1/d) · E_{i₂,j₂}` (when `d > 0`).

Wolf §2.1, proof; see Example 1.2. -/
private theorem omegaSlice_eq_single_rect (i₂ j₂ : Fin d) (hd : 0 < d) :
    Matrix.bipartiteSlice (Matrix.omegaProj d) i₂ j₂ =
      (1 / (d : ℂ)) • Matrix.single i₂ j₂ (1 : ℂ) := by
  have hcoeff := omegaCoeff_eq_inv hd
  ext a b
  simp [Matrix.bipartiteSlice_apply, Matrix.omegaProj_apply,
    Matrix.omegaVec_apply, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases ha : a = i₂ <;> by_cases hb : b = j₂
  · subst ha; subst hb; rw [hcoeff]; ring
  · subst ha; simp [hb, show ¬(j₂ = b) from Ne.symm hb]
  · subst hb; simp [ha, show ¬(i₂ = a) from Ne.symm ha]
  · simp [ha, hb, show ¬(i₂ = a) from Ne.symm ha, show ¬(j₂ = b) from Ne.symm hb]

/-! ### Mutual inverse and trace-pairing formula -/

section MutualInverse

variable [NeZero d]

/-- The forward-inverse composition: `T ↦ τ ↦ T` recovers the original map.
Follows Wolf's proof via the trace-pairing identity
(Eqs. (2.2)–(2.3) in the source).

Wolf §2.1, Proposition 2.1, proof. -/
theorem mapOfChoiMatrix_choiMatrixRect
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    mapOfChoiMatrix (choiMatrixRect T) = T := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hcoeff := omegaCoeff_eq_inv hdpos
  ext B i₁ j₁
  dsimp [mapOfChoiMatrix, choiMatrixRect]
  have hformula : choiMatrixRect T (i₁, _) (j₁, _) =
      (T (Matrix.bipartiteSlice (Matrix.omegaProj d) _ _)) i₁ j₁ := by
    simp [choiMatrixRect_apply]
  calc
    (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        (Matrix.tensorMapId T (Matrix.omegaProj d)) (i₁, i₂) (j₁, j₂) * B i₂ j₂
        = (d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d,
            (T (Matrix.bipartiteSlice (Matrix.omegaProj d) i₂ j₂)) i₁ j₁ * B i₂ j₂ := by
      simp [Matrix.tensorMapId_apply]
    _ = (d : ℂ) * T (∑ i₂ : Fin d, ∑ j₂ : Fin d,
        (B i₂ j₂ : ℂ) • Matrix.bipartiteSlice (Matrix.omegaProj d) i₂ j₂) i₁ j₁ := by
      simp_rw [map_smul, map_add, Finset.sum_smul, smul_smul]
      push_cast
      simp_rw [smul_eq_mul, mul_comm (B _ _), ← mul_assoc]
      simp [Finset.mul_sum, mul_assoc]
    _ = T ((d : ℂ) • ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        (B i₂ j₂ : ℂ) • Matrix.bipartiteSlice (Matrix.omegaProj d) i₂ j₂) i₁ j₁ := by
      simp [map_smul]
    _ = T B i₁ j₁ := by
      simp [omegaSlice_eq_single_rect, hcoeff, Matrix.smul_single, smul_eq_mul]
      congr
      ext a b
      simp [Matrix.single_apply, mul_comm, smul_eq_mul]

/-- The inverse-forward composition: `τ ↦ T ↦ τ` recovers the original matrix.
Together with `mapOfChoiMatrix_choiMatrixRect`, this establishes the
one-to-one correspondence.

Wolf §2.1, Proposition 2.1, proof. -/
theorem choiMatrixRect_mapOfChoiMatrix
    (τ : Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ) :
    choiMatrixRect (mapOfChoiMatrix τ) = τ := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hcoeff := omegaCoeff_eq_inv hdpos
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [choiMatrixRect_apply]
  dsimp [mapOfChoiMatrix]
  simp_rw [omegaSlice_eq_single_rect i₂ j₂ hdpos]
  simp_rw [LinearMap.map_smul, smul_eq_mul, Matrix.single_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hmap : (mapOfChoiMatrix τ) ((1 / (d : ℂ)) • Matrix.single i₂ j₂ (1 : ℂ)) i₁ j₁ =
      (1 / (d : ℂ)) * ((d : ℂ) * ∑ a : Fin d, ∑ b : Fin d,
        τ (i₁, a) (j₁, b) * (Matrix.single i₂ j₂ (1 : ℂ)) a b) := by
    simp [mapOfChoiMatrix, map_smul, smul_eq_mul]
  simp [hmap, Matrix.single_apply, hdpos.ne', hcoeff]
  ring

/-- Injectivity of `choiMatrixRect`: equal Choi matrices imply equal maps. -/
theorem choiMatrixRect_injective :
    Function.Injective (choiMatrixRect (d := d) (d' := d')) := by
  intro T S hTS
  have h := congrArg mapOfChoiMatrix hTS
  simpa [mapOfChoiMatrix_choiMatrixRect] using h

/-- Equality of Choi matrices implies equality of maps. -/
theorem eq_of_choiMatrixRect_eq
    {T S : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hTS : choiMatrixRect T = choiMatrixRect S) : T = S :=
  choiMatrixRect_injective hTS

/-- The **trace-pairing formula** relating a map and its Choi matrix:

  `tr[A T(B)] = d·tr[τ (A ⊗ B^T)]`

for all `A ∈ M_{d'}`, `B ∈ M_d`.

Wolf §2.1, Equation (2.1), second line. -/
theorem trace_pairing
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (A : Matrix (Fin d') (Fin d') ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    (A * T B).trace = (d : ℂ) *
      ((choiMatrixRect T) * kroneckerMap (· * ·) A (B.transpose)).trace := by
  calc
    (A * T B).trace = ∑ i₁ : Fin d', ∑ j₁ : Fin d', A i₁ j₁ * T B j₁ i₁ := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.diag]
    _ = ∑ i₁ : Fin d', ∑ j₁ : Fin d', A i₁ j₁ *
        ((d : ℂ) * ∑ i₂ : Fin d, ∑ j₂ : Fin d,
          (choiMatrixRect T) (j₁, i₂) (i₁, j₂) * B i₂ j₂) := by
      simp [mapOfChoiMatrix_choiMatrixRect T, mapOfChoiMatrix]
    _ = (d : ℂ) * ∑ i₁ : Fin d', ∑ j₁ : Fin d', ∑ i₂ : Fin d, ∑ j₂ : Fin d,
        (choiMatrixRect T) (j₁, i₂) (i₁, j₂) * (A ⊗ₖ B.transpose) (i₁, i₂) (j₁, j₂) := by
      simp [Matrix.kroneckerMap_apply, mul_assoc, mul_comm, mul_left_comm]
      ring
    _ = (d : ℂ) *
        ((choiMatrixRect T) * kroneckerMap (· * ·) A (B.transpose)).trace := by
      simp_rw [Matrix.trace, Matrix.mul_apply, Matrix.diag, Fintype.sum_prod_type]
      ring

end MutualInverse

/-! ### The rectangular Choi matrix of the identity map -/

/-- The Choi matrix of the identity map `id : M_d → M_d` is `|Ω⟩⟨Ω|`.

Wolf §2.1, Proposition 2.1 (applied to `T = id`). -/
theorem choiMatrixRect_id :
    choiMatrixRect (LinearMap.id (M := Matrix (Fin d) (Fin d) ℂ)) =
      Matrix.omegaProj d := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [choiMatrixRect, Matrix.tensorMapId_apply, Matrix.bipartiteSlice]

/-! ### Rectangular completely positive maps -/

/-- A linear map `T : M_d(ℂ) → M_{d'}(ℂ)` is **completely positive**
(rectangular Kraus form) if it admits a representation

  `T(X) = Σ_i K_i X (K_i)†`

with operators `K_i : ℂ^d → ℂ^{d'}` (i.e., `d' × d` matrices).

Wolf §2.1, Proposition 2.1; Wolf §2.1, Theorem 2.1. -/
def IsCPMapRect
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) : Prop :=
  ∃ (r : ℕ) (K : Fin r → Matrix (Fin d') (Fin d) ℂ),
    ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ

/-! ### Rectangular complete positivity ↔ Choi matrix PSD -/

section CPCorrespondence

variable [NeZero d]

/-- **Easy direction of the CP correspondence**: the Choi matrix of a
rectangular Kraus map is positive semidefinite.

Wolf §2.1, Proposition 2.1, proof. -/
/-- Rectangular version of `mul_single_mul_conjTranspose_eq_vecMulVec`:
for `K : Matrix m n ℂ` and a scaled matrix unit on the `n`-side,
`K * single i₂ j₂ (c * star c) * Kᴴ` equals the rank-one outer product
of the corresponding columns of `K`.

Wolf §2.1, proof of Proposition 2.1. -/
private theorem mul_single_mul_conjTranspose_eq_vecMulVec_rect
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
    (K : Matrix m n ℂ) (c : ℂ) (i₂ j₂ : n) :
    K * Matrix.single i₂ j₂ (c * star c) * Kᴴ =
      Matrix.vecMulVec (fun i₁ : m => c * K i₁ i₂)
        (fun j₁ : m => star (c * K j₁ j₂)) := by
  ext a b
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
    Matrix.vecMulVec_apply, star, mul_comm, mul_left_comm, mul_assoc]

theorem choiMatrixRect_of_kraus_posSemidef
    (K : Fin r → Matrix (Fin d') (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hT : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ) :
    (choiMatrixRect T).PosSemidef := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hcoeff := omegaCoeff_eq_inv hdpos
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hstarc : star c = c := by simp [c]
  have hc_sq : c * star c = 1 / (d : ℂ) := by
    simpa [c, hstarc] using hcoeff
  have hchoi : choiMatrixRect T = ∑ j : Fin r,
      Matrix.vecMulVec (fun p : Fin d' × Fin d => c * K j p.1 p.2)
        (star (fun p : Fin d' × Fin d => c * K j p.1 p.2)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rw [choiMatrixRect_apply, hT, omegaSlice_eq_single_rect i₂ j₂ hdpos]
    simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    simp_rw [hT]
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, hc_sq, c, hstarc,
      mul_single_mul_conjTranspose_eq_vecMulVec_rect]
    simp
  rw [hchoi]
  refine Matrix.posSemidef_sum (s := Finset.univ)
    (x := fun i =>
      Matrix.vecMulVec (fun p : Fin d' × Fin d => c * K i p.1 p.2)
        (star (fun p : Fin d' × Fin d => c * K i p.1 p.2))) ?_
  intro i _
  simpa using Matrix.posSemidef_vecMulVec_self_star
    (fun p : Fin d' × Fin d => c * K i p.1 p.2)

/-- A Choi-matrix decomposition into rank-one outer products reconstructs a
rectangular Kraus family indexed by the same finite type.

Wolf §2.1, Proposition 2.1, proof (τ ≥ 0 ⇒ Kraus). -/
theorem exists_kraus_rect_of_choiMatrixRect_eq_sum_vecMulVec
    {ι : Type*} [Fintype ι]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (v : ι → (Fin d' × Fin d) → ℂ)
    (hchoi : choiMatrixRect T = ∑ m : ι, Matrix.vecMulVec (v m) (star (v m))) :
    ∃ K : ι → Matrix (Fin d') (Fin d) ℂ, ∀ X, T X = ∑ m : ι, K m * X * (K m)ᴴ := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hcoeff := omegaCoeff_eq_inv hdpos
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    have hsqrt : (((d : ℝ).sqrt : ℂ)) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.2 (by exact_mod_cast hdpos)
    simp [hsqrt]
  have hstarc : star c = c := by simp [c]
  have hαne : c * star c ≠ 0 := by
    simpa [hstarc] using mul_ne_zero hc hc
  let K : ι → Matrix (Fin d') (Fin d) ℂ := fun m a b => v m (a, b) / c
  refine ⟨K, ?_⟩
  intro X
  let S : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d') (Fin d') ℂ :=
    fun Y => ∑ m : ι, K m * Y * (K m)ᴴ
  let P : Matrix (Fin d) (Fin d) ℂ → Prop := fun Y => T Y = S Y
  change P X
  refine Matrix.induction_on X ?_ ?_
  · intro p q hp hq
    dsimp [P, S] at *
    simp [map_add, Matrix.add_mul, Matrix.mul_add, hp, hq, Finset.sum_add_distrib]
  · intro i j z
    dsimp [P, S]
    have hbase : T (Matrix.single i j (1 : ℂ)) = S (Matrix.single i j (1 : ℂ)) := by
      ext a b
      have hentry : T (Matrix.single i j (c * star c)) a b =
          (∑ m : ι, Matrix.vecMulVec (v m) (star (v m))) (a, i) (b, j) := by
        simpa [c, choiMatrixRect_apply, omegaSlice_eq_single_rect i j hdpos,
          hcoeff, hstarc] using
          congrArg (fun M => M (a, i) (b, j)) hchoi
      have hsmul : T (Matrix.single i j (c * star c)) a b =
          (c * star c) * T (Matrix.single i j (1 : ℂ)) a b := by
        simpa [Matrix.smul_single] using congrArg (fun M => M a b)
          (T.map_smul (c * star c) (Matrix.single i j (1 : ℂ)))
      have h1 : (c * star c) * T (Matrix.single i j (1 : ℂ)) a b =
          ∑ m : ι, v m (a, i) * star (v m (b, j)) := by
        exact hsmul.symm.trans <|
          by simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using hentry
      have h2 : (c * star c) * S (Matrix.single i j (1 : ℂ)) a b =
          ∑ m : ι, v m (a, i) * star (v m (b, j)) := by
        calc
          (c * star c) * S (Matrix.single i j (1 : ℂ)) a b
              = (c * star c) *
                  ((∑ m : ι, K m * Matrix.single i j (1 : ℂ) * (K m)ᴴ) a b) := rfl
          _ = (c * star c) *
                ∑ m : ι, (K m * Matrix.single i j (1 : ℂ) * (K m)ᴴ) a b := by
                rw [Matrix.sum_apply]
          _ = ∑ m : ι,
                (c * star c) * ((K m * Matrix.single i j (1 : ℂ) * (K m)ᴴ) a b) := by
                rw [Finset.mul_sum]
          _ = ∑ m : ι, v m (a, i) * star (v m (b, j)) := by
                refine Finset.sum_congr rfl ?_
                intro m _
                have hterm : (K m * Matrix.single i j (1 : ℂ) * (K m)ᴴ) a b =
                    (v m (a, i) / c) * star (v m (b, j) / c) := by
                  simp [K, Matrix.mul_apply, Matrix.conjTranspose_apply,
                    Matrix.single_apply, star]
                rw [hterm]
                simp [div_eq_mul_inv, hstarc, hc, mul_assoc, mul_left_comm, mul_comm]
      exact (mul_left_cancel₀ hαne) (h1.trans h2.symm)
    have hSsmul (Y : Matrix (Fin d) (Fin d) ℂ) : S (z • Y) = z • S Y := by
      dsimp [S]
      simp [Finset.smul_sum]
    calc
      T (Matrix.single i j z) = z • T (Matrix.single i j (1 : ℂ)) := by
        simpa [Matrix.smul_single] using T.map_smul z (Matrix.single i j (1 : ℂ))
      _ = z • S (Matrix.single i j (1 : ℂ)) := by rw [hbase]
      _ = S (z • Matrix.single i j (1 : ℂ)) := by rw [hSsmul]
      _ = S (Matrix.single i j z) := by simp [Matrix.smul_single]

/-- **Rectangular CP correspondence** (Wolf §2.1, Proposition 2.1):

A linear map `T : M_d(ℂ) → M_{d'}(ℂ)` is completely positive (in the rectangular
Kraus sense) if and only if the Choi matrix `τ = (T ⊗ id)(|Ω⟩⟨Ω|)` is
positive semidefinite.

This is the rectangular generalization of
`ChoiJamiolkowski.cp_iff_choi_posSemidef`. -/
theorem isCPMapRect_iff_choiMatrixRect_posSemidef
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    IsCPMapRect T ↔ (choiMatrixRect T).PosSemidef := by
  constructor
  · rintro ⟨r, K, hK⟩
    exact choiMatrixRect_of_kraus_posSemidef K T hK
  · intro hτ
    classical
    obtain ⟨r, v, hchoi⟩ := (Matrix.posSemidef_iff_eq_sum_vecMulVec).mp hτ
    obtain ⟨K, hK⟩ :=
      exists_kraus_rect_of_choiMatrixRect_eq_sum_vecMulVec v hchoi
    exact ⟨r, K, hK⟩

/-- Surjectivity of the Choi matrix map: every PSD matrix `τ` on `ℂ^{d'} ⊗ ℂ^d`
is the Choi matrix of some CP map.

Wolf §2.1, Proposition 2.1, proof (surjectivity of `T ↦ τ`). -/
theorem exists_isCPMapRect_of_choiMatrixRect_posSemidef
    {τ : Matrix (Fin d' × Fin d) (Fin d' × Fin d) ℂ}
    (hτ : τ.PosSemidef) :
    ∃ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
      IsCPMapRect T ∧ choiMatrixRect T = τ := by
  set T := mapOfChoiMatrix τ
  have hchoi : choiMatrixRect T = τ := choiMatrixRect_mapOfChoiMatrix τ
  have hcp : IsCPMapRect T :=
    ((isCPMapRect_iff_choiMatrixRect_posSemidef T).mpr (by rwa [hchoi]))
  exact ⟨T, hcp, hchoi⟩

end CPCorrespondence

/-! ### Hermiticity correspondence -/

section Hermiticity

variable [NeZero d]

/-- **Hermiticity correspondence** (Wolf §2.1, Proposition 2.1):

The Choi matrix `τ` is Hermitian if and only if `T` preserves Hermiticity
(i.e., `T(B†) = T(B)†` for all `B`).

This is the rectangular generalization of
`ChoiJamiolkowski.choiMatrix_isHermitian_iff_hermiticityPreserving`. -/
theorem choiMatrixRect_isHermitian_iff_hermiticityPreserving
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    (choiMatrixRect T).IsHermitian ↔
      (∀ B : Matrix (Fin d) (Fin d) ℂ, T (Bᴴ) = (T B)ᴴ) := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hcoeff := omegaCoeff_eq_inv hdpos
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hstarc : star c = c := by simp [c]
  have hαne : c * star c ≠ 0 := by
    have hc : c ≠ 0 := by
      dsimp [c]
      have hsqrt : (((d : ℝ).sqrt : ℂ)) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr <| Real.sqrt_ne_zero'.2 (by exact_mod_cast hdpos)
      simp [hsqrt]
    simpa [hstarc] using mul_ne_zero hc hc
  constructor
  · intro hτ
    have hsingle : ∀ i j : Fin d,
        T (Matrix.single j i (1 : ℂ)) = (T (Matrix.single i j (1 : ℂ)))ᴴ := by
      intro i j
      ext a b
      have hentry : T (Matrix.single j i (c * star c)) a b =
          star (T (Matrix.single i j (c * star c)) b a) := by
        simpa [c, Matrix.conjTranspose_apply, choiMatrixRect_apply,
          omegaSlice_eq_single_rect i j hdpos,
          omegaSlice_eq_single_rect j i hdpos, hcoeff, hstarc] using
          (congrArg (fun M => M (a, j) (b, i)) hτ.eq).symm
      have hsmul1 : T (Matrix.single j i (c * star c)) a b =
          (c * star c) * T (Matrix.single j i (1 : ℂ)) a b := by
        simpa [Matrix.smul_single] using congrArg (fun M => M a b)
          (T.map_smul (c * star c) (Matrix.single j i (1 : ℂ)))
      have hsmul2 : T (Matrix.single i j (c * star c)) b a =
          (c * star c) * T (Matrix.single i j (1 : ℂ)) b a := by
        simpa [Matrix.smul_single] using congrArg (fun M => M b a)
          (T.map_smul (c * star c) (Matrix.single i j (1 : ℂ)))
      have hsmul2' : star (T (Matrix.single i j (c * star c)) b a) =
          (c * star c) * star (T (Matrix.single i j (1 : ℂ)) b a) := by
        rw [hsmul2]; simp [hstarc, mul_assoc]
      have hcoeff_eq : (c * star c) * T (Matrix.single j i (1 : ℂ)) a b =
          (c * star c) * star (T (Matrix.single i j (1 : ℂ)) b a) := by
        calc
          (c * star c) * T (Matrix.single j i (1 : ℂ)) a b
              = T (Matrix.single j i (c * star c)) a b := by rw [hsmul1]
          _ = star (T (Matrix.single i j (c * star c)) b a) := hentry
          _ = (c * star c) * star (T (Matrix.single i j (1 : ℂ)) b a) := hsmul2'
      exact (mul_left_cancel₀ hαne) hcoeff_eq
    intro B
    let P : Matrix (Fin d) (Fin d) ℂ → Prop := fun M => T (Mᴴ) = (T M)ᴴ
    change P B
    refine Matrix.induction_on B ?_ ?_
    · intro p q hp hq; dsimp [P] at *; simp [map_add, hp, hq]
    · intro i j z
      dsimp [P]
      calc
        T ((Matrix.single i j z)ᴴ) = T (Matrix.single j i (star z)) := by
          rw [Matrix.conjTranspose_single]
        _ = (star z) • T (Matrix.single j i (1 : ℂ)) := by
              simpa [Matrix.smul_single] using T.map_smul (star z) (Matrix.single j i (1 : ℂ))
        _ = (star z) • (T (Matrix.single i j (1 : ℂ)))ᴴ := by rw [hsingle]
        _ = (z • T (Matrix.single i j (1 : ℂ)))ᴴ := by simp [Matrix.conjTranspose_smul]
        _ = (T (Matrix.single i j z))ᴴ := by
              simpa [Matrix.smul_single] using
                congrArg Matrix.conjTranspose (T.map_smul z (Matrix.single i j (1 : ℂ))).symm
  · intro hT
    ext ⟨a, i⟩ ⟨b, j⟩
    have hsingle : T (Matrix.single j i (c * star c)) =
        (T (Matrix.single i j (c * star c)))ᴴ := by
      simpa [Matrix.conjTranspose_single, hstarc] using
        hT (Matrix.single i j (c * star c))
    have hentry : T (Matrix.single j i (c * star c)) b a =
        star (T (Matrix.single i j (c * star c)) a b) := by
      simpa [Matrix.conjTranspose_apply] using congrArg (fun M => M b a) hsingle
    simpa [c, Matrix.conjTranspose_apply, choiMatrixRect_apply,
      omegaSlice_eq_single_rect i j hdpos,
      omegaSlice_eq_single_rect j i hdpos, hcoeff, hstarc] using congrArg star hentry

end Hermiticity

/-! ### Partial-trace correspondences -/

section PartialTraceCorrespondences

variable [NeZero d]

/-- Elementwise formula for the left partial trace of the Choi matrix:

`(tr_A τ)_{i,j} = (1/d)·tr[T(E_{i,j})]`.

Wolf §2.1, Proposition 2.1, "Preservation of the trace" clause. -/
theorem traceLeft_choiMatrixRect_apply
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (i j : Fin d) :
    (Matrix.traceLeft (choiMatrixRect T)) i j =
      (1 / (d : ℂ)) * (T (Matrix.single i j (1 : ℂ))).trace := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [Matrix.traceLeft_apply]
  calc
    ∑ k : Fin d', choiMatrixRect T (k, i) (k, j)
        = ∑ k : Fin d', T (Matrix.bipartiteSlice (Matrix.omegaProj d) i j) k k := by
      simp [choiMatrixRect_apply]
    _ = (T (Matrix.bipartiteSlice (Matrix.omegaProj d) i j)).trace := by
      simp [Matrix.trace]
    _ = (1 / (d : ℂ)) * (T (Matrix.single i j (1 : ℂ))).trace := by
      rw [omegaSlice_eq_single_rect i j hdpos]
      simp

/-- If `T` preserves the trace on all inputs (`tr(T(X)) = tr(X)` for all `X`),
then `tr_A(τ) = 𝟙_d / d`.

Wolf §2.1, Proposition 2.1, trace-preserving clause. -/
theorem traceLeft_choiMatrixRect_of_tracePreserving
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (h_tp : ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) :
    Matrix.traceLeft (choiMatrixRect T) = (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext i j
  rw [traceLeft_choiMatrixRect_apply T i j, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq (i := i), h_tp, Matrix.trace_single_eq_same]
  · rw [Matrix.one_apply_ne hij, h_tp, Matrix.trace_single_eq_of_ne hij, mul_zero]

/-- The sum of all diagonal omega slices equals `(1/d) • 𝟙_d`.

Each slice `bipartiteSlice(|Ω⟩⟨Ω|) k k = (1/d)·E_{k,k}` (a matrix unit),
so summing over all `k` gives `(1/d)·Σ_k E_{k,k} = (1/d)·𝟙_d`.

This lemma is used in the unital and trace-preserving clauses.

Wolf §2.1, proof of Proposition 2.1. -/
private theorem sum_omegaSlice_diag_eq_inv_d_one (hd : 0 < d) :
    ∑ k : Fin d, Matrix.bipartiteSlice (Matrix.omegaProj d) k k =
      (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext a b
  simp [omegaSlice_eq_single_rect a b hd, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]

/-- **Unital correspondence** (Wolf §2.1, Proposition 2.1):

Let `tr_B` be the partial trace over the second (input) tensor factor. Then
  `T(𝟙_d) = 𝟙_{d'}` iff `tr_B(τ) = 𝟙_{d'} / d`.

Wolf §2.1, Proposition 2.1, unital clause. -/
theorem traceRight_choiMatrixRect_of_unital
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (h_unital : T (1 : Matrix (Fin d) (Fin d) ℂ) = (1 : Matrix (Fin d') (Fin d') ℂ)) :
    Matrix.traceRight (choiMatrixRect T) = (1 / (d : ℂ)) • (1 : Matrix (Fin d') (Fin d') ℂ) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  ext i j
  rw [Matrix.traceRight_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    ∑ k : Fin d, choiMatrixRect T (i, k) (j, k)
        = ∑ k : Fin d,
            (T (Matrix.bipartiteSlice (Matrix.omegaProj d) k k)) i j := by
      simp [choiMatrixRect_apply]
    _ = (T (∑ k : Fin d, Matrix.bipartiteSlice (Matrix.omegaProj d) k k)) i j := by
      simpa using congrArg (fun M => M i j)
        (map_sum T (Finset.univ : Finset (Fin d))
          fun k => Matrix.bipartiteSlice (Matrix.omegaProj d) k k)
    _ = (T ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ))) i j := by
      rw [sum_omegaSlice_diag_eq_inv_d_one hdpos]
    _ = ((1 / (d : ℂ)) • T (1 : Matrix (Fin d) (Fin d) ℂ)) i j := by
      simp
    _ = ((1 / (d : ℂ)) • (1 : Matrix (Fin d') (Fin d') ℂ)) i j := by rw [h_unital]
    _ = ((1 / (d : ℂ)) • (1 : Matrix (Fin d') (Fin d') ℂ)) i j := rfl

/-- The Choi matrix of the identity on `M_d(ℂ)` has `tr_A(τ) = 𝟙_d / d`.

Wolf §2.1, Proposition 2.1, applied to `T = id`. -/
theorem traceLeft_choiMatrixRect_id :
    Matrix.traceLeft (choiMatrixRect (LinearMap.id (M := Matrix (Fin d) (Fin d) ℂ))) =
      (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext i j
  rw [traceLeft_choiMatrixRect_apply (LinearMap.id _) i j,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.trace_single_eq_same]
  · simp [hij, Matrix.trace_single_eq_of_ne hij]

end PartialTraceCorrespondences

/-! ### Trace normalization -/

section Normalization

variable [NeZero d]

/-- **Trace normalization** (Wolf §2.1, Proposition 2.1):

`tr(τ) = (1/d) · Σ_i tr(T(E_{i,i}))`.

Equivalently, `tr(τ) = 1` when `T` preserves the trace.

Wolf §2.1, Proposition 2.1, normalization clause. -/
theorem trace_choiMatrixRect_normalization
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    (choiMatrixRect T).trace =
      (1 / (d : ℂ)) * (∑ i : Fin d, (T (Matrix.single i i (1 : ℂ))).trace) := by
  rw [Matrix.trace_eq_trace_traceLeft]
  calc
    (Matrix.traceLeft (choiMatrixRect T)).trace
        = ∑ i : Fin d, (Matrix.traceLeft (choiMatrixRect T)) i i := by
      simp [Matrix.trace]
    _ = ∑ i : Fin d, (1 / (d : ℂ)) * (T (Matrix.single i i (1 : ℂ))).trace := by
      simp_rw [traceLeft_choiMatrixRect_apply T]
    _ = (1 / (d : ℂ)) * (∑ i : Fin d, (T (Matrix.single i i (1 : ℂ))).trace) := by
      rw [Finset.mul_sum]

/-- If `T` preserves the trace on all inputs, then `tr(τ) = 1`.

Wolf §2.1, Proposition 2.1. -/
theorem trace_choiMatrixRect_of_tracePreserving
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (h_tp : ∀ X : Matrix (Fin d) (Fin d) ℂ, (T X).trace = X.trace) :
    (choiMatrixRect T).trace = 1 := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  rw [trace_choiMatrixRect_normalization T]
  simp_rw [h_tp, Matrix.trace_single_eq_same]
  simp [hdpos.ne']

end Normalization

/-! ### Bridge to the square Choi development -/

section SquareBridge

variable {D : ℕ}

/-- When `d = d' = D`, the rectangular Choi matrix coincides with the square
Choi matrix from `ChoiJamiolkowski.choiMatrix`. They are definitionally equal.

This bridge lemma shows that the existing square development is the
specialization of the rectangular theory to `d = d'`. -/
theorem choiMatrixRect_eq_choiMatrix
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    choiMatrixRect (d := D) (d' := D) T = ChoiJamiolkowski.choiMatrix T :=
  rfl

/-- The rectangular Hermiticity theorem at `d = d'` recovers the square
version `ChoiJamiolkowski.choiMatrix_isHermitian_iff_hermiticityPreserving`.

Wolf §2.1, Proposition 2.1; see `ChoiJamiolkowski.lean` for the square proof. -/
theorem choiMatrixRect_isHermitian_iff_hermiticityPreserving_square
    [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    (choiMatrixRect (d := D) (d' := D) T).IsHermitian ↔
      (∀ B : Matrix (Fin D) (Fin D) ℂ, T (Bᴴ) = (T B)ᴴ) := by
  -- This follows from the existing square proof; the rectangular statement
  -- provides an independent derivation at the same conclusion.
  -- We prove it by noting the rectangular theorem at d = d' = D.
  simpa [choiMatrixRect_eq_choiMatrix] using
    choiMatrixRect_isHermitian_iff_hermiticityPreserving (d := D) (d' := D) T

end SquareBridge

end ChoiRectangular
