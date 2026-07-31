/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Rectangular Choi matrices and a Hilbert--Schmidt rank estimate

This file contains the algebraic estimate used in
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`.  For a linear map
`L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ`, it defines the unnormalized Choi matrix in the
natural `α × β` ordering and proves its Frobenius Parseval identity.  It also proves that
the squared Frobenius norm is at most `finrank ℂ L.range` whenever `L` is a
Hilbert--Schmidt contraction.

The argument is independent of positivity and channel normalization.

## Main definitions

- `Matrix.linearMapMatrix`: the matrix of a linear map in the matrix-unit bases
- `Matrix.rectangularChoi`: the unnormalized rectangular Choi matrix
- `Matrix.IsHilbertSchmidtContraction`: contraction for the Hilbert--Schmidt norm

## Main results

- `Matrix.rectangularChoi_frobenius_parseval`
- `Matrix.rectangularChoi_frobenius_parseval_matrix_units`
- `Matrix.rectangularChoi_frobenius_sq_le_finrank_range`
-/

open scoped ComplexConjugate ComplexOrder Matrix.Norms.Frobenius

namespace Matrix

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

attribute [local instance] Classical.decEq

/-- The coefficient matrix of a linear map between matrix spaces, in the matrix-unit
bases.  Its rows are indexed by output matrix entries and its columns by input entries. -/
noncomputable def linearMapMatrix
    (L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix (β × β) (α × α) ℂ := by
  classical
  exact LinearMap.toMatrix (stdBasis ℂ α α) (stdBasis ℂ β β) L

/-- The unnormalized rectangular Choi matrix of a linear map, in the natural
`α × β` ordering:
`J(L)_{(i,a),(j,b)} = L(E_{ij})_{a,b}`. -/
noncomputable def rectangularChoi
    (L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix (α × β) (α × β) ℂ := by
  classical
  exact fun ia jb ↦ linearMapMatrix L (ia.2, jb.2) (ia.1, jb.1)

/-- Entrywise formula for the coefficient matrix. -/
@[simp]
theorem linearMapMatrix_apply
    (L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (i j : α) (a b : β) :
    linearMapMatrix L (a, b) (i, j) = L (single i j 1) a b := by
  classical
  rw [linearMapMatrix, LinearMap.toMatrix_apply, stdBasis_eq_single]
  simp [stdBasis, Module.Basis.map_repr, Pi.basis_repr, Pi.basisFun_repr]

/-- Entrywise formula for the rectangular Choi matrix. -/
@[simp]
theorem rectangularChoi_apply
    (L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (i j : α) (a b : β) :
    rectangularChoi L (i, a) (j, b) = L (single i j 1) a b := by
  rw [rectangularChoi, linearMapMatrix_apply]

/-- Reshaping a coefficient matrix into the rectangular Choi matrix preserves its
squared Frobenius norm. -/
theorem rectangularChoi_frobenius_parseval
    (L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    (trace ((rectangularChoi L)ᴴ * rectangularChoi L)).re =
      (trace ((linearMapMatrix L)ᴴ * linearMapMatrix L)).re := by
  classical
  rw [trace_conjTranspose_mul_self_re_eq_sum_norm_sq,
    trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
  simp only [rectangularChoi]
  let e : ((α × β) × (α × β)) ≃ ((α × α) × (β × β)) := {
    toFun x := ((x.2.1, x.1.1), (x.2.2, x.1.2))
    invFun x := ((x.1.2, x.2.2), (x.1.1, x.2.1))
    left_inv := by rintro ⟨⟨j, b⟩, ⟨i, a⟩⟩; rfl
    right_inv := by rintro ⟨⟨i, j⟩, ⟨a, b⟩⟩; rfl }
  calc
    ∑ j : α × β, ∑ i : α × β,
        ‖linearMapMatrix L (i.2, j.2) (i.1, j.1)‖ ^ 2 =
        ∑ x : (α × β) × (α × β),
          ‖linearMapMatrix L (x.2.2, x.1.2) (x.2.1, x.1.1)‖ ^ 2 := by
            exact (Fintype.sum_prod_type (fun x : (α × β) × (α × β) ↦
              ‖linearMapMatrix L (x.2.2, x.1.2) (x.2.1, x.1.1)‖ ^ 2)).symm
    _ = ∑ x : (α × α) × (β × β),
          ‖linearMapMatrix L x.2 x.1‖ ^ 2 :=
        Fintype.sum_equiv e _ _ fun _ ↦ rfl
    _ = ∑ j : α × α, ∑ i : β × β, ‖linearMapMatrix L i j‖ ^ 2 := by
          exact Fintype.sum_prod_type
            (fun x : (α × α) × (β × β) ↦ ‖linearMapMatrix L x.2 x.1‖ ^ 2)

/-- Parseval's identity for the rectangular Choi matrix, expressed as the sum
of the squared absolute values of the images of the matrix units. -/
theorem rectangularChoi_frobenius_parseval_matrix_units
    (L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    (trace ((rectangularChoi L)ᴴ * rectangularChoi L)).re =
      ∑ ij : α × α, ∑ ab : β × β,
        ‖L (single ij.1 ij.2 1) ab.1 ab.2‖ ^ 2 := by
  classical
  rw [rectangularChoi_frobenius_parseval,
    trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ fun ij ↦ by
    simp only [Equiv.refl_apply]
    exact Fintype.sum_equiv (Equiv.refl _) _ _ fun ab ↦ by
      rw [linearMapMatrix_apply L ij.1 ij.2 ab.1 ab.2]
      simp

/-- A linear map between matrix spaces is a Hilbert--Schmidt contraction if it does
not increase the Hilbert--Schmidt quadratic form. -/
def IsHilbertSchmidtContraction
    (L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) : Prop :=
  ∀ X, (trace ((L X)ᴴ * L X)).re ≤ (trace (Xᴴ * X)).re

private theorem star_dotProduct_self_re_eq_sum_norm_sq
    {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
  simp [dotProduct, Complex.sq_norm, ← Complex.normSq_eq_conj_mul_self]

private theorem trace_gram_re_le_rank_of_contraction
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ)
    (hA : ∀ x : n → ℂ,
      (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)).re ≤ (star x ⬝ᵥ x).re) :
    (trace (Aᴴ * A)).re ≤ A.rank := by
  classical
  let G := Aᴴ * A
  have hG : G.IsHermitian := isHermitian_conjTranspose_mul_self A
  have heig_le_one : ∀ i, hG.eigenvalues i ≤ 1 := by
    intro i
    let v : n → ℂ := ⇑(hG.eigenvectorBasis i)
    have hvnorm : ‖hG.eigenvectorBasis i‖ = 1 :=
      hG.eigenvectorBasis.orthonormal.1 i
    have hvinner_complex : star v ⬝ᵥ v = 1 := by
      have hinner :
          inner ℂ (hG.eigenvectorBasis i) (hG.eigenvectorBasis i) = (1 : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, hvnorm]
        simp
      calc
        star v ⬝ᵥ v = v ⬝ᵥ star v := dotProduct_comm _ _
        _ = inner ℂ (hG.eigenvectorBasis i) (hG.eigenvectorBasis i) :=
          (EuclideanSpace.inner_eq_star_dotProduct _ _).symm
        _ = 1 := hinner
    have hvinner : (star v ⬝ᵥ v).re = 1 := by
      rw [hvinner_complex]
      norm_num
    have hgram :
        (star (A *ᵥ v) ⬝ᵥ (A *ᵥ v)).re = hG.eigenvalues i := by
      have hgram_complex :
          star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) =
            (hG.eigenvalues i : ℂ) * (star v ⬝ᵥ v) := by
        rw [dotProduct_comm, star_mulVec, dotProduct_comm,
          ← Matrix.dotProduct_mulVec, mulVec_mulVec,
          hG.mulVec_eigenvectorBasis, RCLike.real_smul_eq_coe_smul (K := ℂ),
          dotProduct_smul, smul_eq_mul, dotProduct_comm]
        rfl
      rw [hgram_complex, hvinner_complex]
      simp
    rw [← hgram, ← hvinner]
    exact hA v
  have hrank :
      A.rank = Fintype.card {i // hG.eigenvalues i ≠ 0} := by
    rw [← rank_conjTranspose_mul_self A]
    exact hG.rank_eq_card_non_zero_eigs
  rw [hG.trace_eq_sum_eigenvalues, Complex.re_sum, hrank]
  calc
    ∑ i, hG.eigenvalues i
        ≤ ∑ i, if hG.eigenvalues i ≠ 0 then (1 : ℝ) else 0 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          by_cases hi : hG.eigenvalues i = 0
          · simp [hi]
          · simpa [hi] using heig_le_one i
    _ = Fintype.card {i // hG.eigenvalues i ≠ 0} := by
          rw [Fintype.card_subtype, Finset.card_filter]
          push_cast
          simp

/-- A Hilbert--Schmidt contraction has squared Choi Frobenius norm at most the
dimension of its range.  This is the algebraic estimate used in
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem rectangularChoi_frobenius_sq_le_finrank_range
    (L : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (hL : IsHilbertSchmidtContraction L) :
    ‖rectangularChoi L‖ ^ 2 ≤ Module.finrank ℂ L.range := by
  classical
  let bα := stdBasis ℂ α α
  let bβ := stdBasis ℂ β β
  let A := linearMapMatrix L
  have hA : ∀ x : (α × α) → ℂ,
      (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
    intro x
    let X : Matrix α α ℂ := bα.equivFun.symm x
    have hx : bα.repr X = x := bα.equivFun.apply_symm_apply x
    have hAx : A *ᵥ x = bβ.repr (L X) := by
      rw [← hx]
      simpa [A, linearMapMatrix, bα, bβ] using
        LinearMap.toMatrix_mulVec_repr bα bβ L X
    rw [hAx, star_dotProduct_self_re_eq_sum_norm_sq,
      star_dotProduct_self_re_eq_sum_norm_sq]
    have hout :
        ∑ p : β × β, ‖(bβ.repr (L X)) p‖ ^ 2 =
          (trace ((L X)ᴴ * L X)).re := by
      have hrepr : ∀ p : β × β, (bβ.repr (L X)) p = L X p.1 p.2 := by
        intro p
        simp [bβ, stdBasis, Module.Basis.map_repr, Pi.basis_repr, Pi.basisFun_repr]
      rw [trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
      simp_rw [hrepr]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
    have hin :
        ∑ p : α × α, ‖x p‖ ^ 2 = (trace (Xᴴ * X)).re := by
      have hrepr : ∀ p : α × α, (bα.repr X) p = X p.1 p.2 := by
        intro p
        simp [bα, stdBasis, Module.Basis.map_repr, Pi.basis_repr, Pi.basisFun_repr]
      rw [← hx, trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
      simp_rw [hrepr]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
    rw [hout, hin]
    exact hL X
  rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    rectangularChoi_frobenius_parseval]
  refine (trace_gram_re_le_rank_of_contraction A hA).trans_eq ?_
  rw [Matrix.rank_eq_finrank_range_toLin A bβ bα]
  have hto : Matrix.toLin bα bβ A = L := by
    simp [A, linearMapMatrix, bα, bβ]
  rw [hto]

end Matrix
