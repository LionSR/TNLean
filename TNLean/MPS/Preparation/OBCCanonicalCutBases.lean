/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentationFactorization
import QICLean.Algebra.CompactSVD
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Weighted Schmidt bases at the physical cuts of an open chain

At each cut, retain the strictly positive singular values of the actual
physical coefficient matrix. Its weighted left singular vectors form a
basis of the cut column space, with positive diagonal Gram matrix. The
coordinates of the physical coefficient columns in this basis are the
right coisometry of that same compact singular-value decomposition.

These choices supply the two simultaneous normalizations needed for the
open-boundary canonical form, without any supplied bond density.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal and its
Schmidt construction, lines 431--458 of Papers/quant-ph_0608197/MPSarchive.tex.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace MPSPreparation

/-- The actual compact singular-value decomposition supplies a cut-space
basis whose weighted prefix Gram matrix is positive diagonal and whose
suffix coordinates are row-coisometric. No density matrix is an input.
Source: PGVWC07, Theorem thm:OBC-Vidal, lines 431--458. -/
theorem exists_weightedSchmidtCutBasis {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    ∃ B : Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k),
    ∃ s : Fin (cutCoefficientRank ψ k) → ℝ,
      (∀ q, 0 < s q) ∧
      (let F : Matrix (CutPrefixConfig d N k) (Fin (cutCoefficientRank ψ k)) ℂ :=
        fun u q ↦ (B q).val u
       Fᴴ * F = Matrix.diagonal (fun q ↦ ((s q : ℂ) ^ 2))) ∧
      (let G : Matrix (Fin (cutCoefficientRank ψ k)) (CutSuffixConfig d N k) ℂ :=
        fun q v ↦ B.repr
          ⟨(cutCoefficientMatrix ψ k).col v, Submodule.subset_span ⟨v, rfl⟩⟩ q
       G * Gᴴ = 1) := by
  classical
  let M := cutCoefficientMatrix ψ k
  let S := Classical.choice (Matrix.exists_compactSVD M)
  let F := S.Vᴴ * S.diagonal
  let T := S.inverseDiagonal * S.V
  have hTF : T * F = 1 := by
    calc
      T * F = S.inverseDiagonal * (S.V * S.Vᴴ) * S.diagonal := by
        simp only [T, F, Matrix.mul_assoc]
      _ = 1 := by
        rw [S.V_mul_conjTranspose, Matrix.mul_one, S.inverseDiagonal_mul_diagonal]
  have hM : M = F * S.U := S.factorization_diagonal
  have hF : F = M * S.Uᴴ := by
    calc
      F = F * (S.U * S.Uᴴ) := by rw [S.U_mul_conjTranspose, Matrix.mul_one]
      _ = (F * S.U) * S.Uᴴ := (Matrix.mul_assoc _ _ _).symm
      _ = M * S.Uᴴ := congrArg (fun X ↦ X * S.Uᴴ) hM.symm
  have hmem : ∀ q, F.col q ∈ cutColumnSpace ψ k := by
    intro q
    rw [cutColumnSpace, ← Matrix.range_mulVecLin]
    refine ⟨S.Uᴴ.col q, ?_⟩
    change M *ᵥ S.Uᴴ.col q = F.col q
    rw [← Matrix.col_mul_eq_mulVec_col, ← hF]
  let b : Fin (cutCoefficientRank ψ k) → cutColumnSpace ψ k :=
    fun q ↦ ⟨F.col q, hmem q⟩
  have hinj : Function.Injective F.mulVec := by
    intro x y hxy
    have h := congrArg T.mulVec hxy
    simpa only [Matrix.mulVec_mulVec, hTF, Matrix.one_mulVec] using h
  have hli : LinearIndependent ℂ b :=
    LinearIndependent.of_comp (cutColumnSpace ψ k).subtype
      (Matrix.mulVec_injective_iff.mp hinj)
  let B := basisOfLinearIndependentOfCardEqFinrank' b hli
    (by simp only [Fintype.card_fin, finrank_cutColumnSpace])
  have hB : ∀ q, (B q).val = F.col q := by
    intro q
    change ((basisOfLinearIndependentOfCardEqFinrank' b hli _) q).val = F.col q
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  have hrepr : ∀ v,
      B.equivFun ⟨M.col v, Submodule.subset_span ⟨v, rfl⟩⟩ = S.U.col v := by
    intro v
    let c : Fin (cutCoefficientRank ψ k) → ℂ := fun q ↦ S.U q v
    have hsum : (⟨M.col v, Submodule.subset_span ⟨v, rfl⟩⟩ : cutColumnSpace ψ k)
        = ∑ q, c q • B q := by
      apply Subtype.val_injective
      funext u
      simp only [Submodule.coe_sum, Submodule.coe_smul, hB, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, c]
      change M u v = ∑ q, S.U q v * F u q
      rw [congrFun (congrFun hM u) v, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun q _ ↦ mul_comm _ _
    rw [hsum, B.equivFun_apply]
    exact B.repr_sum_self c
  refine ⟨B, S.singularValues, S.singularValues_pos, ?_, ?_⟩
  · intro F₀
    have hBF : F₀ = F := by
      funext u q
      exact congrFun (hB q) u
    rw [hBF]
    calc
      Fᴴ * F = S.diagonal * (S.V * S.Vᴴ) * S.diagonal := by
        simp only [F, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          S.diagonal_posDef.isHermitian.eq, Matrix.mul_assoc]
      _ = Matrix.diagonal (fun q ↦ (S.singularValues q : ℂ) ^ 2) := by
        rw [S.V_mul_conjTranspose, Matrix.mul_one, Matrix.CompactSVD.diagonal,
          Matrix.diagonal_mul_diagonal]
        congr 1
        funext q
        exact (pow_two _).symm
  · intro G₀
    have hG : G₀ = S.U := by
      funext q v
      exact congrFun (hrepr v) q
    rw [hG]
    exact S.U_mul_conjTranspose

end MPSPreparation
