/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.OpenBoundary.OBCCanonicalConfigurations
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationFactorization
import QICLean.Spectral.Eigenvalue.CompactSVD
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Endpoint normalizations of OBC cut factors

For a normalized state, fixing the endpoint basis vectors to one and to
the physical state gives unit prefix Grams and row-coisometric suffix
factors at both endpoints. These are derived endpoint identities, not
additional density or canonical-form assumptions.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal,
condition 3 and normalization in the proof of free-OBC, lines 431--458
and 511--522.

It also contains the following results.

* `MPSPreparation.exists_weightedSchmidtCutBasis`, `MPSPreparation.exists_canonicalCutBasisFamily`:
  weighted Schmidt bases at the physical cuts of an open chain.
-/

section OBCCanonicalEndpoints

open Matrix
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))

include hψ

/-- The fixed initial cut vector has unit Gram matrix.
Source: PGVWC07, Theorem thm:OBC-Vidal, condition 3. -/
theorem cutPrefixMatrix_zero_gram (hB0 : ∀ q, (B 0 q).val = 1) :
    (cutPrefixMatrix ψ B 0)ᴴ * cutPrefixMatrix ψ B 0 = 1 := by
  classical
  let : IsEmpty {s : Fin N // s.val < 0} := ⟨fun s ↦ Nat.not_lt_zero _ s.property⟩
  let : Unique (Fin (cutCoefficientRank ψ 0)) :=
    Equiv.unique (finCongr (cutCoefficientRank_zero ψ hψ))
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, cutPrefixMatrix_zero ψ B hB0]

/-- The fixed final cut vector is normalized with the physical state.
Source: PGVWC07, Theorem thm:OBC-Vidal, condition 3. -/
theorem cutPrefixMatrix_last_gram (hBN : ∀ q, (B N q).val = fullCutVector ψ)
    (hnorm : ∑ σ, star (ψ σ) * ψ σ = 1) :
    (cutPrefixMatrix ψ B N)ᴴ * cutPrefixMatrix ψ B N = 1 := by
  classical
  let : Unique (Fin (cutCoefficientRank ψ N)) :=
    Equiv.unique (finCongr (cutCoefficientRank_last ψ hψ))
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cutPrefixMatrix, hBN,
    Matrix.one_apply_eq]
  change (∑ u, star (ψ (finalCutPrefixEquiv d N u)) * ψ (finalCutPrefixEquiv d N u)) = 1
  rw [Fintype.sum_equiv (finalCutPrefixEquiv d N) _ (fun σ ↦ star (ψ σ) * ψ σ)
    (fun _ ↦ rfl)]
  exact hnorm

/-- The final suffix factor is a row coisometry because the endpoint
cut basis is the complete physical coefficient vector.
Source: PGVWC07, Theorem thm:OBC-Vidal, conditions 1 and 3. -/
theorem cutSuffixMatrix_last_coisometry (hBN : ∀ q, (B N q).val = fullCutVector ψ) :
    cutSuffixMatrix ψ B N * (cutSuffixMatrix ψ B N)ᴴ = 1 := by
  classical
  let : IsEmpty {s : Fin N // N ≤ s.val} := ⟨fun s ↦ (not_le_of_gt s.val.isLt) s.property⟩
  let : Unique (Fin (cutCoefficientRank ψ N)) :=
    Equiv.unique (finCongr (cutCoefficientRank_last ψ hψ))
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, cutSuffixMatrix_last ψ B hBN]

/-- The initial suffix factor is a row coisometry exactly because the
actual physical state is normalized.
Source: PGVWC07, normalization in the proof of free-OBC, lines 511--522. -/
theorem cutSuffixMatrix_zero_coisometry (hB0 : ∀ q, (B 0 q).val = 1)
    (hnorm : ∑ σ, star (ψ σ) * ψ σ = 1) :
    cutSuffixMatrix ψ B 0 * (cutSuffixMatrix ψ B 0)ᴴ = 1 := by
  classical
  let : IsEmpty {s : Fin N // s.val < 0} := ⟨fun s ↦ Nat.not_lt_zero _ s.property⟩
  let : Unique (Fin (cutCoefficientRank ψ 0)) :=
    Equiv.unique (finCongr (cutCoefficientRank_zero ψ hψ))
  have hG : ∀ q v, cutSuffixMatrix ψ B 0 q v = ψ (initialCutSuffixEquiv d N v) := by
    intro q v
    have h := congrArg (fun M ↦ M (default : CutPrefixConfig d N 0) v)
      (cutCoefficientMatrix_eq_prefix_mul_suffix ψ B 0)
    simp only [Matrix.mul_apply, cutPrefixMatrix_zero ψ B hB0, one_mul,
      Fintype.sum_unique] at h
    have hq : (default : Fin (cutCoefficientRank ψ 0)) = q := Subsingleton.elim _ _
    rw [hq] at h
    exact h.symm.trans (by simp [cutCoefficientMatrix, initialCutSuffixEquiv])
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hG, Matrix.one_apply_eq]
  rw [Fintype.sum_equiv (initialCutSuffixEquiv d N) _ (fun σ ↦ ψ σ * star (ψ σ))
    (fun _ ↦ rfl)]
  simpa only [mul_comm] using hnorm

end MPSPreparation

end OBCCanonicalEndpoints

section OBCCanonicalCutBases

/-!
## Weighted Schmidt bases at the physical cuts of an open chain

At each cut, retain the strictly positive singular values of the actual
physical coefficient matrix. Its weighted left singular vectors form a
basis of the cut column space, with positive diagonal Gram matrix. The
coordinates of the physical coefficient columns in this basis are the
right coisometry of that same compact singular-value decomposition.

These choices supply the two simultaneous normalizations needed for the
open-boundary canonical form, without any supplied bond density.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal and its
Schmidt construction, lines 431--458 of Papers/quant-ph_0608197/MPSarchive.tex.

### Simultaneous weighted Schmidt cut bases with exact endpoints

Weighted compact Schmidt bases are chosen independently at all interior
cuts. At the endpoints their vectors are fixed to one and to the actual
normalized state. The resulting prefix Gram matrices are strictly positive
diagonal, and all suffix factors are row-coisometric simultaneously.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal,
conditions 1--3 and the successive Schmidt construction, lines 431--458.
-/

section

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

end

section

open Matrix
open scoped BigOperators ComplexOrder

namespace MPSPreparation

/-- A normalized nonzero chain of positive length has a simultaneous
family of physical cut bases with exact endpoint vectors, positive diagonal
prefix Grams and row-coisometric suffix factors. The densities and their
positivity are constructed from the actual coefficient tensor.
Source: PGVWC07, Theorem thm:OBC-Vidal, lines 431--458. -/
theorem exists_canonicalCutBasisFamily {d N : ℕ} (hN : 0 < N)
    (ψ : (Fin N → Fin d) → ℂ)
    (hnorm : ∑ σ, star (ψ σ) * ψ σ = 1) :
    ∃ B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k),
      (∀ q, (B 0 q).val = 1) ∧ (∀ q, (B N q).val = fullCutVector ψ) ∧
      ∀ k,
        (∃ lam : Fin (cutCoefficientRank ψ k) → ℝ,
          (∀ q, 0 < lam q) ∧
          (cutPrefixMatrix ψ B k)ᴴ * cutPrefixMatrix ψ B k =
            Matrix.diagonal (fun q ↦ (lam q : ℂ))) ∧
        cutSuffixMatrix ψ B k * (cutSuffixMatrix ψ B k)ᴴ = 1 := by
  classical
  have hψ : ψ ≠ 0 := by
    intro hzero
    simp only [hzero, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨E, hE0, hEN⟩ := exists_cutBasisFamily_with_endpoints ψ hψ hN
  choose C s hs hGram hG using fun k ↦ exists_weightedSchmidtCutBasis ψ k
  let B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k) := fun k ↦
    if h0 : k = 0 then by subst k; exact E 0
    else if hlast : k = N then by subst k; exact E N
    else C k
  have hB0 : ∀ q, (B 0 q).val = 1 := by
    intro q
    simpa only [B, dite_eq_left rfl] using hE0 q
  have hBN : ∀ q, (B N q).val = fullCutVector ψ := by
    intro q
    simpa only [B, hN.ne', ↓reduceDIte] using hEN q
  refine ⟨B, hB0, hBN, ?_⟩
  intro k
  by_cases h0 : k = 0
  · subst k
    refine ⟨⟨fun _ ↦ 1, fun _ ↦ one_pos, ?_⟩,
      cutSuffixMatrix_zero_coisometry ψ hψ B hB0 hnorm⟩
    simpa only [Complex.ofReal_one, Matrix.diagonal_one] using
      cutPrefixMatrix_zero_gram ψ hψ B hB0
  by_cases hlast : k = N
  · subst k
    refine ⟨⟨fun _ ↦ 1, fun _ ↦ one_pos, ?_⟩,
      cutSuffixMatrix_last_coisometry ψ hψ B hBN⟩
    simpa only [Complex.ofReal_one, Matrix.diagonal_one] using
      cutPrefixMatrix_last_gram ψ hψ B hBN hnorm
  have hBk : B k = C k := by simp only [B, h0, hlast, ↓reduceDIte]
  have hP : cutPrefixMatrix ψ B k = cutPrefixMatrix ψ C k := by
    unfold cutPrefixMatrix
    rw [hBk]
  have hS : cutSuffixMatrix ψ B k = cutSuffixMatrix ψ C k := by
    unfold cutSuffixMatrix
    rw [hBk]
  refine ⟨⟨fun q ↦ s k q ^ 2, fun q ↦ sq_pos_of_pos (hs k q), ?_⟩, ?_⟩
  · rw [hP]
    have h := hGram k
    simp only [← Complex.ofReal_pow] at h
    exact h
  · rw [hS]
    exact hG k

end MPSPreparation

end

end OBCCanonicalCutBases
