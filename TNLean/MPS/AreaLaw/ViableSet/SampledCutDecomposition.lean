/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.CutDecomposition
import TNLean.MPS.AreaLaw.ViableSet.SampledProjector
import TNLean.MPS.AreaLaw.ViableSet.ErrorReduction

/-!
# Simultaneous bond bounds for the sampled left factors

Decompose each sampled word separately. If every word has operator Schmidt rank at
most `D` at every cut, its left factors can be chosen with the same bound at all
internal cuts. The sampled sum therefore has at most `ℓ * D` product terms, while
each left factor still has bond bound `D`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
Claim `c:errorreduction`, decomposition `e:decomp`, lines 584–591.
-/

open Matrix
open scoped BigOperators Kronecker

namespace TNLean.MPS.AreaLaw

private theorem operatorSchmidtRank_cutOperator_endpoint_le_one {L q k : ℕ}
    (hk : k = 0 ∨ L ≤ k) (K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) K) ≤ 1 := by
  classical
  have hs : Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) K Finset.univ := by
    constructor
    · simp
    · intro σ τ σ' τ' hσ hτ _ _
      have hσ' : σ = σ' := funext fun v ↦ hσ v (Finset.mem_univ v)
      have hτ' : τ = τ' := funext fun v ↦ hτ v (Finset.mem_univ v)
      rw [hσ', hτ']
  apply hs.operatorSchmidtRank_cutOperator_le_one
  rcases hk with rfl | hk
  · right
    simp [leftBlock]
  · left
    intro v _
    exact mem_leftBlock.mpr (lt_of_lt_of_le v.isLt hk)

/-- Multiplicity bounds give word-rank bounds at every cut, including the two
endpoints. LVV13, `algo53.tex`, lines 584–591 and 626–649. -/
theorem operatorSchmidtRank_cutOperator_bondComplementWord_le_all {L q m κ : ℕ}
    (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i (i + 2))) (I : Fin m → Fin L)
    (hI : ∀ j, letterCount I j ≤ κ) (k : ℕ) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) (bondComplementWord h I)) ≤ q ^ (2 * κ) := by
  by_cases hk0 : k = 0
  · exact (operatorSchmidtRank_cutOperator_endpoint_le_one (Or.inl hk0) _).trans
      (Nat.one_le_pow _ _ hq)
  by_cases hkL : k < L
  · let b : Fin (L - 1) := ⟨k - 1, by omega⟩
    have hb : b.val + 1 = k := by dsimp [b]; omega
    rw [← hb]
    apply operatorSchmidtRank_cutOperator_bondComplementWord_le h hs b I
    simpa only [letterCount, Fin.ext_iff] using hI ⟨b.val, by omega⟩
  · exact (operatorSchmidtRank_cutOperator_endpoint_le_one (Or.inr (by omega)) _).trans
      (Nat.one_le_pow _ _ hq)

/-- Decompose each sampled word at a fixed cut, retaining its rank bound at all
internal left cuts. LVV13, `algo53.tex`, decomposition `e:decomp`, lines 584–591. -/
theorem exists_sampledProjector_cutDecomposition {L q ℓ m i D : ℕ}
    (hi : i ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (E₀ : ℝ) (I : Fin ℓ → Fin m → Fin L)
    (hrank : ∀ t k, operatorSchmidtRank
      (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k)
        (bondComplementWord h (I t))) ≤ D) :
    ∃ (N : ℕ) (A : Fin N → LeftBlockMatrix L q i)
      (B : Fin N → RightBlockMatrix L q i),
      N ≤ ℓ * D ∧ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i)
        (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B j ∧
      ∀ j k, 0 < k → k < i → operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
          ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ D := by
  classical
  choose N A B hN hdec hleft using fun t ↦
    exists_cutDecomposition_of_operatorSchmidtRank_le hi (bondComplementWord h (I t))
      (hrank t)
  let J := (t : Fin ℓ) × Fin (N t)
  let e := (Fintype.equivFin J).symm
  let c : ℂ := (powerNormalization L E₀ ^ m * (ℓ : ℝ)⁻¹ : ℝ)
  refine ⟨Fintype.card J, fun j ↦ c • A (e j).1 (e j).2,
    fun j ↦ B (e j).1 (e j).2, ?_, ?_, ?_⟩
  · change Fintype.card ((t : Fin ℓ) × Fin (N t)) ≤ _
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun t _ ↦ hN t)
  · rw [Equiv.sum_comp e (fun j : J ↦ (c • A j.1 j.2) ⊗ₖ B j.1 j.2),
      Fintype.sum_sigma]
    simp only [Matrix.smul_kronecker, ← Finset.smul_sum, ← hdec]
    ext x y
    simp [sampledProjector, Entropy.cutOperator, reindex_apply, submatrix_apply,
      Matrix.sum_apply, Matrix.smul_apply, c, mul_assoc]
  · intro j k hk0 hki
    have heq : Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
        ((c • A (e j).1 (e j).2).submatrix leftConfigOfFin leftConfigOfFin) =
        c • Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
          ((A (e j).1 (e j).2).submatrix leftConfigOfFin leftConfigOfFin) := rfl
    rw [heq]
    exact (operatorSchmidtRank_smul_le _ _).trans (hleft _ _ k hk0 hki)

end TNLean.MPS.AreaLaw
