/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Arbitrary.ArbitraryTensor
import TNLean.MPS.Tensor.DirectSum.BlockAssembly
import TNLean.MPS.FundamentalTheorem.Arbitrary.GaugeConversions
import TNLean.MPS.FundamentalTheorem.Arbitrary.WeightedSums

/-!
# Block permutations of weighted direct sums, and their complete reducibility

Two weighted direct sums `toTensorFromBlocks μ A` and `toTensorFromBlocks ν B` whose weighted
blocks are gauge related in pairs along a bijection of the block indices are gauge related: the
gauge is a block permutation times the block gauges. The word module of a weighted direct sum of
irreducible blocks is semisimple.

## Main results

* `MPSTensor.isGaugeRelated_toTensorFromBlocks_of_equiv`: block permutation and block gauges.
* `MPSTensor.isSemisimpleModule_wordModule_toTensorFromBlocks`: semisimplicity of the word module.

## Block sums with the same states are gauge equivalent

Let `X` and `Y` be tensors of bond dimension `D`, each gauge related to a block sum
`⨁_k μ_k C_k` with nonzero complex weights and irreducible blocks that have a nonzero letter. If
`X` and `Y` have the same states, they are gauge equivalent.

This contains the case of the irreducible form of arXiv:1708.00029 (Section 2.1, equation
`eq:irreducible-form`, lines 249–253, and the definition at lines 260–262), where the tensor is
such a block sum, the weights are positive and the transfer maps have spectral radius one; the
equality of the bond dimensions is part of the statement here. The relation
`Z A^i = Y B^i Y⁻¹`, `[A^i, Z] = 0` of `thm:bdequal` (lines 643–656) then holds with `Z = 1`; the
blockwise structure of `Z` in that theorem is not stated here.

### Main results

* `MPSTensor.gaugeEquiv_of_sameMPV_of_isGaugeRelated_toTensorFromBlocks`.

### References

* De las Cuevas, Cirac, Schuch, Pérez-García, arXiv:1708.00029, Definition (Irreducible form),
  lines 249–262, and `thm:bdequal`, lines 643–656.
-/

open MPTensor

section

open scoped Matrix

namespace MPSTensor

variable {d : ℕ}

/-- **Block permutation.** If the weighted blocks of two direct sums are gauge related in pairs
along a bijection `e` of the block indices, the two direct sums are gauge related. -/
theorem isGaugeRelated_toTensorFromBlocks_of_equiv {r r' : ℕ} {dim : Fin r → ℕ}
    {dim' : Fin r' → ℕ} {μ : Fin r → ℂ} {ν : Fin r' → ℂ} {A : ∀ k, MPSTensor d (dim k)}
    {B : ∀ k, MPSTensor d (dim' k)} (e : Fin r ≃ Fin r')
    (h : ∀ k, IsGaugeRelated (μ k • A k) (ν (e k) • B (e k))) :
    IsGaugeRelated (toTensorFromBlocks μ A) (toTensorFromBlocks ν B) := by
  classical
  choose X Y hXY hYX hint using h
  have hint' : ∀ k i, (μ k • A k i) * X k = X k * (ν (e k) • B (e k) i) := hint
  refine ⟨∑ k, blockInclusion dim k * X k * (blockInclusion dim' (e k))ᴴ,
    ∑ k, blockInclusion dim' (e k) * Y k * (blockInclusion dim k)ᴴ, ?_, ?_, fun i => ?_⟩
  · simp only [Matrix.sum_mul, Matrix.mul_sum]
    rw [← sum_blockInclusion_mul_conjTranspose dim]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single_of_mem (f := fun l => blockInclusion dim l * X l *
      (blockInclusion dim' (e l))ᴴ * (blockInclusion dim' (e k) * Y k * (blockInclusion dim k)ᴴ))
      k (Finset.mem_univ k)]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (blockInclusion dim' (e k))ᴴ, blockInclusion_conjTranspose_mul_self,
        Matrix.one_mul, ← Matrix.mul_assoc (X k), hXY, Matrix.one_mul]
    · intro l _ hlk
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (blockInclusion dim' (e l))ᴴ,
        blockInclusion_conjTranspose_mul_eq_zero dim' (e.injective.ne hlk),
        Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  · simp only [Matrix.sum_mul, Matrix.mul_sum]
    rw [← sum_blockInclusion_mul_conjTranspose dim',
      ← Equiv.sum_comp e (fun l => blockInclusion dim' l * (blockInclusion dim' l)ᴴ)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single_of_mem (f := fun l => blockInclusion dim' (e l) * Y l *
      (blockInclusion dim l)ᴴ * (blockInclusion dim k * X k * (blockInclusion dim' (e k))ᴴ))
      k (Finset.mem_univ k)]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (blockInclusion dim k)ᴴ, blockInclusion_conjTranspose_mul_self,
        Matrix.one_mul, ← Matrix.mul_assoc (Y k), hYX, Matrix.one_mul]
    · intro l _ hlk
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (blockInclusion dim l)ᴴ,
        blockInclusion_conjTranspose_mul_eq_zero dim hlk,
        Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  · rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [← Matrix.mul_assoc]
    rw [toTensorFromBlocks_mul_blockInclusion, Matrix.mul_assoc (blockInclusion dim k), hint' k i,
      ← Matrix.mul_assoc, Matrix.mul_assoc (blockInclusion dim k * X k),
      ← blockInclusion_conjTranspose_mul_toTensorFromBlocks, ← Matrix.mul_assoc]

/-- **Semisimplicity.** The word module of a weighted direct sum of irreducible blocks is
semisimple. No nonzero letter and no nonzero weight is needed: a block with zero weight acts as
zero, and its word module is a sum of lines. -/
theorem isSemisimpleModule_wordModule_toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) {A : ∀ k, MPSTensor d (dim k)}
    (hirr : ∀ k, Matrix.IsIrreducibleAction (A k)) :
    IsSemisimpleModule (WordAlgebra d) (toTensorFromBlocks μ A).WordModule := by
  classical
  set T := toTensorFromBlocks μ A with hT
  -- the inclusion of the word module of the weighted block `k`
  let f : ∀ k, (μ k • A k).WordModule →ₗ[WordAlgebra d] T.WordModule := fun k =>
    WordAlgebra.linearMapOfLetter
      (((WordModule.toVec T).symm.toLinearMap.comp (Matrix.toLin' (blockInclusion dim k))).comp
        (WordModule.toVec (μ k • A k)).toLinearMap) fun i x => by
      apply (WordModule.toVec T).injective
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply]
      rw [asModuleEquiv_letter_smul, asModuleEquiv_letter_smul, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hT,
        toTensorFromBlocks_mul_blockInclusion]
      rfl
  have hf : ∀ k y, WordModule.toVec T (f k y) =
      blockInclusion dim k *ᵥ WordModule.toVec (μ k • A k) y := fun k y => by
    simp [f]
  -- each weighted block has a semisimple word module
  have hk : ∀ k, IsSemisimpleModule (WordAlgebra d) (μ k • A k).WordModule := by
    intro k
    by_cases hμk : μ k = 0
    · refine isSemisimpleModule_wordModule_of_conjTranspose_mem_adjoin _ fun i => ?_
      simp only [Pi.smul_apply, hμk, zero_smul, Matrix.conjTranspose_zero]
      exact zero_mem _
    · rcases Nat.eq_zero_or_pos (dim k) with h0 | hpos
      · refine isSemisimpleModule_wordModule_of_conjTranspose_mem_adjoin _ fun i => ?_
        have hsub : ((μ k • A k) i)ᴴ = (μ k • A k) i := by
          ext a
          exact absurd a.2 (by omega)
        rw [hsub]
        exact Algebra.subset_adjoin ⟨i, rfl⟩
      · have := (isIrreducibleAction_and_pos_iff_isSimpleModule (μ k • A k)).1
          ⟨isIrreducibleAction_smul (hirr k) hμk, hpos⟩
        infer_instance
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun k => LinearMap.range (f k)) (fun k => ?_) ?_
  · have := hk k
    exact IsSemisimpleModule.range (f k)
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : x = ∑ k, f k ((WordModule.toVec (μ k • A k)).symm
        ((blockInclusion dim k)ᴴ *ᵥ WordModule.toVec T x)) := by
      apply (WordModule.toVec T).injective
      rw [map_sum]
      simp only [hf, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec]
      rw [← Matrix.sum_mulVec, sum_blockInclusion_mul_conjTranspose, Matrix.one_mulVec]
    rw [hx]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.mem_iSup_of_mem k (LinearMap.mem_range_self _ _)

end MPSTensor

end

section

namespace MPSTensor

variable {d D : ℕ}

/-- **Block sums with the same states are gauge equivalent.** Let `X` be gauge related to
`⨁_k μ_k C_k` and `Y` to `⨁_l μ'_l C'_l`, with nonzero weights and irreducible blocks that have a
nonzero letter. If `X` and `Y` have the same states, they are gauge equivalent: the weighted
blocks are gauge related along a bijection of the block indices, hence so are the block sums. -/
theorem gaugeEquiv_of_sameMPV_of_isGaugeRelated_toTensorFromBlocks {r r' : ℕ} {dim : Fin r → ℕ}
    {dim' : Fin r' → ℕ} {blocks : ∀ k, MPSTensor d (dim k)} {blocks' : ∀ k, MPSTensor d (dim' k)}
    {μ : Fin r → ℂ} {μ' : Fin r' → ℂ} {X Y : MPSTensor d D}
    (hμ : ∀ k, μ k ≠ 0) (hμ' : ∀ k, μ' k ≠ 0)
    (hirr : ∀ k, Matrix.IsIrreducibleAction (blocks k)) (hlet : ∀ k, ∃ i, blocks k i ≠ 0)
    (hirr' : ∀ k, Matrix.IsIrreducibleAction (blocks' k)) (hlet' : ∀ k, ∃ i, blocks' k i ≠ 0)
    (hX : IsGaugeRelated (toTensorFromBlocks μ blocks) X)
    (hY : IsGaugeRelated (toTensorFromBlocks μ' blocks') Y) (h : SameMPV X Y) :
    GaugeEquiv X Y := by
  have hsum : ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
      ∑ k, μ k ^ N * mpv (blocks k) σ = ∑ k, μ' k ^ N * mpv (blocks' k) σ := by
    intro N hN σ
    have e1 := hX.sameMPV₂Pos N hN σ
    have e2 := hY.sameMPV₂Pos N hN σ
    rw [mpv_toTensorFromBlocks_eq_sum] at e1 e2
    simp only [smul_eq_mul] at e1 e2
    rw [e1, e2]
    exact h N σ
  obtain ⟨τ, hτ⟩ := (forall_sum_pow_mul_mpv_eq_iff_exists_equiv_isGaugeRelated hirr hlet hirr'
    hlet' hμ hμ').1 hsum
  exact isGaugeRelated_iff_gaugeEquiv.1
    ((hX.symm.trans (isGaugeRelated_toTensorFromBlocks_of_equiv τ hτ)).trans hY)

end MPSTensor

end
