/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.CanonicalArbitraryInteractionDegeneracy

/-!
# Cancellation of unequal weighted canonical block vectors

Three nonzero bond-one blocks satisfy the canonical conditions of PGVWC07,
Theorem 4. At thirteen sites their weighted vectors are pairwise unequal,
but two cancel. An actual positive one-site interaction annihilates their
normalized sum and does not annihilate the first block.

**Local fix (literal weighted finite-vector distinctness):** This example
concerns the literal inequality of the displayed weighted vectors in
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 1321–1330, followed by
Theorem 11 (`2blocks.1`), lines 1407–1422. Interpreting “different states”
projectively excludes the example. The formulation distinction is recorded
in `docs/paper-gaps/pgvwc07_direct_sum_input.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor.CanonicalBlockCancellation

/-- The bond-one product tensor of a computational-basis letter. -/
def basisTensor (b : Fin 2) : MPSTensor 2 1 :=
  fun i => if i = b then 1 else 0

/-- The three source-canonical blocks: two opposite product tensors and a
different product tensor. All three have positive bond dimension. -/
def blocks : Fin 3 → MPSTensor 2 1 :=
  ![basisTensor 0, (-1 : ℂ) • basisTensor 0, basisTensor 1]

/-- The actual weighted direct sum, with all three positive weights equal to one. -/
noncomputable def tensor : MPSTensor 2 (∑ _j : Fin 3, 1) :=
  toTensorFromBlocks (fun _ : Fin 3 => (1 : ℂ)) blocks

private theorem scalar_matrix (X : Matrix (Fin 1) (Fin 1) ℂ) :
    X = X 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- The displayed tensor carries every actual condition of the source's
canonical form, including positive weights and faithful diagonal fixed points.
Source: PGVWC07, Theorem 4, lines 742–762. -/
noncomputable def canonicalData : PGVWC07CanonicalFormData tensor where
  r := 3
  dim := fun _ => 1
  dim_pos _ := by norm_num
  weight := fun _ => 1
  weight_pos _ := by norm_num
  weight_le_one _ := le_rfl
  blocks := blocks
  unital j := by
    fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [blocks, basisTensor]
  dual_fixedPoint j := by
    refine ⟨1, Matrix.PosDef.one, ?_, ?_⟩
    · exact Matrix.isDiag_one
    · fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [blocks, basisTensor]
  fixedPoint_scalar _ X _ := ⟨X 0 0, scalar_matrix X⟩
  index := finSigmaFinEquiv
  reconstruct i := by simp [tensor, toTensorFromBlocks]

private theorem injective_of_letter {A : MPSTensor 2 1} {i : Fin 2}
    {c : ℂ} (hc : c ≠ 0) (hi : A i = c • (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
    Kraus.IsInjective A := by
  apply top_unique
  intro X _
  have hA : A i ∈ Submodule.span ℂ (Set.range A) :=
    Submodule.subset_span ⟨i, rfl⟩
  have hOne : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ Submodule.span ℂ (Set.range A) := by
    have h := (Submodule.span ℂ (Set.range A)).smul_mem c⁻¹ hA
    simpa only [hi, smul_smul, inv_mul_cancel₀ hc, one_smul] using h
  rw [scalar_matrix X]
  exact (Submodule.span ℂ (Set.range A)).smul_mem _ hOne

/-- Every block satisfies the source condition C1 at the common length one. -/
theorem blocks_c1 (j : Fin 3) : Kraus.IsNBlkInjective (blocks j) 1 := by
  apply Kraus.isNBlkInjective_one_of_isInjective
  fin_cases j
  · exact injective_of_letter (i := 0) one_ne_zero (by simp [blocks, basisTensor])
  · exact injective_of_letter (i := 0) (neg_ne_zero.mpr one_ne_zero)
      (by simp [blocks, basisTensor])
  · exact injective_of_letter (i := 1) one_ne_zero (by simp [blocks, basisTensor])

private theorem basisTensor_evalWord (b : Fin 2) (w : List (Fin 2)) :
    Kraus.evalWord (basisTensor b) w =
      if ∀ i ∈ w, i = b then 1 else 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [Kraus.evalWord_cons, ih]
    by_cases hi : i = b <;> simp [basisTensor, hi]

private theorem basisTensor_mpv {N : ℕ} (b : Fin 2) (σ : Cfg 2 N) :
    mpv (basisTensor b) σ = if σ = fun _ => b then 1 else 0 := by
  simp only [mpv, coeff, basisTensor_evalWord, List.forall_mem_ofFn_iff]
  by_cases h : σ = fun _ => b
  · subst σ
    simp
  · have h' : ¬ ∀ k, σ k = b := fun hk => h (funext hk)
    simp [h, h']

private theorem neg_basisTensor_mpv {N : ℕ} (σ : Cfg 2 N) :
    mpv ((-1 : ℂ) • basisTensor 0) σ = (-1 : ℂ) ^ N * mpv (basisTensor 0) σ := by
  simp only [mpv, coeff]
  rw [show ((-1 : ℂ) • basisTensor 0) = fun i => (-1 : ℂ) • basisTensor 0 i from rfl,
    Kraus.evalWord_smul, List.length_ofFn, Matrix.trace_smul, smul_eq_mul]

private theorem basisTensor_state {N : ℕ} (b : Fin 2) :
    mpvState (basisTensor b) N = PiLp.single 2 (fun _ => b) (1 : ℂ) := by
  ext σ
  simp only [mpvState_apply, basisTensor_mpv, PiLp.single_apply]

private theorem blocks_mpv_const (j : Fin 3) (b : Fin 2) :
    mpv (blocks j) (fun _ : Fin 13 => b) =
      ![if b = 0 then 1 else 0, if b = 0 then -1 else 0, if b = 1 then 1 else 0] j := by
  fin_cases j
  · change mpv (basisTensor 0) _ = if b = 0 then 1 else 0
    rw [basisTensor_mpv]
    by_cases hb : b = 0 <;> norm_num [hb, funext_iff]
  · change mpv ((-1 : ℂ) • basisTensor 0) _ = if b = 0 then -1 else 0
    rw [neg_basisTensor_mpv, basisTensor_mpv]
    by_cases hb : b = 0 <;> norm_num [hb, funext_iff]
  · change mpv (basisTensor 1) _ = if b = 1 then 1 else 0
    rw [basisTensor_mpv]
    by_cases hb : b = 1 <;> norm_num [hb, funext_iff]

/-- The actual thirteen-site sum is the normalized all-one product vector. -/
theorem tensor_state_thirteen :
    mpvState tensor 13 = mpvState (basisTensor 1) 13 := by
  ext σ
  simp only [mpvState_apply]
  rw [tensor, mpv_toTensorFromBlocks_eq_sum]
  simp [blocks, Fin.sum_univ_succ]

/-- No vanishing or unnormalized total state is used in the example. -/
theorem norm_tensor_state_thirteen : ‖mpvState tensor 13‖ = 1 := by
  rw [tensor_state_thirteen, basisTensor_state]
  simp

/-- At the chosen source volume the three nonzero weighted block vectors are
pairwise unequal as vectors. Opposite vectors still determine the same ray. -/
theorem blocks_pairwise_ne_thirteen :
    Pairwise fun i j => mpvState (blocks i) 13 ≠ mpvState (blocks j) 13 := by
  intro i j hij heq
  have h0 := congrArg (fun ψ : MPVSpace 2 13 => ψ (fun _ => 0)) heq
  simp only [mpvState_apply, blocks_mpv_const] at h0
  clear heq
  fin_cases i <;> fin_cases j <;> first | exact hij rfl | norm_num at h0

/-- The positive one-site projection penalizing the letter zero. -/
noncomputable def interaction : MPVSpace 2 1 →ₗ[ℂ] MPVSpace 2 1 :=
  Matrix.toEuclideanLin (Matrix.diagonal fun σ : Cfg 2 1 =>
    if σ 0 = 0 then (1 : ℂ) else 0)

/-- Positivity is a property of the actual displayed diagonal projection. -/
theorem interaction_isPositive : interaction.IsPositive := by
  apply Matrix.isPositive_toEuclideanLin_iff.mpr
  apply Matrix.PosSemidef.diagonal
  intro σ
  dsimp only [Pi.zero_apply]
  split_ifs
  exacts [zero_le_one, le_rfl]

private theorem interaction_apply (ψ : MPVSpace 2 1) (σ : Cfg 2 1) :
    interaction ψ σ = (if σ 0 = 0 then (1 : ℂ) else 0) * ψ σ := by
  change (Matrix.diagonal _).mulVec _ σ = _
  exact Matrix.mulVec_diagonal _ _ σ

private theorem interaction_groundSpaceMap (b : Fin 2)
    (X : Matrix (Fin 1) (Fin 1) ℂ) :
    interaction ((WithLp.linearEquiv 2 ℂ (NSiteSpace 2 1)).symm
      (groundSpaceMap (basisTensor b) 1 X)) =
      (if b = 0 then (1 : ℂ) else 0) •
        (WithLp.linearEquiv 2 ℂ (NSiteSpace 2 1)).symm
          (groundSpaceMap (basisTensor b) 1 X) := by
  ext σ
  rw [interaction_apply]
  simp only [PiLp.smul_apply, WithLp.linearEquiv_symm_apply]
  by_cases hσ : σ 0 = b
  · simp [basisTensor, hσ]
  · simp [basisTensor, hσ]

private theorem local_interaction_product {N : ℕ} (hN : 1 ≤ N)
    (i : Fin N) (b : Fin 2) :
    periodicLocalInteractionES interaction i (mpvState (basisTensor b) N) =
      (if b = 0 then (1 : ℂ) else 0) • mpvState (basisTensor b) N := by
  let U := cyclicActiveBlockConfigLinearIsometryEquiv 2 1 hN i
  apply U.injective
  rw [map_smul]
  rw [cyclicActiveBlock_periodicLocalInteractionES_apply interaction hN i]
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  have hfiber : ContinuousLinearMap.rightFiber (U (mpvState (basisTensor b) N)) τ =
      (WithLp.linearEquiv 2 ℂ (NSiteSpace 2 1)).symm
        (groundSpaceMap (basisTensor b) 1 (Kraus.evalWord (basisTensor b) (List.ofFn τ))) := by
    ext σ'
    exact cyclicActiveBlock_mpvState_apply (basisTensor b) hN i σ' τ
  change (ContinuousLinearMap.rightFiberwiseMap
    (LinearMap.toContinuousLinearMap interaction) (U (mpvState (basisTensor b) N)))
      (σ, τ) = _
  rw [ContinuousLinearMap.rightFiberwiseMap_apply_apply, hfiber,
    LinearMap.coe_toContinuousLinearMap', interaction_groundSpaceMap]
  simp only [PiLp.smul_apply, WithLp.linearEquiv_symm_apply]
  simp only [U, cyclicActiveBlock_mpvState_apply]
  rfl

/-- The actual normalized sum is killed by the actual positive periodic
Hamiltonian at the exact source volume bound (13=3(3-1)(1+1)+1). -/
theorem tensor_ground_thirteen :
    periodicInteractionHamiltonianES interaction 13 (mpvState tensor 13) = 0 := by
  rw [tensor_state_thirteen, periodicInteractionHamiltonianES, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simpa using local_interaction_product (by norm_num : 1 ≤ 13) i 1

/-- The first nonzero canonical block is not a ground vector. This contradicts
the first conclusion of PGVWC07 Theorem 11 under the literal weighted
finite-vector reading, not a projective reading of “different states.” -/
theorem first_block_not_ground_thirteen :
    periodicInteractionHamiltonianES interaction 13 (mpvState (blocks 0) 13) ≠ 0 := by
  intro hzero
  have hlocal := (WeightedPositiveKernel.apply_sum_eq_zero_iff
    (fun i : Fin 13 => periodicLocalInteractionES_isPositive interaction_isPositive i)
      (mpvState (blocks 0) 13)).mp hzero 0
  have hfixed : periodicLocalInteractionES interaction (0 : Fin 13)
      (mpvState (basisTensor 0) 13) = mpvState (basisTensor 0) 13 := by
    simpa only [↓reduceIte, one_smul] using
      local_interaction_product (by norm_num : 1 ≤ 13) (0 : Fin 13) 0
  change periodicLocalInteractionES interaction (0 : Fin 13)
    (mpvState (basisTensor 0) 13) = 0 at hlocal
  rw [hfixed] at hlocal
  have hcoeff := congrArg (fun ψ : MPVSpace 2 13 => ψ (fun _ => 0)) hlocal
  simp only [mpvState_apply, PiLp.zero_apply] at hcoeff
  rw [basisTensor_mpv] at hcoeff
  simp at hcoeff

/-- Every displayed component is nonzero at the chosen source volume. -/
theorem blocks_nonzero_thirteen (j : Fin 3) : mpvState (blocks j) 13 ≠ 0 := by
  intro hzero
  have h0 := congrArg (fun ψ : MPVSpace 2 13 => ψ (fun _ => 0)) hzero
  have h1 := congrArg (fun ψ : MPVSpace 2 13 => ψ (fun _ => 1)) hzero
  simp only [mpvState_apply, blocks_mpv_const, PiLp.zero_apply] at h0 h1
  fin_cases j <;> simp_all

/-- An actual instance of all standing assumptions at the exact source bound
violates the first conclusion under the literal weighted finite-vector reading.
Source: PGVWC07, lines 1314–1330 and Theorem 11, lines 1407–1422. -/
theorem literal_weighted_vector_counterexample :
    canonicalData.r = 3 ∧
    (∀ j, Kraus.IsNBlkInjective (canonicalData.blocks j) 1) ∧
    (∀ j, mpvState (canonicalData.blocks j) 13 ≠ 0) ∧
    Pairwise (fun i j =>
      (canonicalData.weight i : ℂ) ^ 13 • mpvState (canonicalData.blocks i) 13 ≠
      (canonicalData.weight j : ℂ) ^ 13 • mpvState (canonicalData.blocks j) 13) ∧
    13 = 3 * (canonicalData.r - 1) * (1 + 1) + 1 ∧
    ‖mpvState tensor 13‖ = 1 ∧ interaction.IsPositive ∧
    periodicInteractionHamiltonianES interaction 13 (mpvState tensor 13) = 0 ∧
    periodicInteractionHamiltonianES interaction 13
      (mpvState (canonicalData.blocks (0 : Fin 3)) 13) ≠ 0 := by
  refine ⟨rfl, blocks_c1, blocks_nonzero_thirteen, ?_, by decide,
    norm_tensor_state_thirteen, interaction_isPositive, tensor_ground_thirteen,
    first_block_not_ground_thirteen⟩
  simpa only [canonicalData, Complex.ofReal_one, one_pow, one_smul] using
    blocks_pairwise_ne_thirteen

end MPSTensor.CanonicalBlockCancellation
