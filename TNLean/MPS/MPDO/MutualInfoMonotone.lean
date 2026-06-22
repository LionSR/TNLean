/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.AreaLaw
import TNLean.Entropy.StrongSubadditivity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Strong subadditivity for contiguous blocks of an MPDO

This file develops the strong-subadditivity (SSA) inequality specialised to a
tripartite split of a configuration on `a + b + c` contiguous spins, as the core
analytic step toward the mutual-information monotonicity of arXiv:1606.00608,
Proposition (`PropILILp1`, line 801).

The axiomatised SSA (`Entropy.strongSubadditivity`) is stated on a flat product
index `Fin dA × Fin dB × Fin dC`. The `tripartiteSplitEquiv` cast carries a
configuration `Fin (a + b + c) → Fin d` onto `Fin (d^a) × Fin (d^b) × Fin (d^c)`,
and `ssa_cast_ineq` transports SSA through that cast (the entropy of the cast
state equals the entropy of the original, by reindex invariance). `traceC_corr`
identifies the tripartite trace over the last factor with the contiguous-block
reduction keeping the first `a + b` spins.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Proposition
  (`PropILILp1`, line 801), Appendix proof (line 1319).
-/

open Matrix
open scoped Matrix ComplexOrder

/-- The cast carrying a configuration on `a + b + c` contiguous spins onto the
flat product `Fin (d^a) × Fin (d^b) × Fin (d^c)` used by the strong-subadditivity
axiom: split into the three contiguous segments, then flatten each. -/
noncomputable def tripartiteSplitEquiv (d a b c : ℕ) :
    (Fin (a + b + c) → Fin d) ≃ Fin (d ^ a) × Fin (d ^ b) × Fin (d ^ c) :=
  (blockSplitEquiv d (a + b) c).trans
    (((blockSplitEquiv d a b).prodCongr (Equiv.refl _)).trans
      ((Equiv.prodAssoc _ _ _).trans
        (finFunctionFinEquiv.prodCongr
          (finFunctionFinEquiv.prodCongr finFunctionFinEquiv))))

/-- The cast carrying a configuration on `a + b` contiguous spins onto the flat
product `Fin (d^a) × Fin (d^b)`. -/
noncomputable def biSplitEquiv (d a b : ℕ) :
    (Fin (a + b) → Fin d) ≃ Fin (d ^ a) × Fin (d ^ b) :=
  (blockSplitEquiv d a b).trans (finFunctionFinEquiv.prodCongr finFunctionFinEquiv)

/-- **Strong subadditivity through the contiguous-block cast.** For a trace-one
positive semidefinite state `σ` on `a + b + c` spins, casting to the flat
product index and applying the SSA axiom yields
`S(σ) + S(tr_AC) ≤ S(tr_C) + S(tr_A)`, where the partial traces are taken of the
cast state. -/
theorem ssa_cast_ineq {d a b c : ℕ}
    (σ : Matrix (Fin (a + b + c) → Fin d) (Fin (a + b + c) → Fin d) ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    vonNeumannEntropy σ hσ.1
      + vonNeumannEntropy (Matrix.traceAC_ABC (σ.submatrix (tripartiteSplitEquiv d a b c).symm
            (tripartiteSplitEquiv d a b c).symm))
          (Matrix.traceAC_ABC_isHermitian (hσ.submatrix _).1)
    ≤ vonNeumannEntropy (Matrix.traceC_ABC (σ.submatrix (tripartiteSplitEquiv d a b c).symm
            (tripartiteSplitEquiv d a b c).symm))
          (Matrix.traceC_ABC_isHermitian (hσ.submatrix _).1)
      + vonNeumannEntropy (Matrix.traceA_ABC (σ.submatrix (tripartiteSplitEquiv d a b c).symm
            (tripartiteSplitEquiv d a b c).symm))
          (Matrix.traceA_ABC_isHermitian (hσ.submatrix _).1) := by
  set E := tripartiteSplitEquiv d a b c with hE
  have hcast : (σ.submatrix E.symm E.symm).PosSemidef ∧ (σ.submatrix E.symm E.symm).trace = 1 :=
    ⟨hσ.submatrix E.symm, by rw [Matrix.trace_submatrix_equiv]; exact htr⟩
  have ssa := Entropy.strongSubadditivity (σ.submatrix E.symm E.symm) hcast
  simp only [Entropy.vonNeumannEntropy] at ssa
  rwa [vonNeumannEntropy_submatrix_equiv E.symm σ hσ.1] at ssa

/-- The tripartite trace over the last factor of the cast state is the
contiguous-block reduction keeping the first `a + b` spins (reindexed by the
bi-split cast). -/
theorem traceC_corr {d a b c : ℕ}
    (σ : Matrix (Fin (a + b + c) → Fin d) (Fin (a + b + c) → Fin d) ℂ) :
    Matrix.traceC_ABC (σ.submatrix (tripartiteSplitEquiv d a b c).symm
        (tripartiteSplitEquiv d a b c).symm)
      = (blockReducedState d (a + b) c σ).submatrix
          (biSplitEquiv d a b).symm (biSplitEquiv d a b).symm := by
  ext ab1 ab2
  simp only [Matrix.traceC_ABC, Matrix.submatrix_apply, blockReducedState,
    Matrix.partialTraceRight_apply, tripartiteSplitEquiv, biSplitEquiv,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.refl_symm,
    Equiv.prodAssoc_symm_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id_eq]
  exact Fintype.sum_equiv finFunctionFinEquiv.symm _ _ (fun _ => rfl)

/-- **Prefix consistency for the reduced block state.** Reducing the first
`a + b + c` spins of the normalized MPO and then keeping the first `a + b` of
those agrees with directly keeping the first `a + b` spins. This identifies the
`traceC`-side of `ssa_cast_ineq` (which keeps the first `a + b` of the `a+b+c`
block) with the `a + b` block entropy. -/
theorem reducedBlockState_prefix {d D : ℕ} (M : MPOTensor d D) {N a b c : ℕ}
    (h3 : a + b + c ≤ N) :
    blockReducedState d (a + b) c (MPOTensor.reducedBlockState M N (a + b + c) h3)
      = MPOTensor.reducedBlockState M N (a + b) ((Nat.le_add_right _ c).trans h3) := by
  rw [MPOTensor.reducedBlockState, blockReducedState_comp]
  have h : (a + b) + (c + (N - (a + b + c))) = (a + b) + (N - (a + b)) := by omega
  rw [← blockReducedState_submatrix_finCongr h, MPOTensor.reducedBlockState]
  congr 1

/-! ## Translation invariance of the block reduced state -/

/-- The normalized periodic MPDO is invariant under a `p`-fold cyclic shift of
both configurations. -/
theorem normalizedMPO_comp_finRotate_pow {d D : ℕ} (M : MPOTensor d D) (N p : ℕ)
    (C C' : Fin N → Fin d) :
    M.normalizedMPO N (C ∘ (finRotate N : Fin N → Fin N)^[p])
        (C' ∘ (finRotate N : Fin N → Fin N)^[p])
      = M.normalizedMPO N C C' := by
  have h := MPOTensor.mpo_submatrix_finRotate_pow M N p
  simp only [MPOTensor.normalizedMPO, Matrix.smul_apply]
  congr 1
  have key := congrFun (congrFun h C) C'
  simpa only [Matrix.submatrix_apply] using key

/-- Closed-form entrywise expansion of the reduced block state. -/
theorem reducedBlockState_eq_sum {d D : ℕ} (M : MPOTensor d D) {N m : ℕ} (hm : m ≤ N)
    (u v : Fin m → Fin d) :
    M.reducedBlockState N m hm u v
      = ∑ w : Fin (N - m) → Fin d,
          M.normalizedMPO N (Fin.append u w ∘ Fin.cast (show N = m + (N - m) by omega))
            (Fin.append v w ∘ Fin.cast (show N = m + (N - m) by omega)) := by
  rw [MPOTensor.reducedBlockState]
  simp only [blockReducedState, partialTraceRight_apply, Matrix.submatrix_apply,
    blockSplitEquiv_symm_apply, MPOTensor.blockReindexEquiv, Equiv.arrowCongr_symm,
    Equiv.refl_symm, finCongr_symm]
  rfl

/-- Appending `u` to a suffix-reindexed config equals reindexing the whole
append: `append u (w ∘ cast) ∘ cast = append u w ∘ cast`. -/
theorem append_glue {d N m k k' : ℕ} (u : Fin m → Fin d) (w : Fin k → Fin d)
    (h1 : k' = k) (h2 : N = m + k') (h3 : N = m + k) :
    (Fin.append u (w ∘ Fin.cast h1)) ∘ Fin.cast h2
      = (Fin.append u w) ∘ Fin.cast h3 := by
  funext j
  simp only [Function.comp_apply]
  rcases lt_or_ge j.val m with hj | hj
  · have hL : Fin.cast h2 j = Fin.castAdd k' ⟨j.val, hj⟩ := by apply Fin.ext; simp
    have hR : Fin.cast h3 j = Fin.castAdd k ⟨j.val, hj⟩ := by apply Fin.ext; simp
    rw [hL, hR, Fin.append_left, Fin.append_left]
  · have hL : Fin.cast h2 j = Fin.natAdd m ⟨j.val - m, by omega⟩ := by apply Fin.ext; simp; omega
    have hR : Fin.cast h3 j = Fin.natAdd m ⟨j.val - m, by omega⟩ := by apply Fin.ext; simp; omega
    rw [hL, hR, Fin.append_right, Fin.append_right]
    rfl

/-- **Translation invariance of the block reduced state (windowed form).** The
reduced state keeping an `m`-block with `p` spins traced out before it and `s`
spins after equals the reduced state keeping the first `m` spins (arXiv:1606.00608,
Prop 4.5 appendix: the entropy of a contiguous block depends only on its length). -/
theorem window_block_entropy {d D : ℕ} (M : MPOTensor d D) {N p m s : ℕ} (hB : N = p + m + s)
    (u v : Fin m → Fin d) :
    ∑ x : Fin p → Fin d, ∑ z : Fin s → Fin d,
        M.normalizedMPO N (Fin.append (Fin.append x u) z ∘ Fin.cast hB)
          (Fin.append (Fin.append x v) z ∘ Fin.cast hB)
      = M.reducedBlockState N m (by omega) u v := by
  rw [reducedBlockState_eq_sum]
  set E : (Fin p → Fin d) × (Fin s → Fin d) ≃ (Fin (N - m) → Fin d) :=
    (Equiv.prodComm _ _).trans
      ((blockSplitEquiv d s p).symm.trans
        (Equiv.arrowCongr (finCongr (show s + p = N - m by omega)) (Equiv.refl (Fin d)))) with hE
  rw [← Equiv.sum_comp E, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
  have hEval : E (x, z) = (Fin.append z x) ∘ Fin.cast (show N - m = s + p by omega) := by
    simp only [hE, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      blockSplitEquiv_symm_apply]
    rfl
  rw [hEval,
    append_glue u (Fin.append z x) (show N - m = s + p by omega)
      (show N = m + (N - m) by omega) (show N = m + (s + p) by omega),
    append_glue v (Fin.append z x) (show N - m = s + p by omega)
      (show N = m + (N - m) by omega) (show N = m + (s + p) by omega),
    window_eq_prefix_rotate x u z (show N = m + (s + p) by omega) hB,
    window_eq_prefix_rotate x v z (show N = m + (s + p) by omega) hB,
    normalizedMPO_comp_finRotate_pow]

/-! ## Block-entropy correspondences and Proposition 4.5 -/

section Prop45
open Function MPOTensor

/-- Collapsing the last `c` spins: summing the `(a+b+c)`-block reduced state over
the last `c` spins gives the `(a+b)`-block reduced state. -/
theorem collapse_last {d D : ℕ} (M : MPOTensor d D) {N a b c : ℕ} (h3 : a + b + c ≤ N)
    (U V : Fin (a + b) → Fin d) :
    ∑ y : Fin c → Fin d,
        M.reducedBlockState N (a + b + c) h3 (Fin.append U y) (Fin.append V y)
      = M.reducedBlockState N (a + b) ((Nat.le_add_right _ c).trans h3) U V := by
  rw [← reducedBlockState_prefix M h3, blockReducedState, partialTraceRight_apply]
  simp only [Matrix.submatrix_apply, blockSplitEquiv_symm_apply]

/-- Flattened-index form of `collapse_last`: the sum ranges over `Fin (d ^ c)`. -/
theorem collapse_last' {d D : ℕ} (M : MPOTensor d D) {N a b c : ℕ} (h3 : a + b + c ≤ N)
    (U V : Fin (a + b) → Fin d) :
    ∑ c' : Fin (d ^ c),
        M.reducedBlockState N (a + b + c) h3
          (Fin.append U (finFunctionFinEquiv.symm c'))
          (Fin.append V (finFunctionFinEquiv.symm c'))
      = M.reducedBlockState N (a + b) ((Nat.le_add_right _ c).trans h3) U V := by
  rw [← collapse_last M h3 U V]
  exact Fintype.sum_equiv finFunctionFinEquiv.symm _ _ (fun _ => rfl)

/-- Collapsing the first `a` spins (translation invariance): summing the
`(a+b)`-block reduced state over the first `a` spins gives the `b`-block reduced
state. -/
theorem collapse_first {d D : ℕ} (M : MPOTensor d D) {N a b : ℕ} (hab : a + b ≤ N)
    (B1 B2 : Fin b → Fin d) :
    ∑ a' : Fin (d ^ a),
        M.reducedBlockState N (a + b) hab
          (Fin.append (finFunctionFinEquiv.symm a') B1)
          (Fin.append (finFunctionFinEquiv.symm a') B2)
      = M.reducedBlockState N b (by omega) B1 B2 := by
  rw [← window_block_entropy M (show N = a + b + (N - (a + b)) by omega) B1 B2]
  rw [Fintype.sum_equiv finFunctionFinEquiv.symm _
    (fun x => M.reducedBlockState N (a + b) hab (Fin.append x B1) (Fin.append x B2))
    (fun _ => rfl)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [reducedBlockState_eq_sum]

/-- **traceC correspondence.** Tracing the third tripartite factor of the cast
reduced state recovers the `(a+b)`-block reduced state. -/
theorem traceC_mat {d D : ℕ} (M : MPOTensor d D) {N a b c : ℕ} (h3 : a + b + c ≤ N) :
    Matrix.traceC_ABC ((M.reducedBlockState N (a + b + c) h3).submatrix
        (tripartiteSplitEquiv d a b c).symm (tripartiteSplitEquiv d a b c).symm)
      = (M.reducedBlockState N (a + b) ((Nat.le_add_right _ c).trans h3)).submatrix
          (biSplitEquiv d a b).symm (biSplitEquiv d a b).symm := by
  rw [traceC_corr, reducedBlockState_prefix]

/-- **traceAC correspondence.** Tracing the first and third tripartite factors of
the cast reduced state recovers the middle `b`-block reduced state (translation
invariance moves the middle block to the front). -/
theorem traceAC_mat {d D : ℕ} (M : MPOTensor d D) {N a b c : ℕ} (h3 : a + b + c ≤ N) :
    ∃ e : Fin (d ^ b) ≃ (Fin b → Fin d),
      Matrix.traceAC_ABC ((M.reducedBlockState N (a + b + c) h3).submatrix
        (tripartiteSplitEquiv d a b c).symm (tripartiteSplitEquiv d a b c).symm)
      = (M.reducedBlockState N b (le_trans (by omega) h3)).submatrix e e := by
  refine ⟨finFunctionFinEquiv.symm, ?_⟩
  ext b1 b2
  simp only [Matrix.submatrix_apply, Matrix.traceAC_ABC, tripartiteSplitEquiv,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id_eq, blockSplitEquiv_symm_apply]
  rw [Finset.sum_congr rfl (fun a' _ => collapse_last' M h3
    (Fin.append (finFunctionFinEquiv.symm a') (finFunctionFinEquiv.symm b1))
    (Fin.append (finFunctionFinEquiv.symm a') (finFunctionFinEquiv.symm b2)))]
  rw [collapse_first M (by omega)]

/-- Reduced block state is invariant under a length-cast of the kept config. -/
theorem reducedBlockState_cast {d D : ℕ} (M : MPOTensor d D) {N k k' : ℕ} (h : k' = k)
    (hk : k ≤ N) (W W' : Fin k → Fin d) :
    M.reducedBlockState N k hk W W'
      = M.reducedBlockState N k' (by omega) (W ∘ Fin.cast h) (W' ∘ Fin.cast h) := by
  subst h; rfl

theorem append_assoc_cast {d a b c : ℕ} (A' : Fin a → Fin d) (B1 : Fin b → Fin d)
    (C1 : Fin c → Fin d) :
    (Fin.append (Fin.append A' B1) C1) ∘ Fin.cast (show a + (b + c) = a + b + c by omega)
      = Fin.append A' (Fin.append B1 C1) := by
  rw [Fin.append_assoc]
  funext i
  simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self]

/-- **traceA correspondence.** Tracing the first tripartite factor of the cast
reduced state recovers the `(b+c)`-block reduced state (translation invariance
moves the kept suffix block to the front). -/
theorem traceA_mat {d D : ℕ} (M : MPOTensor d D) {N a b c : ℕ} (h3 : a + b + c ≤ N) :
    ∃ e : Fin (d ^ b) × Fin (d ^ c) ≃ (Fin (b + c) → Fin d),
      Matrix.traceA_ABC ((M.reducedBlockState N (a + b + c) h3).submatrix
        (tripartiteSplitEquiv d a b c).symm (tripartiteSplitEquiv d a b c).symm)
      = (M.reducedBlockState N (b + c) (le_trans (by omega) h3)).submatrix e e := by
  refine ⟨(finFunctionFinEquiv.symm.prodCongr finFunctionFinEquiv.symm).trans
    (blockSplitEquiv d b c).symm, ?_⟩
  ext bc1 bc2
  obtain ⟨b1, c1⟩ := bc1
  obtain ⟨b2, c2⟩ := bc2
  simp only [Matrix.submatrix_apply, Matrix.traceA_ABC, tripartiteSplitEquiv,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id_eq, blockSplitEquiv_symm_apply,
    Equiv.trans_apply]
  rw [Finset.sum_congr rfl (fun a' _ => by
    rw [reducedBlockState_cast M (show a + (b + c) = a + b + c by omega),
      append_assoc_cast, append_assoc_cast])]
  rw [collapse_first M (a := a) (b := b + c) (by omega)]

/-- Block entropy is congruent in the block length. -/
theorem blockEntropy_congr {d D : ℕ} (M : MPOTensor d D) (N : ℕ) {j k : ℕ} (h : j = k)
    (hj : j ≤ N) (hk : k ≤ N) (hM : (mpo M N).PosSemidef) :
    M.blockEntropy N j hj hM = M.blockEntropy N k hk hM := by
  subst h; rfl

/-- The reduced block state of the normalized MPO has unit trace. -/
theorem reducedBlockState_trace {d D : ℕ} (M : MPOTensor d D) (N L : ℕ) (hL : L ≤ N)
    (htr : (mpo M N).trace ≠ 0) :
    (M.reducedBlockState N L hL).trace = 1 := by
  rw [MPOTensor.reducedBlockState, blockReducedState_trace, Matrix.trace_submatrix_equiv,
    normalizedMPO_trace M N htr]

/-- **Strong subadditivity in block-entropy form.** For contiguous segments of
sizes `a`, `b`, `c` fitting in the chain, the block entropies obey
`S_{a+b+c} + S_b ≤ S_{a+b} + S_{b+c}`. This is one application of strong
subadditivity to the normalized MPDO state (arXiv:1606.00608, Prop 4.5 appendix). -/
theorem ssa_block_entropy {d D : ℕ} (M : MPOTensor d D) {N a b c : ℕ} (h3 : a + b + c ≤ N)
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    M.blockEntropy N (a + b + c) h3 hM + M.blockEntropy N b (le_trans (by omega) h3) hM
      ≤ M.blockEntropy N (a + b) ((Nat.le_add_right _ c).trans h3) hM
        + M.blockEntropy N (b + c) (le_trans (by omega) h3) hM := by
  set σ := M.reducedBlockState N (a + b + c) h3 with hσdef
  have hσ : σ.PosSemidef := reducedBlockState_posSemidef M N (a + b + c) h3 hM
  have htr1 : σ.trace = 1 := reducedBlockState_trace M N (a + b + c) h3 htr
  have ssa := ssa_cast_ineq σ hσ htr1
  obtain ⟨eAC, hAC⟩ := traceAC_mat M h3
  obtain ⟨eA, hA⟩ := traceA_mat M h3
  have hEσ : vonNeumannEntropy σ hσ.1 = M.blockEntropy N (a + b + c) h3 hM :=
    vonNeumannEntropy_congr rfl _ _
  have hEC : vonNeumannEntropy (Matrix.traceC_ABC (σ.submatrix
        (tripartiteSplitEquiv d a b c).symm (tripartiteSplitEquiv d a b c).symm))
        (Matrix.traceC_ABC_isHermitian (hσ.submatrix _).1)
      = M.blockEntropy N (a + b) ((Nat.le_add_right _ c).trans h3) hM := by
    rw [vonNeumannEntropy_congr (traceC_mat M h3) _
      (((reducedBlockState_isHermitian M N (a + b) _ hM)).submatrix _),
      vonNeumannEntropy_submatrix_equiv]
    rfl
  have hEAC : vonNeumannEntropy (Matrix.traceAC_ABC (σ.submatrix
        (tripartiteSplitEquiv d a b c).symm (tripartiteSplitEquiv d a b c).symm))
        (Matrix.traceAC_ABC_isHermitian (hσ.submatrix _).1)
      = M.blockEntropy N b (le_trans (by omega) h3) hM := by
    rw [vonNeumannEntropy_congr hAC _
      (((reducedBlockState_isHermitian M N b _ hM)).submatrix _),
      vonNeumannEntropy_submatrix_equiv]
    rfl
  have hEA : vonNeumannEntropy (Matrix.traceA_ABC (σ.submatrix
        (tripartiteSplitEquiv d a b c).symm (tripartiteSplitEquiv d a b c).symm))
        (Matrix.traceA_ABC_isHermitian (hσ.submatrix _).1)
      = M.blockEntropy N (b + c) (le_trans (by omega) h3) hM := by
    rw [vonNeumannEntropy_congr hA _
      (((reducedBlockState_isHermitian M N (b + c) _ hM)).submatrix _),
      vonNeumannEntropy_submatrix_equiv]
    rfl
  rw [hEσ, hEC, hEAC, hEA] at ssa
  linarith [ssa]

/-- **Proposition 4.5 (arXiv:1606.00608): monotonicity of the mutual information.**
For a normalizable periodic MPDO state and `2 * L + 1 ≤ N`, the mutual information
of an `L`-block is nondecreasing: `I_L ≤ I_{L+1}`. This condition contains the
source range `1 ≤ L < ⌊N / 2⌋`. -/
theorem mutualInfoChain_monotone {d D : ℕ} (M : MPOTensor d D) {N L : ℕ} (hN : 2 * L + 1 ≤ N)
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    M.mutualInfoChain N L (by omega) hM
      ≤ M.mutualInfoChain N (L + 1) (by omega) hM := by
  have key := ssa_block_entropy M (a := 1) (b := L) (c := N - 2 * L - 1) (by omega) hM htr
  rw [blockEntropy_congr M N (show 1 + L + (N - 2 * L - 1) = N - L by omega) _
        (Nat.sub_le N L) hM,
      blockEntropy_congr M N (show (1 : ℕ) + L = L + 1 by omega) _ (by omega) hM,
      blockEntropy_congr M N (show L + (N - 2 * L - 1) = N - (L + 1) by omega) _
        (Nat.sub_le N (L + 1)) hM] at key
  simp only [MPOTensor.mutualInfoChain]
  linarith [key]

/-- Block entropies are nonnegative. -/
theorem blockEntropy_nonneg {d D : ℕ} (M : MPOTensor d D) {N m : ℕ} (hm : m ≤ N)
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    0 ≤ M.blockEntropy N m hm hM :=
  vonNeumannEntropy_nonneg_of_posSemidef_trace_one
    (reducedBlockState_posSemidef M N m hm hM)
    (reducedBlockState_trace M N m hm htr)

/-- **Nonnegativity of the mutual information.** For a normalizable periodic MPDO state,
the mutual information of any block is nonnegative, $0 \le I_L$. This is subadditivity of
the von Neumann entropy applied to the bipartition into the first `L` and last `N - L`
spins (strong subadditivity with a trivial middle subsystem). -/
theorem mutualInfoChain_nonneg {d D : ℕ} (M : MPOTensor d D) {N L : ℕ} (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    0 ≤ M.mutualInfoChain N L hL hM := by
  have key := ssa_block_entropy M (a := L) (b := 0) (c := N - L) (by omega) hM htr
  rw [blockEntropy_congr M N (show L + 0 + (N - L) = N by omega) _ (le_refl N) hM,
    blockEntropy_congr M N (show L + 0 = L by omega) _ hL hM,
    blockEntropy_congr M N (show 0 + (N - L) = N - L by omega) _ (Nat.sub_le N L) hM] at key
  have hS0 : 0 ≤ M.blockEntropy N 0 (Nat.zero_le N) hM := blockEntropy_nonneg M _ hM htr
  simp only [MPOTensor.mutualInfoChain]
  linarith [key, hS0]

/-- **Symmetry of the mutual information across the cut.** The mutual information of the
first `L` spins equals that of their complement: `I_L = I_{N-L}`. Immediate from the
symmetric definition `I_L = S_L + S_{N-L} - S_N`. -/
theorem mutualInfoChain_symm {d D : ℕ} (M : MPOTensor d D) {N L : ℕ} (hL : L ≤ N)
    (hM : (mpo M N).PosSemidef) :
    M.mutualInfoChain N L hL hM = M.mutualInfoChain N (N - L) (Nat.sub_le N L) hM := by
  simp only [MPOTensor.mutualInfoChain]
  rw [blockEntropy_congr M N (show N - (N - L) = L by omega) (Nat.sub_le N (N - L)) hL hM]
  ring

/-- The block entropy of the empty block vanishes, $S_0 = 0$. The reduced state of zero
spins is a one-dimensional density matrix, whose entropy is zero. -/
theorem blockEntropy_zero {d D : ℕ} (M : MPOTensor d D) (N : ℕ)
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    M.blockEntropy N 0 (Nat.zero_le N) hM = 0 := by
  have hPSD : (reducedBlockState M N 0 (Nat.zero_le N)).PosSemidef :=
    reducedBlockState_posSemidef M N 0 (Nat.zero_le N) hM
  have hTr : (reducedBlockState M N 0 (Nat.zero_le N)).trace = 1 :=
    reducedBlockState_trace M N 0 (Nat.zero_le N) htr
  have hcard : Fintype.card (Fin 0 → Fin d) = 1 := by simp
  have hle : (reducedBlockState M N 0 (Nat.zero_le N)).rank ≤ 1 :=
    hcard ▸ Matrix.rank_le_card_width _
  have hupper : M.blockEntropy N 0 (Nat.zero_le N) hM ≤ 0 := by
    have h := vonNeumannEntropy_le_log_rank hPSD hTr
    have hlog : Real.log ((reducedBlockState M N 0 (Nat.zero_le N)).rank : ℝ) ≤ 0 :=
      Real.log_nonpos (by positivity) (by exact_mod_cast hle)
    exact le_trans h hlog
  have hlower : 0 ≤ M.blockEntropy N 0 (Nat.zero_le N) hM := blockEntropy_nonneg M _ hM htr
  linarith

/-- The mutual information of the empty block vanishes, $I_0 = 0$. -/
theorem mutualInfoChain_zero {d D : ℕ} (M : MPOTensor d D) (N : ℕ)
    (hM : (mpo M N).PosSemidef) (htr : (mpo M N).trace ≠ 0) :
    M.mutualInfoChain N 0 (Nat.zero_le N) hM = 0 := by
  simp only [MPOTensor.mutualInfoChain, Nat.sub_zero]
  rw [blockEntropy_zero M N hM htr]
  ring

end Prop45
