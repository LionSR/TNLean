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
