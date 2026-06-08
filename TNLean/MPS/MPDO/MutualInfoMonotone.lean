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
