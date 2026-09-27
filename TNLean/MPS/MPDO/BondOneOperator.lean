/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Kraus.Injectivity
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.MPDO.OperatorCyclicSum

/-!
# Matrix product operators of bond dimension one

A matrix product operator tensor of bond dimension one is a family of one-by-one matrices,
so its periodic operator is the tensor product of its one-site matrices, and it is normal
as soon as one of its one-site matrices is nonzero.

## Main results

* `MPOTensor.toMPSTensor_finProdFinEquiv`: the letter of the doubled-index view at an encoded
  pair of physical indices.
* `MPOTensor.mpo_apply_of_bondOne`: the periodic operator of a bond-one tensor is the product
  of its one-site entries.
* `MPOTensor.isNormal_of_bondOne`: a bond-one tensor one of whose one-site matrices is the
  scalar `1` is normal.
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- The letter of the doubled-index view at an encoded pair of physical indices is the
corresponding one-site matrix. -/
@[simp] theorem toMPSTensor_finProdFinEquiv {d D : ℕ} (M : MPOTensor d D) (i j : Fin d) :
    M.toMPSTensor (finProdFinEquiv (i, j)) = M i j := by
  unfold MPOTensor.toMPSTensor
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- The periodic operator of a bond-one tensor is the tensor product of its one-site
matrices. This is the bond-one case of `MPOTensor.mpo_apply_eq_prod_of_forced_bond`: there is
only one closed bond configuration, so no other configuration has to vanish. -/
theorem mpo_apply_of_bondOne {N : ℕ} [NeZero N] {d : ℕ} (M : MPOTensor d 1)
    (σ τ : Fin N → Fin d) :
    M.mpo N σ τ = ∏ k, M (σ k) (τ k) 0 0 := by
  rw [mpo_apply_eq_prod_of_forced_bond M σ τ 0 fun g hg ↦ absurd (Subsingleton.elim g 0) hg]
  rfl

/-- A bond-one tensor one of whose one-site matrices is the scalar `1` is normal: that
matrix already spans the one-by-one matrices. -/
theorem isNormal_of_bondOne {d : ℕ} (M : MPOTensor d 1) (i j : Fin d) (h : M i j 0 0 = 1) :
    Kraus.IsNormal M.toMPSTensor := by
  refine Kraus.IsInjective.isNormal (Submodule.eq_top_of_forall_single_mem _ fun p q => ?_)
  refine Submodule.subset_span ⟨finProdFinEquiv (i, j), ?_⟩
  rw [toMPSTensor_finProdFinEquiv]
  ext a b
  rw [Subsingleton.elim a 0, Subsingleton.elim b 0, Subsingleton.elim p 0,
    Subsingleton.elim q 0, h, Matrix.single_apply_same]

end MPOTensor
