/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.BipartiteSupportAlgebra

/-!
# Support algebras of the two canonical full tensor factors

The full left factor has full left support and scalar right support; the
full right factor has scalar left support and full right support. These
coefficient calculations are used in the direct GNVW shift normalization.

Source: GNVW, arXiv:0910.3675v2, equation RR2x and the shift example,
lines 1251--1268. The nonempty spectator factor is exactly what makes its
diagonal coefficient recover the non-scalar full factor.
-/

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The left support of the full left tensor factor is the whole first
matrix algebra; GNVW, arXiv:0910.3675v2, shift example after RR2x. -/
theorem leftSupportAlgebra_range_leftKroneckerEmbed [Nonempty n] :
    leftSupportAlgebra (leftKroneckerEmbed (m := m) (n := n)).range = ⊤ := by
  classical
  let j : n := Classical.choice inferInstance
  apply eq_top_iff.mpr
  intro A _
  have hcoeff : bipartiteSlice (leftKroneckerEmbed (n := n) A) j j = A := by
    ext i k
    simp [bipartiteSlice_apply, leftKroneckerEmbed_apply, kroneckerMap_apply]
  rw [← hcoeff]
  have hA : leftKroneckerEmbed (n := n) A ∈
      (leftKroneckerEmbed (m := m) (n := n)).range := ⟨A, rfl⟩
  exact bipartite_slice_mem_left_support_algebra
    (leftKroneckerEmbed (m := m) (n := n)).range hA j j

/-- The right support of the full left tensor factor consists of scalars;
GNVW, arXiv:0910.3675v2, shift example after RR2x. -/
theorem rightSupportAlgebra_range_leftKroneckerEmbed :
    rightSupportAlgebra (leftKroneckerEmbed (m := m) (n := n)).range = ⊥ := by
  apply eq_bot_iff.mpr
  apply (right_support_algebra_le_iff _ _).mpr
  intro X hX i j
  obtain ⟨A, rfl⟩ := hX
  rw [StarSubalgebra.mem_bot]
  refine ⟨A i j, ?_⟩
  ext k l
  simp [Algebra.algebraMap_eq_smul_one, operatorBlock_apply, leftKroneckerEmbed_apply,
    kroneckerMap_apply, smul_apply, smul_eq_mul]

/-- The left support of the full right tensor factor consists of scalars;
GNVW, arXiv:0910.3675v2, inverse orientation of the shift example. -/
theorem leftSupportAlgebra_range_rightKroneckerEmbed :
    leftSupportAlgebra (rightKroneckerEmbed (m := m) (n := n)).range = ⊥ := by
  apply eq_bot_iff.mpr
  apply (left_support_algebra_le_iff _ _).mpr
  intro X hX i j
  obtain ⟨A, rfl⟩ := hX
  rw [StarSubalgebra.mem_bot]
  refine ⟨A i j, ?_⟩
  ext k l
  simp [Algebra.algebraMap_eq_smul_one, bipartiteSlice_apply, rightKroneckerEmbed_apply,
    kroneckerMap_apply, smul_apply, smul_eq_mul, mul_comm]

/-- The right support of the full right tensor factor is the whole second
matrix algebra; GNVW, arXiv:0910.3675v2, inverse orientation of the shift example. -/
theorem rightSupportAlgebra_range_rightKroneckerEmbed [Nonempty m] :
    rightSupportAlgebra (rightKroneckerEmbed (m := m) (n := n)).range = ⊤ := by
  classical
  let i : m := Classical.choice inferInstance
  apply eq_top_iff.mpr
  intro A _
  have hcoeff : operatorBlock (rightKroneckerEmbed (m := m) A) i i = A := by
    ext j k
    simp [operatorBlock_apply, rightKroneckerEmbed_apply, kroneckerMap_apply]
  rw [← hcoeff]
  have hA : rightKroneckerEmbed (m := m) A ∈
      (rightKroneckerEmbed (m := m) (n := n)).range := ⟨A, rfl⟩
  exact operator_block_mem_right_support_algebra
    (rightKroneckerEmbed (m := m) (n := n)).range hA i i

end Matrix
