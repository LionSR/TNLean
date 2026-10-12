/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyPartition

/-! # The scalar-unit identification of a tensor memory

Appending an empty memory introduces a scalar tensor factor. Scalar one gives
exactly the memory identification associated with the empty-list equality.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`, lines 246–267.
-/
noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}
namespace Layout
/-- Appending the scalar unit is the literal identification with an empty final
memory. Source: polynomial-PEPS, `04-compression.tex`, lines 246–267. -/
theorem memCongr_append_nil_appendIso_symm_tmul (a : Layout P) (x : Mem a) (z : ℂ) :
    memCongr (List.append_nil a) ((appendIso a []).symm (x ⊗ₜ[ℂ] z)) = z • x := by
  induction a with
  | nil => simp [appendIso, memCongr, mul_comm]
  | cons r a ih =>
      induction x using TensorProduct.inductionOn with
      | tmul u v =>
          rw [appendIso_symm_cons_tmul, memCongr_cons_tmul r (List.append_nil a), ih]
          exact TensorProduct.tmul_smul z u v
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy, smul_add]

/-- A source vector tensored with scalar one is exactly its empty-memory
transport, rather than a supplied coordinate identity.
Source: polynomial-PEPS, `04-compression.tex`, lines 246–267. -/
theorem appendIso_symm_tmul_one_eq_memCongr_symm (a : Layout P) (x : Mem a) :
    (appendIso a []).symm (x ⊗ₜ[ℂ] (1 : ℂ)) = (memCongr (List.append_nil a)).symm x := by
  apply (memCongr (List.append_nil a)).injective
  simpa only [LinearIsometryEquiv.apply_symm_apply, one_smul] using
    memCongr_append_nil_appendIso_symm_tmul a x 1
end Layout
end TNLean.PEPS.PairEffect
