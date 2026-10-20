/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Lattice.PartyCircuit.PreparedSourceGate
import TNLean.Lattice.PartyCircuit.WordRestriction

/-!
# Scalars of gates with no participating parties

A register layout on an empty party type is empty, and every word on that
party type acts as the identity on the scalar memory. Thus a prepared gate
acts by the sum of its original branch coefficients. This sum may vanish,
including when the branch type is empty. The gate's intrinsic contraction
bound implies that its coefficient sum has norm at most one.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), Theorem 5.2, `04-compression.tex`, lines 24–28 and 233–251.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.PairEffect
open ContinuousLinearMap

namespace Word
variable {P : Type} [IsEmpty P] {a b : Layout P}

/-- A branch on no participating parties is the identity on the scalar memory.
Source: polynomial-PEPS manuscript, `04-compression.tex`, lines 24–28 and 233–251. -/
private theorem eval_heq_id_of_isEmpty (w : Word a b) :
    HEq w.eval (ContinuousLinearMap.id ℂ ℂ) := by
  exact (w.eq_nil_and_eval_eq_id_of_parties_eq_empty
    (Finset.eq_empty_of_isEmpty w.parties)).2.2
end Word
namespace Layout
variable {P : Type} [IsEmpty P]
/-- With no parties, every register layout is empty. Source: polynomial-PEPS,
`04-compression.tex`, lines 24–28. -/
private theorem eq_nil_of_isEmpty (a : Layout P) : a = [] := by
  cases a with
  | nil => rfl
  | cons r a => exact isEmptyElim r.owner
end Layout

namespace PreparedSourceGate
variable {P ι : Type} [IsEmpty P] [Fintype ι] {a b : Layout P} {c : ι → ℂ}
/-- A gate on no parties is the scalar sum of its original branch coefficients.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28 and 233–251. -/
theorem eval_heq_coeffSum_smul_id_of_isEmpty (G : PreparedSourceGate c a b) :
    HEq G.eval ((∑ ξ, c ξ) • ContinuousLinearMap.id ℂ ℂ) := by
  cases Layout.eq_nil_of_isEmpty a
  cases Layout.eq_nil_of_isEmpty b
  apply heq_of_eq
  have hbranch : ∀ ξ, (G.branchWord ξ).eval = ContinuousLinearMap.id ℂ ℂ :=
    fun ξ ↦ eq_of_heq ((G.branchWord ξ).eval_heq_id_of_isEmpty)
  simp only [eval, hbranch, ← Finset.sum_smul]
/-- Contractivity bounds the scalar contributed by a zero-party gate.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28 and 233–251. -/
theorem norm_coeffSum_le_one_of_isEmpty (G : PreparedSourceGate c a b) :
    ‖∑ ξ, c ξ‖ ≤ 1 := by
  cases Layout.eq_nil_of_isEmpty a
  cases Layout.eq_nil_of_isEmpty b
  simpa only [eq_of_heq G.eval_heq_coeffSum_smul_id_of_isEmpty, norm_smul,
    norm_id, mul_one] using G.norm_eval_le_one
end PreparedSourceGate
end TNLean.PEPS.PairEffect
