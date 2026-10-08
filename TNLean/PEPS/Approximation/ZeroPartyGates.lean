/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.PreparedSourceGate
import TNLean.PEPS.Approximation.WordRestriction
import TNLean.PEPS.Approximation.SourceCircuitLocations

/-!
# Gates with no participating parties

A register layout on an empty party type is empty, and an allowed monomial
on that type acts as the scalar identity. Hence a prepared gate contributes
exactly the sum of its given branch coefficients. Placing the gate beside
arbitrary spectator memory multiplies that memory by the same scalar.
The gate's contraction bound implies that the scalar has norm at most one.

These statements retain the zero-party gates allowed by the manuscript's
classification: only gates on exactly one party are private. An operator
network formed from gates with nonempty participating sets must retain the
product of the excluded scalar contributions. In a density operator the
corresponding factor is the squared norm of this product.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 24–28 and
233–251, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
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
namespace SourceCircuit
variable {P C ι : Type} [IsEmpty C] [Fintype C] [Fintype ι]
/-- Placing a zero-party gate beside arbitrary spectator memory multiplies
that memory by the original coefficient sum. Source: polynomial-PEPS,
`04-compression.tex`, lines 24–28 and 233–251. -/
theorem eval_gate_eq_coeffSum_smul_id_of_isEmpty (owner : C ↪ P)
    {c : ι → ℂ} (G : PreparedSourceGate c ([] : Layout C) []) (tail : Layout P) :
    (SourceCircuit.gate owner G tail).eval =
      (∑ ξ, c ξ) • ContinuousLinearMap.id ℂ (Mem tail) := by
  have hG : G.eval = (∑ ξ, c ξ) • ContinuousLinearMap.id ℂ ℂ :=
    eq_of_heq G.eval_heq_coeffSum_smul_id_of_isEmpty
  have hO : G.evalAtOwners owner = (∑ ξ, c ξ) • ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp [PreparedSourceGate.evalAtOwners, hG, isoL_apply, Layout.mapOwnerIso]
  ext x
  simp only [eval, hO, Layout.mapOwner_nil, rTensor_smul, rTensor_id, comp_apply,
    smul_apply, id_apply, isoL_apply, map_smul, LinearIsometryEquiv.symm_apply_apply]
  rfl
/-- Empty participation forces the literal placed gate to act by its coefficient sum.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28 and 233–251. -/
theorem eval_gate_heq_coeffSum_smul_id_of_participants_eq_empty
    {P C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P)
    {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P)
    (h : (SourceCircuit.gate owner G tail).participants () = ∅) :
    HEq (SourceCircuit.gate owner G tail).eval
      ((∑ ξ, c ξ) • ContinuousLinearMap.id ℂ (Mem tail)) := by
  let : IsEmpty C := ⟨fun q ↦ by
    simpa only [h, Finset.notMem_empty] using
      (show owner q ∈ (SourceCircuit.gate owner G tail).participants () from
        Finset.mem_map.mpr ⟨q, Finset.mem_univ q, rfl⟩)⟩
  cases Layout.eq_nil_of_isEmpty a
  cases Layout.eq_nil_of_isEmpty b
  exact heq_of_eq (eval_gate_eq_coeffSum_smul_id_of_isEmpty owner G tail)
end SourceCircuit
end TNLean.PEPS.PairEffect
