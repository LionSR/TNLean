/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ZeroPartyGates

/-! # Scalar operations at empty participating sets

Empty-participant gates retain their actual coefficient sums. Their product is
contractive, and a chronology on an empty party type is exactly this scalar
operation on the empty tensor product.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The product of the original coefficient sums at gates with no participants.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28 and 565–588. -/
def emptyGateScalar : {a b : Layout P} → SourceCircuit a b → ℂ
  | _, _, .id _ => 1
  | _, _, .comp w v => emptyGateScalar w * emptyGateScalar v
  | _, _, .localMap .. => 1
  | _, _, @SourceCircuit.gate _ C ι _ _ _ _ _ c _ _ => by
      classical
      exact if Nonempty C then 1 else ∑ ξ : ι, c ξ
  | _, _, .swap .. => 1
  | _, _, .frame _ w => emptyGateScalar w

/-- An actual gate with an empty local party type contributes its coefficient sum.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28 and 565–588. -/
theorem emptyGateScalar_gate_of_isEmpty {C ι : Type} [IsEmpty C] [Fintype C] [Fintype ι]
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) :
    (SourceCircuit.gate owner G tail).emptyGateScalar = ∑ ξ, c ξ := by
  simp only [emptyGateScalar, not_nonempty_iff.mpr (inferInstance : IsEmpty C), ↓reduceIte]

/-- The scalar contributed by all empty-participant gates is a contraction.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28 and 565–588. -/
theorem norm_emptyGateScalar_le_one {a b : Layout P} (w : SourceCircuit a b) :
    ‖w.emptyGateScalar‖ ≤ 1 := by
  induction w with
  | id => exact le_of_eq norm_one
  | comp w v ihw ihv =>
      exact (norm_mul_le _ _).trans
        (by simpa only [one_mul] using mul_le_mul ihw ihv (norm_nonneg _) zero_le_one)
  | localMap => exact le_of_eq norm_one
  | @gate C ι _ _ owner a b c G tail =>
      classical
      dsimp only [emptyGateScalar]
      split
      · exact le_of_eq norm_one
      · rename_i h
        let : IsEmpty C := not_nonempty_iff.mp h
        exact G.norm_coeffSum_le_one_of_isEmpty
  | swap => exact le_of_eq norm_one
  | frame r w ih => exact ih
/-- A chronology on an empty party type is exactly its empty-gate scalar.
This includes empty branch sets, which make the corresponding scalar zero.
Source: polynomial-PEPS, `04-compression.tex`, lines 24–28 and 565–588. -/
theorem eval_heq_emptyGateScalar_smul_id_of_isEmpty [IsEmpty P]
    {a b : Layout P} (w : SourceCircuit a b) :
    HEq w.eval (w.emptyGateScalar • ContinuousLinearMap.id ℂ ℂ) := by
  have hn {T : Type} [IsEmpty T] (a : Layout T) : a = [] :=
    List.eq_nil_iff_forall_not_mem.mpr (fun r _ => isEmptyElim r.owner)
  induction w with
  | id a =>
      cases hn a
      apply heq_of_eq
      simp only [eval, emptyGateScalar, one_smul]
  | @comp a b c w v ihw ihv =>
      cases hn a
      cases hn b
      cases hn c
      apply heq_of_eq
      rw [eval, emptyGateScalar, eq_of_heq ihw, eq_of_heq ihv]
      ext
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_smul, mul_comm]
  | localMap p => exact False.elim (IsEmpty.false p)
  | @gate C ι _ _ owner a b c G tail =>
      let : IsEmpty C := ⟨fun q => IsEmpty.false (owner q)⟩
      cases hn a
      cases hn b
      cases hn tail
      apply heq_of_eq
      rw [eval_gate_eq_coeffSum_smul_id_of_isEmpty]
      simp only [emptyGateScalar, not_nonempty_iff.mpr (inferInstance : IsEmpty C),
        ↓reduceIte]
  | swap r => exact isEmptyElim r.owner
  | frame r => exact isEmptyElim r.owner
end TNLean.PEPS.PairEffect.SourceCircuit
