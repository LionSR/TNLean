/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LocalTransferExpansion

/-!
# The actual monomial list for a register transfer

The local basis decomposition is expressed in the existing gate-expansion
type. Its literal list has one unit-coefficient monomial per basis vector;
every monomial is allowed and has no pair effect. Thus a message of dimension
`d` multiplies the monomial count and absolute coefficient sum by `d`.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 32–43 and 143–149.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-message-resources-transfergateexpansion-01
TNLean.PEPS.PairEffect.PartyGate.eval_transfer
Provenance-ID: 8769-message-resources-transfergateexpansion-02
TNLean.PEPS.PairEffect.PartyGate.isAllowed_effectCount_transfer
Provenance-ID: 8769-message-resources-transfergateexpansion-03
TNLean.PEPS.PairEffect.PartyGate.length_transfer
Provenance-ID: 8769-message-resources-transfergateexpansion-04
TNLean.PEPS.PairEffect.PartyGate.sum_norm_coeff_transfer
Provenance-ID: 8769-message-resources-transfergateexpansion-05
TNLean.PEPS.PairEffect.PartyGate.transfer
Provenance-ID: 8769-message-resources-transfergateexpansion-06
TNLean.PEPS.PairEffect.gate_toGate_eq_sum
-/


noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- The operator of a party expansion is the sum of its actual weighted monomials. -/
theorem gate_toGate_eq_sum {a b : Layout P} (L : PartyGate a b) :
    gate (toGate L) = (L.map fun t ↦ t.1 • t.2.toEffectChain.eval).sum := by
  induction L with
  | nil => rfl
  | cons t L ih => simp only [gate, List.map_cons, List.sum_cons, ih]

namespace PartyGate

open Classical in
/-- The actual message expansion, with one local basis monomial per message coordinate. -/
def transfer (sender receiver : P) (H : HSpace) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (a : Layout P) :
    PartyGate (⟨sender, H⟩ :: a) (⟨receiver, H⟩ :: a) :=
  (Finset.univ : Finset ι).toList.map fun i ↦
    (1, PartyChain.final (Word.transferTerm sender receiver H b i a))

/-- The literal expansion has exactly the dimension of the transferred register
many terms. Zero-dimensional messages give the empty expansion. -/
theorem length_transfer (sender receiver : P) (H : HSpace) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (a : Layout P) :
    (transfer sender receiver H b a).length = Fintype.card ι := by
  simp only [transfer, List.length_map, Finset.length_toList, Finset.card_univ]

/-- Every actual transfer monomial is allowed and has zero pair effects. -/
theorem isAllowed_effectCount_transfer (sender receiver : P) (H : HSpace)
    {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ H) (a : Layout P)
    {t : ℂ × PartyChain (⟨sender, H⟩ :: a) (⟨receiver, H⟩ :: a)}
    (ht : t ∈ transfer sender receiver H b a) :
    t.2.IsAllowed ∧ t.2.toEffectChain.effectCount = 0 := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
  exact ⟨Word.isAllowed_transferTerm sender receiver H b i a, rfl⟩

/-- The coefficient sum is exactly the message dimension. -/
theorem sum_norm_coeff_transfer (sender receiver : P) (H : HSpace)
    {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ H) (a : Layout P) :
    ((transfer sender receiver H b a).map fun t ↦ ‖t.1‖).sum = (Fintype.card ι : ℝ) := by
  simp [transfer, List.map_map]

/-- The constructed monomial list evaluates to the literal identity transfer
between the sender and receiver layouts, on arbitrary spectator memory. -/
theorem eval_transfer (sender receiver : P) (H : HSpace)
    {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ H) (a : Layout P) :
    gate (toGate (transfer sender receiver H b a)) =
      (ContinuousLinearMap.id ℂ (H ⊗[ℂ] Mem a) :
        Mem (⟨sender, H⟩ :: a) →L[ℂ] Mem (⟨receiver, H⟩ :: a)) := by
  classical
  rw [gate_toGate_eq_sum]
  simpa only [transfer, List.map_map, Function.comp_def, PartyChain.toEffectChain, EffectChain.eval,
    one_smul, Finset.sum_map_toList] using Word.sum_eval_transferTerm sender receiver H b a

end PartyGate
end TNLean.PEPS.PairEffect
