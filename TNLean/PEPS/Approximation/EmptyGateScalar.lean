/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ZeroPartyGates
import TNLean.Lattice.PartyCircuit.DistributedSourceComposition

/-!
# The product of empty-participant gate scalars

At each gate with no participating parties, retain the sum of its original
branch coefficients. Multiplying these sums over the distributed composition
defines its empty-gate scalar. Other operations contribute one to this product.
Every prepared gate is intrinsically contractive, so the product has norm at
most one. Neither a nonzero coefficient sum nor a nonempty branch type is
required.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), Theorem 5.2, `04-compression.tex`, lines 24–28 and 565–588.
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

end TNLean.PEPS.PairEffect.SourceCircuit
