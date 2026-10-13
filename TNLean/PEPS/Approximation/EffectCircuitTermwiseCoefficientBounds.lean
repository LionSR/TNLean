/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.GateCoefficientBounds
import TNLean.PEPS.Approximation.ApproximateCircuitResources

/-!
# Coefficient sums from termwise bounds on approximate gate lists

The prescribed expansion at each original gate occurrence has its own bound
on the number of monomials and on each scalar coefficient. These bounds imply
an absolute coefficient-sum bound before effect elimination. The estimate
uses the original ordered lists, independently of all private dimensions.

Source: polynomial-PEPS Theorem 5.2, assumption 3, `04-compression.tex`,
lines 143–149, 199–208 and 590–600.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.EffectCircuit
variable {P : Type}

/-- Every monomial in each prescribed nonprivate gate list contains at most
`r` pair effects and has scalar coefficient of norm at most `C`. Gate
contraction and local allowedness are separate data of the approximation.
Source: polynomial-PEPS Theorem 5.2, assumption 3, `04-compression.tex`,
lines 143–149 and 590–600. -/
def IsTermwiseBounded (r : ℕ) (C : ℝ) : {a b : Layout P} → EffectCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsTermwiseBounded r C ∧ v.IsTermwiseBounded r C
  | _, _, .localMap .. => True
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ G _ =>
      ∀ term ∈ G, term.2.toEffectChain.effectCount ≤ r ∧ ‖term.1‖ ≤ C
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsTermwiseBounded r C

/-- Original monomial counts and individual coefficient bounds give the
absolute coefficient-sum bound at every recorded gate occurrence.
Source: polynomial-PEPS Theorem 5.2, assumption 3, `04-compression.tex`,
lines 143–149 and 199–208. -/
theorem isExpansionBounded_of_isTermwiseBounded {a b : Layout P}
    (w : EffectCircuit a b) {r K : ℕ} {C S : ℝ}
    (hK : ∀ g, w.monomialCount g ≤ K) (ht : w.IsTermwiseBounded r C)
    (hC : 0 ≤ C) (hS : (K : ℝ) * C ≤ S) : w.IsExpansionBounded r S := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact
      ⟨ihw (fun g ↦ hK (.inl g)) ht.1, ihv (fun g ↦ hK (.inr g)) ht.2⟩
  | localMap => trivial
  | gate owner G tail =>
      exact ⟨fun term hterm ↦ (ht term hterm).1,
        (PartyGate.sum_norm_coefficients_le G C (fun term hterm ↦ (ht term hterm).2)).trans
          ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hK ())) hC).trans hS)⟩
  | swap => trivial
  | frame r w ih => exact ih hK ht

/-- Polynomial bounds on original monomial counts and individual coefficients
supply a coefficient-sum bound at least one, with constants fixed independently
of the circuit and its private dimensions. The existing rescaling construction
preserves this sum bound.
Source: polynomial-PEPS Theorem 5.2, assumption 3, `04-compression.tex`,
lines 143–175, 199–208 and 590–600. -/
theorem exists_one_le_isExpansionBounded_of_termwise_power_bounds
    {a b : Layout P} (w : EffectCircuit a b) {r K : ℕ}
    (L C_K C_C : ℝ) (u v : ℕ)
    (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCC : 0 ≤ C_C)
    (hK : ∀ g, w.monomialCount g ≤ K)
    (ht : w.IsTermwiseBounded r (C_C * L ^ v))
    (hKbound : (K : ℝ) ≤ C_K * L ^ u) :
    ∃ B : ℝ≥0, 1 ≤ B ∧ w.IsExpansionBounded r (B : ℝ) ∧
      (B : ℝ) ≤ (1 + C_K * C_C) * L ^ (u + v) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hB1 : 1 ≤ (1 + C_K * C_C) * L ^ (u + v) :=
    one_le_mul_of_one_le_of_one_le
      (le_add_of_nonneg_right (mul_nonneg hCK hCC)) (one_le_pow₀ hL)
  refine ⟨⟨(1 + C_K * C_C) * L ^ (u + v), zero_le_one.trans hB1⟩,
    hB1, ?_, le_rfl⟩
  apply w.isExpansionBounded_of_isTermwiseBounded hK ht (by positivity)
  calc
    (K : ℝ) * (C_C * L ^ v) ≤ (C_K * L ^ u) * (C_C * L ^ v) :=
      mul_le_mul_of_nonneg_right hKbound (by positivity)
    _ = C_K * C_C * L ^ (u + v) := by rw [pow_add]; ring
    _ ≤ (1 + C_K * C_C) * L ^ (u + v) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)

end TNLean.PEPS.PairEffect.EffectCircuit
