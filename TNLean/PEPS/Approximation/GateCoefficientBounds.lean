/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.EffectReplacementExpansion
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Coefficient sums from the original monomial assumptions

A bound on the number of monomials and on each individual scalar coefficient
gives the absolute coefficient-sum bound used in effect elimination. The
conversion acts on the actual gate lists and the original chronology. Empty
lists and nonprivate gates with no participating parties are included.

Source: polynomial-PEPS Theorem 5.2, item 3, `04-compression.tex`, lines 143–149,
and its application at lines 174–175 and 199–208.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

namespace PartyGate

/-- The absolute coefficient sum of an actual gate list is at most its length
times an individual coefficient bound. Source: polynomial-PEPS Theorem 5.2,
item 3, `04-compression.tex`, lines 143–149 and 174–175. -/
theorem sum_norm_coefficients_le {a b : Layout P} (G : PartyGate a b) (C : ℝ)
    (hC : ∀ term ∈ G, ‖term.1‖ ≤ C) :
    (G.map fun term ↦ ‖term.1‖).sum ≤ (G.length : ℝ) * C := by
  have h := List.sum_le_length_nsmul (G.map fun term ↦ ‖term.1‖) C (by
    intro x hx
    obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hx
    exact hC term hterm)
  simpa only [List.length_map, nsmul_eq_mul] using h

/-- Polynomial bounds on the actual list length and individual coefficients
imply a polynomial absolute coefficient sum. Source: polynomial-PEPS Theorem 5.2,
item 3, `04-compression.tex`, lines 143–149 and 174–175. -/
theorem sum_norm_coefficients_le_of_power_bounds {a b : Layout P}
    (G : PartyGate a b) (L C_K C_C : ℝ) (u v : ℕ)
    (hL : 0 ≤ L) (hCC : 0 ≤ C_C)
    (hK : (G.length : ℝ) ≤ C_K * L ^ u)
    (hC : ∀ term ∈ G, ‖term.1‖ ≤ C_C * L ^ v) :
    (G.map fun term ↦ ‖term.1‖).sum ≤ C_K * C_C * L ^ (u + v) := by
  calc
    _ ≤ (G.length : ℝ) * (C_C * L ^ v) := sum_norm_coefficients_le G _ hC
    _ ≤ (C_K * L ^ u) * (C_C * L ^ v) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by rw [pow_add]; ring

end PartyGate
namespace OriginalCircuit

/-- Each actual monomial of every original nonprivate gate has at most `r`
pair effects and scalar coefficient of norm at most `C`. Allowedness of its local
maps is already part of the original gate constructor. Source: polynomial-PEPS
Theorem 5.2, item 3, `04-compression.tex`, lines 143–149. -/
def IsTermwiseBounded (r : ℕ) (C : ℝ) : {a b : Layout P} → OriginalCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsTermwiseBounded r C ∧ v.IsTermwiseBounded r C
  | _, _, .privateMap .. => True
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ G _ _ _ =>
      ∀ term ∈ G, term.2.toEffectChain.effectCount ≤ r ∧ ‖term.1‖ ≤ C
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsTermwiseBounded r C

/-- Termwise bounds imply the existing effect-count and coefficient-sum bounds
on the actual original chronology. Source: polynomial-PEPS Theorem 5.2,
item 3, `04-compression.tex`, lines 143–149 and 174–175. -/
theorem isExpansionBounded_of_isTermwiseBounded {a b : Layout P}
    (w : OriginalCircuit a b) {r K : ℕ} {C S : ℝ}
    (hK : w.IsMonomialBounded K) (ht : w.IsTermwiseBounded r C)
    (hC : 0 ≤ C) (hS : (K : ℝ) * C ≤ S) : w.IsExpansionBounded r S := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw hK.1 ht.1, ihv hK.2 ht.2⟩
  | privateMap => trivial
  | nonprivateGate owner hparticipants G hG hnorm tail =>
    exact ⟨fun term hterm ↦ (ht term hterm).1,
      (PartyGate.sum_norm_coefficients_le G C (fun term hterm ↦ (ht term hterm).2)).trans
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) hC).trans hS)⟩
  | swap => trivial
  | frame r w ih => exact ih hK ht

/-- Polynomial bounds on the actual monomial counts and individual coefficients
give the coefficient-sum bound on the original chronology. Source:
polynomial-PEPS Theorem 5.2, item 3, `04-compression.tex`, lines 143–149 and 174–175. -/
theorem isExpansionBounded_of_termwise_power_bounds {a b : Layout P}
    (w : OriginalCircuit a b) {r K : ℕ} (L C_K C_C : ℝ) (u v : ℕ)
    (hL : 0 ≤ L) (hCC : 0 ≤ C_C)
    (hK : w.IsMonomialBounded K) (ht : w.IsTermwiseBounded r (C_C * L ^ v))
    (hKbound : (K : ℝ) ≤ C_K * L ^ u) :
    w.IsExpansionBounded r (C_K * C_C * L ^ (u + v)) := by
  apply isExpansionBounded_of_isTermwiseBounded w hK ht (by positivity)
  calc
    (K : ℝ) * (C_C * L ^ v) ≤ (C_K * L ^ u) * (C_C * L ^ v) :=
      mul_le_mul_of_nonneg_right hKbound (by positivity)
    _ = _ := by rw [pow_add]; ring

end OriginalCircuit
end TNLean.PEPS.PairEffect
