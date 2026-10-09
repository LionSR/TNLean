/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateGateEvaluation

/-!
# Rescaling actual approximate gate expansions

Multiply all coefficients of each prescribed gate expansion by the same
factor `(1 + δ)⁻¹`. The monomials, their order and their local operations are
unchanged. The resulting expansion is a contraction circuit on exactly the
same input and output layouts.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-approximate-physical-approximategaterescaling-01
TNLean.PEPS.PairEffect.EffectCircuit.rescaledOriginal
Provenance-ID: 8769-approximate-physical-approximategaterescaling-02
TNLean.PEPS.PairEffect.gate_rescalePartyGate
Provenance-ID: 8769-approximate-physical-approximategaterescaling-03
TNLean.PEPS.PairEffect.isAllowed_rescalePartyGate
Provenance-ID: 8769-approximate-physical-approximategaterescaling-04
TNLean.PEPS.PairEffect.monomials_rescalePartyGate
Provenance-ID: 8769-approximate-physical-approximategaterescaling-05
TNLean.PEPS.PairEffect.rescalePartyGate
Provenance-ID: 8769-approximate-physical-approximategaterescaling-06
TNLean.PEPS.PairEffect.sum_norm_rescalePartyGate_le
-/


noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- Common coefficient rescaling of an actual monomial list. -/
def rescalePartyGate {a b : Layout P} (δ : ℝ) (L : PartyGate a b) : PartyGate a b :=
  L.map fun q ↦ ((((1 + δ)⁻¹ : ℝ) : ℂ) * q.1, q.2)

/-- Rescaling preserves the ordered list of monomials, including all original
source and effect occurrences and their endpoint spaces. -/
theorem monomials_rescalePartyGate {a b : Layout P} (δ : ℝ) (L : PartyGate a b) :
    (rescalePartyGate δ L).map Prod.snd = L.map Prod.snd := by
  simp only [rescalePartyGate, List.map_map, Function.comp_def]

/-- The actual operator sum is multiplied by the common rescaling factor. -/
theorem gate_rescalePartyGate {a b : Layout P} (δ : ℝ) (L : PartyGate a b) :
    gate (toGate (rescalePartyGate δ L)) =
      (((1 + δ)⁻¹ : ℝ) : ℂ) • gate (toGate L) := by
  induction L with
  | nil => simp only [rescalePartyGate, List.map_nil, toGate, gate, smul_zero]
  | cons q L ih =>
      simp only [rescalePartyGate, List.map_cons, toGate, gate] at ⊢ ih
      rw [ih, mul_smul, smul_add]

/-- The absolute coefficient sum cannot increase under the common rescaling. -/
theorem sum_norm_rescalePartyGate_le {a b : Layout P} {δ : ℝ}
    (hδ : 0 ≤ δ) (L : PartyGate a b) :
    ((rescalePartyGate δ L).map fun q ↦ ‖q.1‖).sum ≤
      (L.map fun q ↦ ‖q.1‖).sum := by
  simp only [rescalePartyGate, List.map_map, Function.comp_def, norm_mul,
    List.sum_map_mul_left]
  have hc : ‖(((1 + δ)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (norm_inv_one_add_smul_le_one (A := (1 : ℂ)) hδ
        (by simpa only [norm_one] using (le_add_of_nonneg_right hδ : (1 : ℝ) ≤ 1 + δ)))
  exact (mul_le_mul_of_nonneg_right hc
    (List.sum_nonneg (fun x hx ↦ by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg q.1))).trans_eq (one_mul _)

/-- An allowed approximate monomial remains exactly the same allowed monomial
when its coefficient is rescaled. -/
theorem isAllowed_rescalePartyGate {a b : Layout P} (δ : ℝ) (L : PartyGate a b)
    (h : ∀ q ∈ L, q.2.IsAllowed) : ∀ q ∈ rescalePartyGate δ L, q.2.IsAllowed := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  exact h r hr

namespace EffectCircuit
/-- Construct the contraction chronology from its actual approximate lists.
Only coefficients change; original private maps and all register layouts remain
literal constituents of the existing original-circuit syntax. -/
def rescaledOriginal {δ : ℝ} (hδ : 0 ≤ δ) :
    {a b : Layout P} → (w : EffectCircuit a b) → (G : w.GateMaps) →
      w.IsGateApproximation δ G → OriginalCircuit a b
  | _, _, .id a, _, _ => .id a
  | _, _, .comp w v, G, h =>
      .comp (w.rescaledOriginal hδ G.1 h.1) (v.rescaledOriginal hδ G.2 h.2)
  | _, _, .localMap p ha hb A tail, _, h => .privateMap p ha hb A h tail
  | _, _, @EffectCircuit.gate _ _ _ owner a b L tail, G, h =>
      .nonprivateGate owner h.1 (rescalePartyGate δ L)
        (isAllowed_rescalePartyGate δ L h.2.1) (by
          rw [gate_rescalePartyGate]
          exact norm_inv_one_add_smul_le_one hδ
            (norm_le_one_add_of_norm_sub_le h.2.2.1 h.2.2.2)) tail
  | _, _, .swap r s tail, _, _ => .swap r s tail
  | _, _, .frame r w, G, h => .frame r (w.rescaledOriginal hδ G h)
end EffectCircuit
end TNLean.PEPS.PairEffect
