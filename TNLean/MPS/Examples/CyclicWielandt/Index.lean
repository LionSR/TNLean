/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.CyclicWielandt.Spanning
import TNLean.MPS.Examples.CyclicWielandt.Obstruction
import TNLean.Wielandt.Primitivity.EasyDirections
import QICLean.Kraus.Wielandt.SpanGrowth.InvertibleWordSpan

/-!
# The cyclic example has full-Kraus-rank index `D(D-1)`

The upper spanning construction and the predecessor obstruction give the
exact index. The invertible shift ensures that fullness at any earlier
length would persist to the predecessor length.

This is the example in arXiv:0909.5347, source `main.tex`, lines 691–700.
**Local fix:** The upper construction supplies the omitted matrix unit by
subtracting the other diagonal units from the identity word, as documented
in `docs/paper-gaps/spwc10_cyclic_missing_diagonal.tex`.
-/

noncomputable section

namespace MPSTensor.CyclicWielandt

variable {D : ℕ} [NeZero D]

/-- The actual cyclic-shift and jump family is normal for every `D≥2`.
Source: arXiv:0909.5347, source lines 691–700. -/
theorem isNormal (hD : 2 ≤ D) : Kraus.IsNormal (tensor D) := by
  exact ⟨D * (D - 1), Nat.mul_pos (by omega) (by omega), wordSpan_full_length hD⟩

/-- The actual cyclic example is primitive in the paper's vector-spreading
sense. Source: arXiv:0909.5347, source lines 691–700. -/
theorem isPrimitivePaper (hD : 2 ≤ D) : MPSTensor.IsPrimitivePaper (tensor D) :=
  isPrimitivePaper_of_isNormal (tensor D) (isNormal hD)

/-- The full-Kraus-rank index of the cyclic example is exactly `D(D-1)`.
Source: arXiv:0909.5347, source lines 691–700. -/
theorem iIndex_eq (hD : 2 ≤ D) : MPSTensor.iIndex (tensor D) = D * (D - 1) := by
  have hpos : 0 < D * (D - 1) := Nat.mul_pos (by omega) (by omega)
  have hfull := wordSpan_full_length hD
  have hne : {n : ℕ | 0 < n ∧ Kraus.wordSpan (tensor D) n = ⊤}.Nonempty :=
    ⟨D * (D - 1), hpos, hfull⟩
  apply le_antisymm
  · exact Nat.sInf_le ⟨hpos, hfull⟩
  · by_contra h
    have hi : Kraus.wordSpan (tensor D) (MPSTensor.iIndex (tensor D)) = ⊤ :=
      (Nat.sInf_mem hne).2
    have hle : MPSTensor.iIndex (tensor D) ≤ D * (D - 1) - 1 := by omega
    have hpred := Kraus.wordSpan_eq_top_of_ge_of_isUnit (tensor D) 0
      (by simpa using (shift_isUnit (D := D))) hi hle
    exact wordSpan_pred_ne_top hD hpred

/-- In dimensions greater than two, the example exceeds the sharp classical
Wielandt exponent. Source: arXiv:0909.5347, source lines 691–700. -/
theorem classical_bound_lt_iIndex (hD : 2 < D) :
    D ^ 2 - 2 * D + 2 < MPSTensor.iIndex (tensor D) := by
  rw [iIndex_eq (by omega)]
  have hdim : D - 1 + 1 = D := by omega
  have hs : 2 * D ≤ D ^ 2 := by nlinarith
  have hsub : D ^ 2 - 2 * D + 2 * D = D ^ 2 := Nat.sub_add_cancel hs
  nlinarith

end MPSTensor.CyclicWielandt
