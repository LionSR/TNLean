/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixMulRange
import QICLean.Kraus.Wielandt.RectangularSpan.Universality
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Basic
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.NilpIndex
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Quantitative
import QICLean.Kraus.Wielandt.RectangularSpan.UniversalityAux.Sharp
import TNLean.Wielandt.RectangularSpan.Growth

/-!
# Rectangular span universality compatibility names

Transfer-free results are proved for arbitrary finite matrix families in the corresponding
`Kraus` module. The three normality capstones remain specific to matrix product tensors.
-/

open scoped Matrix
namespace MPSTensor
open Module Matrix Wielandt
variable {d D : ℕ}

/-- Compatibility restatement of generic eventual finrank constancy. -/
theorem rectSpan_nilpIndex_finrank_constant'
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ)
    (hfin : finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) =
      finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1))) :
    ∀ m, n ≤ m →
      finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A m) =
        finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) :=
  Kraus.rectSpan_nilpIndex_finrank_constant' A i₀ n hfin

/-- Normality rules out stabilization below the maximal rectangular-span dimension. -/
theorem rectSpan_nilpIndex_strict_growth_of_isNormal
    (A : MPSTensor d D) (i₀ : Fin d) (hN : Kraus.IsNormal A) (n : ℕ)
    (hlt : finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) <
      D * ((A i₀) ^ D).rank) :
    finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) <
      finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1)) := by
  by_contra h
  push_neg at h
  have hmono := Kraus.rectSpan_nilpIndex_finrank_mono A i₀ n
  have hfin : finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) =
      finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1)) := by omega
  obtain ⟨N, hN_range⟩ := exists_rectSpan_eq_range_of_isNormal
    ((A i₀) ^ nilpIndex (toLin' (A i₀))) A hN
  have hN_finrank : finrank ℂ (Kraus.rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A N) =
      D * ((A i₀) ^ D).rank := by
    rw [hN_range, Matrix.finrank_range_mulLeft, Kraus.rank_pow_nilpIndex_eq A i₀]
  have hconst := Kraus.rectSpan_nilpIndex_finrank_constant' A i₀ n hfin
    (max n N) (le_max_left _ _)
  have hmono_N := Kraus.rectSpan_nilpIndex_finrank_mono_le A i₀ (le_max_right n N)
  linarith

/-- Under normality, the sharp rank-one conclusion holds at the exact word length. -/
theorem vecMulVec_eigenvector_exact_wordSpan [NeZero D]
    (A : MPSTensor d D) (i₀ : Fin d) (hN : Kraus.IsNormal A)
    (hNotInv : ¬ IsUnit (toLin' (A i₀))) {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ Kraus.wordSpan A (D ^ 2 - D + 1) := by
  intro ψ
  set r := nilpIndex (toLin' (A i₀))
  have hStrict : ∀ n,
      finrank ℂ (Kraus.rectSpan ((A i₀) ^ r) A n) < D * ((A i₀) ^ D).rank →
      finrank ℂ (Kraus.rectSpan ((A i₀) ^ r) A n) <
        finrank ℂ (Kraus.rectSpan ((A i₀) ^ r) A (n + 1)) :=
    fun n hlt => rectSpan_nilpIndex_strict_growth_of_isNormal A i₀ hN n hlt
  obtain ⟨n₀, hn₀, hstab⟩ :=
    Kraus.rectSpan_nilpIndex_eq_range_of_strict_growth A i₀ hStrict
  have hmem : vecMulVec φ ψ ∈ Kraus.wordSpan A (r + n₀) :=
    Kraus.vecMulVec_eigenvector_mem_wordSpan_nilpIndex A i₀ hμ heig hstab ψ
  have hbound : r + n₀ ≤ D ^ 2 - D + 1 := by
    calc
      r + n₀ ≤ r + D * ((A i₀) ^ D).rank := Nat.add_le_add_left hn₀ _
      _ = D * ((A i₀) ^ D).rank + r := by ring
      _ ≤ D ^ 2 - D + 1 := Kraus.sharp_bound_le A i₀ hNotInv
  exact Kraus.vecMulVec_eigenvector_mem_wordSpan_of_le A i₀ hμ heig hbound hmem

end MPSTensor
