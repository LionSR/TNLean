/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.RectangularSpan.Universality
import TNLean.Wielandt.RectangularSpan.Growth
import TNLean.Wielandt.RectangularSpan.UniversalityAux

/-!
# Rectangular span universality compatibility names

Transfer-free results are proved for arbitrary finite matrix families in the corresponding
`Kraus` module. The three normality capstones remain specific to matrix product tensors.
-/

open scoped Matrix
namespace MPSTensor
open Module Matrix Wielandt
variable {d D : ℕ}

/-- Compatibility restatement of the generic ceiling lemma. -/
theorem strict_growth_reaches_ceiling {a : ℕ → ℕ} {C : ℕ}
    (hmono : ∀ n, a n ≤ a (n + 1)) (hbound : ∀ n, a n ≤ C)
    (hstrict : ∀ n, a n < C → a n < a (n + 1)) : a (C - a 0) = C :=
  Kraus.strict_growth_reaches_ceiling hmono hbound hstrict

/-- Compatibility restatement of generic nilpotent-index span growth. -/
theorem rectSpan_nilpIndex_eq_range_of_strict_growth [NeZero D]
    (A : MPSTensor d D) (i₀ : Fin d)
    (hStrict : ∀ n,
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) <
        D * ((A i₀) ^ D).rank →
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) <
        finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1))) :
    ∃ n₀, n₀ ≤ D * ((A i₀) ^ D).rank ∧
      rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n₀ =
        LinearMap.range (LinearMap.mulLeft ℂ
          ((A i₀) ^ nilpIndex (toLin' (A i₀)))) :=
  Kraus.rectSpan_nilpIndex_eq_range_of_strict_growth A i₀ hStrict

/-- Compatibility restatement of the generic sharp bound from strict growth. -/
theorem wielandt_unconditional_sharp_of_strict_growth [NeZero D]
    (A : MPSTensor d D) (i₀ : Fin d) (hNotInv : ¬ IsUnit (toLin' (A i₀)))
    {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0) (heig : A i₀ *ᵥ φ = μ • φ)
    (hStrict : ∀ n,
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) <
        D * ((A i₀) ^ D).rank →
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) <
        finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1))) :
    ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ cumulativeSpan A (D ^ 2 - D + 1) :=
  Kraus.wielandt_unconditional_sharp_of_strict_growth A i₀ hNotInv hμ heig hStrict

/-- Compatibility restatement of generic left-step surjectivity. -/
theorem rectSpan_leftStep_image_eq_of_finrank_eq
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ)
    (hfin : finrank ℂ (rectSpan ((A i₀) ^ D) A n) =
      finrank ℂ (rectSpan ((A i₀) ^ D) A (n + 1))) :
    ∀ Y ∈ rectSpan ((A i₀) ^ D) A (n + 1),
      ∃ X ∈ rectSpan ((A i₀) ^ D) A n, (A i₀) * X = Y :=
  Kraus.rectSpan_leftStep_image_eq_of_finrank_eq A i₀ n hfin

/-- Compatibility restatement of the generic stabilized left-image identity. -/
theorem rectSpan_eq_mulLeft_image_of_finrank_eq
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ)
    (hfin : finrank ℂ (rectSpan ((A i₀) ^ D) A n) =
      finrank ℂ (rectSpan ((A i₀) ^ D) A (n + 1))) :
    rectSpan ((A i₀) ^ D) A (n + 1) =
      Submodule.map (LinearMap.mulLeft ℂ (A i₀)) (rectSpan ((A i₀) ^ D) A n) :=
  Kraus.rectSpan_eq_mulLeft_image_of_finrank_eq A i₀ n hfin

/-- Compatibility restatement of the nilpotent-index left-image identity. -/
theorem rectSpan_nilpIndex_eq_mulLeft_image_of_finrank_eq
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ)
    (hfin : finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) =
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1))) :
    rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1) =
      Submodule.map (LinearMap.mulLeft ℂ (A i₀))
        (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) :=
  Kraus.rectSpan_nilpIndex_eq_mulLeft_image_of_finrank_eq A i₀ n hfin

/-- Historical matrix-product-tensor name for `Kraus.wordSpan_succ`. -/
theorem wordSpan_succ_eq_mul_right (A : MPSTensor d D) (n : ℕ) :
    wordSpan A (n + 1) = wordSpan A n * wordSpan A 1 :=
  Kraus.wordSpan_succ A n

/-- Compatibility restatement of generic rectangular-span right expansion. -/
theorem rectSpan_succ_eq_iSup_mulRight
    (P : Matrix (Fin D) (Fin D) ℂ) (A : MPSTensor d D) (n : ℕ) :
    rectSpan P A (n + 1) =
      ⨆ j : Fin d, Submodule.map (LinearMap.mulRight ℂ (A j)) (rectSpan P A n) :=
  Kraus.rectSpan_succ_eq_iSup_mulRight P A n

/-- Compatibility restatement of generic stabilization permanence. -/
theorem rectSpan_nilpIndex_succ2_eq_mulLeft_of_finrank_eq
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ)
    (hfin : finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) =
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1))) :
    rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 2) =
      Submodule.map (LinearMap.mulLeft ℂ (A i₀))
        (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1)) :=
  Kraus.rectSpan_nilpIndex_succ2_eq_mulLeft_of_finrank_eq A i₀ n hfin

/-- Compatibility restatement of generic eventual finrank constancy. -/
theorem rectSpan_nilpIndex_finrank_constant'
    (A : MPSTensor d D) (i₀ : Fin d) (n : ℕ)
    (hfin : finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) =
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1))) :
    ∀ m, n ≤ m →
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A m) =
        finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) :=
  Kraus.rectSpan_nilpIndex_finrank_constant' A i₀ n hfin

/-- Normality rules out stabilization below the maximal rectangular-span dimension. -/
theorem rectSpan_nilpIndex_strict_growth_of_isNormal
    (A : MPSTensor d D) (i₀ : Fin d) (hN : IsNormal A) (n : ℕ)
    (hlt : finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) <
      D * ((A i₀) ^ D).rank) :
    finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) <
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1)) := by
  by_contra h
  push Not at h
  have hmono := rectSpan_nilpIndex_finrank_mono A i₀ n
  have hfin : finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A n) =
      finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A (n + 1)) := by omega
  obtain ⟨N, hN_range⟩ := exists_rectSpan_eq_range_of_isNormal
    ((A i₀) ^ nilpIndex (toLin' (A i₀))) A hN
  have hN_finrank : finrank ℂ (rectSpan ((A i₀) ^ nilpIndex (toLin' (A i₀))) A N) =
      D * ((A i₀) ^ D).rank := by
    rw [hN_range, finrank_range_mulLeft, Kraus.rank_pow_nilpIndex_eq A i₀]
  have hconst := Kraus.rectSpan_nilpIndex_finrank_constant' A i₀ n hfin
    (max n N) (le_max_left _ _)
  have hmono_N := Kraus.rectSpan_nilpIndex_finrank_mono_le A i₀ (le_max_right n N)
  linarith

/-- Under normality, every associated rank-one matrix belongs to the sharp cumulative span. -/
theorem wielandt_sharp_unconditional [NeZero D]
    (A : MPSTensor d D) (i₀ : Fin d) (hN : IsNormal A)
    (hNotInv : ¬ IsUnit (toLin' (A i₀))) {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ cumulativeSpan A (D ^ 2 - D + 1) :=
  Kraus.wielandt_unconditional_sharp_of_strict_growth A i₀ hNotInv hμ heig
    (fun n hlt => rectSpan_nilpIndex_strict_growth_of_isNormal A i₀ hN n hlt)

/-- Compatibility restatement of one-step eigenvector padding. -/
theorem vecMulVec_eigenvector_pad_wordSpan
    (A : MPSTensor d D) (i₀ : Fin d) {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) {ψ : Fin D → ℂ} {n : ℕ}
    (hmem : vecMulVec φ ψ ∈ wordSpan A n) :
    vecMulVec φ ψ ∈ wordSpan A (n + 1) :=
  Kraus.vecMulVec_eigenvector_pad_wordSpan A i₀ hμ heig hmem

/-- Compatibility restatement of iterated eigenvector padding. -/
theorem vecMulVec_eigenvector_pad_wordSpan_add
    (A : MPSTensor d D) (i₀ : Fin d) {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) {ψ : Fin D → ℂ} {n : ℕ}
    (hmem : vecMulVec φ ψ ∈ wordSpan A n) (k : ℕ) :
    vecMulVec φ ψ ∈ wordSpan A (n + k) :=
  Kraus.vecMulVec_eigenvector_pad_wordSpan_add A i₀ hμ heig hmem k

/-- Compatibility restatement of monotone eigenvector padding. -/
theorem vecMulVec_eigenvector_mem_wordSpan_of_le
    (A : MPSTensor d D) (i₀ : Fin d) {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) {ψ : Fin D → ℂ} {n m : ℕ} (hnm : n ≤ m)
    (hmem : vecMulVec φ ψ ∈ wordSpan A n) : vecMulVec φ ψ ∈ wordSpan A m :=
  Kraus.vecMulVec_eigenvector_mem_wordSpan_of_le A i₀ hμ heig hnm hmem

/-- Under normality, the sharp rank-one conclusion holds at the exact word length. -/
theorem vecMulVec_eigenvector_exact_wordSpan [NeZero D]
    (A : MPSTensor d D) (i₀ : Fin d) (hN : IsNormal A)
    (hNotInv : ¬ IsUnit (toLin' (A i₀))) {φ : Fin D → ℂ} {μ : ℂ} (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    ∀ ψ : Fin D → ℂ, vecMulVec φ ψ ∈ wordSpan A (D ^ 2 - D + 1) := by
  intro ψ
  set r := nilpIndex (toLin' (A i₀))
  have hStrict : ∀ n,
      finrank ℂ (rectSpan ((A i₀) ^ r) A n) < D * ((A i₀) ^ D).rank →
      finrank ℂ (rectSpan ((A i₀) ^ r) A n) <
        finrank ℂ (rectSpan ((A i₀) ^ r) A (n + 1)) :=
    fun n hlt => rectSpan_nilpIndex_strict_growth_of_isNormal A i₀ hN n hlt
  obtain ⟨n₀, hn₀, hstab⟩ :=
    Kraus.rectSpan_nilpIndex_eq_range_of_strict_growth A i₀ hStrict
  have hmem : vecMulVec φ ψ ∈ wordSpan A (r + n₀) :=
    Kraus.vecMulVec_eigenvector_mem_wordSpan_nilpIndex A i₀ hμ heig hstab ψ
  have hbound : r + n₀ ≤ D ^ 2 - D + 1 := by
    calc
      r + n₀ ≤ r + D * ((A i₀) ^ D).rank := Nat.add_le_add_left hn₀ _
      _ = D * ((A i₀) ^ D).rank + r := by ring
      _ ≤ D ^ 2 - D + 1 := Kraus.sharp_bound_le A i₀ hNotInv
  exact Kraus.vecMulVec_eigenvector_mem_wordSpan_of_le A i₀ hμ heig hbound hmem

end MPSTensor
