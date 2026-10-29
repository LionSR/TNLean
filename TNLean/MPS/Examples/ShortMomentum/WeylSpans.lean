/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.Examples.ShortMomentum.WeylWords
import QICLean.Kraus.Injectivity

/-!
# The actual degree-eight span and the degree-seven trace obstruction

The three-letter fifth-root Weyl tensor is normal, with a concrete
injectivity witness at degree eight. Every word of degree seven is
traceless, whereas every degree at least eight contains a word with
nonzero trace. These are properties of the actual matrix products;
no all-volume Hamiltonian kernel claim is made here.

Source context: SPWC10, arXiv:0909.5347, Theorem 5, main.tex lines 850--880.
See `docs/audits/2026-10-29_weyl_short_volume_candidate.md`.
-/

open Matrix
open scoped BigOperators

namespace MPSTensor.ShortMomentum

/-- Every value of the character is itself a fifth root. -/
theorem rootCharacter_pow_five {ζ : ℂ} (hζ : ζ ^ 5 = 1) (a : ZMod 5) :
    rootCharacter ζ a ^ 5 = 1 := by
  unfold rootCharacter
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]

/-- The exact finite character sum used to reconstruct matrix units. -/
theorem sum_rootCharacter_mul {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (a : ZMod 5) :
    ∑ u : ZMod 5, rootCharacter ζ (u * a) = if a = 0 then 5 else 0 := by
  simp_rw [mul_comm _ a, rootCharacter_mul hζ.pow_eq_one]
  rw [Matrix.sum_pow_val_eq_ite (rootCharacter_pow_five hζ.pow_eq_one a)]
  simp only [rootCharacter_eq_one_iff hζ]

/-- A finite Fourier sum of actual charged matrices is a matrix unit. -/
theorem sum_rootCharacter_smul_chargedWeyl {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (i j : ZMod 5) :
    ∑ u : ZMod 5, rootCharacter ζ (-u * i) • chargedWeyl ζ u (i - j) =
      (5 : ℂ) • Matrix.single i j 1 := by
  ext k l
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst k
    have hindex : i - (i - j) = j := by ring
    by_cases hl : l = j
    · subst l
      simp only [chargedWeyl, hindex, ite_true, ← rootCharacter_add hζ.pow_eq_one,
        show ∀ u : ZMod 5, -u * i + u * i = 0 by intro u; ring,
        rootCharacter_zero, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
        mul_one, Matrix.single_apply_same]
    · simp [chargedWeyl, hindex, hl, Matrix.single_apply, eq_comm]
  · have hki : k - i ≠ 0 := sub_ne_zero.mpr hk
    have hsingle : Matrix.single i j (1 : ℂ) k l = 0 :=
      Matrix.single_apply_of_row_ne hk.symm _ _ _
    rw [hsingle, mul_zero]
    by_cases hl : l = k - (i - j)
    · simp only [chargedWeyl, hl, ite_true, ← rootCharacter_add hζ.pow_eq_one]
      have hexp : ∀ u : ZMod 5, -u * i + u * k = u * (k - i) := by
        intro u
        ring
      simp_rw [hexp]
      rw [sum_rootCharacter_mul hζ, if_neg hki]
    · simp [chargedWeyl, hl]

/-- The actual charged matrices span the entire matrix algebra. -/
theorem span_chargedWeyl_eq_top {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    Submodule.span ℂ (Set.range fun p : ZMod 5 × ZMod 5 ↦ chargedWeyl ζ p.1 p.2) = ⊤ := by
  let S := Submodule.span ℂ
    (Set.range fun p : ZMod 5 × ZMod 5 ↦ chargedWeyl ζ p.1 p.2)
  apply Submodule.eq_top_of_forall_single_mem
  intro i j
  have hmem : (5 : ℂ) • Matrix.single i j 1 ∈ S := by
    rw [← sum_rootCharacter_smul_chargedWeyl hζ i j]
    apply S.sum_mem
    intro u _
    exact S.smul_mem _ (Submodule.subset_span ⟨(u, i - j), rfl⟩)
  have hscaled := S.smul_mem ((5 : ℂ)⁻¹) hmem
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (5 : ℂ) ≠ 0), one_smul] using hscaled

/-- Every charged matrix belongs to the actual word span at every degree
at least eight. -/
theorem chargedWeyl_mem_wordSpan {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (n : ℕ) (hn : 8 ≤ n) (u v : ZMod 5) :
    chargedWeyl ζ u v ∈ Kraus.wordSpan (threeLetterTensor ζ) n := by
  obtain ⟨w, hw, hcharge⟩ := exists_word_of_eight_le_of_charge n hn u v
  have hmem := Kraus.evalWord_mem_wordSpan (threeLetterTensor ζ) w
  rw [hw, evalWord_threeLetterTensor hζ.pow_eq_one, hcharge] at hmem
  have hscaled := (Kraus.wordSpan (threeLetterTensor ζ) n).smul_mem
    (rootCharacter ζ (wordPhase w))⁻¹ hmem
  simpa only [smul_smul, inv_mul_cancel₀ (rootCharacter_ne_zero hζ _), one_smul] using hscaled

/-- Every degree at least eight has the full actual matrix word span. -/
theorem isNBlkInjective_threeLetterTensor_of_eight_le {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) (hn : 8 ≤ n) :
    Kraus.IsNBlkInjective (threeLetterTensor ζ) n := by
  apply top_unique
  rw [← span_chargedWeyl_eq_top hζ]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  exact chargedWeyl_mem_wordSpan hζ n hn u v

/-- Degree eight is an actual injectivity witness for the three-letter tensor. -/
theorem isNBlkInjective_threeLetterTensor_eight {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    Kraus.IsNBlkInjective (threeLetterTensor ζ) 8 :=
  isNBlkInjective_threeLetterTensor_of_eight_le hζ 8 (by omega)

/-- The tensor is genuinely normal despite its exceptional short trace vector. -/
theorem isNormal_threeLetterTensor {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    Kraus.IsNormal (threeLetterTensor ζ) :=
  ⟨8, by norm_num, isNBlkInjective_threeLetterTensor_eight hζ⟩

/-- The degree-seven trace obstruction excludes injectivity at that degree. -/
theorem not_isNBlkInjective_threeLetterTensor_seven {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    ¬ Kraus.IsNBlkInjective (threeLetterTensor ζ) 7 := by
  refine Kraus.not_isNBlkInjective_of_linearMap (Matrix.traceLinearMap (Fin 5) ℂ ℂ) (fun σ ↦ ?_)
    (1 : Matrix (Fin 5) (Fin 5) ℂ) ?_
  · exact trace_evalWord_threeLetterTensor_seven hζ _ (List.length_ofFn σ)
  · norm_num [Matrix.trace_one]

/-- Every degree at least eight contains an actual word with nonzero trace. -/
theorem exists_trace_evalWord_ne_zero_of_eight_le {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (n : ℕ) (hn : 8 ≤ n) :
    ∃ w : List (Fin 3), w.length = n ∧
      (Kraus.evalWord (threeLetterTensor ζ) w).trace ≠ 0 := by
  obtain ⟨a, b, c, hdegree, hab, hbc⟩ := exists_central_counts_of_eight_le n hn
  refine ⟨sortedWord a b c, by simpa using hdegree, ?_⟩
  have hcharge : wordCharge (sortedWord a b c) = 0 := by
    rw [wordCharge_sortedWord]
    exact (countCharge_eq_zero_iff a b c).mpr ⟨hab, hbc⟩
  rw [evalWord_threeLetterTensor hζ.pow_eq_one, hcharge, chargedWeyl_zero, Matrix.trace_smul]
  simp only [Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  exact mul_ne_zero (rootCharacter_ne_zero hζ _) (by norm_num)

end MPSTensor.ShortMomentum
