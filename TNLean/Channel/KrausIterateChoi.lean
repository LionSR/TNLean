/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrameOperator
import TNLean.Channel.KrausRank
import TNLean.Kraus.Injectivity
import TNLean.Kraus.MapIterate

/-!
# Positive-definite Choi matrices of finite Kraus-map iterates

For a finite Kraus family `K`, the operators in the `m`-fold iterate are the
length-`m` Kraus words. Its Choi matrix is therefore the frame operator of the
normalized vectorized words. The Choi matrix is positive definite exactly when
those words span the full matrix algebra.

## Main declarations

* `Kraus.choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top` characterizes one
  fixed iterate.
* `Kraus.eventually_choiMatrix_mapLM_pow_posDef_iff_hasEventuallyFullWordSpan`
  gives the corresponding eventual statement.
-/

open scoped Matrix BigOperators ComplexOrder

namespace Kraus

variable {r D : ℕ}

private theorem span_normalized_uncurry_words_eq_top_iff
    [NeZero D] (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (m : ℕ) :
    Submodule.span ℂ
        (Set.range fun σ : Fin m → Fin r =>
          fun p : Fin D × Fin D =>
            ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) *
              MPSTensor.evalWord K (List.ofFn σ) p.1 p.2) = ⊤ ↔
      wordSpan K m = ⊤ := by
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] ((Fin D × Fin D) → ℂ) :=
    (LinearEquiv.curry ℂ ℂ (Fin D) (Fin D)).symm
  let c : ℂ := (1 : ℂ) / ((D : ℝ).sqrt : ℂ)
  have hD : D ≠ 0 := NeZero.ne D
  have hsqrtR : (D : ℝ).sqrt ≠ 0 :=
    (Real.sqrt_ne_zero (Nat.cast_nonneg D)).2 (Nat.cast_ne_zero.2 hD)
  have hsqrtC : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
    exact_mod_cast hsqrtR
  have hc : c ≠ 0 := one_div_ne_zero hsqrtC
  have hscale :
      Submodule.span ℂ
          (Set.range fun σ : Fin m → Fin r =>
            c • e (MPSTensor.evalWord K (List.ofFn σ))) =
        Submodule.span ℂ
          (Set.range fun σ : Fin m → Fin r =>
            e (MPSTensor.evalWord K (List.ofFn σ))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      change e (MPSTensor.evalWord K (List.ofFn σ)) ∈ _
      rw [← inv_smul_smul₀ hc (e (MPSTensor.evalWord K (List.ofFn σ)))]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
  have hmap :
      Submodule.map e.toLinearMap (wordSpan K m) =
        Submodule.span ℂ
          (Set.range fun σ : Fin m → Fin r =>
            e (MPSTensor.evalWord K (List.ofFn σ))) := by
    rw [wordSpan, Submodule.map_span]
    congr 1
    ext v
    simp
  change Submodule.span ℂ
      (Set.range fun σ : Fin m → Fin r =>
        c • e (MPSTensor.evalWord K (List.ofFn σ))) = ⊤ ↔ _
  rw [hscale, ← hmap]
  exact Submodule.map_eq_top_iff

/-- Wolf, Section 6.8, items 3 and 4 at a fixed iterate: the Choi matrix of a
finite Kraus-map iterate is positive definite exactly when the Kraus words of
that length span the full matrix algebra. -/
theorem choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top
    [NeZero D] (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (m : ℕ) :
    (ChoiJamiolkowski.choiMatrix ((mapLM K) ^ m)).PosDef ↔
      wordSpan K m = ⊤ := by
  let wordEquiv := Fintype.equivFin (Fin m → Fin r)
  let W : Fin (Fintype.card (Fin m → Fin r)) → Matrix (Fin D) (Fin D) ℂ :=
    fun j => MPSTensor.evalWord K (List.ofFn (wordEquiv.symm j))
  have hW : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ((mapLM K) ^ m) X = ∑ j, W j * X * (W j)ᴴ := by
    intro X
    rw [mapLM_pow_apply]
    exact Fintype.sum_equiv wordEquiv _ _ fun σ => by simp [W]
  rw [← ChoiRectangular.choiMatrix_eq_choiJamiolkowski]
  rw [Channel.choiMatrix_eq_sum_vecMulVec_of_kraus W ((mapLM K) ^ m) hW]
  rw [Matrix.posDef_sum_vecMulVec_iff_span_eq_top]
  have hrange :
      Set.range (fun j =>
          fun p : Fin D × Fin D =>
            ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * W j p.1 p.2) =
        Set.range (fun σ : Fin m → Fin r =>
          fun p : Fin D × Fin D =>
            ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) *
              MPSTensor.evalWord K (List.ofFn σ) p.1 p.2) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨wordEquiv.symm j, rfl⟩
    · rintro ⟨σ, rfl⟩
      refine ⟨wordEquiv σ, ?_⟩
      simp [W]
  rw [hrange]
  exact span_normalized_uncurry_words_eq_top_iff K m

/-- Wolf, Section 6.8, items 3 and 4 in eventual form: a finite Kraus family
has eventually full word span exactly when the Choi matrices of all sufficiently
large iterates are positive definite. -/
theorem eventually_choiMatrix_mapLM_pow_posDef_iff_hasEventuallyFullWordSpan
    [NeZero D] (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    (∀ᶠ m : ℕ in Filter.atTop,
      (ChoiJamiolkowski.choiMatrix ((mapLM K) ^ m)).PosDef) ↔
      HasEventuallyFullWordSpan K := by
  constructor
  · intro h
    filter_upwards [h] with m hm
    exact (choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top K m).mp hm
  · intro h
    filter_upwards [h] with m hm
    exact (choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top K m).mpr hm

end Kraus
