/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OBCCanonicalConfigurations

/-!
# Gram recurrences under physical cut extension

The same physical configuration bijections give the forward prefix Gram
and backward suffix Gram identities for any factors satisfying the actual
adjacent-cut recursion. Both the constructed minimal factors and the
original factors of a prescribed OBC tensor use these identities.

Source: PGVWC07, arXiv:quant-ph/0608197, the canonical recursion conditions
in Theorem thm:OBC-Vidal, MPSarchive.tex lines 444--456.
-/

open Matrix
open scoped BigOperators

namespace MPSPreparation

variable {d N k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- The physical prefix extension identity determines the forward Gram
recursion for arbitrary adjacent-cut factors.
Source: PGVWC07, MPSarchive.tex lines 444--456, condition 2. -/
theorem prefixGram_eq_sum_of_extendCutPrefix (hk : k < N)
    (F : Matrix (CutPrefixConfig d N k) ι ℂ)
    (F' : Matrix (CutPrefixConfig d N (k + 1)) κ ℂ) (M : Fin d → Matrix ι κ ℂ)
    (hstep : ∀ u i q, F' (extendCutPrefix k u i) q = (F * M i) u q) :
    ∑ i, (M i)ᴴ * (Fᴴ * F) * M i = F'ᴴ * F' := by
  classical
  calc
    _ = ∑ i, (F * M i)ᴴ * (F * M i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      ext q r
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_comm]
      symm
      rw [← (extendCutPrefixEquiv (d := d) hk).sum_comp, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro i _
      change star (F' (extendCutPrefix k u i) q) * F' (extendCutPrefix k u i) r = _
      rw [hstep, hstep]
      rfl

omit [Fintype ι] in
/-- The physical suffix extension identity determines the backward Gram
recursion for arbitrary adjacent-cut factors.
Source: PGVWC07, MPSarchive.tex lines 444--456, condition 1. -/
theorem suffixGram_eq_sum_of_extendCutSuffix (hk : k < N)
    (G : Matrix ι (CutSuffixConfig d N k) ℂ)
    (G' : Matrix κ (CutSuffixConfig d N (k + 1)) ℂ) (M : Fin d → Matrix ι κ ℂ)
    (hstep : ∀ i v q, G q (extendCutSuffix k i v) = (M i * G') q v) :
    G * Gᴴ = ∑ i, M i * (G' * G'ᴴ) * (M i)ᴴ := by
  classical
  calc
    _ = ∑ i, (M i * G') * (M i * G')ᴴ := by
      ext q r
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [← (extendCutSuffixEquiv (d := d) hk).sum_comp, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro v _
      change G q (extendCutSuffix k i v) * star (G r (extendCutSuffix k i v)) = _
      rw [hstep, hstep]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end MPSPreparation
