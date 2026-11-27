/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationFactorization
import QICLean.Algebra.Combinatorics.FinSumPermutation

/-!
# Physical configuration decompositions for OBC canonical equations

Adjoining one letter is a bijection for both sides of a physical cut.
These actual configuration bijections identify the finite sums in the
canonical Gram recursions, including the two endpoint cuts.

Source: PGVWC07, arXiv:quant-ph/0608197, conditions 1--3 of Theorem
thm:OBC-Vidal, lines 431--458.

## Gram recurrences under physical cut extension

The same physical configuration bijections give the forward prefix Gram
and backward suffix Gram identities for any factors satisfying the actual
adjacent-cut recursion. Both the constructed minimal factors and the
original factors of a prescribed OBC tensor use these identities.

Source: PGVWC07, arXiv:quant-ph/0608197, the canonical recursion conditions
in Theorem thm:OBC-Vidal, MPSarchive.tex lines 444--456.
-/

section

open ManyBody (interval cutMatrix cutRank RegionConfig ComplConfig)

namespace MPSPreparation

/-- The suffix at the initial cut is the complete physical configuration.
Source: PGVWC07, endpoint condition 3 of Theorem thm:OBC-Vidal. -/
def initialCutSuffixEquiv (d N : ℕ) : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 0) ≃ (Fin N → Fin d) where
  toFun v s := v ⟨s, notMem_interval_zero_iff.mpr (Nat.zero_le s.val)⟩
  invFun σ s := σ s.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- The prefix at the final cut is the complete physical configuration.
Source: PGVWC07, endpoint condition 3 of Theorem thm:OBC-Vidal. -/
def finalCutPrefixEquiv (d N : ℕ) : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 N) ≃ (Fin N → Fin d) where
  toFun u s := u ⟨s, mem_interval_zero_iff.mpr s.isLt⟩
  invFun σ s := σ s.val
  left_inv _ := rfl
  right_inv _ := rfl

end MPSPreparation

end

section

open Matrix
open scoped BigOperators

namespace MPSPreparation

variable {d N k : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- The physical prefix extension identity determines the forward Gram
recursion for arbitrary adjacent-cut factors.
Source: PGVWC07, MPSarchive.tex lines 444--456, condition 2. -/
theorem prefixGram_eq_sum_of_extendCutPrefix (hk : k < N)
    (F : Matrix (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) ι ℂ)
    (F' : Matrix (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1))) κ ℂ) (M : Fin d → Matrix ι κ ℂ)
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
      refine Finset.sum_congr₂ fun u _ i _ ↦ ?_
      exact congrArg₂ (fun a b ↦ star a * b) (hstep u i q) (hstep u i r)

omit [Fintype ι] in
/-- The physical suffix extension identity determines the backward Gram
recursion for arbitrary adjacent-cut factors.
Source: PGVWC07, MPSarchive.tex lines 444--456, condition 1. -/
theorem suffixGram_eq_sum_of_extendCutSuffix (hk : k < N)
    (G : Matrix ι (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) ℂ)
    (G' : Matrix κ (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1))) ℂ) (M : Fin d → Matrix ι κ ℂ)
    (hstep : ∀ i v q, G q (extendCutSuffix k i v) = (M i * G') q v) :
    G * Gᴴ = ∑ i, M i * (G' * G'ᴴ) * (M i)ᴴ := by
  classical
  calc
    _ = ∑ i, (M i * G') * (M i * G')ᴴ := by
      ext q r
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [← (extendCutSuffixEquiv (d := d) hk).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr₂ fun i _ v _ ↦ ?_
      exact congrArg₂ (fun a b ↦ a * star b) (hstep i v q) (hstep i v r)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end MPSPreparation

end
