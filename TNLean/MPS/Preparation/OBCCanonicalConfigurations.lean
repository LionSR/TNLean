/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentationFactorization

/-!
# Physical configuration decompositions for OBC canonical equations

Adjoining one letter is a bijection for both sides of a physical cut.
These actual configuration bijections identify the finite sums in the
canonical Gram recursions, including the two endpoint cuts.

Source: PGVWC07, arXiv:quant-ph/0608197, conditions 1--3 of Theorem
thm:OBC-Vidal, lines 431--458.
-/

namespace MPSPreparation

/-- Adjoining a last prefix letter enumerates the next physical prefix
exactly once. Source: PGVWC07, Theorem thm:OBC-Vidal, lines 431--458. -/
def extendCutPrefixEquiv {d N k : ℕ} (hk : k < N) :
    CutPrefixConfig d N k × Fin d ≃ CutPrefixConfig d N (k + 1) where
  toFun ui := extendCutPrefix k ui.1 ui.2
  invFun w := (fun s ↦ w ⟨s.val, by have := s.2; omega⟩,
    w ⟨⟨k, hk⟩, Nat.lt_succ_self k⟩)
  left_inv := by
    rintro ⟨u, i⟩
    apply Prod.ext
    · funext s
      simp only [extendCutPrefix, s.property, dite_true]
    · simp only [extendCutPrefix, Nat.lt_irrefl, dite_false]
  right_inv w := by
    funext s
    by_cases hs : s.val.val < k
    · simp only [extendCutPrefix, hs, dite_true]
    · simp only [extendCutPrefix, hs, dite_false]
      congr 1
      apply Subtype.ext
      apply Fin.ext
      change k = s.val.val
      have := s.property
      omega

/-- Adjoining a first suffix letter enumerates the preceding physical
suffix exactly once. Source: PGVWC07, Theorem thm:OBC-Vidal, lines 431--458. -/
def extendCutSuffixEquiv {d N k : ℕ} (hk : k < N) :
    Fin d × CutSuffixConfig d N (k + 1) ≃ CutSuffixConfig d N k where
  toFun iv := extendCutSuffix k iv.1 iv.2
  invFun w := (w ⟨⟨k, hk⟩, le_rfl⟩, fun s ↦ w ⟨s.val, by have := s.2; omega⟩)
  left_inv := by
    rintro ⟨i, v⟩
    apply Prod.ext
    · simp only [extendCutSuffix, Nat.not_succ_le_self, dite_false]
    · funext s
      simp only [extendCutSuffix, s.property, dite_true]
  right_inv w := by
    funext s
    by_cases hs : k + 1 ≤ s.val.val
    · simp only [extendCutSuffix, hs, dite_true]
    · simp only [extendCutSuffix, hs, dite_false]
      congr 1
      apply Subtype.ext
      apply Fin.ext
      change k = s.val.val
      have := s.property
      omega

/-- The suffix at the initial cut is the complete physical configuration.
Source: PGVWC07, endpoint condition 3 of Theorem thm:OBC-Vidal. -/
def initialCutSuffixEquiv (d N : ℕ) : CutSuffixConfig d N 0 ≃ (Fin N → Fin d) where
  toFun v s := v ⟨s, Nat.zero_le s.val⟩
  invFun σ s := σ s.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- The prefix at the final cut is the complete physical configuration.
Source: PGVWC07, endpoint condition 3 of Theorem thm:OBC-Vidal. -/
def finalCutPrefixEquiv (d N : ℕ) : CutPrefixConfig d N N ≃ (Fin N → Fin d) where
  toFun u s := u ⟨s, s.isLt⟩
  invFun σ s := σ s.val
  left_inv _ := rfl
  right_inv _ := rfl

end MPSPreparation
