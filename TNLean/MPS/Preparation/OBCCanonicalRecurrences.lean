/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.PhysicalCutGramRecurrences

/-!
# The two OBC canonical equations from actual cut factors

The site matrices already used in the minimal open-boundary construction
propagate both physical prefix and suffix factors. Taking their Grams,
with the exact one-letter configuration bijections, gives the density
recursion and the right-canonical equation. Thus neither normalization
is stipulated as a substitute for the physical cut construction.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal,
conditions 1--3, lines 431--458.
-/

open Matrix
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))

/-- The actual bond density is the Gram matrix of the weighted physical
prefix vectors. Source: PGVWC07, Theorem thm:OBC-Vidal, conditions 2--3. -/
noncomputable def cutBondDensity (k : ℕ) :
    Matrix (Fin (cutCoefficientRank ψ k)) (Fin (cutCoefficientRank ψ k)) ℂ :=
  (cutPrefixMatrix ψ B k)ᴴ * cutPrefixMatrix ψ B k

/-- Prefix propagation gives the density recursion for the actual site
matrices. Source: PGVWC07, Theorem thm:OBC-Vidal, condition 2. -/
theorem cutBondDensity_step {k : ℕ} (hk : k < N) :
    ∑ i, (cutSiteMatrix ψ B k i)ᴴ * cutBondDensity ψ B k * cutSiteMatrix ψ B k i =
      cutBondDensity ψ B (k + 1) := by
  exact prefixGram_eq_sum_of_extendCutPrefix hk (cutPrefixMatrix ψ B k)
    (cutPrefixMatrix ψ B (k + 1)) (cutSiteMatrix ψ B k)
    (fun u i q ↦ cutPrefixMatrix_step ψ B k i u q)

/-- Suffix propagation gives the exact backward Gram recursion.
Source: PGVWC07, Theorem thm:OBC-Vidal, condition 1. -/
theorem cutSuffixMatrix_gram_step {k : ℕ} (hk : k < N) :
    cutSuffixMatrix ψ B k * (cutSuffixMatrix ψ B k)ᴴ =
      ∑ i, cutSiteMatrix ψ B k i *
        (cutSuffixMatrix ψ B (k + 1) * (cutSuffixMatrix ψ B (k + 1))ᴴ) *
          (cutSiteMatrix ψ B k i)ᴴ := by
  exact suffixGram_eq_sum_of_extendCutSuffix hk (cutSuffixMatrix ψ B k)
    (cutSuffixMatrix ψ B (k + 1)) (cutSiteMatrix ψ B k)
    (fun i v q ↦ congrFun (cutSuffixMatrix_step ψ B k i v) q)

/-- Row-coisometry of the two physical suffix factors proves the
right-canonical site equation. Source: PGVWC07, Theorem thm:OBC-Vidal,
condition 1, obtained from the actual Schmidt cut factors. -/
theorem sum_cutSiteMatrix_mul_conjTranspose_eq_one {k : ℕ} (hk : k < N)
    (hprev : cutSuffixMatrix ψ B k * (cutSuffixMatrix ψ B k)ᴴ = 1)
    (hnext : cutSuffixMatrix ψ B (k + 1) * (cutSuffixMatrix ψ B (k + 1))ᴴ = 1) :
    ∑ i, cutSiteMatrix ψ B k i * (cutSiteMatrix ψ B k i)ᴴ = 1 := by
  have h := cutSuffixMatrix_gram_step ψ B hk
  rw [hprev, hnext] at h
  simpa only [Matrix.mul_one] using h.symm

/-- A right-canonical site preserves the trace of the actual cut
bond density. Source: PGVWC07, Theorem thm:OBC-Vidal, condition 3. -/
theorem trace_cutBondDensity_step {k : ℕ} (hk : k < N)
    (hiso : ∑ i, cutSiteMatrix ψ B k i * (cutSiteMatrix ψ B k i)ᴴ = 1) :
    Matrix.trace (cutBondDensity ψ B (k + 1)) = Matrix.trace (cutBondDensity ψ B k) := by
  rw [← cutBondDensity_step ψ B hk, Matrix.trace_sum]
  calc
    _ = ∑ i, Matrix.trace
        (cutBondDensity ψ B k * (cutSiteMatrix ψ B k i * (cutSiteMatrix ψ B k i)ᴴ)) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (cutSiteMatrix ψ B k i)ᴴ
          (cutBondDensity ψ B k * cutSiteMatrix ψ B k i)
    _ = Matrix.trace (cutBondDensity ψ B k *
        ∑ i, cutSiteMatrix ψ B k i * (cutSiteMatrix ψ B k i)ᴴ) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = _ := by rw [hiso, Matrix.mul_one]

end MPSPreparation
