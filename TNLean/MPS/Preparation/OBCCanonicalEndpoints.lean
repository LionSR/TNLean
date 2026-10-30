/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OBCCanonicalConfigurations

/-!
# Endpoint normalizations of OBC cut factors

For a normalized state, fixing the endpoint basis vectors to one and to
the physical state gives unit prefix Grams and row-coisometric suffix
factors at both endpoints. These are derived endpoint identities, not
additional density or canonical-form assumptions.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal,
condition 3 and normalization in the proof of free-OBC, lines 431--458
and 511--522.
-/

open Matrix
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k))

include hψ

/-- The fixed initial cut vector has unit Gram matrix.
Source: PGVWC07, Theorem thm:OBC-Vidal, condition 3. -/
theorem cutPrefixMatrix_zero_gram (hB0 : ∀ q, (B 0 q).val = 1) :
    (cutPrefixMatrix ψ B 0)ᴴ * cutPrefixMatrix ψ B 0 = 1 := by
  classical
  let : IsEmpty {s : Fin N // s.val < 0} := ⟨fun s ↦ Nat.not_lt_zero _ s.property⟩
  let : Unique (Fin (cutCoefficientRank ψ 0)) :=
    Equiv.unique (finCongr (cutCoefficientRank_zero ψ hψ))
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, cutPrefixMatrix_zero ψ B hB0]

/-- The fixed final cut vector is normalized with the physical state.
Source: PGVWC07, Theorem thm:OBC-Vidal, condition 3. -/
theorem cutPrefixMatrix_last_gram (hBN : ∀ q, (B N q).val = fullCutVector ψ)
    (hnorm : ∑ σ, star (ψ σ) * ψ σ = 1) :
    (cutPrefixMatrix ψ B N)ᴴ * cutPrefixMatrix ψ B N = 1 := by
  classical
  let : Unique (Fin (cutCoefficientRank ψ N)) :=
    Equiv.unique (finCongr (cutCoefficientRank_last ψ hψ))
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, cutPrefixMatrix, hBN,
    Matrix.one_apply_eq]
  change (∑ u, star (ψ (finalCutPrefixEquiv d N u)) * ψ (finalCutPrefixEquiv d N u)) = 1
  exact ((finalCutPrefixEquiv d N).sum_comp (fun σ ↦ star (ψ σ) * ψ σ)).trans hnorm

/-- The final suffix factor is a row coisometry because the endpoint
cut basis is the complete physical coefficient vector.
Source: PGVWC07, Theorem thm:OBC-Vidal, conditions 1 and 3. -/
theorem cutSuffixMatrix_last_coisometry (hBN : ∀ q, (B N q).val = fullCutVector ψ) :
    cutSuffixMatrix ψ B N * (cutSuffixMatrix ψ B N)ᴴ = 1 := by
  classical
  let : IsEmpty {s : Fin N // N ≤ s.val} := ⟨fun s ↦ (not_le_of_gt s.val.isLt) s.property⟩
  let : Unique (Fin (cutCoefficientRank ψ N)) :=
    Equiv.unique (finCongr (cutCoefficientRank_last ψ hψ))
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, cutSuffixMatrix_last ψ B hBN]

/-- The initial suffix factor is a row coisometry exactly because the
actual physical state is normalized.
Source: PGVWC07, normalization in the proof of free-OBC, lines 511--522. -/
theorem cutSuffixMatrix_zero_coisometry (hB0 : ∀ q, (B 0 q).val = 1)
    (hnorm : ∑ σ, star (ψ σ) * ψ σ = 1) :
    cutSuffixMatrix ψ B 0 * (cutSuffixMatrix ψ B 0)ᴴ = 1 := by
  classical
  let : IsEmpty {s : Fin N // s.val < 0} := ⟨fun s ↦ Nat.not_lt_zero _ s.property⟩
  let : Unique (Fin (cutCoefficientRank ψ 0)) :=
    Equiv.unique (finCongr (cutCoefficientRank_zero ψ hψ))
  have hG : ∀ q v, cutSuffixMatrix ψ B 0 q v = ψ (initialCutSuffixEquiv d N v) := by
    intro q v
    have h := congrArg (fun M ↦ M (default : CutPrefixConfig d N 0) v)
      (cutCoefficientMatrix_eq_prefix_mul_suffix ψ B 0)
    simp only [Matrix.mul_apply, cutPrefixMatrix_zero ψ B hB0, one_mul,
      Fintype.sum_unique] at h
    have hq : (default : Fin (cutCoefficientRank ψ 0)) = q := Subsingleton.elim _ _
    rw [hq] at h
    exact h.symm.trans (by simp [cutCoefficientMatrix, initialCutSuffixEquiv])
  ext q r
  have hqr : q = r := Subsingleton.elim _ _
  subst r
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hG, Matrix.one_apply_eq]
  exact ((initialCutSuffixEquiv d N).sum_comp (fun σ ↦ ψ σ * star (ψ σ))).trans
    (by simpa only [mul_comm] using hnorm)

end MPSPreparation
