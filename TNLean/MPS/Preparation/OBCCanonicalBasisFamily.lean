/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OBCCanonicalCutBases
import TNLean.MPS.Preparation.OBCCanonicalEndpoints

/-!
# Simultaneous weighted Schmidt cut bases with exact endpoints

Weighted compact Schmidt bases are chosen independently at all interior
cuts. At the endpoints their vectors are fixed to one and to the actual
normalized state. The resulting prefix Gram matrices are strictly positive
diagonal, and all suffix factors are row-coisometric simultaneously.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal,
conditions 1--3 and the successive Schmidt construction, lines 431--458.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace MPSPreparation

/-- A normalized nonzero chain of positive length has a simultaneous
family of physical cut bases with exact endpoint vectors, positive diagonal
prefix Grams and row-coisometric suffix factors. The densities and their
positivity are constructed from the actual coefficient tensor.
Source: PGVWC07, Theorem thm:OBC-Vidal, lines 431--458. -/
theorem exists_canonicalCutBasisFamily {d N : ℕ} (hN : 0 < N)
    (ψ : (Fin N → Fin d) → ℂ)
    (hnorm : ∑ σ, star (ψ σ) * ψ σ = 1) :
    ∃ B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k),
      (∀ q, (B 0 q).val = 1) ∧ (∀ q, (B N q).val = fullCutVector ψ) ∧
      ∀ k,
        (∃ lam : Fin (cutCoefficientRank ψ k) → ℝ,
          (∀ q, 0 < lam q) ∧
          (cutPrefixMatrix ψ B k)ᴴ * cutPrefixMatrix ψ B k =
            Matrix.diagonal (fun q ↦ (lam q : ℂ))) ∧
        cutSuffixMatrix ψ B k * (cutSuffixMatrix ψ B k)ᴴ = 1 := by
  classical
  have hψ : ψ ≠ 0 := by
    intro hzero
    simp only [hzero, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨E, hE0, hEN⟩ := exists_cutBasisFamily_with_endpoints ψ hψ hN
  choose C s hs hGram hG using fun k ↦ exists_weightedSchmidtCutBasis ψ k
  let B : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k) := fun k ↦
    if h0 : k = 0 then by subst k; exact E 0
    else if hlast : k = N then by subst k; exact E N
    else C k
  have hB0 : ∀ q, (B 0 q).val = 1 := by
    intro q
    simpa only [B, dite_eq_left rfl] using hE0 q
  have hBN : ∀ q, (B N q).val = fullCutVector ψ := by
    intro q
    simpa only [B, dite_eq_right (Nat.ne_of_gt hN), dite_eq_left rfl] using hEN q
  refine ⟨B, hB0, hBN, ?_⟩
  intro k
  by_cases h0 : k = 0
  · subst k
    refine ⟨⟨fun _ ↦ 1, fun _ ↦ one_pos, ?_⟩,
      cutSuffixMatrix_zero_coisometry ψ hψ B hB0 hnorm⟩
    simpa only [Complex.ofReal_one, Matrix.diagonal_one] using
      cutPrefixMatrix_zero_gram ψ hψ B hB0
  by_cases hlast : k = N
  · subst k
    refine ⟨⟨fun _ ↦ 1, fun _ ↦ one_pos, ?_⟩,
      cutSuffixMatrix_last_coisometry ψ hψ B hBN⟩
    simpa only [Complex.ofReal_one, Matrix.diagonal_one] using
      cutPrefixMatrix_last_gram ψ hψ B hBN hnorm
  refine ⟨⟨fun q ↦ s k q ^ 2, fun q ↦ sq_pos_of_pos (hs k q), ?_⟩, ?_⟩
  · simpa only [cutPrefixMatrix, B, dif_neg h0, dif_neg hlast, Complex.ofReal_pow] using hGram k
  · simpa only [cutSuffixMatrix, B, dif_neg h0, dif_neg hlast] using hG k

end MPSPreparation
