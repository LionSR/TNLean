/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OBCCanonicalBasisFamily
import TNLean.MPS.Preparation.OBCCanonicalRecurrences
import TNLean.MPS.Preparation.CutCoefficientRank

/-!
# Simultaneous Schmidt canonical form of an open-boundary MPS

Every normalized state of positive chain length has a representation with
minimal physical cut ranks, right-canonical site matrices and strictly
positive diagonal bond densities of trace one. The two endpoint densities
are the scalar identity, and the common bond bound is the sharp physical
bound d to the power floor N/2.

The proof chooses weighted Schmidt bases of the actual physical cut
column spaces and uses their exact prefix and suffix recursions. It does
not assume a density family, a canonical representation, or a square
invertible gauge.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal,
conditions 1--3 and the successive Schmidt construction, lines 431--458.
As throughout the source's canonical conditions, a state is normalized;
the positive chain length is the open-chain domain of that statement.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace OBCChainTensor

open MPSPreparation

/-- Every normalized physical state of positive length has an actual
simultaneous OBC canonical representation. Bond dimensions are the actual
Schmidt cut ranks, and the densities are derived positive diagonal Grams.
No canonical or density hypothesis is supplied.
Source: PGVWC07, Theorem thm:OBC-Vidal, lines 431--458, conditions 1--3. -/
theorem exists_canonical_coeff_eq {d N : ℕ} (hN : 0 < N)
    (ψ : (Fin N → Fin d) → ℂ) (hnorm : ∑ σ, star (ψ σ) * ψ σ = 1) :
    ∃ A : OBCChainTensor d (d ^ (N / 2)) N,
    ∃ Λ : (k : Fin (N + 1)) → Matrix (Fin (A.bondDim k)) (Fin (A.bondDim k)) ℂ,
      A.coeff = ψ ∧
      (∀ k, A.bondDim k = cutRank ψ k.val) ∧
      (∀ p, ∑ i, A.tensor p i * (A.tensor p i)ᴴ = 1) ∧
      (∀ p, ∑ i, (A.tensor p i)ᴴ * Λ p.castSucc * A.tensor p i = Λ p.succ) ∧
      Λ 0 = 1 ∧ Λ (Fin.last N) = 1 ∧
      ∀ k, (Λ k).PosDef ∧
        (∃ λ : Fin (A.bondDim k) → ℝ,
          (∀ q, 0 < λ q) ∧ Λ k = Matrix.diagonal (fun q ↦ (λ q : ℂ))) ∧
        Matrix.trace (Λ k) = 1 := by
  classical
  have hψ : ψ ≠ 0 := by
    intro hzero
    simp only [hzero, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at hnorm
    exact zero_ne_one hnorm
  let : NeZero d := ⟨by
    intro hd
    subst d
    apply hψ
    funext σ
    exact Fin.elim0 (σ ⟨0, hN⟩)⟩
  obtain ⟨B, hB0, hBN, hcuts⟩ := exists_canonicalCutBasisFamily hN ψ hnorm
  have hbound : ∀ k : Fin (N + 1), cutCoefficientRank ψ k.val ≤ d ^ (N / 2) := by
    intro k
    rw [cutCoefficientRank_eq_cutRank ψ (Nat.lt_succ_iff.mp k.isLt)]
    exact cutRank_le_pow_half ψ k.val
  let A := minimalCutChain ψ hψ B hbound
  let Λ : (k : Fin (N + 1)) → Matrix (Fin (A.bondDim k)) (Fin (A.bondDim k)) ℂ :=
    fun k ↦ cutBondDensity ψ B k.val
  have hiso : ∀ k, k < N → ∑ i, cutSiteMatrix ψ B k i * (cutSiteMatrix ψ B k i)ᴴ = 1 := by
    intro k hk
    exact sum_cutSiteMatrix_mul_conjTranspose_eq_one ψ B hk (hcuts k).2 (hcuts (k + 1)).2
  have htrace : ∀ k, k ≤ N → Matrix.trace (cutBondDensity ψ B k) = 1 := by
    intro k hk
    induction k with
    | zero =>
        rw [cutBondDensity, cutPrefixMatrix_zero_gram ψ hψ B hB0, Matrix.trace_one]
        simp only [Fintype.card_fin, cutCoefficientRank_zero ψ hψ, Nat.cast_one]
    | succ k ih =>
        rw [trace_cutBondDensity_step ψ B (by omega) (hiso k (by omega)), ih (by omega)]
  refine ⟨A, Λ, funext (minimalCutChain_coeff ψ hψ B hB0 hBN hbound), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact cutCoefficientRank_eq_cutRank ψ (Nat.lt_succ_iff.mp k.isLt)
  · intro p
    exact hiso p.val p.isLt
  · intro p
    exact cutBondDensity_step ψ B p.isLt
  · exact cutPrefixMatrix_zero_gram ψ hψ B hB0
  · exact cutPrefixMatrix_last_gram ψ hψ B hBN hnorm
  · intro k
    obtain ⟨λ, hλ, hdiag⟩ := (hcuts k.val).1
    refine ⟨?_, ⟨λ, hλ, hdiag⟩, htrace k.val (Nat.lt_succ_iff.mp k.isLt)⟩
    change ((cutPrefixMatrix ψ B k.val)ᴴ * cutPrefixMatrix ψ B k.val).PosDef
    rw [hdiag, Matrix.posDef_diagonal_iff]
    intro q
    exact_mod_cast hλ q

end OBCChainTensor
