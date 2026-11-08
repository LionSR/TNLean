/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OBCCanonicalBasisFamily
import TNLean.MPS.Preparation.OBCCanonicalRecurrences
import TNLean.MPS.Preparation.CutCoefficientRank
import TNLean.MPS.Preparation.OBCRectangularCutMaps

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
private theorem exists_canonical_coeff_eq_with_cutBasis {d N : ℕ} (hN : 0 < N)
    (ψ : (Fin N → Fin d) → ℂ) (hnorm : ∑ σ, star (ψ σ) * ψ σ = 1) :
    ∃ A : OBCChainTensor d (d ^ (N / 2)) N,
    ∃ Λ : (k : Fin (N + 1)) → Matrix (Fin (A.bondDim k)) (Fin (A.bondDim k)) ℂ,
      A.coeff = ψ ∧
      (∀ k, A.bondDim k = cutRank ψ k.val) ∧
      (∀ p, ∑ i, A.tensor p i * (A.tensor p i)ᴴ = 1) ∧
      (∀ p, ∑ i, (A.tensor p i)ᴴ * Λ p.castSucc * A.tensor p i = Λ p.succ) ∧
      Λ 0 = 1 ∧ Λ (Fin.last N) = 1 ∧
      (∀ k, (Λ k).PosDef ∧
        (∃ lam : Fin (A.bondDim k) → ℝ,
          (∀ q, 0 < lam q) ∧ Λ k = Matrix.diagonal (fun q ↦ (lam q : ℂ))) ∧
        Matrix.trace (Λ k) = 1) ∧
      ∃ (hψ : ψ ≠ 0)
        (C : ∀ k, Module.Basis (Fin (cutCoefficientRank ψ k)) ℂ (cutColumnSpace ψ k)),
        (∀ q, (C 0 q).val = 1) ∧ (∀ q, (C N q).val = fullCutVector ψ) ∧
        ∃ hbound : ∀ k : Fin (N + 1), cutCoefficientRank ψ k.val ≤ d ^ (N / 2),
          A = minimalCutChain ψ hψ C hbound := by
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
  refine ⟨A, Λ, funext (minimalCutChain_coeff ψ hψ B hB0 hBN hbound), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact cutCoefficientRank_eq_cutRank ψ (Nat.lt_succ_iff.mp k.isLt)
  · intro p
    exact hiso p.val p.isLt
  · intro p
    exact cutBondDensity_step ψ B p.isLt
  · exact cutPrefixMatrix_zero_gram ψ hψ B hB0
  · exact cutPrefixMatrix_last_gram ψ hψ B hBN hnorm
  · intro k
    obtain ⟨lam, hlam, hdiag⟩ := (hcuts k.val).1
    refine ⟨?_, ⟨lam, hlam, hdiag⟩, htrace k.val (Nat.lt_succ_iff.mp k.isLt)⟩
    change ((cutPrefixMatrix ψ B k.val)ᴴ * cutPrefixMatrix ψ B k.val).PosDef
    rw [hdiag, Matrix.posDef_diagonal_iff]
    intro q
    exact_mod_cast hlam q
  · exact ⟨hψ, B, hB0, hBN, hbound, rfl⟩

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
        (∃ lam : Fin (A.bondDim k) → ℝ,
          (∀ q, 0 < lam q) ∧ Λ k = Matrix.diagonal (fun q ↦ (lam q : ℂ))) ∧
        Matrix.trace (Λ k) = 1 := by
  obtain ⟨A, Λ, hcoeff, hbond, hiso, hdensity, hleft, hright, hΛ, _⟩ :=
    exists_canonical_coeff_eq_with_cutBasis hN ψ hnorm
  exact ⟨A, Λ, hcoeff, hbond, hiso, hdensity, hleft, hright, hΛ⟩

/-- Every normalized OBC representation admits the simultaneous Schmidt
canonical form by actual local rectangular maps. Their product is the
identity on each retained minimal bond, and the endpoint identifications
are scalar identities. No square invertible gauge is assumed.
Source: PGVWC07, Theorem free-OBC and Eq. eq.lem.II.9, lines 461--486;
canonical conditions 1--3 in Theorem thm:OBC-Vidal, lines 431--458. -/
theorem exists_canonical_coeff_eq_rectangular_maps {d D N : ℕ} (hN : 0 < N)
    (B : OBCChainTensor d D N) (hnorm : ∑ σ, star (B.coeff σ) * B.coeff σ = 1) :
    ∃ A : OBCChainTensor d (d ^ (N / 2)) N,
    ∃ Λ : (k : Fin (N + 1)) → Matrix (Fin (A.bondDim k)) (Fin (A.bondDim k)) ℂ,
    ∃ Y : (k : Fin (N + 1)) → Matrix (Fin (A.bondDim k)) (Fin (B.bondDim k)) ℂ,
    ∃ Z : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (A.bondDim k)) ℂ,
      A.coeff = B.coeff ∧
      (∀ k, A.bondDim k = cutRank B.coeff k.val) ∧
      (∀ p, ∑ i, A.tensor p i * (A.tensor p i)ᴴ = 1) ∧
      (∀ p, ∑ i, (A.tensor p i)ᴴ * Λ p.castSucc * A.tensor p i = Λ p.succ) ∧
      Λ 0 = 1 ∧ Λ (Fin.last N) = 1 ∧
      (∀ k, (Λ k).PosDef ∧
        (∃ lam : Fin (A.bondDim k) → ℝ,
          (∀ q, 0 < lam q) ∧ Λ k = Matrix.diagonal (fun q ↦ (lam q : ℂ))) ∧
        Matrix.trace (Λ k) = 1) ∧
      (∀ k, Y k * Z k = 1) ∧
      (∀ q r, Y 0 q r = 1) ∧ (∀ q r, Z (Fin.last N) q r = 1) ∧
      ∀ (p : Fin N) (i : Fin d), A.tensor p i = Y p.castSucc * B.tensor p i * Z p.succ := by
  obtain ⟨A, Λ, hcoeff, hbond, hiso, hdensity, hleft, hright, hΛ,
    hψ, C, hC0, hCN, hbound, hA⟩ := exists_canonical_coeff_eq_with_cutBasis hN B.coeff hnorm
  subst A
  obtain ⟨Y, Z, hYZ, hY0, hZN, hsite⟩ :=
    exists_rectangular_maps_to_cutBasis B B.coeff rfl C hC0 hCN
  exact ⟨minimalCutChain B.coeff hψ C hbound, Λ, Y, Z, hcoeff, hbond,
    hiso, hdensity, hleft, hright, hΛ, hYZ, hY0, hZN, hsite⟩

end OBCChainTensor
