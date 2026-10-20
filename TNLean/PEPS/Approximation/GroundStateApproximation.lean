/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExactFiniteException
import TNLean.PEPS.Approximation.PartyColumnRouting

/-!
# The polynomial PEPS approximation from a compressed dyadic operator network

Section 8 of the polynomial-PEPS manuscript assembles Theorem 1.1 in three steps. For
sufficiently large `L`, the protocol of Proposition 7.1 followed by distributed compression
gives a party operator network `σ` on dyadic anchors, with polynomial link dimensions and
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ C L⁻⁵` (`eq:compressed-density`). Lemma 8.1 extracts a nonzero column, and
Lemma 8.2 routes it onto the square with bond dimensions at most `(C₁ L ^ k) ^ χ`
(`eq:final-bond`). Finally, the finitely many sizes below the threshold are covered by exact
spanning-tree PEPS and one enlarged prefactor.

`DyadicOperatorNetworkAt` states the output of the first step for a family of states as a
proposition: the constants and the threshold are fixed before the size and the state, and the
network meets the hypotheses of Lemma 8.2. The family of Theorem 1.1 is
`IsSquareGroundState q J Δ`, the gapped ground vectors of the model. The theorem
`hasPEPSApproximation_of_dyadicOperatorNetworkAt` derives the large-size approximation from it by
the routing step. The small sizes and the final constants are handled in
`polynomialPEPSApproximation_of_ratios`, and Theorem 1.1 is `polynomialPEPSApproximation`.

## Main definitions

* `TNLean.PEPS.Approximation.DyadicOperatorNetworkAt`: the compressed dyadic operator network
  for a family of states, at given constants and threshold.

## Main results

* `TNLean.PEPS.Approximation.HasPEPSApproximation.mono_exponent`: increasing the exponent
  preserves an approximation when `L ≥ 1`.
* `TNLean.PEPS.Approximation.hasPEPSApproximation_of_dyadicOperatorNetworkAt`: the large-size
  approximation at the bond constants `max(C₁, 1) ^ χ` and `max(k, 0) χ + 1`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), Theorem 1.1 `thm:main`,
  `00-introduction.tex:36–57`; §8, `07-assembly.tex:9–63` (error, normalization and
  compression) and `07-assembly.tex:179–214` (order of constants and small sizes); immutable
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. These are original proofs; no OpenAI
  Lean code is copied or adapted.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

/-- Increasing the exponent preserves the same PEPS, phase, and error bound on a square of
side at least one, where `L ^ c ≤ L ^ c'` for `c ≤ c'`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), the choice of the final constants,
`07-assembly.tex:197–214`. -/
theorem HasPEPSApproximation.mono_exponent {C c c' : ℝ} {L q : ℕ} {Ω : StateSpace L q}
    (h : HasPEPSApproximation C c L q Ω) (hC : 0 ≤ C) (hL : 1 ≤ L) (hc : c ≤ c') :
    HasPEPSApproximation C c' L q Ω := by
  obtain ⟨A, hpos, hbound, hne, herr⟩ := h
  refine ⟨A, hpos, fun e ↦ (hbound e).trans ?_, hne, herr⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL) hc) hC

/-- **Compressed dyadic operator network for a family of states, at given constants.** Every
state `Ω` of the family `G` on the square of side `L ≥ max 2 L₀` is approximated by an operator
party network in the following sense. The parties are attached to dyadic blocks of the padded
square, at most `B` to any block; every party has at most `deg` links; every link separation is
at most `c` times either endpoint scale; every link dimension is at most `C₁ L ^ k`; and the
operator `σ` of the network, each party read at the fold of its anchor, satisfies
`‖σ - |Ω⟩⟨Ω|‖₁ ≤ C / L ^ 5`. No positivity or Hermiticity of `σ` is required. Section 8
uses the family `IsSquareGroundState q J Δ` of gapped unit ground vectors of the model.

The fold fixes the genuine sites, at which the source places the physical outputs of the unit
parties (`07-assembly.tex:25–26` and `158–159`).

Source: Polynomial-PEPS manuscript (Sept 24 2026), `eq:compressed-density` and the
paragraph containing it, `07-assembly.tex:53–63`, with the dyadic anchors of
`07-assembly.tex:102–114`, the hypotheses of Lemma 8.2 `lem:routing` supplied by
Proposition 7.1 `prop:protocol` (`07-assembly.tex:128–131`), and the polynomial link
dimensions `C₁ L ^ r` of `07-assembly.tex:164–170`. -/
def DyadicOperatorNetworkAt (q : ℕ) (G : ∀ L : ℕ, StateSpace L q → Prop) (C C₁ k : ℝ)
    (B deg c L₀ : ℕ) : Prop :=
  ∀ L : ℕ, ∀ hL : 2 ≤ L, L₀ ≤ L → ∀ Ω : StateSpace L q, G L Ω →
    ∃ (P Λ : Type) (_ : Fintype P) (_ : DecidableEq P) (_ : Fintype Λ)
      (_ : DecidableEq Λ) (N : PartyNetwork P Λ (q * q)) (A : DyadicPlacement P),
      A.InGrid (paddedSide L) ∧ A.BlockBounded B ∧
      DyadicPlacement.DegreeBounded N.src N.tgt deg ∧
      A.SeparationBounded N.src N.tgt c ∧
      (∀ ℓ, (N.dim ℓ : ℝ) ≤ C₁ * (L : ℝ) ^ k) ∧
      Matrix.rectangularTraceNorm
        (N.operatorCoeff (fun p ↦ foldVertex (lt_of_lt_of_le two_pos hL) (A.anchor p)) -
          Matrix.euclideanOuterProduct Ω Ω) ≤ C / (L : ℝ) ^ 5

/-- On a square of side `L ≥ 2` with `2 C ≤ L`, the error `C / L ^ 5` is less than one and at
most half of `L⁻¹`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), the threshold `L₀` of
`07-assembly.tex:205–206`. -/
private theorem compressed_error_le {C : ℝ} {L : ℕ} (hL : 2 ≤ L) (hC : 2 * C ≤ L) :
    C / (L : ℝ) ^ 5 < 1 ∧ 2 * (C / (L : ℝ) ^ 5) ≤ (L : ℝ)⁻¹ := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have h4 : (L : ℝ) ≤ (L : ℝ) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hhalf : 2 * (C / (L : ℝ) ^ 5) ≤ (L : ℝ)⁻¹ := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    calc 2 * C ≤ (L : ℝ) ^ 4 := hC.trans h4
      _ = (L : ℝ)⁻¹ * (L : ℝ) ^ 5 := by field_simp
  refine ⟨?_, hhalf⟩
  have : (L : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hLpos (by norm_num)]
    linarith
  linarith

/-- **The large-size approximation from a compressed dyadic operator network, at given
constants.** If the compressed dyadic operator network exists for a family `G` of unit states
at the constants `C, C₁, k`, the routing bounds `B, deg, c` and the threshold `L₀`, then every
state of `G` on the square of side `L ≥ 2` with `max L₀ ⌈2 C⌉ ≤ L` has a nonzero PEPS
approximation with bond dimensions at most `max(C₁, 1) ^ χ L ^ (max(k, 0) χ + 1)`, where
`χ = 8 (2 c + 1) B deg` is the congestion of Lemma 8.2, and phase-normalized error at most `L⁻¹`.
The column of Lemma 8.1 is routed by Lemma 8.2; the threshold `⌈2 C⌉` makes the network error
`C L⁻⁵` at most half of `L⁻¹`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), the proof of Theorem 1.1 in §8,
`07-assembly.tex:53–63` (`eq:compressed-density`), `07-assembly.tex:122–177` (Lemmas 8.1 and
8.2, `eq:final-bond`) and `07-assembly.tex:197–206` (the threshold). -/
theorem hasPEPSApproximation_of_dyadicOperatorNetworkAt {q : ℕ}
    {G : ∀ L : ℕ, StateSpace L q → Prop} (hG : ∀ L Ω, G L Ω → ‖Ω‖ = 1) {C C₁ k : ℝ}
    {B deg c L₀ : ℕ} (hnet : DyadicOperatorNetworkAt q G C C₁ k B deg c L₀) :
    ∀ L : ℕ, 2 ≤ L → max L₀ ⌈2 * C⌉₊ ≤ L → ∀ Ω : StateSpace L q, G L Ω →
      HasPEPSApproximation (max C₁ 1 ^ (8 * (2 * c + 1) * B * deg))
        (max k 0 * ((8 * (2 * c + 1) * B * deg : ℕ) : ℝ) + 1) L q Ω := by
  intro L hL hL₀ Ω hΩ
  set χ := 8 * (2 * c + 1) * B * deg
  set C₁' := max C₁ 1
  set k' := max k 0
  obtain ⟨P, Λ, _, _, _, _, N, A, hgrid, hB, hdeg, hsep, hdim, hσ⟩ :=
    hnet L hL (le_of_max_le_left hL₀) Ω hΩ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hdim' : ∀ ℓ, (N.dim ℓ : ℝ) ≤ C₁' * (L : ℝ) ^ k' := fun ℓ ↦
    (hdim ℓ).trans (mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)) (by positivity)
      (by positivity))
  have hC : 2 * C ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hL₀)
  obtain ⟨hη, hηL⟩ := compressed_error_le hL hC
  exact (hasPEPSApproximation_of_fixInput_dyadicRouting _ N A hgrid hB hdeg hsep
    (le_max_right _ _) (le_max_right _ _) hdim' Ω (hG L Ω hΩ) hσ hη hηL).mono_exponent
    (by positivity) (by omega) (by linarith)

end TNLean.PEPS.Approximation
