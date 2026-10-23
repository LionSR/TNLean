/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SchmidtTailConstraint
import TNLean.MPS.AreaLaw.Hastings.SchmidtTailMPS

/-!
# Matrix product state approximation from the entropy of the cuts

Suppose that the unit vector `Ω` on a chain of `L` sites with local dimension `q > 1` satisfies
the approximate factorization of Hastings' Lemma 1 at every internal cut, and that a natural
number `k₀` satisfies `k₀ ≥ exp(2 S_j)/2` for the entropy `S_j` of the first `j` sites at every
internal cut `j`. Truncating every cut onto the `k'` leading eigenvectors of its left marginal,
for `k' ≥ k₀`, gives an open-boundary matrix product state `Φ` of bond dimension at most `k'`
with `‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.

Source: Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
section "Matrix Product States", lines 505–557. The constraint at each cut is eq. `constraint`
with `P = 1/2` and `k₀ = exp(2S)/2` (eq. `k0Ent`); the tail bound and the error of the matrix
product state follow from it as in the source.

**Stage theorem.** The hypothesis that `k₀ ≥ exp(2 S_j)/2` at every internal cut is not part
of Hastings' statement, where the entropy is bounded by the area law proved earlier in the
paper. `isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy` becomes the source's matrix product
state approximation once that hypothesis is discharged from the area law for the ground
state.

The source's `k₀ = exp(2S)/2` is a real number. Here `k₀` is any natural number at least
`exp(2 S_j)/2` at every cut, such as the ceiling of the largest of these; the constraint at a
cut is applied with this common `k₀`, which only weakens it. The error is the squared norm,
documented in `docs/paper-gaps/hastings07_mps_error_measure.tex`.

**Local fix (constant):** the constant `e^{2/ξ'}` replaces the printed `e^{1/ξ'}`, because the
constraint is available only at even exponents. Documented in
`docs/paper-gaps/hastings07_schmidt_tail_constant.tex`.
-/

open Matrix Real
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw.Hastings

variable {L q : ℕ}

/-- **Matrix product state from the entropy of the cuts (stage theorem).** Under the
approximate factorization of Lemma 1 at every internal cut, if the natural number `k₀`
satisfies `k₀ ≥ exp(2 S_j)/2` for the entropy `S_j` of the first `j` sites at every internal
cut `j`, then for every `k' ≥ k₀` the
truncation `Φ` onto the `k'` leading eigenvectors at every cut is an open-boundary matrix product
state of bond dimension at most `k'` with
`‖Φ - Ω‖² ≤ (L - 1) 4 C₁² e^{2/ξ'} (k'/k₀)^{-1/(ξ' log q)}`.
Hastings, arXiv:0705.2024v4, lines 505–557, with the constant described in the module
docstring. -/
theorem isOpenMPS_norm_sub_sq_le_of_factorization_of_entropy (hq : 1 < q)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) {ξ' C₁ : ℝ} (hξ' : 0 < ξ')
    (hfact : ∀ j ∈ Finset.Ico 1 L, ∀ m : ℕ, j + m ≤ L →
      ∃ (OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (SB SL SR : Finset (Fin L)),
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OB SB ∧ SB ⊆ leftBlock L (j + m) ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OL SL ∧ SL ⊆ leftBlock L j ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) OR SR ∧ Disjoint SR (leftBlock L j) ∧
      ‖OB * OL * OR - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
        C₁ * Real.exp (-(m / ξ')))
    {k₀ : ℕ}
    (hk₀ : ∀ j ∈ Finset.Ico 1 L,
      Real.exp (2 * Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L j) Ω) / 2 ≤
        k₀)
    {k' : ℕ} (hk' : k₀ ≤ k') :
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k)
        Ω).leadingEigenprojection k'
    let Φ := sequentialTruncation P (L - 1) Ω
    IsOpenMPS L q k' (fun x ↦ Φ x) ∧
      ‖Φ - Ω‖ ^ 2 ≤ ((L - 1 : ℕ) : ℝ) *
        (4 * C₁ ^ 2 * exp (2 / ξ') * ((k' : ℝ) / k₀) ^ (-1 / (ξ' * log q))) := by
  intro P Φ
  rcases Nat.lt_or_ge L 2 with hL | hL
  · -- Without an internal cut there is nothing to truncate.
    refine ⟨(isOpenMPS_sequentialTruncation_leadingEigenprojection Ω hΩ k').1, ?_⟩
    have h := norm_sequentialTruncation_leadingEigenprojection_sub_sq_le Ω hΩ k'
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty] at h
    rw [show L - 1 = 0 by omega, Nat.cast_zero, zero_mul]
    exact h
  · have hk₀pos : (0 : ℝ) < k₀ :=
      lt_of_lt_of_le (by positivity) (hk₀ 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩))
    refine isOpenMPS_norm_sub_sq_le_of_schmidtTail_geometric Ω hΩ
      (by exact_mod_cast hq) hξ' (by positivity) hk₀pos ?_ (by exact_mod_cast hk')
    intro j hj m n hn
    exact one_sub_kyFanNorm_le_of_factorization_of_entropy hq.le hΩ j (hfact j hj) (hk₀ j hj)
      m n (by exact_mod_cast hn)

end TNLean.MPS.AreaLaw.Hastings
