/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Spectral.PhysicalCorrelationBinomial
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Polynomial factors and finite transients in physical correlations

The exact binomial expansion is rewritten as polynomial-times-exponential
terms only at nonzero eigenvalues. The zero-eigenvalue contribution is kept
as a finite transient. Polynomial degrees are strictly below the respective
generalized-eigenspace stabilization indices, the maximal Jordan-block sizes.

## References

- arXiv:2011.12127, Section II.B.3, lines 433–441, with the Jordan correction
  documented in `docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.
-/

open scoped Matrix BigOperators Polynomial

namespace MPSTensor

private noncomputable def correlationJordanPolynomial (μ : ℂ) (c : ℕ → ℂ) (k : ℕ) :
    Polynomial ℂ :=
  ∑ j ∈ Finset.range k,
    ((j.factorial : ℂ)⁻¹ * (μ ^ j)⁻¹ * c j) • descPochhammer ℂ j

private theorem correlationJordanPolynomial_degree (μ : ℂ) (c : ℕ → ℂ) (k : ℕ) :
    (correlationJordanPolynomial μ c k).degree < (k : WithBot ℕ) := by
  apply (Polynomial.degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe k)).2
  intro j hj
  apply (Polynomial.degree_smul_le _ _).trans_lt
  apply Polynomial.degree_le_natDegree.trans_lt
  rw [descPochhammer_natDegree]
  exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hj)

private theorem correlationJordanPolynomial_eval_mul {μ : ℂ} (hμ : μ ≠ 0)
    (c : ℕ → ℂ) (k n : ℕ) :
    (correlationJordanPolynomial μ c k).eval (n : ℂ) * μ ^ n =
      ∑ j ∈ Finset.range k, (n.choose j : ℂ) * μ ^ (n - j) * c j := by
  simp only [correlationJordanPolynomial, Polynomial.eval_finsetSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_smul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  simp only [smul_eq_mul]
  have hjfac : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  by_cases hj : j ≤ n
  · have hpow : μ ^ n = μ ^ (n - j) * μ ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [hpow]
    field_simp [hμ, hjfac]
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)]

private theorem correlation_binomial_to_polynomial
    (s : Finset ℂ) (c : ℂ → ℕ → ℂ) (k : ℂ → ℕ) :
    ∃ p : ℂ → Polynomial ℂ, ∃ t : ℕ → ℂ,
      (∀ μ ∈ s.erase 0, (p μ).degree < (k μ : WithBot ℕ)) ∧
      (∀ n, k 0 ≤ n → t n = 0) ∧ ∀ n,
        (∑ μ ∈ s, ∑ j ∈ Finset.range (k μ),
          (n.choose j : ℂ) * μ ^ (n - j) * c μ j) =
        t n + ∑ μ ∈ s.erase 0, (p μ).eval (n : ℂ) * μ ^ n := by
  classical
  let t : ℕ → ℂ := fun n => if 0 ∈ s then
    ∑ j ∈ Finset.range (k 0), (n.choose j : ℂ) * (0 : ℂ) ^ (n - j) * c 0 j else 0
  refine ⟨fun μ => correlationJordanPolynomial μ (c μ) (k μ), t, ?_, ?_, ?_⟩
  · intro μ _
    exact correlationJordanPolynomial_degree μ (c μ) _
  · intro n hn
    dsimp [t]
    split_ifs
    · apply Finset.sum_eq_zero
      intro j hj
      have hjn : j < n := (Finset.mem_range.mp hj).trans_le hn
      simp [zero_pow (Nat.sub_ne_zero_of_lt hjn)]
    · rfl
  · intro n
    have hp (μ : ℂ) (hμ : μ ∈ s.erase 0) :=
      correlationJordanPolynomial_eval_mul (Finset.ne_of_mem_erase hμ) (c μ) (k μ) n
    simp_rw [Finset.sum_congr rfl hp]
    by_cases hz : 0 ∈ s
    · rw [← Finset.add_sum_erase s _ hz]
      simp [t, hz]
    · simp [t, hz]

/-- A physical connected correlator is a finite sum of polynomial-weighted
nonzero exponentials plus an explicitly retained zero-eigenvalue transient.
The formula holds at every separation, including adjacent observable blocks.
The degree bound uses the actual generalized-eigenspace stabilization index,
not an assumed diagonalization. -/
theorem physicalConnectedCorrelator_exists_jordan_expansion {d D : ℕ}
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : Matrix.trace ρ ≠ 0)
    (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) :
    let T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) := Kraus.transferMap A - fixedPointProj ρ hρ
    ∃ s : Finset ℂ, ∃ p : ℂ → Polynomial ℂ, ∃ t : ℕ → ℂ,
      0 ∉ s ∧ (∀ μ ∈ s, T.HasEigenvalue μ) ∧
      (∀ μ ∈ s, (p μ).degree < (T.maxGenEigenspaceIndex μ : WithBot ℕ)) ∧
      (∀ n, T.maxGenEigenspaceIndex 0 ≤ n → t n = 0) ∧
      ∀ n, physicalConnectedCorrelator A ρ hρ L₁ L₂ X Y n =
        t n + ∑ μ ∈ s, (p μ).eval (n : ℂ) * μ ^ n := by
  classical
  dsimp only
  let T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) := Kraus.transferMap A - fixedPointProj ρ hρ
  obtain ⟨s, c, hs, hsum⟩ :=
    physicalConnectedCorrelator_exists_binomial_expansion A ρ hρ L₁ L₂ X Y
  obtain ⟨p, t, hp, ht, hpt⟩ := correlation_binomial_to_polynomial s c T.maxGenEigenspaceIndex
  refine ⟨s.erase 0, p, t, Finset.notMem_erase _ _, ?_, hp, ht, ?_⟩
  · intro μ hμ
    exact hs μ (Finset.mem_of_mem_erase hμ)
  · intro n
    exact (hsum n).trans (hpt n)

end MPSTensor
