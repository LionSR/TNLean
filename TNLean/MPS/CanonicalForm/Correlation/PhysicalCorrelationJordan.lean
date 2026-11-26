/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RingTheory.Polynomial.Pochhammer
import TNLean.MPS.CanonicalForm.Correlation.DecayingCorrelations
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Polynomial factors and finite transients in physical correlations

The exact binomial expansion is rewritten as polynomial-times-exponential
terms only at nonzero eigenvalues. The zero-eigenvalue contribution is kept
as a finite transient. Polynomial degrees are strictly below the respective
generalized-eigenspace stabilization indices, the maximal Jordan-block sizes.

It also contains the following results.

* `MPSTensor.physicalConnectedCorrelator_exists_binomial_expansion`: all-separation binomial
  expansion of physical correlations.

## References

- arXiv:2011.12127, Section II.B.3, lines 433–441, with the Jordan correction
  documented in `docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.
-/

section PhysicalCorrelationBinomial

/-!
## All-separation binomial expansion of physical correlations

The complementary transfer map is decomposed into generalized eigenspaces
using Mathlib. On each component the commuting binomial formula gives an
exact finite expansion, including at zero separation and zero eigenvalue.
No diagonalizability or assumed spectral expansion is required.

### References

- arXiv:2011.12127, Section II.B.3, lines 433–441.

**Local fix (Jordan factors and nilpotent transients):** The source's
pure-exponential claim needs the all-separation binomial correction; see
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

private theorem transfer_pairing_pow_binomial {D : ℕ}
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ)
    {μ : ℂ} {v : Matrix (Fin D) (Fin D) ℂ} {k : ℕ}
    (hv : ((T - μ • 1) ^ k) v = 0) (n : ℕ) :
    F ((T ^ n) v) = ∑ j ∈ Finset.range k,
      (n.choose j : ℂ) * μ ^ (n - j) * F (((T - μ • 1) ^ j) v) := by
  classical
  let N := T - μ • 1
  have hcomm : Commute N (μ • 1) := (Algebra.commutes μ N).symm
  have hbin : F ((T ^ n) v) = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℂ) * μ ^ (n - j) * F ((N ^ j) v) := by
    conv_lhs => rw [show T = N + μ • 1 by simp [N], hcomm.add_pow n]
    simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply,
      Module.End.natCast_apply, smul_pow, one_pow, LinearMap.smul_apply,
      Module.End.one_apply, map_smul, map_nsmul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  rw [hbin]
  rcases le_total k (n + 1) with hk | hk
  · symm
    apply Finset.sum_subset (Finset.range_mono hk)
    intro j _ hj
    have hkj : k ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    have hzero : (N ^ j) v = 0 := Module.End.pow_map_zero_of_le hkj hv
    change (n.choose j : ℂ) * μ ^ (n - j) * F ((N ^ j) v) = 0
    rw [hzero, map_zero, mul_zero]
  · apply Finset.sum_subset (Finset.range_mono hk)
    intro j _ hj
    have hnj : n < j := by
      simp only [Finset.mem_range] at hj
      omega
    simp [Nat.choose_eq_zero_of_lt hnj]

private theorem transfer_pairing_exists_binomial {D : ℕ}
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ) (Z : Matrix (Fin D) (Fin D) ℂ) :
    ∃ s : Finset ℂ, ∃ c : ℂ → ℕ → ℂ,
      (∀ μ ∈ s, T.HasEigenvalue μ) ∧ ∀ n : ℕ,
        F ((T ^ n) Z) = ∑ μ ∈ s, ∑ j ∈ Finset.range (T.maxGenEigenspaceIndex μ),
          (n.choose j : ℂ) * μ ^ (n - j) * c μ j := by
  classical
  have hZ : Z ∈ ⨆ μ : ℂ, T.maxGenEigenspace μ := by
    rw [T.iSup_maxGenEigenspace_eq_top]
    trivial
  obtain ⟨v, hv, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hZ
  have hnil (μ : ℂ) : ((T - μ • 1) ^ T.maxGenEigenspaceIndex μ) (v μ) = 0 := by
    have h := hv μ
    rw [T.maxGenEigenspace_eq] at h
    simpa only [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker,
      Algebra.algebraMap_eq_smul_one] using h
  refine ⟨v.support, fun μ j => F (((T - μ • 1) ^ j) (v μ)), ?_, ?_⟩
  · intro μ hμ
    apply Module.End.hasEigenvalue_of_hasGenEigenvalue
      (k := T.maxGenEigenspaceIndex μ)
    rw [Module.End.hasGenEigenvalue_iff]
    intro hbot
    have h := hv μ
    rw [T.maxGenEigenspace_eq, hbot, Submodule.mem_bot] at h
    exact (Finsupp.mem_support_iff.mp hμ) h
  · intro n
    rw [← hsum, map_finsuppSum, map_finsuppSum]
    apply Finset.sum_congr rfl
    intro μ _
    exact transfer_pairing_pow_binomial T F (hnil μ) n

/-- Every centered physical connected correlator has an exact finite binomial
spectral expansion at every separation. The cutoff is the generalized-eigenspace
stabilization index of the actual complementary transfer map; zero eigenvalues
are retained rather than discarded.

Source: arXiv:2011.12127, Section II.B.3, source lines 433–441.
The Jordan correction is documented in
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`. -/
theorem physicalConnectedCorrelator_exists_binomial_expansion {d D : ℕ}
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : Matrix.trace ρ ≠ 0)
    (L₁ L₂ : ℕ) (X : Matrix (Cfg d L₁) (Cfg d L₁) ℂ)
    (Y : Matrix (Cfg d L₂) (Cfg d L₂) ℂ) :
    let T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) := Kraus.transferMap A - fixedPointProj ρ hρ
    ∃ s : Finset ℂ, ∃ c : ℂ → ℕ → ℂ,
      (∀ μ ∈ s, T.HasEigenvalue μ) ∧
      ∀ n : ℕ, physicalConnectedCorrelator A ρ hρ L₁ L₂ X Y n =
        ∑ μ ∈ s, ∑ j ∈ Finset.range (T.maxGenEigenspaceIndex μ),
          (n.choose j : ℂ) * μ ^ (n - j) * c μ j := by
  exact transfer_pairing_exists_binomial
    (Kraus.transferMap A - fixedPointProj ρ hρ)
    ((Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (physicalObservableTransfer A L₁ X))
    (physicalObservableTransfer A L₂ Y ρ -
      fixedPointProj ρ hρ (physicalObservableTransfer A L₂ Y ρ))

end MPSTensor

end PhysicalCorrelationBinomial

section PhysicalCorrelationJordan

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
not an assumed diagonalization.

Source: arXiv:2011.12127, Section II.B.3, source lines 433–441.
The Jordan correction is documented in
`docs/paper-gaps/cpgsv21_correlator_diagonalizable_expansion.tex`. -/
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

end PhysicalCorrelationJordan
