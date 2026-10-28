/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TraceExpFiniteJensen
import TNLean.Algebra.BernsteinExponentialBound
import QICLean.Analysis.TraceExponentialPerturbation

/-!
# Finite uniform Hermitian Bernstein inequality

For independent uniform samples of a centered Hermitian matrix family, the upper
spectral tail satisfies the Bernstein bound with the variance norm and coefficient
`1/3`. A larger upper bound for the variance norm may be used as well. The proof
includes zero variance, zero threshold and zero sample count, with Lean's convention
that division by zero is zero.

**Scope restriction (finite uniform Hermitian samples):** These results are finite
uniform specializations supporting the matrix Bernstein theorem used by LVV,
arXiv:1307.5143v1, Theorem 2.13. Tropp's general probability formulation and the
non-Hermitian norm bound remain separate results. The precise scope and extension
plan are recorded in `docs/paper-gaps/finite_uniform_matrix_bernstein.tex`.

The proof follows Tropp, *User-friendly tail bounds for sums of random matrices*,
Corollary 3.3, Lemma 3.4, Proposition 3.1 and Theorem 6.1(ii):
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

open Classical in
/-- Finite uniform trace-exponential estimate for independent Hermitian samples.
This combines Tropp, Lemma 3.4, with the Bernstein exponential majorant. -/
theorem average_trace_exp_sum_le_bernstein
    {α n : Type*} [Fintype α] [Nonempty α] [Fintype n] [DecidableEq n] [Nonempty n]
    (Z : α → Matrix n n ℂ) (hZ : ∀ a, (Z a).IsHermitian)
    (hmean : ∑ a, Z a = 0) {R θ : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3) (hnorm : ∀ a, ‖Z a‖ ≤ R) (m : ℕ) :
    (Fintype.card α : ℝ)⁻¹ ^ m *
        (∑ σ : Fin m → α, (NormedSpace.exp (θ • ∑ j, Z (σ j))).trace.re) ≤
      (Fintype.card n : ℝ) * Real.exp
        ((m : ℝ) * (θ ^ 2 / (2 * (1 - θ * R / 3))) *
          ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, Z a ^ 2‖) := by
  classical
  let c : ℝ := θ ^ 2 / (2 * (1 - θ * R / 3))
  let M : Matrix n n ℂ := (Fintype.card α : ℝ)⁻¹ •
    ∑ a, NormedSpace.exp (θ • Z a)
  let V : Matrix n n ℂ := (Fintype.card α : ℝ)⁻¹ • ∑ a, Z a ^ 2
  have hj := sum_trace_exp_iid_le (fun a ↦ θ • Z a)
    (fun a ↦ (hZ a).smul (IsSelfAdjoint.all θ)) m isHermitian_zero
  have hi := mul_le_mul_of_nonneg_left hj
    (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card α))) m)
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfirst : (Fintype.card α : ℝ)⁻¹ ^ m *
      (∑ σ : Fin m → α, (NormedSpace.exp (θ • ∑ j, Z (σ j))).trace.re) ≤
      (NormedSpace.exp ((m : ℝ) • CFC.log M)).trace.re := by
    simpa only [zero_add, Finset.smul_sum, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hα, one_pow, one_mul, M, Finset.smul_sum] using hi
  have hlog : CFC.log M ≤ (c * ‖V‖) • (1 : Matrix n n ℂ) :=
    log_average_exp_le_bernstein Z hZ hmean hR hθ hθR hnorm
  have hbound : (m : ℝ) • CFC.log M ≤
      ((m : ℝ) * c * ‖V‖) • (1 : Matrix n n ℂ) := by
    have ht : (m : ℝ) • CFC.log M ≤
        (m : ℝ) • ((c * ‖V‖) • (1 : Matrix n n ℂ)) :=
      smul_le_smul_of_nonneg_left hlog (Nat.cast_nonneg m)
    simpa only [smul_smul, mul_assoc] using ht
  have htrace := (IsSelfAdjoint.log.isHermitian.smul (IsSelfAdjoint.all (m : ℝ))).re_trace_exp_le
    (isHermitian_one.smul (IsSelfAdjoint.all ((m : ℝ) * c * ‖V‖))) hbound
  refine hfirst.trans (htrace.trans_eq ?_)
  rw [← zero_add (((m : ℝ) * c * ‖V‖) • (1 : Matrix n n ℂ)), exp_add_smul_one]
  simp only [NormedSpace.exp_zero, trace_smul, trace_one, Complex.real_smul,
    Complex.re_ofReal_mul, Complex.natCast_re]
  exact mul_comm _ _

end Matrix

namespace Matrix

private theorem exp_le_trace_exp_of_spectrum
    {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℂ} (hS : S.IsHermitian) {x τ θ : ℝ}
    (hx : x ∈ spectrum ℝ S) (hτ : τ ≤ x) (hθ : 0 ≤ θ) :
    Real.exp (θ * τ) ≤ (NormedSpace.exp (θ • S)).trace.re := by
  obtain ⟨i, rfl⟩ := hS.spectrum_real_eq_range_eigenvalues ▸ hx
  have heq : (NormedSpace.exp (θ • S)).trace.re =
      ∑ j, Real.exp (θ * hS.eigenvalues j) := by
    rw [← CFC.real_exp_eq_normedSpace_exp ((hS.smul (IsSelfAdjoint.all θ)).isSelfAdjoint),
      ← cfc_comp_const_mul θ Real.exp S (ha := hS.isSelfAdjoint), hS.cfc_eq]
    exact hS.trace_cfc_eq_sum_re (fun x ↦ Real.exp (θ * x))
  rw [heq]
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ hθ)).trans
    (Finset.single_le_sum (f := fun j ↦ Real.exp (θ * hS.eigenvalues j))
      (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i))

open Classical in
/-- Finite uniform exponential Markov bound for the upper spectral tail.
This is the finite counterpart of Tropp, Proposition 3.1, with an explicit variance bound. -/
theorem finite_uniform_spectral_tail_bound
    {α n : Type*} [Fintype α] [Nonempty α] [Fintype n] [DecidableEq n] [Nonempty n]
    (Z : α → Matrix n n ℂ) (hZ : ∀ a, (Z a).IsHermitian)
    (hmean : ∑ a, Z a = 0) {R θ τ σ2 : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3) (hnorm : ∀ a, ‖Z a‖ ≤ R)
    (hvariance : ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, Z a ^ 2‖ ≤ σ2) (m : ℕ) :
    ((Finset.univ.filter fun σ : Fin m → α ↦
        ∃ x ∈ spectrum ℝ (∑ j, Z (σ j)), τ ≤ x).card : ℝ) /
        (Fintype.card (Fin m → α) : ℝ) ≤
      (Fintype.card n : ℝ) * Real.exp
        (-θ * τ + (m : ℝ) * (θ ^ 2 / (2 * (1 - θ * R / 3))) *
          σ2) := by
  classical
  let bad : Finset (Fin m → α) := Finset.univ.filter fun σ ↦
    ∃ x ∈ spectrum ℝ (∑ j, Z (σ j)), τ ≤ x
  have hsum (σ : Fin m → α) : (∑ j, Z (σ j)).IsHermitian :=
    (isSelfAdjoint_sum Finset.univ fun j _ ↦ (hZ (σ j)).isSelfAdjoint).isHermitian
  have hmarkov : (bad.card : ℝ) * Real.exp (θ * τ) ≤
      ∑ σ : Fin m → α, (NormedSpace.exp (θ • ∑ j, Z (σ j))).trace.re := by
    calc
      _ = ∑ _σ ∈ bad, Real.exp (θ * τ) := by simp
      _ ≤ ∑ σ ∈ bad, (NormedSpace.exp (θ • ∑ j, Z (σ j))).trace.re := by
        apply Finset.sum_le_sum
        intro σ hσ
        obtain ⟨x, hx, hτ⟩ := (Finset.mem_filter.mp hσ).2
        exact exp_le_trace_exp_of_spectrum (hsum σ) hx hτ hθ
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun σ _ _ ↦ ((hsum σ).smul (IsSelfAdjoint.all θ)).re_trace_exp_nonneg)
  have hm := average_trace_exp_sum_le_bernstein Z hZ hmean hR hθ hθR hnorm m
  have hcoef : 0 ≤ (m : ℝ) * (θ ^ 2 / (2 * (1 - θ * R / 3))) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hmcap := hm.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvariance hcoef)) (Nat.cast_nonneg _))
  have hcard : (Fintype.card (Fin m → α) : ℝ) = (Fintype.card α : ℝ) ^ m := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hfrac : (bad.card : ℝ) / (Fintype.card (Fin m → α) : ℝ) * Real.exp (θ * τ) ≤
      (Fintype.card n : ℝ) * Real.exp
        ((m : ℝ) * (θ ^ 2 / (2 * (1 - θ * R / 3))) *
          σ2) := by
    calc
      _ ≤ (∑ σ : Fin m → α, (NormedSpace.exp (θ • ∑ j, Z (σ j))).trace.re) /
          (Fintype.card (Fin m → α) : ℝ) := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right hmarkov (Nat.cast_nonneg _)
      _ ≤ _ := by simpa only [hcard, div_eq_inv_mul, inv_pow] using hmcap
  have hq := (le_div_iff₀ (Real.exp_pos (θ * τ))).mpr hfrac
  calc
    _ ≤ _ := hq
    _ = _ := by rw [Real.exp_add, neg_mul, Real.exp_neg]; ring

end Matrix

namespace Real

private theorem bernstein_parameter {v R τ : ℝ} (hv : 0 < v) (hR : 0 ≤ R) (hτ : 0 ≤ τ) :
    0 ≤ τ / (v + R * τ / 3) ∧ τ / (v + R * τ / 3) * R < 3 ∧
      -(τ / (v + R * τ / 3)) * τ +
        ((τ / (v + R * τ / 3)) ^ 2 / (2 * (1 - τ / (v + R * τ / 3) * R / 3))) * v =
      -(τ ^ 2) / (2 * v + 2 * R * τ / 3) := by
  have hden : 0 < v + R * τ / 3 := by positivity
  have hsmall : τ / (v + R * τ / 3) * R < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  refine ⟨div_nonneg hτ hden.le, hsmall, ?_⟩
  have hone : 1 - τ / (v + R * τ / 3) * R / 3 ≠ 0 := by linarith
  have hd2 : 2 * v + 2 * R * τ / 3 ≠ 0 := by positivity
  field_simp
  ring

end Real

namespace Matrix

open Classical in
/-- The upper spectral Bernstein bound for finite independent uniform Hermitian samples.
This is the finite uniform, norm-bounded specialization of Tropp, Theorem 6.1(ii).
The variance norm may be replaced by any larger real number. -/
theorem finite_uniform_hermitian_bernstein_of_variance_le
    {α n : Type*} [Fintype α] [Nonempty α] [Fintype n] [DecidableEq n] [Nonempty n]
    (Z : α → Matrix n n ℂ) (hZ : ∀ a, (Z a).IsHermitian)
    (hmean : ∑ a, Z a = 0) {R τ σ2 : ℝ}
    (hR : 0 ≤ R) (hτ : 0 ≤ τ) (hnorm : ∀ a, ‖Z a‖ ≤ R)
    (hvariance : ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, Z a ^ 2‖ ≤ σ2) (m : ℕ) :
    ((Finset.univ.filter fun σ : Fin m → α ↦
        ∃ x ∈ spectrum ℝ (∑ j, Z (σ j)), τ ≤ x).card : ℝ) /
        (Fintype.card (Fin m → α) : ℝ) ≤
      (Fintype.card n : ℝ) * Real.exp
        (-(τ ^ 2) / (2 * (m : ℝ) * σ2 +
          2 * R * τ / 3)) := by
  classical
  let v : ℝ := (m : ℝ) * σ2
  have hσ : 0 ≤ σ2 := (norm_nonneg _).trans hvariance
  have hv : 0 ≤ v := mul_nonneg (Nat.cast_nonneg _) hσ
  by_cases hvp : 0 < v
  · obtain ⟨hθ, hθR, hid⟩ := Real.bernstein_parameter hvp hR hτ
    have ht := finite_uniform_spectral_tail_bound (τ := τ) Z hZ hmean hR hθ hθR hnorm hvariance m
    have heq : -(τ / (v + R * τ / 3)) * τ +
        (m : ℝ) * ((τ / (v + R * τ / 3)) ^ 2 /
          (2 * (1 - τ / (v + R * τ / 3) * R / 3))) *
            σ2 =
        -(τ ^ 2) / (2 * (m : ℝ) * σ2 +
          2 * R * τ / 3) := by
      convert hid using 1 <;> dsimp [v] <;> ring
    simpa only [heq] using ht
  · have hv0 : v = 0 := le_antisymm (le_of_not_gt hvp) hv
    by_cases hrt : 0 < R * τ
    · have hRp : 0 < R := by nlinarith
      have hτp : 0 < τ := by nlinarith
      have hθ : 0 ≤ 3 / (2 * R) := by positivity
      have hθR : 3 / (2 * R) * R < 3 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * R)]
        linarith
      have ht := finite_uniform_spectral_tail_bound (τ := τ) Z hZ hmean hR hθ hθR hnorm hvariance m
      have hm0 : (m : ℝ) * σ2 = 0 := hv0
      have heq : -(3 / (2 * R)) * τ +
          (m : ℝ) * ((3 / (2 * R)) ^ 2 / (2 * (1 - 3 / (2 * R) * R / 3))) *
            σ2 =
          -(τ ^ 2) / (2 * (m : ℝ) * σ2 +
            2 * R * τ / 3) := by
        have hzero : (m : ℝ) * ((3 / (2 * R)) ^ 2 /
            (2 * (1 - 3 / (2 * R) * R / 3))) *
            σ2 = 0 := by
          calc
            _ = ((3 / (2 * R)) ^ 2 / (2 * (1 - 3 / (2 * R) * R / 3))) *
                ((m : ℝ) * σ2) := by ring
            _ = 0 := by rw [hm0, mul_zero]
        rw [hzero, add_zero, mul_assoc 2, hm0, mul_zero, zero_add]
        field_simp
      simpa only [heq] using ht
    · have hrt0 : R * τ = 0 := le_antisymm (le_of_not_gt hrt) (mul_nonneg hR hτ)
      have hden : 2 * (m : ℝ) * σ2 +
          2 * R * τ / 3 = 0 := by
        rw [mul_assoc 2, show (m : ℝ) * σ2 = 0 from hv0,
          mul_zero, mul_assoc 2, hrt0]
        norm_num
      rw [hden, div_zero, Real.exp_zero, mul_one]
      have hc : (0 : ℝ) < Fintype.card (Fin m → α) := by exact_mod_cast Fintype.card_pos
      calc
        _ ≤ 1 := (div_le_one hc).mpr (by exact_mod_cast Finset.card_filter_le _ _)
        _ ≤ _ := by exact_mod_cast Fintype.card_pos (α := n)

end Matrix
