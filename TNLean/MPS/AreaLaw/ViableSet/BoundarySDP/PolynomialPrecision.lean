/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.DyadicPrecision

/-!
# Uniform polynomial precision for rounding retained families

Polynomial bounds on the retained cardinality and the effective bond dimension,
together with inverse-polynomial accuracy, give one quadratic bound for the
dyadic precision exponent at every cut. The constant is chosen before the
chain length, cut, and retained family.
-/

namespace TNLean.MPS.AreaLaw

/-- A dyadic constant controls the inverse-polynomial rounding mesh uniformly
over all families satisfying a fixed polynomial cardinality bound. -/
theorem inv_two_pow_le_polynomial_family_rounding_mesh
    {C p a L v r : ℕ} {α : ℝ} (hL : 1 ≤ L) (hα : 0 < α)
    (hv : v ≤ C * L ^ p) (hr : (2 * (C + 1) : ℝ) ≤ α * 2 ^ r) :
    (2 ^ (r + (a + p) * L) : ℝ)⁻¹ ≤ α / (2 * (L : ℝ) ^ a * (v + 1)) := by
  have hLpow : 1 ≤ L ^ p := Nat.one_le_pow p L hL
  have hcard : v + 1 ≤ (C + 1) * L ^ p := by nlinarith
  have hcardreal : (v + 1 : ℝ) ≤ (C + 1) * (L : ℝ) ^ p := by exact_mod_cast hcard
  have hLtwo : (L : ℝ) ≤ (2 : ℝ) ^ L := by
    exact_mod_cast (Nat.lt_two_pow_self (n := L)).le
  have hpow : (L : ℝ) ^ (a + p) ≤ (2 : ℝ) ^ ((a + p) * L) := by
    calc
      (L : ℝ) ^ (a + p) ≤ ((2 : ℝ) ^ L) ^ (a + p) := by gcongr
      _ = _ := by rw [← pow_mul, Nat.mul_comm L]
  have hden : 2 * (L : ℝ) ^ a * (v + 1) ≤ α * 2 ^ (r + (a + p) * L) := by
    calc
      2 * (L : ℝ) ^ a * (v + 1) ≤
          2 * (L : ℝ) ^ a * ((C + 1) * (L : ℝ) ^ p) := by gcongr
      _ = (2 * (C + 1) : ℝ) * (L : ℝ) ^ (a + p) := by rw [pow_add]; ring
      _ ≤ (α * 2 ^ r) * (2 : ℝ) ^ ((a + p) * L) :=
        mul_le_mul hr hpow (by positivity) (by positivity)
      _ = α * 2 ^ (r + (a + p) * L) := by rw [pow_add]; ring
  have hdenpos : 0 < 2 * (L : ℝ) ^ a * (v + 1) := by positivity
  apply (le_div_iff₀ hdenpos).mpr
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (by positivity)).mpr hden

/-- The dimension and accuracy contributions to dyadic precision fit one
quadratic polynomial in the chain length. -/
theorem tensor_precision_expression_le_quadratic (qbit Dbit s r a p L : ℕ) :
    qbit * L + (Dbit + Nat.clog 2 L * s) * (L + 1) + (L + 1) + L +
      (r + (a + p) * L) ≤ (qbit + Dbit + s + 2 + r + a + p) * (L + 1) ^ 2 := by
  have hlog : Nat.clog 2 L ≤ L :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := L)).le
  have hL : L ≤ (L + 1) ^ 2 := by nlinarith
  have hLone : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hprod : L * (L + 1) ≤ (L + 1) ^ 2 := by nlinarith
  have hone : 1 ≤ (L + 1) ^ 2 := by nlinarith
  have hmiddle : (Dbit + Nat.clog 2 L * s) * (L + 1) ≤
      (Dbit + L * s) * (L + 1) := by gcongr
  nlinarith [Nat.mul_le_mul_left qbit hL, Nat.mul_le_mul_left Dbit hLone,
    Nat.mul_le_mul_left s hprod, Nat.mul_le_mul_left r hone,
    Nat.mul_le_mul_left (a + p) hL]

/-- A quadratic precision bound also bounds the common rational parameter
height by a power of two with quadratic exponent. -/
theorem dyadic_height_le_quadratic_of_precision_le
    {t E L : ℕ} (ht : t ≤ E * (L + 1) ^ 2) :
    (2 : ℕ) ^ (2 * t + 5) ≤ 2 ^ ((2 * E + 5) * (L + 1) ^ 2) := by
  have hone : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow 2 (L + 1) (by omega)
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  nlinarith [Nat.mul_le_mul_left 5 hone]

/-- Polynomial cardinality and bond bounds give a uniform quadratic precision
exponent for rational orthonormal-family rounding at accuracy `α / L^a`.
Both the exponent constant and the resulting height bound are fixed before
the length, cut, actual cardinality, and actual bond dimension. -/
theorem exists_tensor_dyadic_precision_quadratic_bound
    (q C p D s a : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ E : ℕ, ∀ (L k v B : ℕ), 1 ≤ L → k ≤ L → v ≤ C * L ^ p → B ≤ D * L ^ s →
      let θ : ℝ := α / (2 * (L : ℝ) ^ a * (v + 1))
      let t := Nat.clog 2 ⌈(q ^ k : ℝ) * (max 1 (max 1 B) : ℝ) ^ (k + 1) *
        (k + 1) * 2 ^ k / θ⌉₊
      t ≤ E * (L + 1) ^ 2 ∧
        (2 : ℕ) ^ (2 * t + 5) ≤ 2 ^ ((2 * E + 5) * (L + 1) ^ 2) := by
  let r := Nat.clog 2 ⌈(2 * (C + 1) : ℝ) / α⌉₊
  let E := Nat.clog 2 q + Nat.clog 2 (D + 1) + s + 2 + r + a + p
  refine ⟨E, fun L k v B hL hk hv hB ↦ ?_⟩
  dsimp only
  have hr : (2 * (C + 1) : ℝ) ≤ α * 2 ^ r := by
    exact (mul_inv_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ r)).mp
      (mul_inv_two_pow_clog_natCeil_le (K := (2 * (C + 1) : ℝ)) hα)
  have hmesh := inv_two_pow_le_polynomial_family_rounding_mesh (a := a) hL hα hv hr
  have hmax : max 1 (max 1 B) ≤ (D + 1) * L ^ s := by
    have hpow : 1 ≤ L ^ s := Nat.one_le_pow s L hL
    apply max_le
    · nlinarith
    · apply max_le <;> nlinarith
  have hprec := tensor_dyadic_precision_le_of_polynomial_bond
    (Nat.le_pow_clog (by norm_num : 1 < 2) q) hmax hk hmesh
  have hquadratic := tensor_precision_expression_le_quadratic
    (Nat.clog 2 q) (Nat.clog 2 (D + 1)) s r a p L
  have ht := hprec.trans hquadratic
  simpa only [Nat.cast_max, Nat.cast_one] using
    And.intro ht (dyadic_height_le_quadratic_of_precision_le ht)

end TNLean.MPS.AreaLaw
