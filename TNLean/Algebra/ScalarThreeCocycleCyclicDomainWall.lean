/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicExamples
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant

/-!
# Domain-wall invariants of the cyclic three-cocycles

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section IV.C, `Intequiv`,
`Papers/2405.00439/MPU-DW.tex` lines 2013–2021: the interchange of `o(g) + 1` domain walls
created by `g` multiplies the state by the gauge-invariant phase `∏_{k=1}^{o(g)} ω⁻¹(g, g^k, g)`.
Section IV.D, lines 2038–2067: for the cocycles `ω_j` of `ℤ_n` this phase is
`exp{−(2πi j/n²) a ∑_{k=0}^{o(a)−1} (ka + a − [ka + a])}`, tabulated for `n = 3` and `n = 4`.

**Formalized here.** The phase is the inverse of the cyclic invariant
`ScalarThreeCochain.cyclicInvariant` at `m = o(g)`, hence gauge invariant. For `ω_j` the
printed exponential formula holds, the carry sum equals `o(a) · a`, and the phase is
`exp(−2πi j a² / (n · gcd(n, a)))`. Every entry of the two printed tables is correct. The
cyclic invariant of `ω_j` at the generator is `ζ^j`, so the cocycles `ω_j` with `j` distinct
modulo `n` lie in distinct classes, as line 2040 asserts. Residues are represented in
`{0, …, n − 1}`, the source's convention, and `ka` in the printed sum is the residue of `ka`.

## Main definitions

* `TNLean.Algebra.ScalarThreeCochain.domainWallPhase`: `∏_{k=1}^{o(g)} ω⁻¹(g, g^k, g)`.

## Main results

* `TNLean.Algebra.ScalarThreeCochain.domainWallPhase_eq_inv_cyclicInvariant`,
  `TNLean.Algebra.ScalarThreeCochain.CohomologousTo.domainWallPhase_eq`: gauge invariance.
* `TNLean.Algebra.ScalarThreeCochain.cyclicInvariant_cyclicCocycle`: the cyclic invariant of
  `ω_j` is `ζ^{j a ⌊m a / n⌋}`.
* `TNLean.Algebra.ScalarThreeCochain.domainWallPhase_cyclicCocycle_eq_exp_sum`: the printed
  formula of line 2042.
* `TNLean.Algebra.ScalarThreeCochain.domainWallPhase_cyclicCocycle`,
  `TNLean.Algebra.ScalarThreeCochain.domainWallPhase_cyclicCocycle_eq_exp`: the closed form.
* `TNLean.Algebra.ScalarThreeCochain.domainWallPhase_cyclicCocycle_three`,
  `TNLean.Algebra.ScalarThreeCochain.domainWallPhase_cyclicCocycle_four`: the printed tables.
* `TNLean.Algebra.ScalarThreeCochain.not_cohomologousTo_cyclicCocycle`: distinct classes.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

open Complex

namespace TNLean.Algebra.ScalarThreeCochain

/-! ### The domain-wall phase of a three-cochain -/

section General

variable {G : Type*} [Group G]

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2013–2021 (`Intequiv`).
The phase `∏_{k=1}^{o(g)} ω⁻¹(g, g^k, g)` acquired by interchanging the domain walls created by
`g`. -/
def domainWallPhase (ω : ScalarThreeCochain G) (g : G) : ℂˣ :=
  ∏ k ∈ Finset.Icc 1 (orderOf g), (ω g (g ^ k) g)⁻¹

/-- A product over `1, …, m` equals the product over `0, …, m − 1` when the factors at `0`
and `m` agree. -/
private theorem prod_Icc_one_eq_prod_range {M : Type*} [CommGroup M] (f : ℕ → M) (m : ℕ)
    (h : f m = f 0) : ∏ k ∈ Finset.Icc 1 m, f k = ∏ k ∈ Finset.range m, f k := by
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := rfl
  have h1 := Finset.prod_range_succ f m
  have h2 := Finset.prod_range_succ' f m
  rw [hIcc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  simp only [add_comm 1]
  rw [h] at h1
  exact mul_right_cancel (h2.symm.trans h1)

/-- Bridge: the domain-wall phase is the inverse of the cyclic invariant at `m = o(g)`. -/
theorem domainWallPhase_eq_inv_cyclicInvariant (ω : ScalarThreeCochain G) (g : G) :
    domainWallPhase ω g = (cyclicInvariant ω g (orderOf g))⁻¹ := by
  rw [domainWallPhase, cyclicInvariant, ← Finset.prod_inv_distrib]
  exact prod_Icc_one_eq_prod_range _ _ (by rw [pow_orderOf_eq_one, pow_zero])

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2015: the domain-wall phase
is gauge invariant; cohomologous three-cochains have the same phase. -/
theorem CohomologousTo.domainWallPhase_eq {ω η : ScalarThreeCochain G}
    (h : CohomologousTo ω η) (g : G) : domainWallPhase ω g = domainWallPhase η g := by
  rw [domainWallPhase_eq_inv_cyclicInvariant, domainWallPhase_eq_inv_cyclicInvariant,
    h.cyclicInvariant_eq (pow_orderOf_eq_one g)]

end General

/-! ### The cyclic cocycles -/

variable {n : ℕ} [NeZero n]

/-- The residue of `a^k` is the residue of `k a`. -/
theorem val_toAdd_pow (a : Multiplicative (ZMod n)) (k : ℕ) :
    (Multiplicative.toAdd (a ^ k)).val = k * (Multiplicative.toAdd a).val % n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, toAdd_mul, ZMod.val_add, ih, Nat.mod_add_mod, add_one_mul]

/-- The carries of `k a + a` over `k < m` add up to `⌊m a / n⌋`. -/
theorem sum_carry (A m : ℕ) :
    ∑ k ∈ Finset.range m, (k * A % n + A) / n = m * A / n := by
  have hn := NeZero.pos n
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (m + 1) * A = (m * A % n + A) + n * (m * A / n) := by
      have := Nat.mod_add_div (m * A) n; rw [add_one_mul]; omega
    rw [h1, Nat.add_mul_div_left _ _ hn, add_comm]

/-- Project result: **the cyclic invariant of `ω_j`**,
`∏_{k < m} ω_j(a, a^k, a) = ζ^{j a ⌊m a / n⌋}`, for every `m`. -/
theorem cyclicInvariant_cyclicCocycle (j : ℕ) (a : Multiplicative (ZMod n)) (m : ℕ) :
    (cyclicInvariant (cyclicCocycle n j) a m : ℂ) =
      rootOfUnity n ^ (j * (Multiplicative.toAdd a).val *
        (m * (Multiplicative.toAdd a).val / n)) := by
  rw [cyclicInvariant, Units.coe_prod]
  simp only [cyclicCocycle_val, val_toAdd_pow, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum,
    sum_carry]

/-- The order of `a` in `ℤ_n` is `n / gcd(n, a)`. -/
theorem orderOf_eq_div_gcd (a : Multiplicative (ZMod n)) :
    orderOf a = n / n.gcd (Multiplicative.toAdd a).val := by
  change orderOf (Multiplicative.ofAdd (Multiplicative.toAdd a)) = _
  rw [orderOf_ofAdd_eq_addOrderOf]
  conv_lhs => rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd a)]
  exact ZMod.addOrderOf_coe _ (NeZero.ne n)

/-- Project result: `o(a) · a = n · (a / gcd(n, a))`; in particular `n` divides `o(a) · a`. -/
theorem orderOf_mul_val (a : Multiplicative (ZMod n)) :
    orderOf a * (Multiplicative.toAdd a).val =
      n * ((Multiplicative.toAdd a).val / n.gcd (Multiplicative.toAdd a).val) := by
  rw [orderOf_eq_div_gcd]
  obtain ⟨p, hp⟩ := Nat.gcd_dvd_left n (Multiplicative.toAdd a).val
  obtain ⟨q, hq⟩ := Nat.gcd_dvd_right n (Multiplicative.toAdd a).val
  have hg : 0 < n.gcd (Multiplicative.toAdd a).val := Nat.gcd_pos_of_pos_left _ (NeZero.pos n)
  set g := n.gcd (Multiplicative.toAdd a).val
  set A := (Multiplicative.toAdd a).val
  rw [hp, hq, Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg]
  ring

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2042: **the printed formula**
`∏_{k=1}^{o(a)} ω_j⁻¹(a, a^k, a) = exp{−(2πi j/n²) a ∑_{k=0}^{o(a)−1} (ka + a − [ka + a])}`,
with `ka` the residue of `k a`. -/
theorem domainWallPhase_cyclicCocycle_eq_exp_sum (j : ℕ) (a : Multiplicative (ZMod n)) :
    (domainWallPhase (cyclicCocycle n j) a : ℂ) =
      Complex.exp (-(2 * Real.pi * Complex.I * j / (n : ℂ) ^ 2) *
        (Multiplicative.toAdd a).val *
        ∑ k ∈ Finset.range (orderOf a),
          (((Multiplicative.toAdd (a ^ k)).val + (Multiplicative.toAdd a).val -
            (Multiplicative.toAdd (a ^ k) + Multiplicative.toAdd a).val : ℕ) : ℂ)) := by
  rw [domainWallPhase_eq_inv_cyclicInvariant, cyclicInvariant, ← Finset.prod_inv_distrib,
    Units.coe_prod, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [Units.val_inv_eq_inv_val, cyclicCocycle, Units.val_mk0, ← Complex.exp_neg]
  congr 1
  ring

/-- Project result: the carry sum of line 2042 is
`∑_{k=0}^{o(a)−1} (ka + a − [ka + a]) = o(a) · a`. -/
theorem sum_carry_orderOf (a : Multiplicative (ZMod n)) :
    ∑ k ∈ Finset.range (orderOf a),
        ((Multiplicative.toAdd (a ^ k)).val + (Multiplicative.toAdd a).val -
          (Multiplicative.toAdd (a ^ k) + Multiplicative.toAdd a).val) =
      orderOf a * (Multiplicative.toAdd a).val := by
  have hterm : ∀ k, (Multiplicative.toAdd (a ^ k)).val + (Multiplicative.toAdd a).val -
      (Multiplicative.toAdd (a ^ k) + Multiplicative.toAdd a).val =
      n * ((k * (Multiplicative.toAdd a).val % n + (Multiplicative.toAdd a).val) / n) := by
    intro k
    rw [ZMod.val_add, val_toAdd_pow]
    have := Nat.mod_add_div (k * (Multiplicative.toAdd a).val % n +
      (Multiplicative.toAdd a).val) n
    omega
  simp only [hterm, ← Finset.mul_sum, sum_carry, orderOf_mul_val]
  rw [Nat.mul_div_cancel_left _ (NeZero.pos n)]

/-- Project result: **the closed form of the domain-wall phase of `ω_j`**,
`∏_{k=1}^{o(a)} ω_j⁻¹(a, a^k, a) = ζ^{−j a (a / gcd(n, a))} = exp(−2πi j a² / (n gcd(n, a)))`,
with `ζ = exp(2πi/n)`. -/
theorem domainWallPhase_cyclicCocycle (j : ℕ) (a : Multiplicative (ZMod n)) :
    (domainWallPhase (cyclicCocycle n j) a : ℂ) =
      (rootOfUnity n ^ (j * (Multiplicative.toAdd a).val *
        ((Multiplicative.toAdd a).val / n.gcd (Multiplicative.toAdd a).val)))⁻¹ := by
  rw [domainWallPhase_eq_inv_cyclicInvariant, Units.val_inv_eq_inv_val,
    cyclicInvariant_cyclicCocycle, orderOf_mul_val, Nat.mul_div_cancel_left _ (NeZero.pos n)]

/-- Project result: **the closed form as an exponential**,
`∏_{k=1}^{o(a)} ω_j⁻¹(a, a^k, a) = exp(−2πi j a² / (n gcd(n, a)))`. -/
theorem domainWallPhase_cyclicCocycle_eq_exp (j : ℕ) (a : Multiplicative (ZMod n)) :
    (domainWallPhase (cyclicCocycle n j) a : ℂ) =
      Complex.exp (-(2 * Real.pi * Complex.I * j * ((Multiplicative.toAdd a).val : ℂ) ^ 2 /
        ((n : ℂ) * (n.gcd (Multiplicative.toAdd a).val : ℕ)))) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hg : ((n.gcd (Multiplicative.toAdd a).val : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left _ (NeZero.pos n)).ne'
  rw [domainWallPhase_cyclicCocycle, rootOfUnity, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_div (Nat.gcd_dvd_right _ _) hg]
  field_simp

omit [NeZero n] in
/-- `(ζ^k)⁻¹ = ζ^l` whenever `ζ^n = 1` and `n ∣ k + l`. -/
private theorem inv_pow_eq_pow {ζ : ℂ} {k l : ℕ} (h : ζ ^ n = 1) (hkl : (k + l) % n = 0) :
    (ζ ^ k)⁻¹ = ζ ^ l := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add, pow_eq_pow_mod _ h, hkl, pow_zero]

/-- The primitive cube root `exp(2πi/3)` and its conjugate `exp(−2πi/3) = ζ₃²`. -/
private theorem exp_neg_two_pi_div_three :
    Complex.exp (-(2 * Real.pi / 3) * Complex.I) = rootOfUnity 3 ^ 2 := by
  rw [← inv_pow_eq_pow (n := 3) (k := 1) (rootOfUnity_pow 3) (by norm_num), pow_one,
    rootOfUnity, ← Complex.exp_neg]
  congr 1
  ring

private theorem exp_two_pi_div_three :
    Complex.exp ((2 * Real.pi / 3) * Complex.I) = rootOfUnity 3 ^ 1 := by
  rw [pow_one, rootOfUnity]
  congr 1
  ring

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2046–2054: **the printed
`n = 3` table**, with rows `j = 1, 2` and columns `a = 1, 2`. -/
theorem domainWallPhase_cyclicCocycle_three :
    (domainWallPhase (cyclicCocycle 3 1) (Multiplicative.ofAdd 1) : ℂ) =
        Complex.exp (-(2 * Real.pi / 3) * Complex.I) ∧
      (domainWallPhase (cyclicCocycle 3 1) (Multiplicative.ofAdd 2) : ℂ) =
        Complex.exp (-(2 * Real.pi / 3) * Complex.I) ∧
      (domainWallPhase (cyclicCocycle 3 2) (Multiplicative.ofAdd 1) : ℂ) =
        Complex.exp ((2 * Real.pi / 3) * Complex.I) ∧
      (domainWallPhase (cyclicCocycle 3 2) (Multiplicative.ofAdd 2) : ℂ) =
        Complex.exp ((2 * Real.pi / 3) * Complex.I) := by
  have v1 : (1 : ZMod 3).val = 1 := rfl
  have v2 : (2 : ZMod 3).val = 2 := rfl
  simp only [domainWallPhase_cyclicCocycle, exp_neg_two_pi_div_three, exp_two_pi_div_three,
    toAdd_ofAdd, v1, v2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact inv_pow_eq_pow (rootOfUnity_pow 3) (by norm_num)

/-- `exp(2πi/4) = i`. -/
private theorem rootOfUnity_four : rootOfUnity 4 = Complex.I := by
  rw [rootOfUnity, show (2 * Real.pi * Complex.I / ((4 : ℕ) : ℂ)) = Real.pi / 2 * Complex.I by
    push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2056–2066: **the printed
`n = 4` table**, with rows `j = 1, 2, 3` and columns `a = 1, 2, 3`. -/
theorem domainWallPhase_cyclicCocycle_four :
    (domainWallPhase (cyclicCocycle 4 1) (Multiplicative.ofAdd 1) : ℂ) = -Complex.I ∧
      (domainWallPhase (cyclicCocycle 4 1) (Multiplicative.ofAdd 2) : ℂ) = -1 ∧
      (domainWallPhase (cyclicCocycle 4 1) (Multiplicative.ofAdd 3) : ℂ) = -Complex.I ∧
      (domainWallPhase (cyclicCocycle 4 2) (Multiplicative.ofAdd 1) : ℂ) = -1 ∧
      (domainWallPhase (cyclicCocycle 4 2) (Multiplicative.ofAdd 2) : ℂ) = 1 ∧
      (domainWallPhase (cyclicCocycle 4 2) (Multiplicative.ofAdd 3) : ℂ) = -1 ∧
      (domainWallPhase (cyclicCocycle 4 3) (Multiplicative.ofAdd 1) : ℂ) = Complex.I ∧
      (domainWallPhase (cyclicCocycle 4 3) (Multiplicative.ofAdd 2) : ℂ) = -1 ∧
      (domainWallPhase (cyclicCocycle 4 3) (Multiplicative.ofAdd 3) : ℂ) = Complex.I := by
  have v1 : (1 : ZMod 4).val = 1 := rfl
  have v2 : (2 : ZMod 4).val = 2 := rfl
  have v3 : (3 : ZMod 4).val = 3 := rfl
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  simp only [domainWallPhase_cyclicCocycle, rootOfUnity_four, toAdd_ofAdd, v1, v2, v3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [pow_eq_pow_mod _ h4]
      norm_num [pow_succ, Complex.inv_I]

/-- Project result: the cyclic invariant of `ω_j` at the generator `1` of `ℤ_n`, with
`m = n`, is `ζ^j`. -/
theorem cyclicInvariant_cyclicCocycle_one (hn : 1 < n) (j : ℕ) :
    (cyclicInvariant (cyclicCocycle n j) (Multiplicative.ofAdd 1) n : ℂ) =
      rootOfUnity n ^ j := by
  have h1 : (1 : ZMod n).val = 1 := by
    have : Fact (1 < n) := ⟨hn⟩
    exact ZMod.val_one n
  rw [cyclicInvariant_cyclicCocycle, toAdd_ofAdd, h1, mul_one, mul_one,
    Nat.div_self (NeZero.pos n), mul_one]

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040: **the cocycles `ω_j`
lie in distinct classes**: `ω_j` and `ω_{j'}` are cohomologous only if `j ≡ j' mod n`. -/
theorem not_cohomologousTo_cyclicCocycle (hn : 1 < n) {j j' : ℕ} (h : ¬ j ≡ j' [MOD n]) :
    ¬ CohomologousTo (cyclicCocycle n j) (cyclicCocycle n j') := by
  intro hc
  have heq := congrArg Units.val
    (hc.cyclicInvariant_eq (g := Multiplicative.ofAdd (1 : ZMod n)) (n := n) (by
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero]))
  rw [cyclicInvariant_cyclicCocycle_one hn, cyclicInvariant_cyclicCocycle_one hn] at heq
  have hprim : IsPrimitiveRoot (rootOfUnity n) n :=
    Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  rw [pow_eq_pow_mod j hprim.pow_eq_one, pow_eq_pow_mod j' hprim.pow_eq_one] at heq
  exact h (hprim.pow_inj (Nat.mod_lt _ (NeZero.pos n)) (Nat.mod_lt _ (NeZero.pos n)) heq)

end TNLean.Algebra.ScalarThreeCochain
