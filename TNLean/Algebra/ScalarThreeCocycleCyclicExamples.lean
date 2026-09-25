/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import TNLean.Algebra.ScalarThreeCocycle

/-!
# Explicit scalar three-cocycles on `ℤ_n` and on `ℤ₂ × ℤ₂`

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section IV.D,
`Papers/2405.00439/MPU-DW.tex` line 2040: the three-cocycles
`ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}` of `ℤ_n`, with `[b + c] = b + c mod n`
and `j = 0, …, n − 1`.

**Formalized here.** For every `n` and `j`, `ω_j` is a normalized scalar three-cocycle with
unit-modulus values, and `ω_j(a,b,c) = ζ^{j a ⌊(b + c)/n⌋}` with `ζ = exp(2πi/n)`. The
three-cocycle `(−1)^{a₁ b₂ c₂}` of `ℤ₂ × ℤ₂` is a standard representative that is not
printed in the sources on disk; its cocycle, normalization, and modulus facts are project
results. Residues are represented by their values in `{0, …, n − 1}`, the source's
convention, and the groups are written multiplicatively.

## Main definitions

* `TNLean.Algebra.ScalarThreeCochain.cyclicCocycle`: the cocycles `ω_j` of `ℤ_n`.
* `TNLean.Algebra.ScalarThreeCochain.kleinCocycle`: the cocycle `(−1)^{a₁ b₂ c₂}`.

## Main results

* `TNLean.Algebra.ScalarThreeCochain.cyclicCocycle_isCocycle`,
  `TNLean.Algebra.ScalarThreeCochain.cyclicCocycle_isNormalized`,
  `TNLean.Algebra.ScalarThreeCochain.cyclicCocycle_norm`: `ω_j` is a normalized
  unit-modulus cocycle.
* `TNLean.Algebra.ScalarThreeCochain.kleinCocycle_isCocycle`,
  `TNLean.Algebra.ScalarThreeCochain.kleinCocycle_isNormalized`,
  `TNLean.Algebra.ScalarThreeCochain.kleinCocycle_norm`: the same for `(−1)^{a₁ b₂ c₂}`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

namespace TNLean.Algebra.ScalarThreeCochain

/-! ### The cyclic groups `ℤ_n` -/

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040.
The three-cocycle `ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}` of `ℤ_n`, with
residues represented in `{0, …, n − 1}`. -/
def cyclicCocycle (n j : ℕ) [NeZero n] : ScalarThreeCochain (Multiplicative (ZMod n)) :=
  fun a b c ↦ Units.mk0
    (Complex.exp (2 * Real.pi * Complex.I * j * (Multiplicative.toAdd a).val *
      ((Multiplicative.toAdd b).val + (Multiplicative.toAdd c).val -
        (Multiplicative.toAdd b + Multiplicative.toAdd c).val : ℕ) / (n : ℂ) ^ 2))
    (Complex.exp_ne_zero _)

/-- Project result: the primitive root `exp(2πi/n)`, the base of the values of `ω_j`. -/
def rootOfUnity (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem rootOfUnity_pow (n : ℕ) [NeZero n] : rootOfUnity n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).pow_eq_one

private theorem pow_eq_pow_of_modEq {n A B : ℕ} {ζ : ℂ} (h : ζ ^ n = 1)
    (hAB : A ≡ B [MOD n]) : ζ ^ A = ζ ^ B := by
  rw [pow_eq_pow_mod A h, pow_eq_pow_mod B h, hAB]

/-- Project result: **the value of `ω_j`**, `ω_j(a,b,c) = ζ^{j a ⌊(b + c)/n⌋}` with
`ζ = exp(2πi/n)`, since `b + c − [b + c] = n ⌊(b + c)/n⌋`. -/
theorem cyclicCocycle_val (n j : ℕ) [NeZero n] (a b c : Multiplicative (ZMod n)) :
    (cyclicCocycle n j a b c : ℂ) =
      rootOfUnity n ^ (j * (Multiplicative.toAdd a).val *
        (((Multiplicative.toAdd b).val + (Multiplicative.toAdd c).val) / n)) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hsub : (Multiplicative.toAdd b).val + (Multiplicative.toAdd c).val -
      (Multiplicative.toAdd b + Multiplicative.toAdd c).val =
      n * (((Multiplicative.toAdd b).val + (Multiplicative.toAdd c).val) / n) := by
    rw [ZMod.val_add]
    have := Nat.mod_add_div ((Multiplicative.toAdd b).val + (Multiplicative.toAdd c).val) n
    omega
  rw [cyclicCocycle, Units.val_mk0, hsub, rootOfUnity, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The carry identity `⌊(k+l)/n⌋ + ⌊(h + [k+l])/n⌋ = ⌊(h+k)/n⌋ + ⌊([h+k] + l)/n⌋`: both sides
count the multiples of `n` in `h + k + l`. -/
private theorem carry_add (n h k l : ℕ) (hn : 0 < n) :
    (k + l) / n + (h + (k + l) % n) / n = (h + k) / n + ((h + k) % n + l) / n := by
  have h1 : h + k + l = (h + (k + l) % n) + n * ((k + l) / n) := by
    have := Nat.mod_add_div (k + l) n; omega
  have h2 : h + k + l = ((h + k) % n + l) + n * ((h + k) / n) := by
    have := Nat.mod_add_div (h + k) n; omega
  have e1 := Nat.add_mul_div_left (h + (k + l) % n) ((k + l) / n) hn
  have e2 := Nat.add_mul_div_left ((h + k) % n + l) ((h + k) / n) hn
  rw [← h1] at e1
  rw [← h2] at e2
  omega

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040.
**`ω_j` is a three-cocycle** of `ℤ_n` for every `n` and `j`. -/
theorem cyclicCocycle_isCocycle (n j : ℕ) [NeZero n] : IsCocycle (cyclicCocycle n j) := by
  intro g h k l
  apply Units.ext
  simp only [Units.val_mul, cyclicCocycle_val, ← pow_add, toAdd_mul, ZMod.val_add]
  apply pow_eq_pow_of_modEq (rootOfUnity_pow n)
  set G := (Multiplicative.toAdd g).val
  set H := (Multiplicative.toAdd h).val
  set K := (Multiplicative.toAdd k).val
  set L := (Multiplicative.toAdd l).val
  have hc := carry_add n H K L (NeZero.pos n)
  calc
    j * ((G + H) % n) * ((K + L) / n) + j * G * ((H + (K + L) % n) / n)
        ≡ j * (G + H) * ((K + L) / n) + j * G * ((H + (K + L) % n) / n) [MOD n] :=
      ((Nat.mod_modEq _ _).mul_left _ |>.mul_right _).add_right _
    _ = (j * G * ((K + L) / n) + j * G * ((H + (K + L) % n) / n)) + j * H * ((K + L) / n) := by
      ring
    _ = j * G * ((H + K) / n) + j * G * (((H + K) % n + L) / n) + j * H * ((K + L) / n) := by
      rw [← mul_add, ← mul_add, hc]

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040.
**`ω_j` is normalized**: it equals one whenever an argument is the identity. -/
theorem cyclicCocycle_isNormalized (n j : ℕ) [NeZero n] : IsNormalized (cyclicCocycle n j) := by
  have hlt : ∀ x : ZMod n, x.val < n := fun x ↦ ZMod.val_lt x
  refine ⟨fun h k ↦ ?_, fun g k ↦ ?_, fun g h ↦ ?_⟩ <;> apply Units.ext <;>
    simp only [cyclicCocycle_val, Units.val_one, toAdd_one, ZMod.val_zero, mul_zero,
      zero_mul, pow_zero, zero_add, add_zero]
  · rw [Nat.div_eq_of_lt (hlt _), mul_zero, pow_zero]
  · rw [Nat.div_eq_of_lt (hlt _), mul_zero, pow_zero]

/-- Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 2040.
The values of `ω_j` are phases. -/
theorem cyclicCocycle_norm (n j : ℕ) [NeZero n] (a b c : Multiplicative (ZMod n)) :
    ‖(cyclicCocycle n j a b c : ℂ)‖ = 1 := by
  rw [cyclicCocycle_val, norm_pow,
    Complex.norm_eq_one_of_pow_eq_one (rootOfUnity_pow n) (NeZero.ne n), one_pow]

/-! ### The Klein four-group `ℤ₂ × ℤ₂` -/

/-- The three-cocycle `ω(a,b,c) = (−1)^{a₁ b₂ c₂}` of `ℤ₂ × ℤ₂`.

Source: arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex` line 1848: the type-II component
`ω_II(a b^i, a^j b, a^k b) = −1`, all other values `+1`, which is this formula in the coordinates
`a = (1,0)`, `b = (0,1)`; its class is `(0,0,1)` in the table of lines 1856–1872. -/
def kleinCocycle : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2)) :=
  fun a b c ↦
    (-1) ^ ((Multiplicative.toAdd a).1 * (Multiplicative.toAdd b).2 *
      (Multiplicative.toAdd c).2).val

private theorem neg_one_pow_val_add (x y : ZMod 2) :
    ((-1 : ℂˣ) ^ x.val) * (-1) ^ y.val = (-1) ^ (x + y).val := by
  apply Units.ext
  push_cast
  rw [← pow_add, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two]

/-- Project result: **`(−1)^{a₁ b₂ c₂}` is a three-cocycle**: its exponent is an additive
three-cocycle with values in `ℤ₂`. -/
theorem kleinCocycle_isCocycle : IsCocycle kleinCocycle := by
  intro g h k l
  simp only [kleinCocycle, neg_one_pow_val_add, toAdd_mul, Prod.fst_add, Prod.snd_add]
  congr 2
  ring

/-- Project result: `(−1)^{a₁ b₂ c₂}` is normalized. -/
theorem kleinCocycle_isNormalized : IsNormalized kleinCocycle := by
  refine ⟨fun _ _ ↦ ?_, fun _ _ ↦ ?_, fun _ _ ↦ ?_⟩ <;> simp [kleinCocycle]

/-- Project result: the values of `(−1)^{a₁ b₂ c₂}` are signs. -/
theorem kleinCocycle_norm (a b c : Multiplicative (ZMod 2 × ZMod 2)) :
    ‖(kleinCocycle a b c : ℂ)‖ = 1 := by
  simp [kleinCocycle]

end TNLean.Algebra.ScalarThreeCochain
