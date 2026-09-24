/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import TNLean.Algebra.ScalarThreeCocycleCyclicTwoExamples
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.CZXUnitary
import TNLean.MPS.MPU.GroupCocycleMPO

/-!
# Group matrix product operators from a three-cocycle: cyclic and Klein instances

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563), subsubsection "Periodic
boundary condition case", `Papers/2203.12563/REsubmission.tex` line 2224: for the nontrivial
three-cocycle of `ℤ₂` the periodic operator is `U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`; line 2070:
`W_g = CZ (1 ⊗ Z)` and `L_g = X`. Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section IV.C,
`Papers/2405.00439/MPU-DW.tex` line 2040: the three-cocycles
`ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}` of `ℤ_n`, with `[b + c] = b + c mod n`.

**Formalized here.** The periodic operators of the construction in `GroupCocycleMPO` for
three groups: for `ℤ₂` with the cocycle `ω(g,g,g) = −1`, the operator of the generator
equals `∏ CZ_{i,i+1} Z_i ∏ X_i` as a matrix, and the gate is `W_g = CZ (1 ⊗ Z)`; for `ℤ_n`
with `ω_j`, the functions `ω_j` are normalized unit-modulus three-cocycles for every `n` and
`j`, so the construction satisfies the operator laws of a matrix product unitary
representation, with an explicit kernel; for `ℤ₂ × ℤ₂` with `ω(a,b,c) = (−1)^{a₁ b₂ c₂}`
the same holds. The last cocycle is a standard representative, not taken from the sources on
disk.

Residues are represented by their values in `{0, …, n − 1}`, the source's convention.
The groups are written multiplicatively as `Multiplicative (ZMod n)`. The kernels of the
periodic operators are derived from the contraction `mpo_tensor_apply`; the sources do not
print them.

## Main definitions

* `MPOTensor.GroupCocycle.czxDecorated`: the operator `∏ CZ_{i,i+1} Z_i ∏ X_i`.
* `MPOTensor.GroupCocycle.cyclicCocycle`: the cocycles `ω_j` of `ℤ_n`.
* `MPOTensor.GroupCocycle.kleinCocycle`: the cocycle `(−1)^{a₁ b₂ c₂}` of `ℤ₂ × ℤ₂`.

## Main results

* `MPOTensor.GroupCocycle.wGate_cyclicTwo`: `W_g = CZ (1 ⊗ Z)` for the generator of `ℤ₂`.
* `MPOTensor.GroupCocycle.mpo_tensor_cyclicTwo`: `U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`.
* `MPOTensor.GroupCocycle.cyclicCocycle_isCocycle`,
  `MPOTensor.GroupCocycle.cyclicCocycle_isNormalized`,
  `MPOTensor.GroupCocycle.cyclicCocycle_norm`: `ω_j` is a normalized unit-modulus cocycle.
* `MPOTensor.GroupCocycle.mpo_tensor_cyclic_apply`, `MPOTensor.GroupCocycle.cyclic_operator_laws`:
  the kernel and the operator laws for `ℤ_n` and `ω_j`.
* `MPOTensor.GroupCocycle.kleinCocycle_isCocycle`,
  `MPOTensor.GroupCocycle.mpo_tensor_klein_apply`: the `ℤ₂ × ℤ₂` instance.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

open scoped BigOperators Matrix

namespace MPOTensor.GroupCocycle

open TNLean.Algebra TNLean.Algebra.ScalarThreeCochain

/-! ### The group `ℤ₂` -/

local notation "s₂" => (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))

/-- The identification of `ℤ₂` with the qubit basis `Fin 2`. -/
def bitEquiv : Multiplicative (ZMod 2) ≃ Fin 2 := Multiplicative.toAdd

/-- The gate value of the generator on the bit pair `(k,l)` is the sign of `CZ (1 ⊗ Z)`,
`(−1)^{kl + l}`. -/
private theorem cyclicTwo_site (k l : Fin 2) :
    (cyclicTwoCocycle 1 s₂ (bitEquiv.symm l) ((bitEquiv.symm l)⁻¹ * bitEquiv.symm k) : ℂ) =
      (-1) ^ (k.val * l.val) * (-1) ^ l.val := by
  unfold cyclicTwoCocycle
  fin_cases k <;> fin_cases l <;> split_ifs with h <;>
    first | (exfalso; revert h; decide) | simp

/-- **`W_g = CZ (1 ⊗ Z)`** for the generator of `ℤ₂` and the cocycle `ω(g,g,g) = −1`.

Source: arXiv:2203.12563, line 2070. -/
theorem wGate_cyclicTwo :
    wGate (cyclicTwoCocycle 1) s₂ =
      Matrix.diagonal fun kl : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ↦
        (-1 : ℂ) ^ ((bitEquiv kl.1).val * (bitEquiv kl.2).val) * (-1) ^ (bitEquiv kl.2).val := by
  rw [wGate]
  congr 1
  funext kl
  simpa using cyclicTwo_site (bitEquiv kl.1) (bitEquiv kl.2)

/-- The operator `∏ CZ_{i,i+1} Z_i ∏ X_i` on a periodic chain of `N` qubits: all spins are
flipped by `CZXCompression.spinFlip`, then each controlled-`Z` and each `Z` contributes its
sign on the flipped configuration `s`. Its entry at `(s, t)` is
`(−1)^{∑ s_i s_{i+1} + ∑ s_i}` when `s` is the flip of `t`, and zero otherwise. Without the
factors `Z_i` this is the operator `CZXCompression.mpo_czxTensor` of the undecorated CZX
tensor, whose sign is taken on the input configuration instead.

Source: arXiv:2203.12563, line 2224. -/
def czxDecorated (N : ℕ) [NeZero N] : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  Matrix.monomial (CZXCompression.spinFlip N) fun t ↦
    (-1 : ℂ) ^ (CZXCompression.czExponent (CZXCompression.spinFlip N t) +
      ∑ i, (CZXCompression.spinFlip N t i).val)

/-- On the flipped pair, the gate sign `(−1)^{kl + l}` of the input bits equals the sign
`(−1)^{(rev k)(rev l) + rev k}` of the flipped bits. -/
private theorem site_rev (k l : Fin 2) :
    (-1 : ℂ) ^ (k.val * l.val) * (-1) ^ l.val =
      (-1) ^ (k.rev.val * l.rev.val) * (-1) ^ k.rev.val := by
  fin_cases k <;> fin_cases l <;> simp [Fin.rev]

/-- **For the nontrivial three-cocycle of `ℤ₂`, `U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`** on every
nonempty periodic chain.

Source: arXiv:2203.12563, line 2224. -/
theorem mpo_tensor_cyclicTwo (N : ℕ) [NeZero N] :
    mpo (tensor bitEquiv (cyclicTwoCocycle 1) s₂) N = czxDecorated N := by
  ext s t
  have hshift : shift bitEquiv s₂ N t = CZXCompression.spinFlip N t := by
    funext i
    rw [shift_apply, CZXCompression.spinFlip_apply]
    generalize t i = a
    revert a
    decide
  rw [mpo_tensor_apply, czxDecorated, Matrix.monomial_apply, hshift]
  split_ifs with hs
  · simp only [CZXCompression.czExponent, CZXCompression.spinFlip_apply, cyclicTwo_site,
      site_rev, Finset.prod_mul_distrib, pow_add, Finset.prod_pow_eq_pow_sum]
  · rfl

/-! ### The cyclic groups `ℤ_n` -/

/-- The three-cocycle `ω_j(a,b,c) = exp{2πi j a (b + c − [b + c]) / n²}` of `ℤ_n`, with
residues represented in `{0, …, n − 1}`.

Source: arXiv:2405.00439, line 2040. -/
def cyclicCocycle (n j : ℕ) [NeZero n] : ScalarThreeCochain (Multiplicative (ZMod n)) :=
  fun a b c ↦ Units.mk0
    (Complex.exp (2 * Real.pi * Complex.I * j * (Multiplicative.toAdd a).val *
      ((Multiplicative.toAdd b).val + (Multiplicative.toAdd c).val -
        (Multiplicative.toAdd b + Multiplicative.toAdd c).val : ℕ) / (n : ℂ) ^ 2))
    (Complex.exp_ne_zero _)

/-- The primitive root `exp(2πi/n)`. -/
def rootOfUnity (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem rootOfUnity_pow (n : ℕ) [NeZero n] : rootOfUnity n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).pow_eq_one

private theorem pow_eq_pow_of_modEq {n A B : ℕ} {ζ : ℂ} (h : ζ ^ n = 1)
    (hAB : A ≡ B [MOD n]) : ζ ^ A = ζ ^ B := by
  rw [pow_eq_pow_mod A h, pow_eq_pow_mod B h, hAB]

/-- **The value of `ω_j`**: `ω_j(a,b,c) = ζ^{j a ⌊(b + c)/n⌋}` with `ζ = exp(2πi/n)`, since
`b + c − [b + c] = n ⌊(b + c)/n⌋`. -/
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

/-- **`ω_j` is a three-cocycle** of `ℤ_n` for every `n` and `j`.

Source: arXiv:2405.00439, line 2040. -/
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

/-- **`ω_j` is normalized**: it equals one whenever an argument is the identity. -/
theorem cyclicCocycle_isNormalized (n j : ℕ) [NeZero n] : IsNormalized (cyclicCocycle n j) := by
  have hlt : ∀ x : ZMod n, x.val < n := fun x ↦ ZMod.val_lt x
  refine ⟨fun h k ↦ ?_, fun g k ↦ ?_, fun g h ↦ ?_⟩ <;> apply Units.ext <;>
    simp only [cyclicCocycle_val, Units.val_one, toAdd_one, ZMod.val_zero, mul_zero,
      zero_mul, pow_zero, zero_add, add_zero]
  · rw [Nat.div_eq_of_lt (hlt _), mul_zero, pow_zero]
  · rw [Nat.div_eq_of_lt (hlt _), mul_zero, pow_zero]

/-- The values of `ω_j` are phases. -/
theorem cyclicCocycle_norm (n j : ℕ) [NeZero n] (a b c : Multiplicative (ZMod n)) :
    ‖(cyclicCocycle n j a b c : ℂ)‖ = 1 := by
  rw [cyclicCocycle_val, norm_pow,
    Complex.norm_eq_one_of_pow_eq_one (rootOfUnity_pow n) (NeZero.ne n), one_pow]

/-- The identification of `ℤ_{m+1}` with `Fin (m+1)`. -/
def residueEquiv (m : ℕ) : Multiplicative (ZMod (m + 1)) ≃ Fin (m + 1) := Multiplicative.toAdd

/-- **The periodic operator of `ω_j` on `ℤ_{m+1}`**: the entry at `(s, t)` vanishes unless
`s_i = g + t_i` at every site, and then equals `∏_i ζ^{j g ⌊(t_{i+1} + [t_i − t_{i+1}])/n⌋}`
with `n = m + 1` and `ζ = exp(2πi/n)`.

Source: arXiv:2203.12563, lines 2204–2222; arXiv:2405.00439, line 2040. The kernel is
derived from `mpo_tensor_apply`; the sources do not print it. -/
theorem mpo_tensor_cyclic_apply (m j : ℕ) (g : Multiplicative (ZMod (m + 1)))
    {N : ℕ} [NeZero N] (s t : Fin N → Fin (m + 1)) :
    mpo (tensor (residueEquiv m) (cyclicCocycle (m + 1) j) g) N s t =
      if s = fun i ↦ residueEquiv m g + t i then
        ∏ i, rootOfUnity (m + 1) ^ (j * (residueEquiv m g).val *
          (((t (i + 1)).val + (t i - t (i + 1)).val) / (m + 1)))
      else 0 := by
  rw [mpo_tensor_apply]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [cyclicCocycle_val, toAdd_mul, toAdd_inv, neg_add_eq_sub]
  rfl

/-- The four operator laws for `ℤ_n` with the cocycle `ω_j`, for every `n = m + 1` and `j`.

Source: arXiv:2203.12563, lines 2204–2222; arXiv:2405.00439, lines 1684 and 2040. -/
theorem cyclic_operator_laws (m j : ℕ) :
    (∀ g, IsMPUPos ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor g)) ∧
      (∀ N, 0 < N → mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor 1) N = 1) ∧
      (∀ g h N, 0 < N →
        mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor g) N *
            mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor h) N =
          mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor (g * h)) N) ∧
      (∀ g N, 0 < N → (mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor g) N)ᴴ =
          mpo ((family (residueEquiv m) (cyclicCocycle (m + 1) j)).tensor g⁻¹) N) :=
  family_operator_laws (residueEquiv m) (cyclicCocycle_isCocycle (m + 1) j)
    (cyclicCocycle_isNormalized (m + 1) j) (cyclicCocycle_norm (m + 1) j)

/-! ### The Klein four-group `ℤ₂ × ℤ₂` -/

/-- The three-cocycle `ω(a,b,c) = (−1)^{a₁ b₂ c₂}` of `ℤ₂ × ℤ₂`. -/
def kleinCocycle : ScalarThreeCochain (Multiplicative (ZMod 2 × ZMod 2)) :=
  fun a b c ↦
    (-1) ^ ((Multiplicative.toAdd a).1 * (Multiplicative.toAdd b).2 *
      (Multiplicative.toAdd c).2).val

private theorem neg_one_pow_val_add (x y : ZMod 2) :
    ((-1 : ℂˣ) ^ x.val) * (-1) ^ y.val = (-1) ^ (x + y).val := by
  apply Units.ext
  push_cast
  rw [← pow_add, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two]

/-- **`(−1)^{a₁ b₂ c₂}` is a three-cocycle**: its exponent is an additive three-cocycle
with values in `ℤ₂`. -/
theorem kleinCocycle_isCocycle : IsCocycle kleinCocycle := by
  intro g h k l
  simp only [kleinCocycle, neg_one_pow_val_add, toAdd_mul, Prod.fst_add, Prod.snd_add]
  congr 2
  ring

/-- `(−1)^{a₁ b₂ c₂}` is normalized. -/
theorem kleinCocycle_isNormalized : IsNormalized kleinCocycle := by
  refine ⟨fun _ _ ↦ ?_, fun _ _ ↦ ?_, fun _ _ ↦ ?_⟩ <;> simp [kleinCocycle]

/-- The values of `(−1)^{a₁ b₂ c₂}` are signs. -/
theorem kleinCocycle_norm (a b c : Multiplicative (ZMod 2 × ZMod 2)) :
    ‖(kleinCocycle a b c : ℂ)‖ = 1 := by
  simp [kleinCocycle]

/-- The identification of `ℤ₂ × ℤ₂` with `Fin 4`. -/
def kleinEquiv : Multiplicative (ZMod 2 × ZMod 2) ≃ Fin 4 :=
  Multiplicative.toAdd.trans (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)

/-- **The periodic operator of `(−1)^{a₁ b₂ c₂}`**: writing `x_i ∈ ℤ₂ × ℤ₂` for the
configuration `t`, the entry at `(s, t)` vanishes unless `s` is the shift of `t` by `g`, and
then equals `(−1)^{∑_i g₁ x_{i+1,2} (x_{i,2} − x_{i+1,2})}`.

Source: arXiv:2203.12563, lines 2204–2222. The kernel is derived from `mpo_tensor_apply`; the
sources do not print it. -/
theorem mpo_tensor_klein_apply (g : Multiplicative (ZMod 2 × ZMod 2)) {N : ℕ} [NeZero N]
    (s t : Fin N → Fin 4) :
    mpo (tensor kleinEquiv kleinCocycle g) N s t =
      if s = shift kleinEquiv g N t then
        ∏ i, (-1 : ℂ) ^ ((Multiplicative.toAdd g).1 *
          (Multiplicative.toAdd (kleinEquiv.symm (t (i + 1)))).2 *
            ((Multiplicative.toAdd (kleinEquiv.symm (t i))).2 -
              (Multiplicative.toAdd (kleinEquiv.symm (t (i + 1)))).2)).val
      else 0 := by
  rw [mpo_tensor_apply]
  congr 1
  simp only [kleinCocycle, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, toAdd_mul,
    toAdd_inv, neg_add_eq_sub, Prod.snd_sub]

/-- The four operator laws for the `ℤ₂ × ℤ₂` instance. -/
theorem klein_operator_laws :
    (∀ g, IsMPUPos ((family kleinEquiv kleinCocycle).tensor g)) ∧
      (∀ N, 0 < N → mpo ((family kleinEquiv kleinCocycle).tensor 1) N = 1) ∧
      (∀ g h N, 0 < N →
        mpo ((family kleinEquiv kleinCocycle).tensor g) N *
            mpo ((family kleinEquiv kleinCocycle).tensor h) N =
          mpo ((family kleinEquiv kleinCocycle).tensor (g * h)) N) ∧
      (∀ g N, 0 < N → (mpo ((family kleinEquiv kleinCocycle).tensor g) N)ᴴ =
          mpo ((family kleinEquiv kleinCocycle).tensor g⁻¹) N) :=
  family_operator_laws kleinEquiv kleinCocycle_isCocycle kleinCocycle_isNormalized
    kleinCocycle_norm

end MPOTensor.GroupCocycle
