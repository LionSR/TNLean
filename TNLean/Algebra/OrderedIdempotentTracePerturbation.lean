/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IdempotentTracePerturbation

/-!
# Ordered products near an idempotent, with quadratic trace error

The second-order trace estimate for powers extends to an ordered product of different
factors. The same idempotent compresses the perturbation of each factor to zero. Uniform
bounds on the three complementary blocks give the same scalar recurrence as in the
constant-factor case. No commutation between distinct factors is assumed.

These are project results for the unequal-block preparation estimate associated with
arXiv:2307.01696, Supplemental Material, proof of Lemma 1 and
extension to non-normal tensors, Lemma 1' (i), eq. `fid_err_gen_normal`. The source gives a
first-order
bound; the quadratic rate uses the cancellation of the compressed perturbations.
-/

namespace IsIdempotentElem

variable {R : Type*} [NormedRing R] {e : R}

private def perturbedProduct (e : R) (Z : ℕ → R) (M : ℕ) : R :=
  ((List.range M).map fun j => e + Z j).prod

private def complementProduct (e : R) (Z : ℕ → R) (M : ℕ) : R :=
  ((List.range M).map fun j => (1 - e) * Z j * (1 - e)).prod

private theorem perturbedProduct_zero (Z : ℕ → R) : perturbedProduct e Z 0 = 1 := rfl

private theorem complementProduct_zero (Z : ℕ → R) : complementProduct e Z 0 = 1 := rfl

private theorem perturbedProduct_succ (Z : ℕ → R) (M : ℕ) :
    perturbedProduct e Z (M + 1) = perturbedProduct e Z M * (e + Z M) := by
  simp only [perturbedProduct, List.range_succ, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]

private theorem complementProduct_succ (Z : ℕ → R) (M : ℕ) :
    complementProduct e Z (M + 1) =
      complementProduct e Z M * ((1 - e) * Z M * (1 - e)) := by
  simp only [complementProduct, List.range_succ, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]

private theorem product_mul_self (he : IsIdempotentElem e) (Z : ℕ → R)
    (hZ : ∀ j, e * Z j * e = 0) (P : R) (M : ℕ) :
    P * perturbedProduct e Z (M + 1) * e =
      P * perturbedProduct e Z M * e +
        P * perturbedProduct e Z M * (1 - e) * ((1 - e) * Z M * e) := by
  rw [perturbedProduct_succ, ← mul_assoc P]
  simpa only [Nat.zero_add, pow_one, pow_zero, mul_one] using
    mul_add_pow_succ_mul_self he (hZ M) (P * perturbedProduct e Z M) 0

private theorem product_mul_one_sub (he : IsIdempotentElem e) (Z : ℕ → R)
    (P : R) (M : ℕ) :
    P * perturbedProduct e Z (M + 1) * (1 - e) =
      P * perturbedProduct e Z M * e * (e * Z M * (1 - e)) +
        P * perturbedProduct e Z M * (1 - e) * ((1 - e) * Z M * (1 - e)) := by
  rw [perturbedProduct_succ, ← mul_assoc P]
  simpa only [Nat.zero_add, pow_one, pow_zero, mul_one] using
    mul_add_pow_succ_mul_one_sub (Z := Z M) he (P * perturbedProduct e Z M) 0

private theorem norm_complementProduct_le (Z : ℕ → R) {ζ : ℝ}
    (hζ : ∀ j, ‖(1 - e) * Z j * (1 - e)‖ ≤ ζ) (M : ℕ) :
    ‖(1 - e) * complementProduct e Z M‖ ≤ ‖1 - e‖ * ζ ^ M := by
  induction M with
  | zero => simp only [complementProduct_zero, mul_one, pow_zero, le_refl]
  | succ M ih =>
    have hζ0 : 0 ≤ ζ := (norm_nonneg _).trans (hζ M)
    rw [complementProduct_succ, ← mul_assoc]
    calc ‖(1 - e) * complementProduct e Z M * ((1 - e) * Z M * (1 - e))‖
        ≤ ‖(1 - e) * complementProduct e Z M‖ * ‖(1 - e) * Z M * (1 - e)‖ :=
          norm_mul_le _ _
      _ ≤ ‖1 - e‖ * ζ ^ M * ζ := mul_le_mul ih (hζ M) (norm_nonneg _) (by positivity)
      _ = ‖1 - e‖ * ζ ^ (M + 1) := by ring

private theorem norm_self_mul_product_le (he : IsIdempotentElem e) (Z : ℕ → R)
    (hZ : ∀ j, e * Z j * e = 0) {β β' ζ : ℝ}
    (hβ : ∀ j, ‖(1 - e) * Z j * e‖ ≤ β) (hβ' : ∀ j, ‖e * Z j * (1 - e)‖ ≤ β')
    (hζ : ∀ j, ‖(1 - e) * Z j * (1 - e)‖ ≤ ζ) (hζ1 : ζ < 1) (M : ℕ) :
    ‖e * perturbedProduct e Z M * e - e‖ ≤ ‖e‖ * ((1 + β * β' / (1 - ζ)) ^ M - 1) ∧
      ‖e * perturbedProduct e Z M * (1 - e)‖ ≤ ‖e‖ * β' / (1 - ζ) * (1 + β * β' / (1 - ζ)) ^ M := by
  have hee : e * e = e := he
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0)
  have hβ'0 : 0 ≤ β' := (norm_nonneg _).trans (hβ' 0)
  have hζ0 : 0 ≤ ζ := (norm_nonneg _).trans (hζ 0)
  have h1ζ : 0 < 1 - ζ := by linarith
  set k := β * β' / (1 - ζ) with hk
  have hk0 : 0 ≤ k := by positivity
  set t := ‖e‖
  have ht : 0 ≤ t := norm_nonneg _
  induction M with
  | zero =>
    simp only [perturbedProduct_zero, pow_zero, mul_one, hee, sub_self, norm_zero,
      mul_zero, le_refl, true_and]
    rw [mul_sub, mul_one, hee, sub_self, norm_zero]
    positivity
  | succ M ih =>
    obtain ⟨ihx, ihy⟩ := ih
    set x := e * perturbedProduct e Z M * e
    set y := e * perturbedProduct e Z M * (1 - e)
    have hρ1 : 1 ≤ 1 + k := by linarith
    have hpow : 1 ≤ (1 + k) ^ M := one_le_pow₀ hρ1
    have hx : ‖x‖ ≤ t * (1 + k) ^ M := by
      calc ‖x‖ = ‖(x - e) + e‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - e‖ + t := norm_add_le _ _
        _ ≤ t * ((1 + k) ^ M - 1) + t := by gcongr
        _ = t * (1 + k) ^ M := by ring
    constructor
    · rw [product_mul_self he Z hZ, add_sub_right_comm]
      calc ‖x - e + y * ((1 - e) * Z M * e)‖
          ≤ ‖x - e‖ + ‖y‖ * β :=
            (norm_add_le _ _).trans (add_le_add le_rfl ((norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_left (hβ M) (norm_nonneg _))))
        _ ≤ t * ((1 + k) ^ M - 1) + t * β' / (1 - ζ) * (1 + k) ^ M * β := by gcongr
        _ = t * ((1 + k) ^ (M + 1) - 1) := by
            rw [hk, pow_succ]; field_simp; ring
    · rw [product_mul_one_sub he Z]
      calc ‖x * (e * Z M * (1 - e)) + y * ((1 - e) * Z M * (1 - e))‖
          ≤ ‖x‖ * β' + ‖y‖ * ζ :=
            (norm_add_le _ _).trans (add_le_add
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hβ' M) (norm_nonneg _)))
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hζ M) (norm_nonneg _))))
        _ ≤ t * (1 + k) ^ M * β' + t * β' / (1 - ζ) * (1 + k) ^ M * ζ := by gcongr
        _ = t * β' / (1 - ζ) * (1 + k) ^ M := by field_simp; ring
        _ ≤ t * β' / (1 - ζ) * (1 + k) ^ (M + 1) := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hρ1)
              (by positivity)

private theorem norm_one_sub_mul_product_le (he : IsIdempotentElem e) (Z : ℕ → R)
    (hZ : ∀ j, e * Z j * e = 0)
    {β β' ζ : ℝ} (hβ : ∀ j, ‖(1 - e) * Z j * e‖ ≤ β) (hβ' : ∀ j, ‖e * Z j * (1 - e)‖ ≤ β')
    (hζ : ∀ j, ‖(1 - e) * Z j * (1 - e)‖ ≤ ζ) (hζ1 : ζ < 1) (M : ℕ) :
    ‖(1 - e) * perturbedProduct e Z M * e‖ ≤
        ‖1 - e‖ * β / (1 - ζ) * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M) ∧
      ‖(1 - e) * perturbedProduct e Z M * (1 - e) - (1 - e) * complementProduct e Z M‖ ≤
        ‖1 - e‖ * β * β' / (1 - ζ) ^ 2 * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M) := by
  have hee : e * e = e := he
  have hff : (1 - e) * (1 - e) = 1 - e := he.one_sub
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0)
  have hβ'0 : 0 ≤ β' := (norm_nonneg _).trans (hβ' 0)
  have hζ0 : 0 ≤ ζ := (norm_nonneg _).trans (hζ 0)
  have h1ζ : 0 < 1 - ζ := by linarith
  set k := β * β' / (1 - ζ) with hk
  set s := ‖1 - e‖
  have hs : 0 ≤ s := norm_nonneg _
  induction M with
  | zero =>
    simp only [perturbedProduct_zero, complementProduct_zero, pow_zero, mul_one, sub_self,
      mul_zero, hff, norm_zero, le_refl, and_true]
    rw [sub_mul, one_mul, hee, sub_self, norm_zero]
  | succ M ih =>
    obtain ⟨ihx, ihy⟩ := ih
    set W := (1 - e) * Z M * (1 - e)
    set x := (1 - e) * perturbedProduct e Z M * e
    set y := (1 - e) * perturbedProduct e Z M * (1 - e)
    have hfW : ‖(1 - e) * complementProduct e Z M‖ ≤ s * ζ ^ M := norm_complementProduct_le Z hζ M
    constructor
    · rw [product_mul_self he Z hZ]
      have e1 : x + y * ((1 - e) * Z M * e) =
          x + (y - (1 - e) * complementProduct e Z M) * ((1 - e) * Z M * e) +
            (1 - e) * complementProduct e Z M * ((1 - e) * Z M * e) := by
        noncomm_ring
      rw [e1]
      calc ‖x + (y - (1 - e) * complementProduct e Z M) * ((1 - e) * Z M * e) +
          (1 - e) * complementProduct e Z M * ((1 - e) * Z M * e)‖
          ≤ ‖x‖ + ‖y - (1 - e) * complementProduct e Z M‖ * β +
            ‖(1 - e) * complementProduct e Z M‖ * β := by
            refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
              (add_le_add le_rfl ?_)) ?_) <;>
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hβ M) (norm_nonneg _))
        _ ≤ s * β / (1 - ζ) * ((1 + k) ^ M - ζ ^ M) +
              s * β * β' / (1 - ζ) ^ 2 * ((1 + k) ^ M - ζ ^ M) * β + s * ζ ^ M * β := by
            gcongr
        _ ≤ s * β / (1 - ζ) * ((1 + k) ^ (M + 1) - ζ ^ (M + 1)) := by
            have e2 : s * β / (1 - ζ) * ((1 + k) ^ (M + 1) - ζ ^ (M + 1)) -
                (s * β / (1 - ζ) * ((1 + k) ^ M - ζ ^ M) +
                  s * β * β' / (1 - ζ) ^ 2 * ((1 + k) ^ M - ζ ^ M) * β + s * ζ ^ M * β) =
                s * β * β' / (1 - ζ) ^ 2 * β * ζ ^ M := by
              rw [hk, pow_succ, pow_succ]; field_simp; ring
            have : 0 ≤ s * β * β' / (1 - ζ) ^ 2 * β * ζ ^ M := by positivity
            linarith
    · rw [product_mul_one_sub he Z]
      have e1 : x * (e * Z M * (1 - e)) + y * W - (1 - e) * complementProduct e Z (M + 1) =
          x * (e * Z M * (1 - e)) + (y - (1 - e) * complementProduct e Z M) * W := by
        rw [complementProduct_succ]
        dsimp only [W]
        noncomm_ring
      rw [e1]
      calc ‖x * (e * Z M * (1 - e)) + (y - (1 - e) * complementProduct e Z M) * W‖
          ≤ ‖x‖ * β' + ‖y - (1 - e) * complementProduct e Z M‖ * ζ :=
            (norm_add_le _ _).trans (add_le_add
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hβ' M) (norm_nonneg _)))
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hζ M) (norm_nonneg _))))
        _ ≤ s * β / (1 - ζ) * ((1 + k) ^ M - ζ ^ M) * β' +
              s * β * β' / (1 - ζ) ^ 2 * ((1 + k) ^ M - ζ ^ M) * ζ := by gcongr
        _ ≤ s * β * β' / (1 - ζ) ^ 2 * ((1 + k) ^ (M + 1) - ζ ^ (M + 1)) := by
            have e2 : s * β * β' / (1 - ζ) ^ 2 * ((1 + k) ^ (M + 1) - ζ ^ (M + 1)) -
                (s * β / (1 - ζ) * ((1 + k) ^ M - ζ ^ M) * β' +
                  s * β * β' / (1 - ζ) ^ 2 * ((1 + k) ^ M - ζ ^ M) * ζ) =
                s * β * β' / (1 - ζ) ^ 2 * k * (1 + k) ^ M +
                  s * β / (1 - ζ) * β' * ζ ^ M := by
              have key : ∀ P Q : ℝ,
                  s * β * β' / (1 - ζ) ^ 2 * (P * (1 + k) - Q * ζ) -
                    (s * β / (1 - ζ) * (P - Q) * β' + s * β * β' / (1 - ζ) ^ 2 * (P - Q) * ζ) =
                  s * β * β' / (1 - ζ) ^ 2 * k * P + s * β / (1 - ζ) * β' * Q := by
                intro P Q; rw [hk]; field_simp; ring
              rw [pow_succ, pow_succ]
              exact key _ _
            have : 0 ≤ s * β * β' / (1 - ζ) ^ 2 * k * (1 + k) ^ M +
                s * β / (1 - ζ) * β' * ζ ^ M := by positivity
            linarith

private theorem norm_trace_product_add_sub_le (he : IsIdempotentElem e) (Z : ℕ → R)
    (hZ : ∀ j, e * Z j * e = 0)
    {tr : R →+ ℂ} (htr : ∀ x y, tr (x * y) = tr (y * x)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖tr x‖ ≤ K * ‖x‖) {β β' ζ : ℝ}
    (hβ : ∀ j, ‖(1 - e) * Z j * e‖ ≤ β) (hβ' : ∀ j, ‖e * Z j * (1 - e)‖ ≤ β')
    (hζ : ∀ j, ‖(1 - e) * Z j * (1 - e)‖ ≤ ζ) (hζ1 : ζ < 1) (M : ℕ) :
    ‖tr (perturbedProduct e Z M) - tr e‖ ≤
      K * (‖e‖ * ((1 + β * β' / (1 - ζ)) ^ M - 1) +
        ‖1 - e‖ * (β * β' / (1 - ζ) ^ 2 * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M) + ζ ^ M)) := by
  obtain ⟨hx, -⟩ := norm_self_mul_product_le he Z hZ hβ hβ' hζ hζ1 M
  obtain ⟨-, hy⟩ := norm_one_sub_mul_product_le he Z hZ hβ hβ' hζ hζ1 M
  have hW := norm_complementProduct_le Z hζ M
  have hsplit : tr (perturbedProduct e Z M) - tr e =
      tr (e * perturbedProduct e Z M * e - e) +
        tr ((1 - e) * perturbedProduct e Z M * (1 - e) -
          (1 - e) * complementProduct e Z M) +
        tr ((1 - e) * complementProduct e Z M) := by
    rw [trace_eq_add htr he (perturbedProduct e Z M), map_sub, map_sub]
    ring
  rw [hsplit]
  refine (norm_add₃_le).trans ?_
  have e1 := hK (e * perturbedProduct e Z M * e - e)
  have e2 := hK ((1 - e) * perturbedProduct e Z M * (1 - e) - (1 - e) * complementProduct e Z M)
  have e3 := hK ((1 - e) * complementProduct e Z M)
  have : K * ‖e * perturbedProduct e Z M * e - e‖ +
      K * ‖(1 - e) * perturbedProduct e Z M * (1 - e) -
        (1 - e) * complementProduct e Z M‖ + K * ‖(1 - e) * complementProduct e Z M‖ ≤
      K * (‖e‖ * ((1 + β * β' / (1 - ζ)) ^ M - 1)) +
        K * (‖1 - e‖ * β * β' / (1 - ζ) ^ 2 * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M)) +
          K * (‖1 - e‖ * ζ ^ M) := by
    gcongr
  have e4 : K * (‖e‖ * ((1 + β * β' / (1 - ζ)) ^ M - 1)) +
      K * (‖1 - e‖ * β * β' / (1 - ζ) ^ 2 * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M)) +
        K * (‖1 - e‖ * ζ ^ M) =
      K * (‖e‖ * ((1 + β * β' / (1 - ζ)) ^ M - 1) +
        ‖1 - e‖ * (β * β' / (1 - ζ) ^ 2 * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M) + ζ ^ M)) := by
    ring
  linarith

/-- The trace of an ordered product of canceled perturbations has quadratic error.
For `f = 1 - e`, every factor satisfies `e Z_j e = 0`, and the three complementary blocks
are bounded by `z ≤ 1/2`. For `M ≥ 2` the bound is
`K (‖e‖ + 3‖f‖) (2 M z²) exp(2 M z²)`, without any commutation between the factors.

Project extension of the idempotent perturbation estimate to the unequal-block construction
in arXiv:2307.01696, Supplemental Material, proof of Lemma 1 and
extension to non-normal tensors, Lemma 1' (i), eq. `fid_err_gen_normal`. -/
theorem norm_trace_prod_add_sub_le_of_le (he : IsIdempotentElem e) (Z : ℕ → R)
    (hZ : ∀ j, e * Z j * e = 0)
    {tr : R →+ ℂ} (htr : ∀ x y, tr (x * y) = tr (y * x)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖tr x‖ ≤ K * ‖x‖) {z : ℝ}
    (h₁ : ∀ j, ‖(1 - e) * Z j * e‖ ≤ z) (h₂ : ∀ j, ‖e * Z j * (1 - e)‖ ≤ z)
    (h₃ : ∀ j, ‖(1 - e) * Z j * (1 - e)‖ ≤ z) (hz : z ≤ 1 / 2) {M : ℕ} (hM : 2 ≤ M) :
    ‖tr (((List.range M).map fun j => e + Z j).prod) - tr e‖ ≤
      K * (‖e‖ + 3 * ‖1 - e‖) * (M * (2 * z ^ 2)) * Real.exp (M * (2 * z ^ 2)) := by
  have hz0 : 0 ≤ z := (norm_nonneg _).trans (h₁ 0)
  have h1z : 1 / 2 ≤ 1 - z := by linarith
  have hk : z * z / (1 - z) ≤ 2 * z ^ 2 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hk0 : 0 ≤ z * z / (1 - z) := div_nonneg (by positivity) (by linarith)
  have hB : z * z / (1 - z) ^ 2 ≤ 4 * z ^ 2 := by
    have h14 : 1 / 4 ≤ (1 - z) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h14 (sq_nonneg z)]
  set y := (M : ℝ) * (2 * z ^ 2)
  have hy : 0 ≤ y := by positivity
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hρ : (1 + z * z / (1 - z)) ^ M ≤ (1 + 2 * z ^ 2) ^ M := by gcongr
  have hρexp : (1 + 2 * z ^ 2) ^ M ≤ Real.exp y := by
    calc (1 + 2 * z ^ 2) ^ M ≤ Real.exp (2 * z ^ 2) ^ M := by
          gcongr; linarith [Real.add_one_le_exp (2 * z ^ 2)]
      _ = Real.exp y := (Real.exp_nat_mul _ M).symm
  have hρ1 := one_add_pow_sub_one_le_mul_exp (by positivity : 0 ≤ 2 * z ^ 2) M
  have hzM : z ^ M ≤ z ^ 2 := pow_le_pow_of_le_one hz0 (by linarith) hM
  have hexp1 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have hmain := norm_trace_product_add_sub_le he Z hZ htr hK0 hK h₁ h₂ h₃ (by linarith) M
  refine hmain.trans ?_
  have hpow0 : 0 ≤ z ^ M := pow_nonneg hz0 M
  have ha : ‖e‖ * ((1 + z * z / (1 - z)) ^ M - 1) ≤ ‖e‖ * (y * Real.exp y) := by
    gcongr; linarith
  have hb : z * z / (1 - z) ^ 2 * ((1 + z * z / (1 - z)) ^ M - z ^ M) ≤ 2 * (y * Real.exp y) := by
    calc z * z / (1 - z) ^ 2 * ((1 + z * z / (1 - z)) ^ M - z ^ M)
        ≤ 4 * z ^ 2 * ((1 + z * z / (1 - z)) ^ M - z ^ M) := by
          refine mul_le_mul_of_nonneg_right hB (sub_nonneg.2 ?_)
          exact pow_le_pow_left₀ hz0 (by linarith) M
      _ ≤ 4 * z ^ 2 * Real.exp y := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
      _ ≤ 2 * (y * Real.exp y) := by
          have : 4 * z ^ 2 ≤ 2 * y := by simp only [y]; nlinarith
          nlinarith [Real.exp_pos y]
  have hc : z ^ M ≤ y * Real.exp y := by
    have : z ^ 2 ≤ y := by simp only [y]; nlinarith
    nlinarith [Real.exp_pos y]
  have hfin : ‖e‖ * ((1 + z * z / (1 - z)) ^ M - 1) +
      ‖1 - e‖ * (z * z / (1 - z) ^ 2 * ((1 + z * z / (1 - z)) ^ M - z ^ M) + z ^ M) ≤
      (‖e‖ + 3 * ‖1 - e‖) * (y * Real.exp y) := by
    have := mul_le_mul_of_nonneg_left (add_le_add hb hc) (norm_nonneg (1 - e))
    nlinarith
  calc K * (‖e‖ * ((1 + z * z / (1 - z)) ^ M - 1) +
        ‖1 - e‖ * (z * z / (1 - z) ^ 2 * ((1 + z * z / (1 - z)) ^ M - z ^ M) + z ^ M))
      ≤ K * ((‖e‖ + 3 * ‖1 - e‖) * (y * Real.exp y)) := by gcongr
    _ = K * (‖e‖ + 3 * ‖1 - e‖) * y * Real.exp y := by ring

private theorem norm_scalarProduct_le_one (α : ℕ → ℂ) (hα : ∀ j, ‖α j‖ ≤ 1) (M : ℕ) :
    ‖((List.range M).map α).prod‖ ≤ 1 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_singleton, List.prod_singleton, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hα M) (norm_nonneg _)).trans (by simpa using ih)

private theorem product_smul {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (α : ℕ → ℂ) (Y : ℕ → A) (M : ℕ) :
    ((List.range M).map fun j => α j • Y j).prod =
      ((List.range M).map α).prod • ((List.range M).map Y).prod := by
  induction M with
  | zero => simp
  | succ M ih =>
    simp only [List.range_succ, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, ih, smul_mul_smul_comm]

/-- Ordered factors with a common scalar compression have quadratic trace error.
Let `e` be idempotent with `tr e = 1`. For each factor `T_j`, suppose
`e T_j e = α_j e`, `‖T_j - e‖ ≤ δ`, `‖α_j‖ ≤ 1`, and `‖1 - α_j‖ ≤ δ²`.
There is a constant `C > 0`, depending only on `e` and the trace bound, such that for `M ≥ 2`
and `C M δ² < 1`, the ordered trace error is at most `C M δ² exp(C M δ²)`.

This project result supplies the unequal-block extension of the second-order preparation
estimate; compare arXiv:2307.01696, Supplemental Material, proof of Lemma 1 and
extension to non-normal tensors, Lemma 1' (i), eq. `fid_err_gen_normal`. The compression
hypotheses are proved from the positive polar factors in that application. The restriction
`M ≥ 2` is necessary for a general trace estimate: a single complementary block can
contribute to first order. -/
theorem exists_norm_trace_prod_sub_one_le_sq {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    {e : A} (he : IsIdempotentElem e) {tr : A →ₗ[ℂ] ℂ}
    (htr : ∀ x y, tr (x * y) = tr (y * x)) (he1 : tr e = 1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖tr x‖ ≤ K * ‖x‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℕ → A) (α : ℕ → ℂ) (δ : ℝ) (M : ℕ), 2 ≤ M →
      (∀ j, e * T j * e = α j • e) → (∀ j, ‖T j - e‖ ≤ δ) →
      (∀ j, ‖α j‖ ≤ 1) → (∀ j, ‖1 - α j‖ ≤ δ ^ 2) → C * (M * δ ^ 2) < 1 →
      ‖tr ((List.range M).map T).prod - 1‖ ≤
        C * (M * δ ^ 2) * Real.exp (C * (M * δ ^ 2)) := by
  set c₅ := ‖e‖ + ‖1 - e‖
  set c₄ := 2 * (1 + ‖e‖)
  set zc := c₅ ^ 4 * c₄ ^ 2
  set E₀ := K * (‖e‖ + 3 * ‖1 - e‖)
  have hzc : 0 ≤ zc := by positivity
  have hE₀ : 0 ≤ E₀ := by positivity
  set C := 4 + 4 * zc + 2 * E₀ * zc
  have hC0 : 0 ≤ 2 * E₀ * zc := by positivity
  refine ⟨C, by positivity, fun T α δ M hM2 heT hT hα1 hα hsmall => ?_⟩
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hT 0)
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  set y := (M : ℝ) * δ ^ 2 with hydef
  have hy0 : 0 ≤ y := by positivity
  have hδy : δ ^ 2 ≤ y := le_mul_of_one_le_left (sq_nonneg _) hM
  have hy4 : 4 * y < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by
    simp only [C]; linarith) hy0) hsmall
  have hδ1 : δ ≤ 1 := by nlinarith
  have hα0 : ∀ j, 3 / 4 ≤ ‖α j‖ := fun j => by
    have h := norm_sub_norm_le (1 : ℂ) (α j)
    rw [norm_one] at h
    nlinarith [hα j]
  have hαne : ∀ j, α j ≠ 0 := fun j => by
    intro h
    have := hα0 j
    rw [h, norm_zero] at this
    norm_num at this
  set Z : ℕ → A := fun j => (α j)⁻¹ • T j - e with hZdef
  have hZ : ∀ j, e * Z j * e = 0 := fun j => by
    rw [hZdef, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, heT, smul_smul,
      inv_mul_cancel₀ (hαne j), one_smul, he.eq, he.eq, sub_self]
  have hTZ : ∀ j, T j = α j • (e + Z j) := fun j => by
    rw [hZdef, add_sub_cancel, smul_smul, mul_inv_cancel₀ (hαne j), one_smul]
  have hZn : ∀ j, ‖Z j‖ ≤ c₄ * δ := fun j => by
    have h : Z j = (α j)⁻¹ • ((T j - e) + (1 - α j) • e) := by
      rw [hZdef, smul_add, sub_smul, one_smul, smul_sub, smul_sub, smul_smul,
        inv_mul_cancel₀ (hαne j), one_smul]
      abel_nf
    rw [h, norm_smul, norm_inv]
    have h1 : ‖(T j - e) + (1 - α j) • e‖ ≤ δ + δ * ‖e‖ := by
      refine (norm_add_le _ _).trans (add_le_add (hT j) ?_)
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right ((hα j).trans (by nlinarith)) (norm_nonneg _)
    have h2 : ‖α j‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith [hα0 j]) (by norm_num)]
      linarith [hα0 j]
    calc ‖α j‖⁻¹ * ‖(T j - e) + (1 - α j) • e‖ ≤ 2 * (δ + δ * ‖e‖) :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = c₄ * δ := by simp only [c₄]; ring
  set z := c₅ * (c₄ * δ) * c₅ with hzdef
  have hblock : ∀ (j : ℕ) (a b : A), ‖a‖ ≤ c₅ → ‖b‖ ≤ c₅ → ‖a * Z j * b‖ ≤ z :=
    fun j a b ha hb =>
      (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul ha (hZn j)
        (norm_nonneg _) (by positivity))) hb (norm_nonneg _) (by positivity))
  have ht₁ : ‖e‖ ≤ c₅ := le_add_of_nonneg_right (norm_nonneg _)
  have ht₂ : ‖1 - e‖ ≤ c₅ := le_add_of_nonneg_left (norm_nonneg _)
  have hz2 : z ^ 2 = zc * δ ^ 2 := by simp only [z, zc]; ring
  have hz0 : 0 ≤ z := by positivity
  have hz : z ≤ 1 / 2 := by
    have h1 : zc * δ ^ 2 ≤ zc * y := mul_le_mul_of_nonneg_left hδy hzc
    have h0 : 4 * zc * y < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by
      simp only [C]; linarith) hy0) hsmall
    have h2 : z ^ 2 < (1 / 2) ^ 2 := by rw [hz2]; linarith only [h1, h0]
    exact (pow_lt_pow_iff_left₀ hz0 (by norm_num) two_ne_zero).1 h2 |>.le
  have hpert := norm_trace_prod_add_sub_le_of_le he Z hZ
    (tr := tr.toAddMonoidHom) htr hK0 hK (fun j => hblock j _ _ ht₂ ht₁)
    (fun j => hblock j _ _ ht₁ ht₂) (fun j => hblock j _ _ ht₂ ht₂) hz hM2
  simp only [LinearMap.toAddMonoidHom_coe, he1] at hpert
  have hMz : (M : ℝ) * (2 * z ^ 2) = 2 * zc * y := by rw [hz2, hydef]; ring
  rw [hMz] at hpert
  set a := ((List.range M).map α).prod
  set P := ((List.range M).map fun j => e + Z j).prod
  have hprod : ((List.range M).map T).prod = a • P := by
    have hmap : (List.range M).map T = (List.range M).map fun j => α j • (e + Z j) := by
      exact List.map_congr_left fun j _ => hTZ j
    rw [hmap, product_smul]
  have ha : ‖a‖ ≤ 1 := norm_scalarProduct_le_one α hα1 M
  have haerr : ‖a - 1‖ ≤ y * Real.exp y := by
    have h := norm_prod_range_sub_pow_le_of_isIdempotentElem
      (show IsIdempotentElem (1 : ℂ) by simp [IsIdempotentElem])
      (X := α) (c := 1) (by simp) (by simp)
      (fun j => by simpa only [norm_sub_rev] using hα j) M
    simp only [one_pow, one_mul] at h
    exact h.trans (one_add_pow_sub_one_le_mul_exp (sq_nonneg δ) M)
  have hsplit : tr ((List.range M).map T).prod - 1 = a * (tr P - 1) + (a - 1) := by
    rw [hprod, map_smul, smul_eq_mul]
    ring
  have hC1 : 1 ≤ C := by simp only [C]; linarith
  have hexp : Real.exp y ≤ Real.exp (C * y) := Real.exp_le_exp.2 (by nlinarith)
  have hexp' : Real.exp (2 * zc * y) ≤ Real.exp (C * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by simp only [C]; linarith) hy0)
  rw [hsplit]
  calc ‖a * (tr P - 1) + (a - 1)‖
      ≤ 1 * (E₀ * (2 * zc * y) * Real.exp (2 * zc * y)) + y * Real.exp y := by
        refine (norm_add_le _ _).trans (add_le_add ?_ haerr)
        rw [norm_mul]
        exact mul_le_mul ha hpert (norm_nonneg _) zero_le_one
    _ ≤ C * y * Real.exp (C * y) := by
        have h1 : E₀ * (2 * zc * y) * Real.exp (2 * zc * y) ≤
            2 * E₀ * zc * y * Real.exp (C * y) := by
          rw [show E₀ * (2 * zc * y) = 2 * E₀ * zc * y by ring]
          exact mul_le_mul_of_nonneg_left hexp' (by positivity)
        have h2 : y * Real.exp y ≤ 4 * y * Real.exp (C * y) := by
          calc y * Real.exp y ≤ y * Real.exp (C * y) :=
                mul_le_mul_of_nonneg_left hexp hy0
            _ ≤ 4 * y * Real.exp (C * y) :=
                mul_le_mul_of_nonneg_right (by linarith only [hy0]) (Real.exp_pos _).le
        have h3 : (2 * E₀ * zc + 4) * y * Real.exp (C * y) ≤ C * y * Real.exp (C * y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by simp only [C]; linarith)
            hy0) (by positivity)
        have h4 : (2 * E₀ * zc + 4) * y * Real.exp (C * y) =
            2 * E₀ * zc * y * Real.exp (C * y) + 4 * y * Real.exp (C * y) := by ring
        simpa only [one_mul] using (add_le_add h1 h2).trans (h4 ▸ h3)

end IsIdempotentElem
