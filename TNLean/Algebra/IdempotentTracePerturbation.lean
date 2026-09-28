/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.NormedRingTelescoping

/-!
# Traces of powers of an idempotent perturbed without first-order term

Let `e` be an idempotent of a normed ring, `f = 1 - e`, and let `Z` satisfy `e Z e = 0`. Write
`β`, `β'`, `ζ` for bounds on the norms of the blocks `f Z e`, `e Z f`, `f Z f`, with `ζ < 1`, and
put `ρ = 1 + β β' / (1 - ζ)`. For a trace `tr` bounded by `K ‖·‖`,
`|tr (e + Z)^M - tr e| ≤ K (‖e‖ (ρ^M - 1) + ‖f‖ (β β' / (1 - ζ)² (ρ^M - ζ^M) + ζ^M))`.

Here `ρ - 1` is of second order in `Z`. A nonzero block `e Z e` would contribute `M ‖e Z e‖` to
the exponent. Since it vanishes, the off-diagonal blocks enter only through the products
`e Z f (f Z f)^k f Z e`, each of second order. The only first-order contribution is
`tr (f (f Z f)^M)`, of order `ζ^M`, which is of second order once `M ≥ 2`.

The bound is a project result. It replaces the first-order iteration of arXiv:2103.13367,
Supplemental Material, eqs. (29)–(33), in which the error of `tr T^M` is linear in `‖T - e‖`.

The proof follows the blocks `P (e + Z)^M e` and `P (e + Z)^M f` of the powers for `P = e` and
`P = f`, which satisfy a two-term linear recursion in `M`, and bounds them by induction.

## Main declarations

* `IsIdempotentElem.norm_trace_add_pow_sub_le` — the bound above.
* `IsIdempotentElem.norm_trace_add_pow_sub_le_of_le` — its form for one bound `z ≤ 1/2` on the
  three blocks and `M ≥ 2`:
  `|tr (e + Z)^M - tr e| ≤ K (‖e‖ + 3 ‖f‖) (2 M z²) e^{2 M z²}`.
-/

namespace IsIdempotentElem

variable {R : Type*} [NormedRing R] {e Z : R}

/-- The `e`-column of `(e + Z)^{M+1}`: `P T^{M+1} e = P T^M e + P T^M f (f Z e)` for
`T = e + Z`, `f = 1 - e`, and `e Z e = 0`. -/
theorem mul_add_pow_succ_mul_self (he : IsIdempotentElem e) (hZ : e * Z * e = 0) (P : R)
    (M : ℕ) :
    P * (e + Z) ^ (M + 1) * e =
      P * (e + Z) ^ M * e + P * (e + Z) ^ M * (1 - e) * ((1 - e) * Z * e) := by
  have hee : e * e = e := he
  rw [pow_succ, ← mul_assoc P]
  set X := P * (e + Z) ^ M
  have key : X * (e + Z) * e - (X * e + X * (1 - e) * ((1 - e) * Z * e)) =
      X * (e * e - e) + X * (e * Z * e) - X * (e * e - e) * Z * e := by
    noncomm_ring
  rw [hee, sub_self, hZ] at key
  simpa [sub_eq_zero] using key

/-- The `f`-column of `(e + Z)^{M+1}`: `P T^{M+1} f = P T^M e (e Z f) + P T^M f (f Z f)` for
`T = e + Z` and `f = 1 - e`. -/
theorem mul_add_pow_succ_mul_one_sub (he : IsIdempotentElem e) (P : R) (M : ℕ) :
    P * (e + Z) ^ (M + 1) * (1 - e) =
      P * (e + Z) ^ M * e * (e * Z * (1 - e)) +
        P * (e + Z) ^ M * (1 - e) * ((1 - e) * Z * (1 - e)) := by
  have hee : e * e = e := he
  rw [pow_succ, ← mul_assoc P]
  set X := P * (e + Z) ^ M
  have key : X * (e + Z) * (1 - e) - (X * e * (e * Z * (1 - e)) +
      X * (1 - e) * ((1 - e) * Z * (1 - e))) =
      -(X * (e * e - e)) - 2 * (X * (e * e - e) * Z) + 2 * (X * (e * e - e) * Z * e) := by
    noncomm_ring
  rw [hee, sub_self] at key
  simpa [sub_eq_zero] using key

/-- `‖f (f Z f)^M‖ ≤ ‖f‖ ζ^M` when `‖f Z f‖ ≤ ζ`. -/
theorem norm_mul_pow_le {f W : R} {ζ : ℝ} (hW : ‖W‖ ≤ ζ) (M : ℕ) :
    ‖f * W ^ M‖ ≤ ‖f‖ * ζ ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hζ0 : 0 ≤ ζ := (norm_nonneg _).trans hW
    rw [pow_succ, ← mul_assoc]
    calc ‖f * W ^ M * W‖ ≤ ‖f * W ^ M‖ * ‖W‖ := norm_mul_le _ _
      _ ≤ ‖f‖ * ζ ^ M * ζ := mul_le_mul ih hW (norm_nonneg _) (by positivity)
      _ = ‖f‖ * ζ ^ (M + 1) := by ring

/-- **The `e`-row of the powers.** With `e Z e = 0`, `‖f Z e‖ ≤ β`, `‖e Z f‖ ≤ β'`,
`‖f Z f‖ ≤ ζ < 1`, and `ρ = 1 + β β' / (1 - ζ)`, the blocks of `T^M = (e + Z)^M` satisfy
`‖e T^M e - e‖ ≤ ‖e‖ (ρ^M - 1)` and `‖e T^M f‖ ≤ ‖e‖ β' / (1 - ζ) ρ^M`. -/
theorem norm_self_mul_add_pow_le (he : IsIdempotentElem e) (hZ : e * Z * e = 0) {β β' ζ : ℝ}
    (hβ : ‖(1 - e) * Z * e‖ ≤ β) (hβ' : ‖e * Z * (1 - e)‖ ≤ β')
    (hζ : ‖(1 - e) * Z * (1 - e)‖ ≤ ζ) (hζ1 : ζ < 1) (M : ℕ) :
    ‖e * (e + Z) ^ M * e - e‖ ≤ ‖e‖ * ((1 + β * β' / (1 - ζ)) ^ M - 1) ∧
      ‖e * (e + Z) ^ M * (1 - e)‖ ≤ ‖e‖ * β' / (1 - ζ) * (1 + β * β' / (1 - ζ)) ^ M := by
  have hee : e * e = e := he
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ
  have hβ'0 : 0 ≤ β' := (norm_nonneg _).trans hβ'
  have hζ0 : 0 ≤ ζ := (norm_nonneg _).trans hζ
  have h1ζ : 0 < 1 - ζ := by linarith
  set k := β * β' / (1 - ζ) with hk
  have hk0 : 0 ≤ k := by positivity
  set t := ‖e‖
  have ht : 0 ≤ t := norm_nonneg _
  induction M with
  | zero =>
    simp only [pow_zero, mul_one, hee, sub_self, norm_zero, mul_zero, le_refl, true_and]
    rw [mul_sub, mul_one, hee, sub_self, norm_zero]
    positivity
  | succ M ih =>
    obtain ⟨ihx, ihy⟩ := ih
    set x := e * (e + Z) ^ M * e
    set y := e * (e + Z) ^ M * (1 - e)
    have hρ1 : 1 ≤ 1 + k := by linarith
    have hpow : 1 ≤ (1 + k) ^ M := one_le_pow₀ hρ1
    have hx : ‖x‖ ≤ t * (1 + k) ^ M := by
      calc ‖x‖ = ‖(x - e) + e‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - e‖ + t := norm_add_le _ _
        _ ≤ t * ((1 + k) ^ M - 1) + t := by gcongr
        _ = t * (1 + k) ^ M := by ring
    constructor
    · rw [mul_add_pow_succ_mul_self he hZ, add_sub_right_comm]
      calc ‖x - e + y * ((1 - e) * Z * e)‖
          ≤ ‖x - e‖ + ‖y‖ * β :=
            (norm_add_le _ _).trans (add_le_add le_rfl ((norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_left hβ (norm_nonneg _))))
        _ ≤ t * ((1 + k) ^ M - 1) + t * β' / (1 - ζ) * (1 + k) ^ M * β := by gcongr
        _ = t * ((1 + k) ^ (M + 1) - 1) := by
            rw [hk, pow_succ]; field_simp; ring
    · rw [mul_add_pow_succ_mul_one_sub he]
      calc ‖x * (e * Z * (1 - e)) + y * ((1 - e) * Z * (1 - e))‖
          ≤ ‖x‖ * β' + ‖y‖ * ζ :=
            (norm_add_le _ _).trans (add_le_add
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hβ' (norm_nonneg _)))
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hζ (norm_nonneg _))))
        _ ≤ t * (1 + k) ^ M * β' + t * β' / (1 - ζ) * (1 + k) ^ M * ζ := by gcongr
        _ = t * β' / (1 - ζ) * (1 + k) ^ M := by field_simp; ring
        _ ≤ t * β' / (1 - ζ) * (1 + k) ^ (M + 1) := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hρ1)
              (by positivity)

/-- **The `f`-row of the powers.** In the setting of `norm_self_mul_add_pow_le`, with
`f = 1 - e` and `W = f Z f`, the blocks of `T^M = (e + Z)^M` satisfy
`‖f T^M e‖ ≤ ‖f‖ β / (1 - ζ) (ρ^M - ζ^M)` and
`‖f T^M f - f W^M‖ ≤ ‖f‖ β β' / (1 - ζ)² (ρ^M - ζ^M)`. -/
theorem norm_one_sub_mul_add_pow_le (he : IsIdempotentElem e) (hZ : e * Z * e = 0)
    {β β' ζ : ℝ} (hβ : ‖(1 - e) * Z * e‖ ≤ β) (hβ' : ‖e * Z * (1 - e)‖ ≤ β')
    (hζ : ‖(1 - e) * Z * (1 - e)‖ ≤ ζ) (hζ1 : ζ < 1) (M : ℕ) :
    ‖(1 - e) * (e + Z) ^ M * e‖ ≤
        ‖1 - e‖ * β / (1 - ζ) * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M) ∧
      ‖(1 - e) * (e + Z) ^ M * (1 - e) - (1 - e) * ((1 - e) * Z * (1 - e)) ^ M‖ ≤
        ‖1 - e‖ * β * β' / (1 - ζ) ^ 2 * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M) := by
  have hee : e * e = e := he
  have hff : (1 - e) * (1 - e) = 1 - e := he.one_sub
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ
  have hβ'0 : 0 ≤ β' := (norm_nonneg _).trans hβ'
  have hζ0 : 0 ≤ ζ := (norm_nonneg _).trans hζ
  have h1ζ : 0 < 1 - ζ := by linarith
  set k := β * β' / (1 - ζ) with hk
  set W := (1 - e) * Z * (1 - e)
  set s := ‖1 - e‖
  have hs : 0 ≤ s := norm_nonneg _
  induction M with
  | zero =>
    simp only [pow_zero, mul_one, sub_self, mul_zero, hff, norm_zero, le_refl, and_true]
    rw [sub_mul, one_mul, hee, sub_self, norm_zero]
  | succ M ih =>
    obtain ⟨ihx, ihy⟩ := ih
    set x := (1 - e) * (e + Z) ^ M * e
    set y := (1 - e) * (e + Z) ^ M * (1 - e)
    have hfW : ‖(1 - e) * W ^ M‖ ≤ s * ζ ^ M := norm_mul_pow_le hζ M
    constructor
    · rw [mul_add_pow_succ_mul_self he hZ]
      have e1 : x + y * ((1 - e) * Z * e) =
          x + (y - (1 - e) * W ^ M) * ((1 - e) * Z * e) + (1 - e) * W ^ M * ((1 - e) * Z * e) := by
        noncomm_ring
      rw [e1]
      calc ‖x + (y - (1 - e) * W ^ M) * ((1 - e) * Z * e) + (1 - e) * W ^ M * ((1 - e) * Z * e)‖
          ≤ ‖x‖ + ‖y - (1 - e) * W ^ M‖ * β + ‖(1 - e) * W ^ M‖ * β := by
            refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
              (add_le_add le_rfl ?_)) ?_) <;>
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hβ (norm_nonneg _))
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
    · rw [mul_add_pow_succ_mul_one_sub he]
      have e1 : x * (e * Z * (1 - e)) + y * W - (1 - e) * W ^ (M + 1) =
          x * (e * Z * (1 - e)) + (y - (1 - e) * W ^ M) * W := by
        rw [pow_succ]; noncomm_ring
      rw [e1]
      calc ‖x * (e * Z * (1 - e)) + (y - (1 - e) * W ^ M) * W‖
          ≤ ‖x‖ * β' + ‖y - (1 - e) * W ^ M‖ * ζ :=
            (norm_add_le _ _).trans (add_le_add
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hβ' (norm_nonneg _)))
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hζ (norm_nonneg _))))
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

/-- A trace splits along a complementary pair of idempotents: `tr x = tr (e x e) + tr (f x f)`
for `f = 1 - e`. -/
theorem trace_eq_add {tr : R →+ ℂ} (htr : ∀ x y, tr (x * y) = tr (y * x))
    (he : IsIdempotentElem e) (x : R) :
    tr x = tr (e * x * e) + tr ((1 - e) * x * (1 - e)) := by
  have hee : e * e = e := he
  have hfe : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h1 : tr (e * x * (1 - e)) = 0 := by
    rw [htr, ← mul_assoc, hfe, zero_mul, map_zero]
  have h2 : tr ((1 - e) * x * e) = 0 := by
    rw [htr, ← mul_assoc, hef, zero_mul, map_zero]
  have hx : x = e * x * e + e * x * (1 - e) + (1 - e) * x * e + (1 - e) * x * (1 - e) := by
    noncomm_ring
  conv_lhs => rw [hx]
  rw [map_add, map_add, map_add, h1, h2, add_zero, add_zero]

/-- **Trace of the powers of an idempotent perturbed without first-order term.** Let `e` be an
idempotent of a normed ring, `f = 1 - e`, and `e Z e = 0`, with `‖f Z e‖ ≤ β`, `‖e Z f‖ ≤ β'`,
`‖f Z f‖ ≤ ζ < 1`, and put `ρ = 1 + β β' / (1 - ζ)`. For an additive `tr` with
`tr (x y) = tr (y x)` and `‖tr x‖ ≤ K ‖x‖`,
`‖tr (e + Z)^M - tr e‖ ≤ K (‖e‖ (ρ^M - 1) + ‖f‖ (β β' / (1 - ζ)² (ρ^M - ζ^M) + ζ^M))`.

Project result. It gives the approximation error of the log-depth preparation at
rate `2γ/ξ` in `MPSTensor.exists_approximationError_le`. -/
theorem norm_trace_add_pow_sub_le (he : IsIdempotentElem e) (hZ : e * Z * e = 0)
    {tr : R →+ ℂ} (htr : ∀ x y, tr (x * y) = tr (y * x)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖tr x‖ ≤ K * ‖x‖) {β β' ζ : ℝ}
    (hβ : ‖(1 - e) * Z * e‖ ≤ β) (hβ' : ‖e * Z * (1 - e)‖ ≤ β')
    (hζ : ‖(1 - e) * Z * (1 - e)‖ ≤ ζ) (hζ1 : ζ < 1) (M : ℕ) :
    ‖tr ((e + Z) ^ M) - tr e‖ ≤
      K * (‖e‖ * ((1 + β * β' / (1 - ζ)) ^ M - 1) +
        ‖1 - e‖ * (β * β' / (1 - ζ) ^ 2 * ((1 + β * β' / (1 - ζ)) ^ M - ζ ^ M) + ζ ^ M)) := by
  obtain ⟨hx, -⟩ := norm_self_mul_add_pow_le he hZ hβ hβ' hζ hζ1 M
  obtain ⟨-, hy⟩ := norm_one_sub_mul_add_pow_le he hZ hβ hβ' hζ hζ1 M
  have hW := norm_mul_pow_le (f := 1 - e) hζ M
  set W := (1 - e) * Z * (1 - e)
  have hsplit : tr ((e + Z) ^ M) - tr e =
      tr (e * (e + Z) ^ M * e - e) + tr ((1 - e) * (e + Z) ^ M * (1 - e) - (1 - e) * W ^ M) +
        tr ((1 - e) * W ^ M) := by
    rw [trace_eq_add htr he ((e + Z) ^ M), map_sub, map_sub]
    ring
  rw [hsplit]
  refine (norm_add₃_le).trans ?_
  have e1 := hK (e * (e + Z) ^ M * e - e)
  have e2 := hK ((1 - e) * (e + Z) ^ M * (1 - e) - (1 - e) * W ^ M)
  have e3 := hK ((1 - e) * W ^ M)
  have : K * ‖e * (e + Z) ^ M * e - e‖ +
      K * ‖(1 - e) * (e + Z) ^ M * (1 - e) - (1 - e) * W ^ M‖ + K * ‖(1 - e) * W ^ M‖ ≤
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

/-- **Trace of the powers of an idempotent perturbed without first-order term**, with one bound
`z ≤ 1/2` on the blocks `f Z e`, `e Z f`, `f Z f` and `M ≥ 2`:
`‖tr (e + Z)^M - tr e‖ ≤ K (‖e‖ + 3 ‖f‖) (2 M z²) e^{2 M z²}`. The bound is of second order in
`z`, uniformly in `M` as long as `M z²` stays bounded.

Project result; see `norm_trace_add_pow_sub_le`. -/
theorem norm_trace_add_pow_sub_le_of_le (he : IsIdempotentElem e) (hZ : e * Z * e = 0)
    {tr : R →+ ℂ} (htr : ∀ x y, tr (x * y) = tr (y * x)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ‖tr x‖ ≤ K * ‖x‖) {z : ℝ}
    (h₁ : ‖(1 - e) * Z * e‖ ≤ z) (h₂ : ‖e * Z * (1 - e)‖ ≤ z)
    (h₃ : ‖(1 - e) * Z * (1 - e)‖ ≤ z) (hz : z ≤ 1 / 2) {M : ℕ} (hM : 2 ≤ M) :
    ‖tr ((e + Z) ^ M) - tr e‖ ≤
      K * (‖e‖ + 3 * ‖1 - e‖) * (M * (2 * z ^ 2)) * Real.exp (M * (2 * z ^ 2)) := by
  have hz0 : 0 ≤ z := (norm_nonneg _).trans h₁
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
  have hmain := norm_trace_add_pow_sub_le he hZ htr hK0 hK h₁ h₂ h₃ (by linarith) M
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

end IsIdempotentElem
