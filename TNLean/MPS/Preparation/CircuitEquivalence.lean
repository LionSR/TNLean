/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryMulVecInner
import TNLean.MPS.Preparation.LogDepthPreparation
import TNLean.Circuit.ProductStateCircuit

/-!
# Normal MPS are transformed into each other by circuits of depth `O(log(N/ε))`

arXiv:2307.01696, "Discussion and outlook": "Our results also imply that MPS in the same phase
can be transformed into each other using a log-depth circuit". The states of that paper are the
normal MPS, which "all lie in the topologically trivial phase" (main text, before eq. (1)); this
file proves the statement for them, as a consequence of eq. (1)
(`MPSPreparation.exists_isPreparedInDepth_le_log_of_mpvState_ne_zero`).

**Scope restriction (normal tensors):** the source's claim concerns "MPS in the same phase"; this
file treats only the case where both tensors are normal, the trivial phase of the classification
without symmetry. Non-normal states are not treated, and nothing is claimed about phases defined
with a symmetry. Documented in `docs/paper-gaps/mswc24_same_phase_circuit_normal_case.tex`.

Write `|φ_N(A)⟩` for the periodic state of `A` and `|φ_N(A)⟩/‖φ_N(A)‖` for its normalization
when it is nonzero. If `U_A |0⋯0⟩` approximates `|φ_N(A)⟩/‖φ_N(A)‖` and `U_B |0⋯0⟩` approximates
`|φ_N(B)⟩/‖φ_N(B)‖`, up to scalars, then `U_B U_A†` maps the first normalized state close to the
second. The adjoint of a local circuit is a local
circuit of the same depth (`QuantumCircuit.IsLocalCircuitOfDepth.star`), depths add in series
(`QuantumCircuit.IsLocalCircuitOfDepth.mul`), and the two product vectors are replaced by
`|0⋯0⟩` with two more layers each
(`QuantumCircuit.IsPreparedInDepth.exists_eq_smul_mulVec_productVector_single_zero`).

The error is measured as in eq. (1), by `ε(ψ, φ) = 1 - |⟨ψ|φ⟩|`. It is not a metric, but it
satisfies `ε(x, z) ≤ 2 (ε(x, y) + ε(y, z))` on unit vectors
(`MPSPreparation.one_sub_norm_inner_le_two_mul_add`), since `2 ε(x, y)` is the squared distance
from `x` to the closest unit multiple of `y`.

## Main results

* `MPSPreparation.exists_isLocalCircuitOfDepth_le_log_of_mpvState_ne_zero`: for normal tensors
  `A` and `B` with the same physical dimension there is `c`, depending only on `A` and `B`, such
  that for `N ≥ 2`, `0 < ε ≤ 1`, `|φ_N(A)⟩ ≠ 0` and `|φ_N(B)⟩ ≠ 0`, a local circuit of depth at
  most `c log(N/ε)` maps `|φ_N(A)⟩/‖φ_N(A)‖` to a vector `ψ` with
  `1 - |⟨ψ|φ_N(B)⟩|/‖φ_N(B)‖ ≤ ε`.
* `MPSPreparation.exists_isLocalCircuitOfDepth_le_log`: the same for every `N ≥ N₀`, without the
  conditions `|φ_N(A)⟩ ≠ 0` and `|φ_N(B)⟩ ≠ 0`.
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace
open QuantumCircuit

namespace MPSPreparation

/-! ### The error `1 - |⟨x|y⟩|` -/

section Error

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For unit vectors `a`, `b` and a unit scalar `c`, `1 - |⟨a|b⟩| ≤ ‖a - c b‖² / 2`. -/
theorem one_sub_norm_inner_le_norm_sub_smul_sq {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {c : ℂ} (hc : ‖c‖ = 1) : 1 - ‖⟪a, b⟫_ℂ‖ ≤ ‖a - c • b‖ ^ 2 / 2 := by
  rw [@norm_sub_sq ℂ, norm_smul, hc, ha, hb, inner_smul_right]
  have h1 := RCLike.re_le_norm (c * ⟪a, b⟫_ℂ)
  rw [norm_mul, hc, one_mul] at h1
  linarith

/-- For unit vectors `a`, `b` some unit multiple of `b` is at squared distance
`2 (1 - |⟨a|b⟩|)` from `a`. -/
theorem exists_norm_sub_smul_sq_eq {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖a - c • b‖ ^ 2 = 2 * (1 - ‖⟪a, b⟫_ℂ‖) := by
  set z := ⟪a, b⟫_ℂ
  have key : ∀ c : ℂ, ‖c‖ = 1 → c * z = (‖z‖ : ℂ) →
      ‖a - c • b‖ ^ 2 = 2 * (1 - ‖z‖) := fun c hc hcz => by
    rw [@norm_sub_sq ℂ, norm_smul, hc, ha, hb, inner_smul_right]
    change 1 ^ 2 - 2 * RCLike.re (c * z) + (1 * 1) ^ 2 = _
    rw [hcz, RCLike.re_to_complex, Complex.ofReal_re]
    ring
  by_cases hz : z = 0
  · exact ⟨1, norm_one, key 1 norm_one (by simp [hz])⟩
  · have hz' : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hc : ‖star z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr hz)]
    refine ⟨star z / ‖z‖, hc, key _ hc ?_⟩
    rw [div_mul_eq_mul_div, Complex.star_def, Complex.conj_mul', div_eq_iff hz']
    ring

/-- **The triangle step for the error.** For unit vectors `x`, `y`, `z`,
`1 - |⟨x|z⟩| ≤ 2 ((1 - |⟨x|y⟩|) + (1 - |⟨y|z⟩|))`. -/
theorem one_sub_norm_inner_le_two_mul_add {x y z : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hz : ‖z‖ = 1) :
    1 - ‖⟪x, z⟫_ℂ‖ ≤ 2 * ((1 - ‖⟪x, y⟫_ℂ‖) + (1 - ‖⟪y, z⟫_ℂ‖)) := by
  obtain ⟨c₁, hc₁, h₁⟩ := exists_norm_sub_smul_sq_eq hx hy
  obtain ⟨c₂, hc₂, h₂⟩ := exists_norm_sub_smul_sq_eq hy hz
  have hc : ‖c₁ * c₂‖ = 1 := by rw [norm_mul, hc₁, hc₂, one_mul]
  have htri : ‖x - (c₁ * c₂) • z‖ ≤ ‖x - c₁ • y‖ + ‖y - c₂ • z‖ := by
    calc ‖x - (c₁ * c₂) • z‖ = ‖(x - c₁ • y) + c₁ • (y - c₂ • z)‖ := by
          rw [smul_sub, mul_smul]; congr 1; abel
      _ ≤ ‖x - c₁ • y‖ + ‖c₁ • (y - c₂ • z)‖ := norm_add_le _ _
      _ = ‖x - c₁ • y‖ + ‖y - c₂ • z‖ := by rw [norm_smul, hc₁, one_mul]
  have h := one_sub_norm_inner_le_norm_sub_smul_sq hx hz hc
  have hsq : ‖x - (c₁ * c₂) • z‖ ^ 2 ≤ 2 * (‖x - c₁ • y‖ ^ 2 + ‖y - c₂ • z‖ ^ 2) := by
    nlinarith [norm_nonneg (x - (c₁ * c₂) • z), norm_nonneg (x - c₁ • y),
      norm_nonneg (y - c₂ • z), sq_nonneg (‖x - c₁ • y‖ - ‖y - c₂ • z‖)]
  rw [h₁, h₂] at hsq
  linarith

end Error

/-! ### Transforming normal MPS into each other -/

variable {d : ℕ}

/-- **Normal MPS are transformed into each other in depth `O(log(N/ε))`** (arXiv:2307.01696,
"Discussion and outlook": "MPS in the same phase can be transformed into each other using a
log-depth circuit"; the normal MPS "all lie in the topologically trivial phase", main text before
eq. (1)). For normal tensors `A` and `B` with the same physical dimension there is `c`, depending
only on `A` and `B`, with the following property. For every `N ≥ 2` and `0 < ε ≤ 1` such that
the periodic states `|φ_N(A)⟩` and `|φ_N(B)⟩` do not vanish, some local circuit `U` of depth at
most `c log(N/ε)` maps the normalized state `|φ_N(A)⟩/‖φ_N(A)‖` to a vector `ψ` with
`1 - |⟨ψ|φ_N(B)⟩|/‖φ_N(B)‖ ≤ ε`.

The circuit is `U_B U_A†`, where `U_A |0⋯0⟩` and `U_B |0⋯0⟩` prepare the normalized states
`|φ_N(A)⟩/‖φ_N(A)‖` and `|φ_N(B)⟩/‖φ_N(B)‖`, up to scalars, with error `ε/4` by eq. (1)
(`exists_isPreparedInDepth_le_log_of_mpvState_ne_zero`). The periodic states are assumed
nonzero, as in that theorem; see the Local fix (nonvanishing periodic state) of
`TNLean.MPS.Preparation.LogDepthPreparation`, documented in
`docs/paper-gaps/mswc24_depth_upper_bound_nonzero_state.tex`. -/
theorem exists_isLocalCircuitOfDepth_le_log_of_mpvState_ne_zero {D D' : ℕ} (A : MPSTensor d D)
    (B : MPSTensor d D') (hA : Kraus.IsNormal A) (hB : Kraus.IsNormal B) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N → mpvState A N ≠ 0 →
      mpvState B N ≠ 0 → ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
        IsLocalCircuitOfDepth U T ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
        ∃ ψ : MPVSpace d N, (fun s => ψ s) = U *ᵥ (fun s => normalizedMPVState A N s) ∧
          1 - ‖⟪ψ, normalizedMPVState B N⟫_ℂ‖ ≤ ε := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, fun ε _ _ N _ _ h0 _ => absurd ?_ h0⟩
    ext s; exact (s ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩).elim0
  obtain ⟨cA, hcA⟩ := exists_isPreparedInDepth_le_log_of_mpvState_ne_zero A hA
  obtain ⟨cB, hcB⟩ := exists_isPreparedInDepth_le_log_of_mpvState_ne_zero B hB
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨3 * max cA 0 + 3 * max cB 0 + 4 / Real.log 2,
    fun ε hε hε1 N _ hN h0A h0B => ?_⟩
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨ψA, TA, hψA, hTA, hpA, herrA⟩ := hcA (ε / 4) hε4 (by linarith) N hN h0A
  obtain ⟨ψB, TB, hψB, hTB, hpB, herrB⟩ := hcB (ε / 4) hε4 (by linarith) N hN h0B
  -- Both preparations start from `|0⋯0⟩`, up to scalars.
  have hne : ∀ v : MPVSpace d N, ‖v‖ = 1 → (fun s => v s) ≠ 0 := fun v hv h0 => by
    have : v = 0 := by ext s; exact congrFun h0 s
    rw [this, norm_zero] at hv
    exact zero_ne_one hv
  obtain ⟨UA, hUA, a, ha⟩ :=
    hpA.exists_eq_smul_mulVec_productVector_single_zero hd (hne ψA hψA)
  obtain ⟨UB, hUB, b, hb⟩ :=
    hpB.exists_eq_smul_mulVec_productVector_single_zero hd (hne ψB hψB)
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hne ψB hψB (by rw [hb, zero_smul])
  set U := UB * star UA
  have hU : IsLocalCircuitOfDepth U (TA + 2 + (TB + 2)) := hUA.star.mul hUB
  have hUu := hU.mem_unitary
  -- `U` maps `ψA` to the multiple `(a / b) ψB` of `ψB`.
  have hUA' : star UA * UA = 1 := Unitary.star_mul_self_of_mem hUA.mem_unitary
  have hUψ : U *ᵥ (fun s => ψA s) = fun s => ((a / b) • ψB) s := by
    have : (fun s => ((a / b) • ψB) s) = (a / b) • fun s => ψB s := rfl
    rw [this, hb, ha, mulVec_smul, mulVec_mulVec, Matrix.mul_assoc, hUA', Matrix.mul_one,
      smul_smul, div_mul_cancel₀ _ hb0]
  have hnA := norm_normalizedMPVState h0A
  have hnB := norm_normalizedMPVState h0B
  set φA := normalizedMPVState A N
  set φB := normalizedMPVState B N
  set ψ : MPVSpace d N := WithLp.toLp 2 (U *ᵥ fun s => φA s)
  have hψ : (fun s => ψ s) = U *ᵥ fun s => φA s := rfl
  have hχ := Matrix.norm_eq_of_mulVec_eq hUu hUψ.symm
  have hκ : ‖(a / b) • ψB‖ = 1 := hχ.trans hψA
  refine ⟨U, TA + 2 + (TB + 2), hU, ?_, ψ, hψ, ?_⟩
  · -- `log(4N/ε) ≤ 3 log(N/ε)` and `4 ≤ (4 / log 2) log(N/ε)`.
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : Real.log 2 ≤ Real.log (N / ε) :=
      Real.log_le_log two_pos (hN2.trans (le_div_self (by positivity) hε hε1))
    have h4 : Real.log (N / (ε / 4)) ≤ 3 * Real.log (N / ε) := by
      rw [show (N : ℝ) / (ε / 4) = 4 * (N / ε) by field_simp,
        Real.log_mul (by norm_num) (by positivity),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      linarith
    have hlogpos : 0 ≤ Real.log (N / (ε / 4)) := (hl2.le.trans hlog).trans
      (Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by positivity) hε4
        (by linarith)))
    have hA' : (TA : ℝ) ≤ 3 * max cA 0 * Real.log (N / ε) := by
      calc (TA : ℝ) ≤ cA * Real.log (N / (ε / 4)) := hTA
        _ ≤ max cA 0 * Real.log (N / (ε / 4)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogpos
        _ ≤ max cA 0 * (3 * Real.log (N / ε)) :=
          mul_le_mul_of_nonneg_left h4 (le_max_right _ _)
        _ = 3 * max cA 0 * Real.log (N / ε) := by ring
    have hB' : (TB : ℝ) ≤ 3 * max cB 0 * Real.log (N / ε) := by
      calc (TB : ℝ) ≤ cB * Real.log (N / (ε / 4)) := hTB
        _ ≤ max cB 0 * Real.log (N / (ε / 4)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogpos
        _ ≤ max cB 0 * (3 * Real.log (N / ε)) :=
          mul_le_mul_of_nonneg_left h4 (le_max_right _ _)
        _ = 3 * max cB 0 * Real.log (N / ε) := by ring
    have h4' : (4 : ℝ) ≤ 4 / Real.log 2 * Real.log (N / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      linarith
    push_cast
    nlinarith
  · -- The triangle step through `U ψA = (a / b) ψB`.
    have h1 : ⟪ψ, (a / b) • ψB⟫_ℂ = ⟪φA, ψA⟫_ℂ := Matrix.inner_eq_of_mulVec_eq hUu hψ hUψ.symm
    have hψn : ‖ψ‖ = 1 := (Matrix.norm_eq_of_mulVec_eq hUu hψ).trans hnA
    have hab : ‖a / b‖ = 1 := by rwa [norm_smul, hψB, mul_one] at hκ
    have h2 : ‖⟪(a / b) • ψB, φB⟫_ℂ‖ = ‖⟪ψB, φB⟫_ℂ‖ := by
      rw [inner_smul_left, norm_mul, Complex.norm_conj, hab, one_mul]
    have htri := one_sub_norm_inner_le_two_mul_add hψn hκ hnB
    rw [h1, h2, norm_inner_symm φA ψA] at htri
    linarith

/-- **Normal MPS are transformed into each other in depth `O(log(N/ε))`, long chains**
(arXiv:2307.01696, "Discussion and outlook"). For normal tensors `A` and `B` with the same
physical dimension and bond dimensions at least `1` there are `c` and `N₀`, depending only on `A`
and `B`, such that for every `N ≥ N₀` and `0 < ε ≤ 1` some local circuit of depth at most
`c log(N/ε)` maps the normalized state `|φ_N(A)⟩/‖φ_N(A)‖` to a vector `ψ` with
`1 - |⟨ψ|φ_N(B)⟩|/‖φ_N(B)‖ ≤ ε`.

This is `exists_isLocalCircuitOfDepth_le_log_of_mpvState_ne_zero` together with
`exists_mpvState_ne_zero_of_le`, as `exists_isPreparedInDepth_le_log` is for eq. (1). -/
theorem exists_isLocalCircuitOfDepth_le_log {D D' : ℕ} [NeZero D] [NeZero D']
    (A : MPSTensor d D) (B : MPSTensor d D') (hA : Kraus.IsNormal A) (hB : Kraus.IsNormal B) :
    ∃ (c : ℝ) (N₀ : ℕ), ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
        IsLocalCircuitOfDepth U T ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
        ∃ ψ : MPVSpace d N, (fun s => ψ s) = U *ᵥ (fun s => normalizedMPVState A N s) ∧
          1 - ‖⟪ψ, normalizedMPVState B N⟫_ℂ‖ ≤ ε := by
  obtain ⟨c, hc⟩ := exists_isLocalCircuitOfDepth_le_log_of_mpvState_ne_zero A B hA hB
  obtain ⟨NA, hNA⟩ := exists_mpvState_ne_zero_of_le A hA
  obtain ⟨NB, hNB⟩ := exists_mpvState_ne_zero_of_le B hB
  exact ⟨c, max (max NA NB) 2, fun ε hε hε1 N _ hN =>
    hc ε hε hε1 N (le_of_max_le_right hN) (hNA N (le_of_max_le_left (le_of_max_le_left hN)))
      (hNB N (le_of_max_le_right (le_of_max_le_left hN)))⟩

end MPSPreparation
