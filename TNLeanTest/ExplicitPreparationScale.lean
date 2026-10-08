/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.AllLengthPrescribedSlope
import TNLean.MPS.Preparation.OrderedMixingScale

/-!
# Explicit preparation scale regressions

Check accuracy endpoints, remainder partitions, and the selected physical blocking scale.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder

/-! The constant polynomial and the endpoint `N = ε = 1` retain the accuracy term. -/

example {K r N ε q : ℝ} (hK : 0 < K) (hr : 0 < r) (hN : 1 ≤ N)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : (1 / r) * Real.log (N / ε) + max (Real.log K) 0 / r ≤ q) :
    K * Real.exp (-(r * q)) ≤ ε := by
  simpa using mul_pow_mul_exp_neg_le_of_le (k := 0) hK hr hN hε hε1
    (by simp) le_rfl hq

example {K r q : ℝ} (hK : 0 < K) (hr : 0 < r)
    (hq : max (Real.log K) 0 / r ≤ q) : K * Real.exp (-(r * q)) ≤ 1 := by
  simpa using mul_pow_mul_exp_neg_le_of_le (k := 1) (N := 1) (ε := 1)
    (a := 1 / r) hK hr le_rfl zero_lt_one le_rfl (by simp) le_rfl (by simpa using hq)

/-! A nondivisible ring uses one enlarged final block, still shorter than twice the scale. -/

example : remainderBlockLengths 3 8 0 = 3 := by decide
example : remainderBlockLengths 3 8 1 = 5 := by decide
example : (∑ j, remainderBlockLengths 3 8 j) = 8 :=
  sum_remainderBlockLengths (by decide) (by decide)

/-! At the one-site accuracy endpoint, the scale is four and the rate branch is vacuous. -/

example (d : ℕ) (hd : 0 < d) (A : VaryingBondChain d 1 1) (hA : state A ≠ 0) :
    ∃ (ψ : MPVSpace d 1) (T : ℕ), ‖ψ‖ = 1 ∧ IsPreparedInDepth T (fun s => ψ s) ∧
      1 - ‖⟪ψ, (‖state A‖ : ℂ)⁻¹ • state A⟫_ℂ‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_min_of_rate d 1 hd
  have h := hC 1 A hA 1 1 0 0 1 4 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl
  obtain ⟨_, ψ, T, hψ, _, hp, he⟩ := h (by norm_num)
  exact ⟨ψ, T, hψ, hp, he⟩

/-! The prescribed-slope theorem supplies the concrete ceiling, without a divisibility premise. -/

example (d D : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, ∀ (A B : MPSTensor d D) (ζ : ℂ) (σ : Matrix (Fin D) (Fin D) ℂ) (t : ℝ),
      ζ ≠ 0 → (∀ (N : ℕ) (s : Fin N → Fin d), mpv B s = ζ ^ N * mpv A s) →
      Kraus.IsNormal B → IsLeftCanonical B → σ.PosDef → σ.trace = 1 →
      Kraus.transferMap B σ = σ → 0 < t → t < 1 →
      (∀ μ, Module.End.HasEigenvalue (Kraus.transferMap B) μ → μ ≠ 1 → ‖μ‖ ≤ t) →
      ∀ a : ℝ, correlationLength t / 2 < a →
        ∃ b : ℝ, 1 ≤ b ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∀ (N : ℕ) [NeZero N], mpvState A N ≠ 0 →
            ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧
              T ≤ C * min N ⌈a * Real.log (N / ε) + b⌉₊ ∧
              IsPreparedInDepth T (fun s => ψ s) ∧
              1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_allLength_of_slope d D hd
  refine ⟨C, fun A B ζ σ t hζ hmpv hNB hLC hσ htr hfix ht0 ht1 hlam a ha => ?_⟩
  obtain ⟨b, hb, h⟩ := hC A B ζ σ t hζ hmpv hNB hLC hσ htr hfix ht0 ht1 hlam a ha
  exact ⟨b, hb, fun ε hε hε1 N _ hA => h ε hε hε1 N _ hA (Nat.le_ceil _)⟩
