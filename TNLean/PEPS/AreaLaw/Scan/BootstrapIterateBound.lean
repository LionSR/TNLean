/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ExponentBootstrap

/-!
# A closed-form bound for the iterated bootstrap constants

The safe-box constant of Proposition 9.5 is the value after finitely many rounds of the
recursion `C_{j+1} = G C_j + V (N C_j)²` of `boxBootstrapConstant`. If one round is dominated
by a monotone map `F` with `x ≤ F x`, then every constant `C_j` with `j ≤ M` is at most the
`M`-th iterate `F^[M] C₀`. For a power map `F x = A (1 + x)^K` with `A ≥ 1` and `K ≥ 1`,
this iterate is at most `((A + 1)(1 + C₀))^((2K)^M)`, an expression without recursion.

This is an auxiliary result: the source fixes the number of rounds but does not bound the
constants they produce.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, proof of Proposition 9.5, `prop:small-box`,
`08-scanner.tex`, lines 788–803.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- **The bootstrap constants are dominated by the iterates of a majorant.** If one bootstrap
round sends every `C ≥ 0` to at most `F C`, where `F` is monotone on `[0, ∞)` and satisfies
`x ≤ F x` there, then the constant after `j` rounds is at most `F^[M] C₀` for every `M ≥ j`.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803. -/
theorem boxBootstrapConstant_le_iterate {V C₀ : ℝ} {G F : ℝ → ℝ} {N : ℝ → ℕ} (hV : 0 ≤ V)
    (hC₀ : 0 ≤ C₀) (hG : ∀ C, 0 ≤ C → 0 ≤ G C) (hF : MonotoneOn F (Set.Ici 0))
    (hFx : ∀ x, 0 ≤ x → x ≤ F x) (hstep : ∀ C, 0 ≤ C → boxBootstrapStep V G N C ≤ F C)
    {j M : ℕ} (hjM : j ≤ M) :
    boxBootstrapConstant V G N C₀ j ≤ F^[M] C₀ := by
  have hlow : ∀ k : ℕ, C₀ ≤ F^[k] C₀ := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k hk =>
      rw [Function.iterate_succ_apply']
      exact hk.trans (hFx _ (hC₀.trans hk))
  have hmono : Monotone fun k : ℕ ↦ F^[k] C₀ := by
    refine monotone_nat_of_le_succ fun k ↦ ?_
    simp only [Function.iterate_succ_apply']
    exact hFx _ (hC₀.trans (hlow k))
  have hiter : ∀ k : ℕ, boxBootstrapConstant V G N C₀ k ≤ F^[k] C₀ := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k hk =>
      rw [Function.iterate_succ_apply']
      have hCk := boxBootstrapConstant_nonneg (N := N) hV hC₀ hG k
      exact (hstep _ hCk).trans (hF hCk (hC₀.trans (hlow k)) hk)
  exact (hiter j).trans (hmono hjM)

/-- The iterates of the power map `x ↦ A (1 + x)^K`, with `0 ≤ A` and `1 ≤ K`, started at
`x ≥ 0`, satisfy `1 + F^[j] x ≤ ((A + 1)(1 + x))^((2K)^j)`. -/
theorem one_add_iterate_mul_one_add_pow_le {A x : ℝ} {K : ℕ} (hA : 0 ≤ A) (hK : 1 ≤ K)
    (hx : 0 ≤ x) (j : ℕ) :
    1 + (fun y : ℝ ↦ A * (1 + y) ^ K)^[j] x ≤ ((A + 1) * (1 + x)) ^ ((2 * K) ^ j) := by
  set f : ℝ → ℝ := fun y ↦ A * (1 + y) ^ K
  set b := (A + 1) * (1 + x)
  have hb : 1 ≤ b := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hAb : A + 1 ≤ b := le_mul_of_one_le_right (by linarith) (by linarith)
  have hnonneg : ∀ k : ℕ, 0 ≤ f^[k] x := by
    intro k
    induction k with
    | zero => exact hx
    | succ k hk =>
      rw [Function.iterate_succ_apply']
      exact mul_nonneg hA (pow_nonneg (by linarith) K)
  induction j with
  | zero => simpa [b] using le_mul_of_one_le_left (by linarith) (by linarith : (1 : ℝ) ≤ A + 1)
  | succ j hj =>
    rw [Function.iterate_succ_apply']
    have hu : 1 ≤ 1 + f^[j] x := le_add_of_nonneg_right (hnonneg j)
    have hm : 1 ≤ (2 * K) ^ j := Nat.one_le_pow _ _ (by omega)
    calc 1 + A * (1 + f^[j] x) ^ K ≤ (A + 1) * (1 + f^[j] x) ^ K := by
          nlinarith [one_le_pow₀ (n := K) hu]
      _ ≤ b * (b ^ (2 * K) ^ j) ^ K :=
          mul_le_mul hAb (pow_le_pow_left₀ (by linarith) hj K) (by positivity) (by linarith)
      _ = b ^ (1 + K * (2 * K) ^ j) := by
          rw [← pow_mul, mul_comm ((2 * K) ^ j), pow_add, pow_one]
      _ ≤ b ^ (2 * K) ^ (j + 1) := by
          refine pow_le_pow_right₀ hb ?_
          rw [pow_succ]
          nlinarith

/-- **A closed-form bound for the bootstrap constants.** If one bootstrap round sends every
`C ≥ 0` to at most `A (1 + C)^K`, with `1 ≤ A` and `1 ≤ K`, then the constant after `j ≤ M`
rounds is at most `((A + 1)(1 + C₀))^((2K)^M)`. Source: proof of Proposition 9.5,
`08-scanner.tex`, lines 788–803. -/
theorem boxBootstrapConstant_le_pow_pow {V C₀ A : ℝ} {K : ℕ} {G : ℝ → ℝ} {N : ℝ → ℕ}
    (hV : 0 ≤ V) (hC₀ : 0 ≤ C₀) (hG : ∀ C, 0 ≤ C → 0 ≤ G C) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hstep : ∀ C, 0 ≤ C → boxBootstrapStep V G N C ≤ A * (1 + C) ^ K) {j M : ℕ}
    (hjM : j ≤ M) :
    boxBootstrapConstant V G N C₀ j ≤ ((A + 1) * (1 + C₀)) ^ ((2 * K) ^ M) := by
  have hF : MonotoneOn (fun y : ℝ ↦ A * (1 + y) ^ K) (Set.Ici 0) := fun x hx y _ hxy ↦
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [Set.mem_Ici.mp hx]) (by linarith) K)
      (by linarith)
  have hFx : ∀ x : ℝ, 0 ≤ x → x ≤ A * (1 + x) ^ K := fun x hx ↦
    calc x ≤ 1 + x := by linarith
      _ ≤ (1 + x) ^ K := le_self_pow₀ (by linarith) (by omega)
      _ ≤ A * (1 + x) ^ K := le_mul_of_one_le_left (by positivity) hA
  calc boxBootstrapConstant V G N C₀ j ≤ (fun y : ℝ ↦ A * (1 + y) ^ K)^[M] C₀ :=
        boxBootstrapConstant_le_iterate hV hC₀ hG hF hFx hstep hjM
    _ ≤ 1 + (fun y : ℝ ↦ A * (1 + y) ^ K)^[M] C₀ := le_add_of_nonneg_left zero_le_one
    _ ≤ _ := one_add_iterate_mul_one_add_pow_le (by linarith) hK hC₀ M

end TNLean.PEPS.AreaLaw.Scan
