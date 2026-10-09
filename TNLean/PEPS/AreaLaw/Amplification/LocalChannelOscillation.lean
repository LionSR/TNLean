/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelShellOscillation

/-!
# Finite local-channel oscillation increments

For increasing finite regions, the oscillation of an actual localized root
channel is bounded by the original oscillation and the shells whose regions
contain the observed site. The coefficients come from the actual localization
errors of a positive contraction. All statements allow arbitrary finite
spectators and arbitrary, not necessarily Hermitian, observables.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 124–139, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the finite-radius calculation underlying
`eq:amplification-oscillation-increment`; no graph metric, infinite-radius
limit, or deterministic propagation estimate is assumed.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- The zeroth channel shell costs two; a successor shell costs the sum of
the two square-root localization errors. Source: area law,
`09-amplification.tex`, lines 101–106 and 124–132. -/
noncomputable def localRootChannelShellBound (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => 2
  | l + 1 => 4 * (Real.sqrt (ε (l + 1)) + Real.sqrt (ε l))

/-- The shell coefficients are nonnegative, including at radius zero.
Source: area law, `09-amplification.tex`, lines 101–106. -/
theorem localRootChannelShellBound_nonneg (ε : ℕ → ℝ) (l : ℕ) :
    0 ≤ localRootChannelShellBound ε l := by
  cases l with
  | zero => norm_num [localRootChannelShellBound]
  | succ l =>
    exact mul_nonneg (by norm_num)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- Actual localization errors control every finite shell by the physical
oscillations in its region. Only errors through that radius are required.
Source: area law, `eq:amplification-shell-oscillation`, lines 101–121. -/
theorem norm_localRootChannelShell_le_sum_siteOscillation
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (ε : ℕ → ℝ) (l : ℕ)
    (hε : ∀ j ≤ l, ‖k - siteExpectation q (regions j) k‖ ≤ ε j)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannelShell regions k l B‖ ≤
      localRootChannelShellBound ε l * ∑ z ∈ regions l, siteOscillation q z B := by
  cases l with
  | zero =>
    exact norm_localRootChannelShell_zero_le_sum_siteOscillation regions hregions hk₀ hk₁ B
  | succ l =>
    exact norm_localRootChannelShell_succ_le_sum_siteOscillation regions hregions hk₀ hk₁ l
      (hε (l + 1) le_rfl) (hε l (Nat.le_succ l)) B

/-- The finite-radius oscillation increment for the actual local root channel.
Only shells whose regions contain `y` contribute, and only actual expectation
errors through `n` are used. Source: area law,
`eq:amplification-oscillation-increment`, lines 124–139, before taking the
radius limit and specializing the regions to metric neighborhoods. -/
theorem siteOscillation_localRootChannel_le
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (ε : ℕ → ℝ) (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (regions l) k‖ ≤ ε l)
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (localRootChannel (regions n) k B) ≤
      siteOscillation q y B +
        2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => y ∈ regions l),
          localRootChannelShellBound ε l * ∑ z ∈ regions l, siteOscillation q z B := by
  classical
  let a (l : ℕ) :=
    localRootChannelShellBound ε l * ∑ z ∈ regions l, siteOscillation q z B
  have ha (l : ℕ) : 0 ≤ a l :=
    mul_nonneg (localRootChannelShellBound_nonneg ε l)
      (Finset.sum_nonneg fun z _ => siteOscillation_nonneg z B)
  change siteOscillation q y (localRootChannel (regions n) k B) ≤
    siteOscillation q y B +
      2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => y ∈ regions l), a l
  rw [Finset.sum_filter]
  revert hε
  induction n with
  | zero =>
    intro hε
    by_cases hy : y ∈ regions 0
    · have hsplit : localRootChannel (regions 0) k B =
          B + localRootChannelShell regions k 0 B := by
        simp only [localRootChannelShell, add_sub_cancel]
      have hnorm := norm_localRootChannelShell_le_sum_siteOscillation
        regions hregions hk₀ hk₁ ε 0 hε B
      change ‖localRootChannelShell regions k 0 B‖ ≤ a 0 at hnorm
      have hosc := siteOscillation_le_two_mul_norm y (localRootChannelShell regions k 0 B)
      calc
        _ ≤ siteOscillation q y B +
            siteOscillation q y (localRootChannelShell regions k 0 B) := by
          rw [hsplit]
          exact siteOscillation_add_le y _ _
        _ ≤ siteOscillation q y B + 2 * a 0 := by linarith
        _ = _ := by simp [hy]
    · simpa [hy] using
        siteOscillation_localRootChannel_le_of_notMem (regions 0) hk₀ hk₁ y hy B
  | succ n ih =>
    intro hε
    by_cases hy : y ∈ regions (n + 1)
    · have hsplit : localRootChannel (regions (n + 1)) k B =
          localRootChannel (regions n) k B + localRootChannelShell regions k (n + 1) B := by
        simp only [localRootChannelShell, add_sub_cancel]
      have hnorm := norm_localRootChannelShell_le_sum_siteOscillation
        regions hregions hk₀ hk₁ ε (n + 1) hε B
      change ‖localRootChannelShell regions k (n + 1) B‖ ≤ a (n + 1) at hnorm
      have hosc := siteOscillation_le_two_mul_norm y
        (localRootChannelShell regions k (n + 1) B)
      have hprev := ih fun l hl => hε l (hl.trans (Nat.le_succ n))
      calc
        _ ≤ siteOscillation q y (localRootChannel (regions n) k B) +
            siteOscillation q y (localRootChannelShell regions k (n + 1) B) := by
          rw [hsplit]
          exact siteOscillation_add_le y _ _
        _ ≤ (siteOscillation q y B +
              2 * ∑ l ∈ Finset.range (n + 1), if y ∈ regions l then a l else 0) +
            2 * a (n + 1) := by linarith
        _ = _ := by
          rw [Finset.sum_range_succ (n := n + 1)]
          simp only [hy, ite_true, mul_add, add_assoc]
    · apply (siteOscillation_localRootChannel_le_of_notMem
        (regions (n + 1)) hk₀ hk₁ y hy B).trans
      apply le_add_of_nonneg_right
      exact mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun l _ => by split_ifs <;> [exact ha l; exact le_rfl])

end TNLean.PEPS.AreaLaw
