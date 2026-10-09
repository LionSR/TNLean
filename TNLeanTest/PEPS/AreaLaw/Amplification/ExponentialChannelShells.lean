import TNLean.PEPS.AreaLaw.Amplification.ExponentialChannelShells

/-! Boundary consumers for explicit stretched-exponential channel-shell bounds. -/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit TNLean.PEPS.AreaLaw Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

-- The zeroth coefficient remains two even when every localization error vanishes.
example {c α : ℝ} (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    localRootChannelShellBound (fun j => 0 * Real.exp (-(c * (j : ℝ) ^ α))) 0 ≤ 2 := by
  simpa only [Real.sqrt_zero, mul_zero, zero_mul, add_zero, Nat.cast_zero,
    Real.zero_rpow hα.ne', neg_zero, Real.exp_zero, mul_one] using
    localRootChannelShellBound_le_exp (C := 0) le_rfl hc hα hα₁ 0

-- The first successor includes the radius-zero localization error.
example {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    4 * (Real.sqrt (C * Real.exp (-c)) + Real.sqrt C) ≤
      (2 + 8 * Real.sqrt C * Real.exp (c / 2)) * Real.exp (-(c / 2)) := by
  simpa only [localRootChannelShellBound, Nat.zero_add, Nat.cast_zero, Nat.cast_one,
    Real.one_rpow, Real.zero_rpow hα.ne', mul_one, mul_zero, neg_zero,
    Real.exp_zero] using localRootChannelShellBound_le_exp hC hc hα hα₁ 1

-- Ordinary exponential decay is included at the endpoint alpha = 1.
example {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (l : ℕ) :
    localRootChannelShellBound (fun j => C * Real.exp (-(c * j))) l ≤
      (2 + 8 * Real.sqrt C * Real.exp (c / 2)) * Real.exp (-(c / 2 * l)) := by
  simpa only [Real.rpow_one] using
    localRootChannelShellBound_le_exp hC hc (show (0 : ℝ) < 1 by norm_num) le_rfl l

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

-- No nonempty spectator hypothesis is required for the finite one-event estimate.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (regions l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (B : Matrix ((ι → Fin q) × Fin 0) ((ι → Fin q) × Fin 0) ℂ) :
    siteOscillation q y (localRootChannel (regions n) k B) ≤
      siteOscillation q y B +
        2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => y ∈ regions l),
          ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
            Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
              ∑ z ∈ regions l, siteOscillation q z B :=
  siteOscillation_localRootChannel_le_exp regions hregions hk₀ hk₁ hC hc hα hα₁ n hε y B

-- The filtered sum vanishes for a site outside the terminal region.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (regions l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (hy : y ∉ regions n)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (localRootChannel (regions n) k B) ≤ siteOscillation q y B := by
  have hfilter : (Finset.range (n + 1)).filter (fun l => y ∈ regions l) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    obtain ⟨hl, hyl⟩ := Finset.mem_filter.mp hl
    exact hy (hregions (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) hyl)
  simpa only [hfilter, Finset.sum_empty, mul_zero, add_zero] using
    siteOscillation_localRootChannel_le_exp regions hregions hk₀ hk₁ hC hc hα hα₁ n hε y B

-- An arbitrary spectator-only observable has zero physical shell oscillation.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (l : ℕ)
    (hε : ∀ j ≤ l, ‖k - siteExpectation q (regions j) k‖ ≤
      C * Real.exp (-(c * (j : ℝ) ^ α))) (D : Matrix Aux Aux ℂ) :
    localRootChannelShell regions k l ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ D) = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [siteOscillation_one_kronecker, Finset.sum_const_zero, mul_zero] using
    norm_localRootChannelShell_le_exp_sum_siteOscillation regions hregions hk₀ hk₁
      hC hc hα hα₁ l hε ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ D)

/--
info: 'TNLean.PEPS.AreaLaw.localRootChannelShellBound_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms localRootChannelShellBound_le_exp

/--
info: 'TNLean.PEPS.AreaLaw.norm_localRootChannelShell_le_exp_sum_siteOscillation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_localRootChannelShell_le_exp_sum_siteOscillation

/--
info: 'TNLean.PEPS.AreaLaw.siteOscillation_localRootChannel_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms siteOscillation_localRootChannel_le_exp
