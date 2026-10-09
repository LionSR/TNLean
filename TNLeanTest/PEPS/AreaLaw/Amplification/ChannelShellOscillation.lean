/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelShellOscillation

/-! Edge cases and raw-backed axiom guards for actual shell oscillations. -/

open QuantumCircuit TNLean.PEPS.AreaLaw Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

-- Averaging the entire physical system removes the zeroth shell error.
example {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannelShell (fun _ => ∅) k 0 B = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa using norm_localRootChannelShell_zero_le_sum_siteOscillation
    (fun _ => ∅) (fun _ _ _ => Finset.Subset.refl _) hk₀ hk₁ B

-- A non-Hermitian spectator-only operator has no physical oscillation.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (C : Matrix Aux Aux ℂ) :
    localRootChannelShell regions k 0 ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C) =
      0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [siteOscillation_one_kronecker, Finset.sum_const_zero, mul_zero] using
    norm_localRootChannelShell_zero_le_sum_siteOscillation regions hregions hk₀ hk₁
      ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C)

-- Exact localization at both radii forces the actual successor shell to vanish.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (l : ℕ) (hNext : siteExpectation q (regions (l + 1)) k = k)
    (hPrev : siteExpectation q (regions l) k = k)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannelShell regions k (l + 1) B = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa using norm_localRootChannelShell_succ_le_sum_siteOscillation regions hregions
    hk₀ hk₁ l (εNext := 0) (εPrev := 0) (by simp [hNext]) (by simp [hPrev]) B

-- The off-region bound also includes the zero-dimensional spectator.
example (K : Finset ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (y : ι) (hy : y ∉ K)
    (B : Matrix ((ι → Fin q) × Fin 0) ((ι → Fin q) × Fin 0) ℂ) :
    siteOscillation q y (localRootChannel K k B) ≤ siteOscillation q y B :=
  siteOscillation_localRootChannel_le_of_notMem K hk₀ hk₁ y hy B

/--
info: 'TNLean.PEPS.AreaLaw.siteOscillation_localRootChannel_le_of_notMem' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms siteOscillation_localRootChannel_le_of_notMem
/--
info: 'TNLean.PEPS.AreaLaw.norm_localRootChannelShell_zero_le_sum_siteOscillation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_localRootChannelShell_zero_le_sum_siteOscillation
/--
info: 'TNLean.PEPS.AreaLaw.norm_localRootChannelShell_succ_le_sum_siteOscillation' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_localRootChannelShell_succ_le_sum_siteOscillation
