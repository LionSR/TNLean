import TNLean.PEPS.AreaLaw.Amplification.LocalChannelOscillation

/-! Boundary consumers for the actual finite local-channel increment. -/

open QuantumCircuit TNLean.PEPS.AreaLaw Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

-- The inclusive zeroth radius retains the factor four and its membership test.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (localRootChannel (regions 0) k B) ≤ siteOscillation q y B +
      if y ∈ regions 0 then 4 * ∑ z ∈ regions 0, siteOscillation q z B else 0 := by
  classical
  simpa [Finset.sum_filter, localRootChannelShellBound, mul_ite, ← mul_assoc,
    show (2 : ℝ) * 2 = 4 by norm_num] using
    siteOscillation_localRootChannel_le regions hregions hk₀ hk₁
      (fun l => ‖k - siteExpectation q (regions l) k‖) 0 (fun _ _ => le_rfl) y B

-- Empty regions have no contributing shells at any cutoff.
example {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (n : ℕ) (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (localRootChannel ∅ k B) ≤ siteOscillation q y B := by
  simpa using siteOscillation_localRootChannel_le (fun _ => ∅)
    (fun _ _ _ => Finset.Subset.refl _) hk₀ hk₁
    (fun _ => ‖k - siteExpectation q ∅ k‖) n (fun _ _ => le_rfl) y B

-- A site outside the terminal region is excluded from every shell in the sum.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (n : ℕ) (y : ι) (hy : y ∉ regions n)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (localRootChannel (regions n) k B) ≤ siteOscillation q y B := by
  have hfilter : (Finset.range (n + 1)).filter (fun l => y ∈ regions l) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    obtain ⟨hl, hyl⟩ := Finset.mem_filter.mp hl
    exact hy (hregions (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) hyl)
  simpa only [hfilter, Finset.sum_empty, mul_zero, add_zero] using
    siteOscillation_localRootChannel_le regions hregions hk₀ hk₁
      (fun l => ‖k - siteExpectation q (regions l) k‖) n (fun _ _ => le_rfl) y B

-- No nonemptiness requirement is hidden in the spectator dimension.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (ε : ℕ → ℝ) (n : ℕ)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (regions l) k‖ ≤ ε l)
    (y : ι) (B : Matrix ((ι → Fin q) × Fin 0) ((ι → Fin q) × Fin 0) ℂ) :
    siteOscillation q y (localRootChannel (regions n) k B) ≤ siteOscillation q y B +
      2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l => y ∈ regions l),
        localRootChannelShellBound ε l * ∑ z ∈ regions l, siteOscillation q z B :=
  siteOscillation_localRootChannel_le regions hregions hk₀ hk₁ ε n hε y B

-- A spectator-only observable can be arbitrary, including non-Hermitian.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (n : ℕ) (y : ι) (C : Matrix Aux Aux ℂ) :
    siteOscillation q y
      (localRootChannel (regions n) k ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C)) =
      0 := by
  apply le_antisymm _ (siteOscillation_nonneg y _)
  simpa only [siteOscillation_one_kronecker, Finset.sum_const_zero, mul_zero, add_zero] using
    siteOscillation_localRootChannel_le regions hregions hk₀ hk₁
      (fun l => ‖k - siteExpectation q (regions l) k‖) n (fun _ _ => le_rfl) y
      ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ C)

-- Actual zero errors eliminate successor shells but preserve the base contribution.
example (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hlocal : k ∈ supportedOperators q (regions 0 : Set ι))
    (n : ℕ) (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (localRootChannel (regions n) k B) ≤ siteOscillation q y B +
      if y ∈ regions 0 then 4 * ∑ z ∈ regions 0, siteOscillation q z B else 0 := by
  classical
  have herror (l : ℕ) : ‖k - siteExpectation q (regions l) k‖ ≤ (0 : ℝ) := by
    have hlocal' : k ∈ supportedOperators q (regions l : Set ι) :=
      supportedOperators_mono (by exact hregions (Nat.zero_le l)) hlocal
    simp [siteExpectation_of_mem_supportedOperators (regions l) hlocal']
  have hsum (m : ℕ) :
      (∑ l ∈ Finset.range (m + 1), if y ∈ regions l then
        localRootChannelShellBound (fun _ => 0) l * ∑ z ∈ regions l, siteOscillation q z B
        else 0) = if y ∈ regions 0 then 2 * ∑ z ∈ regions 0, siteOscillation q z B else 0 := by
    induction m with
    | zero => simp [localRootChannelShellBound]
    | succ m ih =>
      rw [Finset.sum_range_succ (n := m + 1)]
      simpa [localRootChannelShellBound] using ih
  have h := siteOscillation_localRootChannel_le regions hregions hk₀ hk₁
    (fun _ => 0) n (fun l _ => herror l) y B
  rw [Finset.sum_filter, hsum] at h
  simpa [mul_ite, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using h

/--
info: 'TNLean.PEPS.AreaLaw.localRootChannelShellBound' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms localRootChannelShellBound

/--
info: 'TNLean.PEPS.AreaLaw.localRootChannelShellBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms localRootChannelShellBound_nonneg

/--
info: 'TNLean.PEPS.AreaLaw.norm_localRootChannelShell_le_sum_siteOscillation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms norm_localRootChannelShell_le_sum_siteOscillation

/--
info: 'TNLean.PEPS.AreaLaw.siteOscillation_localRootChannel_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms siteOscillation_localRootChannel_le
