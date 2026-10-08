/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs

/-!
# Selection of a low-defect charge point

Normalizing the integrated entropy inequality by the `nm` charge rounds and the interval length
`ε/2`, and averaging, selects a charge round and a parameter `p_k ∈ [ε/2, ε]` with
`𝒬(p_k)/(KnD) ≤ δ_n + o_k(1)` (`scanner:selected-density`).

## Main results

* `TNLean.PEPS.AreaLaw.Scan.exists_mem_Icc_le_of_sum_integral_le`: averaging over finitely many
  continuous functions on an interval.
* `TNLean.PEPS.AreaLaw.Scan.tendsto_log_div_nat`: `log (k + 2) / k → 0`.
* `TNLean.PEPS.AreaLaw.Scan.exists_selected_density`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  section file `08-scanner.tex`, lines 471–490 and 529–532.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open Filter Topology Set Asymptotics

/-- Averaging: if the integrals of finitely many continuous functions over `[α, β]` sum to at
most `|T| (β - α) c`, one of them takes a value at most `c` somewhere on `[α, β]`
(lines 480–490). -/
theorem exists_mem_Icc_le_of_sum_integral_le {R : ℕ} (Q : Fin R → ℝ → ℝ) (T : Finset (Fin R))
    (hT : T.Nonempty) {α β c : ℝ} (hαβ : α < β)
    (hcont : ∀ r ∈ T, ContinuousOn (Q r) (Icc α β))
    (h : ∑ r ∈ T, ∫ p in α..β, Q r p ≤ T.card * ((β - α) * c)) :
    ∃ r ∈ T, ∃ p ∈ Icc α β, Q r p ≤ c := by
  rw [← nsmul_eq_mul, ← Finset.sum_const] at h
  obtain ⟨r, hr, hle⟩ := Finset.exists_le_of_sum_le hT h
  refine ⟨r, hr, ?_⟩
  obtain ⟨p₀, hp₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hαβ.le) (hcont r hr)
  refine ⟨p₀, hp₀, ?_⟩
  by_contra hlt
  push Not at hlt
  have hint : ∫ p in α..β, Q r p₀ ≤ ∫ p in α..β, Q r p :=
    intervalIntegral.integral_mono_on hαβ.le intervalIntegrable_const
      ((hcont r hr).intervalIntegrable_of_Icc hαβ.le) fun x hx ↦ hmin hx
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  nlinarith [sub_pos.2 hαβ]

/-- `log (k + 2) / k → 0`: the replica floor `β_k = O(log(k+2))` does not survive the
normalization by `k` (lines 452–455). -/
theorem tendsto_log_div_nat :
    Tendsto (fun k : ℕ ↦ Real.log (k + 2) / k) atTop (𝓝 0) := by
  have h2 : Tendsto (fun k : ℕ ↦ (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hO : (fun k : ℕ ↦ (k : ℝ) + 2) =O[atTop] fun k : ℕ ↦ (k : ℝ) := by
    refine IsBigO.of_bound 3 ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    linarith
  exact ((Real.isLittleO_log_id_atTop.comp_tendsto h2).trans_isBigO hO).tendsto_div_nhds_zero

/-- Among the residues below `2N`, exactly `N` are odd. -/
theorem card_filter_odd {R N : ℕ} (h : R = 2 * N) :
    (Finset.univ.filter fun r : Fin R ↦ (r : ℕ) % 2 = 1).card = N := by
  rw [← Finset.card_fin N]
  refine (Finset.card_bij' (s := (Finset.univ : Finset (Fin N)))
    (fun (i : Fin N) _ ↦ (⟨2 * i + 1, by omega⟩ : Fin R))
    (fun (r : Fin R) _ ↦ (⟨r / 2, by have := r.isLt; omega⟩ : Fin N)) ?_ ?_ ?_ ?_).symm
  · intro i _; simp
  · intro r _; simp
  · intro i _; ext; simp; omega
  · intro r hr; simp at hr; ext; simp; omega

/-- There are exactly `nm` charge rounds among the `2nm` rounds (lines 106–107). -/
theorem card_chargeRounds (X : ScannerExponents) (n : ℕ) :
    (X.chargeRounds n).card = n * X.m n :=
  card_filter_odd (by unfold ScannerExponents.rounds; ring)

/-- The selected density bound `scanner:selected-density` (lines 471–490). For fixed scale
constants, uniformly in the scan data at every sufficiently large `n`, the integrated entropy
inequality at `k` yields a charge round and a common `p_k ∈ [ε/2, ε]` with
`𝒬(p_k)/(KnD) ≤ δ_n + ρ_k`, where `ρ_k → 0` depends on the fixed data but not on the selected
round or parameter (lines 393–395, 529–532). -/
theorem exists_selected_density (X : ScannerExponents) (κ : ScanConstants) (C₁ C_T : ℝ) :
    ∃ Cδ : ℝ, 0 ≤ Cδ ∧ ∀ᶠ n in atTop, ScaleFacts X n C₁ → ∀ S : ScanData X κ n,
      S.terminalBound ≤ C_T * X.W * (n : ℝ) ^ (1 + X.e) →
      ∃ ρ : ℕ → ℝ, (∀ k, 0 ≤ ρ k) ∧ Tendsto ρ atTop (𝓝 0) ∧
        ∀ k, 1 ≤ k → S.IntegratedChargeBound k →
          ∃ r ∈ X.chargeRounds n, ∃ p ∈ Icc (X.eps n / 2) (X.eps n),
            (S.round r).chargeDefect k p / (X.K n * n * X.D n) ≤ X.delta Cδ κ.Cl n + ρ k := by
  have hc := κ.c_pos
  refine ⟨2 * |C_T| * |C₁| / κ.c + 4 * κ.C / κ.c,
    by have := κ.one_le_C; positivity, Eventually.of_forall fun n hF S hT ↦ ?_⟩
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hF.two_le_n
  have hm : (1 : ℝ) ≤ X.m n := by exact_mod_cast hF.one_le_m
  have hK : (1 : ℝ) ≤ X.K n := by exact_mod_cast hF.one_le_K
  have hD : (1 : ℝ) ≤ X.D n := by exact_mod_cast hF.one_le_D
  have hε := hF.eps_pos
  have hW : 1 ≤ X.W := X.one_le_W
  have haK : X.a n * X.K n = X.W := by
    unfold ScannerExponents.a; field_simp
  set M : ℝ := X.W * κ.c * n * X.m n * X.eps n / 2 with hM
  have hMpos : 0 < M := by positivity
  set R : ℝ := ((X.rounds n : ℕ) : ℝ) with hR
  have hR2 : R = 2 * n * X.m n := by simp [hR, ScannerExponents.rounds]
  refine ⟨fun k ↦ (S.rem k + (1 + R) * S.β k / k) / M, fun k ↦ ?_, ?_, ?_⟩
  · have := S.rem_nonneg k; have := S.β_nonneg k; positivity
  · have hβ : Tendsto (fun k : ℕ ↦ S.β k / k) atTop (𝓝 0) := by
      have hlim := (tendsto_log_div_nat.const_mul S.Cβ)
      rw [mul_zero] at hlim
      refine squeeze_zero (fun k ↦ div_nonneg (S.β_nonneg k) k.cast_nonneg) (fun k ↦ ?_) hlim
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (S.β_le k) k.cast_nonneg
    have := ((S.tendsto_rem.add (hβ.const_mul (1 + R))).div_const M)
    simp only [add_zero, mul_zero, zero_div] at this
    simpa only [mul_div_assoc] using this
  intro k hk hI
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set δ := X.delta (2 * |C_T| * |C₁| / κ.c + 4 * κ.C / κ.c) κ.Cl n with hδ
  set ρk := (S.rem k + (1 + R) * S.β k / k) / M with hρk
  have hKnD : 0 < (X.K n : ℝ) * n * X.D n := by positivity
  have hcard := card_chargeRounds X n
  have hne : (X.chargeRounds n).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.mul_pos (by have := hF.two_le_n; omega) hF.one_le_m
  have hsub : Icc (X.eps n / 2) (X.eps n) ⊆ Ioo 0 1 := fun p hp ↦
    ⟨by linarith [hp.1], by linarith [hp.2, hF.eps_lt_one]⟩
  -- The normalization of the integrated inequality (lines 476–484).
  set Ssum := ∑ r ∈ X.chargeRounds n, ∫ p in (X.eps n / 2)..(X.eps n), (S.round r).chargeDefect k p
  have hA : 0 < k * X.a n * (κ.c / (n * X.D n)) := by
    unfold ScannerExponents.a; positivity
  set P : ℝ := (n : ℝ) ^ (X.e - X.mu)
  set A4 : ℝ := X.a n ^ (1 / 4 : ℝ)
  set Lg : ℝ := Real.log n ^ κ.Cl
  have hP : 0 ≤ P := by positivity
  have hA4 : 0 ≤ A4 := by unfold A4 ScannerExponents.a; positivity
  have hLg : 0 ≤ Lg := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  -- The terminal term: `T ≤ |C_T| W n m |C₁| n^{e-μ}`.
  have hne' : (n : ℝ) ^ X.e ≤ X.m n * (|C₁| * P) := by
    have h1 := hF.pow_e_div_m_le
    rw [div_le_iff₀ (by linarith)] at h1
    calc (n : ℝ) ^ X.e ≤ C₁ * P * X.m n := h1
      _ ≤ |C₁| * P * X.m n := by gcongr; exact le_abs_self _
      _ = _ := by ring
  have hTb : S.terminalBound ≤ |C_T| * X.W * n * X.m n * |C₁| * P := by
    have h1 : (n : ℝ) ^ (1 + X.e) = n * (n : ℝ) ^ X.e := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have h2 : C_T * X.W * (n : ℝ) ^ (1 + X.e) ≤ |C_T| * X.W * (n * (X.m n * (|C₁| * P))) := by
      rw [h1]
      apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
        (mul_le_mul_of_nonneg_left hne' (by linarith)) (by positivity) (by positivity)
    nlinarith
  have hδM : M * δ = X.W * n * X.m n * (|C_T| * |C₁| + 2 * κ.C) * (P + A4 * Lg) := by
    rw [hδ, hM, ScannerExponents.delta]
    field_simp
    ring
  have hkey : S.β k + k * (S.terminalBound + S.rem k) +
      R * (κ.C * k * X.a n * X.K n * A4 * Lg + S.β k) ≤ k * M * (δ + ρk) := by
    have hρ : k * M * ρk = k * S.rem k + (1 + R) * S.β k := by
      rw [hρk]; field_simp
    have hC := κ.one_le_C
    have hcross : 0 ≤ X.W * n * X.m n * (|C_T| * |C₁| * A4 * Lg + 2 * κ.C * P) := by
      positivity
    have h3 : k * (X.W * n * X.m n * (|C_T| * |C₁| + 2 * κ.C) * (P + A4 * Lg)) ≥
        k * (|C_T| * X.W * n * X.m n * |C₁| * P) + R * (κ.C * k * X.W * A4 * Lg) := by
      rw [hR2]; nlinarith
    have h4 : κ.C * k * X.a n * X.K n * A4 * Lg = κ.C * k * X.W * A4 * Lg := by
      rw [← haK]; ring
    have h5 : (k : ℝ) * M * (δ + ρk) = k * (M * δ) + k * M * ρk := by ring
    have hkT := mul_le_mul_of_nonneg_left hTb (Nat.cast_nonneg (α := ℝ) k)
    rw [h5, hρ, hδM, h4]
    linarith
  have hmain : k * X.a n * (κ.c / (n * X.D n)) * Ssum ≤
      k * X.a n * (κ.c / (n * X.D n)) *
        (((X.chargeRounds n).card : ℝ) * ((X.eps n - X.eps n / 2) *
          (X.K n * n * X.D n * (δ + ρk)))) := by
    refine hI.trans (le_of_le_of_eq hkey ?_)
    rw [hcard, hM]; push_cast
    have : X.a n * X.K n = X.W := haK
    field_simp
    rw [← this]; ring
  obtain ⟨r, hr, p, hp, hQ⟩ := exists_mem_Icc_le_of_sum_integral_le
    (fun r ↦ (S.round r).chargeDefect k) (X.chargeRounds n) hne (by linarith)
    (fun r _ ↦ (S.continuousOn_chargeDefect r k).mono hsub)
    (c := X.K n * n * X.D n * (δ + ρk)) (le_of_mul_le_mul_left hmain hA)
  exact ⟨r, hr, p, hp, by rw [div_le_iff₀ hKnD]; linarith⟩

end TNLean.PEPS.AreaLaw.Scan
