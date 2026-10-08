/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Budgets
import TNLean.PEPS.AreaLaw.Scan.EntropyBalance
import TNLean.PEPS.AreaLaw.Scan.Selection
import TNLean.PEPS.AreaLaw.Scan.EnergyBalance

/-!
# The scanner estimate (Proposition 9.2)

Assembly of Proposition 9.2 (`prop:scanner`) from the integrated entropy balance, the
selection of a low-defect charge point, the energy accounting at that point, and the
comparator budgets.

**Scope restriction (inputs as hypotheses):** the conclusions of Lemma 9.1
(`scanner:histories`), Proposition 7.4 (`prop:transport`), Proposition 8.1
(`prop:comparators`), Lemma 2.1 (`lem:continuity`) and Lemma 2.3 (`lem:tail`) for the concrete
scan are the fields of `ScanData`; this module proves the step of the source from those
conclusions to Proposition 9.2. The theorem becomes the source statement once a `ScanData` is
constructed from the scan geometry and the transported states.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.scanner_estimate`: Proposition 9.2.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 9.2, section file `08-scanner.tex`, lines 349–533.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open Filter Topology Set

/-- **Proposition 9.2** (the scanner estimate, `08-scanner.tex`, lines 349–397). For all
sufficiently large `n` and every scan at scale `n`, the comparator budgets
`B_sh ≤ C_b (n L^e + n)`, `B_exc ≤ C_b n D`, `𝓑 ≤ C_b n D (log n)^{C_{lb}}` hold, and there is a
remainder `ρ_k → 0`, uniform over the selected round and parameter, such that for every
replica count `k ≥ 1` some charge round and common `p_k ∈ [ε/2, ε]` satisfy
`𝒬(p_k)/(KnD) ≤ δ_n + ρ_k` (`scanner:selected-density`) and
`E_def ≤ C n^ℓ D² W² (log n)^{C_l} (δ_n^{1/8} + ε + n^{-100}) + C n^{-1000} + ρ_k`
(`scanner:energy-output`). The constants depend only on the fixed exponents and on the
constants `κ` of the inputs. -/
theorem scanner_estimate (X : ScannerExponents) (κ : ScanConstants) :
    ∃ Cb Clb C Cl Cδ : ℝ, ∀ᶠ n in atTop, ∀ S : ScanData X κ n,
      (S.Bsh ≤ Cb * (n * (X.L n : ℝ) ^ X.e + n) ∧ S.Bexc ≤ Cb * n * X.D n ∧
        S.Bmarg ≤ Cb * n * X.D n * Real.log n ^ Clb) ∧
      ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k, 1 ≤ k →
        ∃ r ∈ X.chargeRounds n, ∃ p ∈ Icc (X.eps n / 2) (X.eps n),
          (S.round r).chargeDefect k p / (X.K n * n * X.D n) ≤ X.delta Cδ κ.Cl n + ρ k ∧
          S.defectEnergy r k p ≤
            C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * X.W ^ 2 * Real.log n ^ Cl *
                (X.delta Cδ κ.Cl n ^ (1 / 8 : ℝ) + X.eps n + (n : ℝ) ^ (-100 : ℝ)) +
              C * (n : ℝ) ^ (-1000 : ℝ) + ρ k := by
  obtain ⟨C₁, hC₁⟩ := eventually_scaleFacts X
  obtain ⟨Cb, Clb, hB⟩ := exists_budgets X κ
  obtain ⟨Cδ, hCδ, hsel⟩ := exists_selected_density X κ C₁ Cb
  obtain ⟨C, Cl, hE⟩ := exists_defectEnergy_le X κ C₁ Cδ hCδ
  refine ⟨Cb, Clb, C, Cl, Cδ, ?_⟩
  filter_upwards [hC₁, hB, hsel, hE] with n hfacts hb hs he
  intro S
  obtain ⟨hBsh, hBexc, hBmarg, hT⟩ := hb S
  refine ⟨⟨hBsh, hBexc, hBmarg⟩, ?_⟩
  obtain ⟨ρ, hρ0, hρ, hρsel⟩ := hs hfacts S hT
  obtain ⟨Λ, hΛ, hΛE⟩ := he hfacts S
  have hρ8 : Tendsto (fun k ↦ ρ k ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    simpa [Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0)] using
      hρ.rpow_const (p := (1 / 8 : ℝ)) (Or.inr (by norm_num))
  refine ⟨fun k ↦ ρ k + Λ * (S.rem k + ρ k ^ (1 / 8 : ℝ)), ?_, ?_⟩
  · simpa using hρ.add ((S.tendsto_rem.add hρ8).const_mul Λ)
  intro k hk
  obtain ⟨r, hr, p, hp, hQ⟩ := hρsel k hk (S.integratedChargeBound hfacts k hk)
  have hextra : 0 ≤ Λ * (S.rem k + ρ k ^ (1 / 8 : ℝ)) :=
    mul_nonneg hΛ (add_nonneg (S.rem_nonneg k) (Real.rpow_nonneg (hρ0 k) _))
  refine ⟨r, hr, p, hp, by linarith, ?_⟩
  have := hΛE r k p (ρ k) hp (hρ0 k) hQ
  linarith [hρ0 k]

end TNLean.PEPS.AreaLaw.Scan
