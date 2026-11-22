/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Real.ExplicitThresholds
import TNLean.PEPS.AreaLaw.BoxExponent.BootstrapParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TNLean.PEPS.AreaLaw.Regions.SelectedSchmidtEntropyBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.Convert

/-!
# Replica limits and entropy absorption in the rectangle bootstrap

At a fixed physical scale, the two rough norm comparisons contain the same
entropy for every replica count. Vanishing remainders can therefore be removed
before the coefficient loss is absorbed. Neither comparison value nor defect
sequence needs to converge. A separate numerical estimate then chooses the
large-scale threshold for the manuscript's defect and auxiliary scales; it is
given explicitly by `bootstrapComparisonLossThreshold`.

The norm comparisons are explicit hypotheses of the scalar theorem. Their
physical proofs, the common vector and label sequence, and the substitutions
of the typical entropy and auxiliary dimension are not supplied by this module.
Those substitutions must already be included in the two additive budgets.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:bootstrap-energy` and `scanner:bootstrap-comparison`,
lines 744–769, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.

## Typical-entropy substitution after the rough replica comparisons

The selected spectral set and its auxiliary vector are formed from one supplied
physical state. The replica limit retains the entropy of that selected vector.
Only afterward is it replaced by the original regional entropy, with the
selected-mass correction included in the additive cost.

The two rough comparisons are explicit hypotheses. Their physical derivation,
the construction of the scanner, and the entropy exponent improvement remain
separate results.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, `comparator:typical-entropies`, lines 37–55, and
`comparator:rough-upper` and `comparator:rough-lower`, lines 154–166, and
`comparator:high-label`, lines 240–270;
`08-scanner.tex`, `scanner:bootstrap-comparison`, lines 755–769, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

open Filter
open scoped Topology

namespace TNLean.PEPS.AreaLaw.Scan

/-- The fixed entropy is bounded after taking the replica limit in both rough
comparisons and using their coefficient margin. The three remainders vanish
at the fixed physical scale; the additive budgets include any typical-entropy
and auxiliary-dimension substitutions.
Source: `08-scanner.tex`, lines 755–769, `scanner:bootstrap-comparison`. -/
theorem entropy_le_of_replica_comparisons
    {S C τ E Bᵤ Bₗ : ℝ} {F d rᵤ rₗ rₑ : ℕ → ℝ}
    (hS : 0 ≤ S) (hC : 0 ≤ C) (hτ : 0 < τ)
    (hsmall : C * (τ + E / τ) ≤ 1)
    (hrᵤ : Tendsto rᵤ atTop (𝓝 0))
    (hrₗ : Tendsto rₗ atTop (𝓝 0))
    (hrₑ : Tendsto rₑ atTop (𝓝 0))
    (hdefect : ∀ᶠ k in atTop, d k ≤ E + rₑ k)
    (hupper : ∀ᶠ k in atTop, F k ≤ 2 * S + Bᵤ + rᵤ k)
    (hlower : ∀ᶠ k in atTop,
      (4 - C * (τ + d k / τ)) * S - Bₗ - rₗ k ≤ F k) :
    S ≤ Bᵤ + Bₗ := by
  have hbound : ∀ᶠ k in atTop,
      (2 - C * (τ + E / τ)) * S ≤
        Bᵤ + Bₗ + rᵤ k + rₗ k + (C / τ) * S * rₑ k := by
    filter_upwards [hdefect, hupper, hlower] with k hd hu hl
    have hquot : d k / τ ≤ (E + rₑ k) / τ :=
      div_le_div_of_nonneg_right hd hτ.le
    have hloss : C * (τ + d k / τ) * S ≤
        C * (τ + (E + rₑ k) / τ) * S :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl τ) hquot) hC) hS
    have hsplit : C * (τ + (E + rₑ k) / τ) * S =
        C * (τ + E / τ) * S + (C / τ) * S * rₑ k := by ring
    rw [hsplit] at hloss
    nlinarith only [hu, hl, hloss]
  have hlimit : Tendsto
      (fun k ↦ Bᵤ + Bₗ + rᵤ k + rₗ k + (C / τ) * S * rₑ k)
      atTop (𝓝 (Bᵤ + Bₗ)) := by
    simpa only [add_zero, mul_zero] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Bᵤ + Bₗ) atTop
        (𝓝 (Bᵤ + Bₗ))).add hrᵤ).add hrₗ).add (hrₑ.const_mul ((C / τ) * S))
  have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds hlimit hbound
  have hmargin : 1 ≤ 2 - C * (τ + E / τ) := by linarith only [hsmall]
  exact (le_mul_of_one_le_left hS hmargin).trans hlim

/-- The explicit threshold `⌈max 1 (max 3 (C (1 + Cₑ)) ^ (4 / ν))⌉₊` beyond which
`n ^ (ν / 4) ≥ max 3 (C (1 + Cₑ))`, with `ν = ν(e₀)` the fixed bootstrap error exponent
(`08-scanner.tex`, lines 744–769). -/
noncomputable def bootstrapComparisonLossThreshold (C Cₑ e₀ : ℝ) : ℕ :=
  Real.natRpowThreshold (BootstrapParameters.nu e₀ / 4) (max 3 (C * (1 + Cₑ)))

/-- With the fixed bootstrap error exponent, at every `n` from the explicit threshold
`bootstrapComparisonLossThreshold C Cₑ e₀` on, the relative coefficient loss is at most one
and the auxiliary fraction lies below one half.
Source: `08-scanner.tex`, lines 744–769, `scanner:bootstrap-energy`. -/
theorem bootstrap_comparison_loss_of_threshold_le (C Cₑ : ℝ) {e₀ : ℝ}
    (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) {n : ℕ}
    (hthr : bootstrapComparisonLossThreshold C Cₑ e₀ ≤ n) :
    let τ := (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4)
    let E := Cₑ * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2)
    0 < τ ∧ τ < 1 / 2 ∧ C * (τ + E / τ) ≤ 1 := by
  obtain ⟨hg₀, _, _, _, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  have hν₄ : 0 < BootstrapParameters.nu e₀ / 4 := div_pos (div_pos hg₀ (by norm_num)) (by norm_num)
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Real.one_le_natRpowThreshold _ _).trans hthr
  have hpow := Real.le_natCast_rpow_of_natRpowThreshold_le hν₄ hthr
  have hP : 0 < (n : ℝ) ^ (BootstrapParameters.nu e₀ / 4) := Real.rpow_pos_of_pos hnpos _
  have hτ : (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4) =
      ((n : ℝ) ^ (BootstrapParameters.nu e₀ / 4))⁻¹ := by
    rw [neg_div, Real.rpow_neg hnpos.le]
  dsimp only
  refine ⟨Real.rpow_pos_of_pos hnpos _, ?_, ?_⟩
  · rw [hτ, inv_lt_comm₀ hP (by norm_num)]
    linarith [le_max_left 3 (C * (1 + Cₑ))]
  have hsplit : C * ((n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4) +
      Cₑ * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2) /
        (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4)) =
      C * (1 + Cₑ) * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4) := by
    rw [mul_div_assoc, ← Real.rpow_sub hnpos,
      show -BootstrapParameters.nu e₀ / 2 - (-BootstrapParameters.nu e₀ / 4) =
        -BootstrapParameters.nu e₀ / 4 by ring]
    ring
  rw [hsplit, hτ, ← div_eq_mul_inv, div_le_one hP]
  exact (le_max_right _ _).trans hpow

/-- With the fixed bootstrap error exponent, one threshold makes the relative
coefficient loss at most one and the auxiliary fraction lie below one half.
This threshold is chosen after the fixed-scale
replica limit; it requires no replica convergence rate uniform in the scale.
Source: `08-scanner.tex`, lines 744–769, `scanner:bootstrap-energy`. -/
theorem exists_bootstrap_comparison_loss_threshold (C Cₑ : ℝ) {e₀ : ℝ}
    (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let τ := (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 4)
      let E := Cₑ * (n : ℝ) ^ (-BootstrapParameters.nu e₀ / 2)
      0 < τ ∧ τ < 1 / 2 ∧ C * (τ + E / τ) ≤ 1 :=
  ⟨_, Real.one_le_natRpowThreshold _ _,
    fun _ => bootstrap_comparison_loss_of_threshold_le C Cₑ he₀ he₀₁⟩

end TNLean.PEPS.AreaLaw.Scan

end

section

noncomputable section
open Filter Matrix
open scoped Topology Matrix ComplexOrder
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

open Classical in
/-- The rough comparisons for one selected Schmidt spectrum bound the original
regional entropy after the fixed-system replica limit. The substitution cost
is \(7(w-\log z)\), in addition to the original \(-\log z\) term in the upper comparison.
The comparison value and defect sequence need not converge, and no bound of
the defect by the auxiliary fraction is assumed.
Source: `07-comparators.tex`, `comparator:typical-entropies`, lines 37–55,
and `comparator:rough-upper` and `comparator:rough-lower`, lines 154–166, and
`comparator:high-label`, lines 240–270;
`08-scanner.tex`, `scanner:bootstrap-comparison`, lines 755–769. -/
theorem regionEntropy_le_of_rough_typical_comparisons
    {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1)
    (X : Finset (Site Λ))
    (E : Finset (ManyBody.RegionConfig (fun _ : Site Λ => Fin q) X))
    (w : ℝ)
    (hz : 0 < (ManyBody.regionState_isHermitian X Ωt).spectralRestrictionMass E)
    (hE : ∀ i ∈ E,
      Real.exp (-ManyBody.regionEntropy Ωt X - w) ≤
          (ManyBody.regionState_isHermitian X Ωt).eigenvalues i ∧
        (ManyBody.regionState_isHermitian X Ωt).eigenvalues i ≤
          Real.exp (-ManyBody.regionEntropy Ωt X + w))
    {C τ a Edef Bsh Bexc : ℝ}
    {F d rᵤ rₗ rₑ : ℕ → ℝ}
    (hC : 0 ≤ C) (hτ : 0 < τ) (_hτhalf : τ < 1 / 2)
    (_ha : 0 < a) (hEdef : 0 ≤ Edef)
    (hsmall : 2 * C * (τ + Edef / τ) ≤ 1)
    (hrᵤ : Tendsto rᵤ atTop (𝓝 0))
    (hrₗ : Tendsto rₗ atTop (𝓝 0))
    (hrₑ : Tendsto rₑ atTop (𝓝 0))
    (hdefect : ∀ᶠ k in atTop, d k ≤ Edef + rₑ k) :
    let β := fun _ : Site Λ => Fin q
    let split := ManyBody.cutEquiv β X
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split Ωt
    let z := (ManyBody.regionState_isHermitian X Ωt).spectralRestrictionMass E
    let ψ : ManyBody.ComplConfig β X × Fin E.card → ℂ := fun x =>
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let S := ManyBody.regionEntropy Ωt X
    let S' := vonNeumannEntropy
      (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
      (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
    let η := w - Real.log z
    (∀ᶠ k in atTop,
      F k ≤ 2 * Real.log (E.card : ℝ) - Real.log z +
        4 * Bsh / z + 4 * Bexc + rᵤ k) →
    (∀ᶠ k in atTop,
      4 * S' - 2 * C * (τ * Real.log (E.card : ℝ) + Real.binEntropy τ / a) -
        C * (d k / τ) * max 0 (2 * S') - rₗ k ≤ F k) →
    S ≤ 7 * η - Real.log z + 4 * Bsh / z + 4 * Bexc +
      2 * C * Real.binEntropy τ / a := by
  intro β split ΩX z ψ S S' η hupper hlower
  have hbounds := TNLean.PEPS.AreaLaw.abs_log_card_and_selectedSchmidtEntropy_sub_le
    Ωt hΩt X E w hz hE
  have hρ : ManyBody.regionState Ωt X = Matrix.partialTraceRight
      (Matrix.vecMulVec ΩX (star ΩX)) :=
    ManyBody.regionState_eq_partialTraceRight_cutVector X Ωt
  have hS' : 0 ≤ S' :=
    let hp := (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight
    let hzX : 0 < hp.isHermitian.spectralRestrictionMass E :=
      by simpa only [← hρ] using hz
    (vonNeumannEntropy_nonneg_of_posSemidef_trace_one
      (hp.normalizedSpectralRestriction_posSemidef E hzX)
      (hp.isHermitian.trace_normalizedSpectralRestriction E hzX.ne')).trans_eq
        (Matrix.entropy_compressedTypicalPureState_equivFin_swap ΩX E hzX).symm
  have hupper' : ∀ᶠ k in atTop,
      F k ≤ 2 * S' +
        (2 * Real.log (E.card : ℝ) - 2 * S' - Real.log z +
          4 * Bsh / z + 4 * Bexc) + rᵤ k :=
    hupper.mono fun k hk ↦ by linarith only [hk]
  have hlower_nonmax : ∀ᶠ k in atTop,
      4 * S' - 2 * C * (τ * Real.log (E.card : ℝ) + Real.binEntropy τ / a) -
        C * (d k / τ) * (2 * S') - rₗ k ≤ F k :=
    hlower.mono fun k hk ↦ by
      simpa only [max_eq_right
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS')] using hk
  have hlower' : ∀ᶠ k in atTop,
      (4 - (2 * C) * (τ + d k / τ)) * S' -
        (2 * C * τ * (Real.log (E.card : ℝ) - S') +
          2 * C * Real.binEntropy τ / a) - rₗ k ≤ F k :=
    hlower_nonmax.mono fun k hk ↦ by convert hk using 1; ring
  have hscalar := entropy_le_of_replica_comparisons
    hS' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
    hτ hsmall hrᵤ hrₗ hrₑ hdefect hupper' hlower'
  have hcost : (2 + 2 * C * τ) * (Real.log (E.card : ℝ) - S') ≤ 6 * η := by
    have hη0 : 0 ≤ η :=
      (abs_nonneg (Real.log (E.card : ℝ) - S)).trans hbounds.1
    have hτloss : 2 * C * τ ≤ 1 := by
      nlinarith only [hsmall, mul_nonneg hC (div_nonneg hEdef hτ.le)]
    have hdiff : Real.log (E.card : ℝ) - S' ≤ 2 * η := by
      linarith only [(abs_le.mp hbounds.1).2, (abs_le.mp hbounds.2).1]
    calc
      (2 + 2 * C * τ) * (Real.log (E.card : ℝ) - S') ≤
          (2 + 2 * C * τ) * (2 * η) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ ≤ 3 * (2 * η) :=
        mul_le_mul_of_nonneg_right (by linarith only [hτloss]) (by positivity)
      _ = 6 * η := by ring
  nlinarith only [hscalar, hcost, (abs_le.mp hbounds.2).1]

end TNLean.PEPS.AreaLaw.Scan
end

end
