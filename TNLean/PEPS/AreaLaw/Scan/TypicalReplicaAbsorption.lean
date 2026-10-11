/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.SelectedSchmidtEntropyBounds
import TNLean.PEPS.AreaLaw.Scan.BootstrapReplicaAbsorption
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Typical-entropy substitution after the rough replica comparisons

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

noncomputable section
open Filter Matrix
open scoped Topology Matrix ComplexOrder

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
theorem regionalEntropy_le_of_rough_typical_comparisons
    {Λ : Finset (ℤ × ℤ)} {q : ℕ}
    (Ωt : StateSpace Λ q) (hΩt : ‖Ωt‖ = 1)
    (X : Finset (Site Λ))
    (E : Finset (FiniteProduct.Configuration (fun _ : Site Λ => Fin q) X))
    (w : ℝ)
    (hz : 0 < (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E)
    (hE : ∀ i ∈ E,
      Real.exp (-regionalEntropy Λ q Ωt X - w) ≤
          (reducedState_isHermitian Λ q Ωt X).eigenvalues i ∧
        (reducedState_isHermitian Λ q Ωt X).eigenvalues i ≤
          Real.exp (-regionalEntropy Λ q Ωt X + w))
    {C τ a Edef Bsh Bexc : ℝ}
    {F d rᵤ rₗ rₑ : ℕ → ℝ}
    (hC : 0 ≤ C) (hτ : 0 < τ) (hτhalf : τ < 1 / 2)
    (ha : 0 < a) (hEdef : 0 ≤ Edef)
    (hsmall : 2 * C * (τ + Edef / τ) ≤ 1)
    (hrᵤ : Tendsto rᵤ atTop (𝓝 0))
    (hrₗ : Tendsto rₗ atTop (𝓝 0))
    (hrₑ : Tendsto rₑ atTop (𝓝 0))
    (hdefect : ∀ᶠ k in atTop, d k ≤ Edef + rₑ k) :
    let β := fun _ : Site Λ => Fin q
    let split := FiniteProduct.splitEquiv β X
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split Ωt
    let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x =>
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let S := regionalEntropy Λ q Ωt X
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
  have hρ : reducedState Λ q Ωt X = Matrix.partialTraceRight
      (Matrix.vecMulVec ΩX (star ΩX)) :=
    (reducedState_eq_finiteProduct Λ q Ωt X).trans
      (FiniteProduct.reducedPure_eq_partialTrace β Ωt X)
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
  done

end TNLean.PEPS.AreaLaw.Scan
