/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TwoFamilies
import QICLean.Entropy.SelectedSchmidtEntropy

/-!
# Entropy and dimension of a supplied selected Schmidt spectrum

The selected vector is formed from the given physical state and spectral set.
Its auxiliary entropy and the logarithm of the selected dimension are compared
with the original regional entropy, retaining the selected-mass correction.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, `comparator:typical-entropies`, lines 37–55, and
`comparator:high-label`, lines 240–270, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder

namespace TNLean.PEPS.AreaLaw

open Classical in
/-- For a unit physical state and a supplied positive-mass spectral set in an
exponential window, both the logarithmic selected dimension and the entropy of
the actual selected auxiliary marginal differ from the original regional
entropy by at most the window width minus the logarithm of the selected mass.
Source: `07-comparators.tex`, `comparator:typical-entropies`, lines 37–55,
and `comparator:high-label`, lines 240–270. -/
theorem abs_log_card_and_selectedSchmidtEntropy_sub_le
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
          Real.exp (-regionalEntropy Λ q Ωt X + w)) :
    let β := fun _ : Site Λ => Fin q
    let split := FiniteProduct.splitEquiv β X
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split Ωt
    let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
    let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x =>
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let η := w - Real.log z
    |Real.log (E.card : ℝ) - regionalEntropy Λ q Ωt X| ≤ η ∧
      |vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
          (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian -
        regionalEntropy Λ q Ωt X| ≤ η := by
  have hbounds := (reducedState_posSemidef Λ q Ωt X).typicalSpectralRestriction_entropy_bounds
    E w hz hE
  done

end TNLean.PEPS.AreaLaw
