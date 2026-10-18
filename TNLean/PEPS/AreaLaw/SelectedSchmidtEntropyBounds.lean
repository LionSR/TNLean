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
open TNLean.Lattice

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
  intro β split ΩX z ψ η
  have hρ : reducedState Λ q Ωt X = Matrix.partialTraceRight
      (Matrix.vecMulVec ΩX (star ΩX)) :=
    (reducedState_eq_finiteProduct Λ q Ωt X).trans
      (FiniteProduct.reducedPure_eq_partialTrace β Ωt X)
  have hselected := Matrix.entropy_compressedTypicalPureState_equivFin_swap ΩX E
    (by simpa only [← hρ] using hz)
  have hz1 : z ≤ 1 := (reducedState_posSemidef Λ q Ωt X).spectralRestrictionMass_le_one
    (by simpa only [reducedState_eq_finiteProduct] using
      (FiniteProduct.trace_reducedPure β Ωt hΩt X)) E
  rw [(reducedState_isHermitian Λ q Ωt X).rank_normalizedSpectralRestriction E hz.ne'
    (fun i hi => (Real.exp_pos _).trans_le (hE i hi).1)] at hbounds
  rw [abs_of_nonpos (Real.log_nonpos hz.le hz1)] at hbounds
  simp only at hselected
  have hσ :=
    congrArg (fun A : {A : Matrix (FiniteProduct.Configuration β X)
        (FiniteProduct.Configuration β X) ℂ // A.IsHermitian} =>
      A.2.normalizedSpectralRestriction E)
      (Subtype.ext
        (a1 := ⟨reducedState Λ q Ωt X, reducedState_isHermitian Λ q Ωt X⟩)
        (a2 := ⟨Matrix.partialTraceRight (Matrix.vecMulVec ΩX (star ΩX)),
          (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian⟩) hρ)
  have hEntropy := hselected.trans
    (vonNeumannEntropy_congr hσ
      ((reducedState_posSemidef Λ q Ωt X).normalizedSpectralRestriction_posSemidef
        E hz).isHermitian
      (Matrix.PosSemidef.normalizedSpectralRestriction_posSemidef
        (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight E
        (by simpa only [← hρ] using hz)).isHermitian).symm
  simpa only [η, regionalEntropy, sub_eq_add_neg, ← hEntropy] using! hbounds

end TNLean.PEPS.AreaLaw
