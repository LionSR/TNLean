/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteSetTruncationGap
import TNLean.PEPS.AreaLaw.GlobalSchmidtBellPrevector

/-!
# The common-label initial vector for the finite-set truncation

The truncated Hamiltonian and its ground vector satisfy the same perturbation,
gap and trace-distance estimates as in the finite-set truncation theorem. For
each actual positive-mass spectral restriction, this same ground vector then
determines one auxiliary label sequence in physical-site coordinates.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`03-quasilocal.tex`, `prop:truncation`, lines 405–433, and
`07-comparators.tex`, `comparator:prevector` and `comparator:high-label`,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Filter QuantumCircuit

namespace TNLean.PEPS.AreaLaw

/-- The finite-set truncation's exact ground vector determines one selected
Schmidt--Bell label sequence and its initial vector in the original site
coordinates. The energy equation belongs to the truncated Hamiltonian.
The spectral restriction is used only to choose the label sequence.
Source: area-law manuscript, `03-quasilocal.tex`, `prop:truncation`,
lines 405–433; `07-comparators.tex`, `comparator:prevector` and
`comparator:high-label`, lines 130–147 and 240–281; `08-scanner.tex`,
lines 50–59, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The two auxiliary projections are their literal transported operators;
identification with the site-label projectors is a separate result. -/
open Classical in
theorem exists_finiteSetTruncation_schmidtBellPrevector_of_gap
    (R vR : ℕ) (b₀ Kg : ℝ) (kg : ℕ) {J Δ Kb μ C₀ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hKb : 0 ≤ Kb) (hμ : 0 ≤ μ) (hC₀ : 0 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
        (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι), (∀ k, a k ∈ X k) →
        ∀ (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ), (∀ k, (h k).IsHermitian) →
        (∀ k, h k ∈ supportedOperators q (X k : Set ι)) →
        (∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R) →
        (∀ k, (X k).card ≤ vR) →
        (∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀) →
        (∀ x (d : ℕ),
          ((Finset.univ.filter fun y => G.edist x y = d).card : ℝ) ≤ Kg * ((d : ℝ) + 1) ^ kg) →
        (∀ x (d : ℕ), ((graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2) →
        (∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) →
        (∀ k, ‖h k‖ ≤ J) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (ι → Fin q)), ‖Ω‖ = 1 →
        (∑ k, h k) *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        ((∑ k, h k) - (E₀ : ℂ) • 1 -
          (Δ : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
        ∀ n : ℝ, 2 ≤ n → ∀ S₀ : Finset ι, (S₀.card : ℝ) ≤ C₀ * n ^ 2 →
        let cs := SpectralFilter.positiveNormalization 1 (Δ / 2) J
        let g := Δ / cs
        let k := fun i =>
          SpectralFilter.positiveConstraint cs
            (SpectralFilter.centeredFilter 1 (Δ / 2) (∑ j, h j) Ω (h i))
        let r₀ := ⌈C₁ * Real.log n ^ 2⌉₊
        let ε := min (n ^ (-1000 : ℝ)) (g / 4)
        let Ht := ∑ i, truncatedConstraint q G S₀ r₀ (a i) (k i)
        (∀ i, truncatedConstraint q G S₀ r₀ (a i) (k i) ∈
          supportedOperators q (designatedSupport G S₀ r₀ (a i) : Set ι)) ∧
        (∀ i, 0 ≤ truncatedConstraint q G S₀ r₀ (a i) (k i) ∧
          truncatedConstraint q G S₀ r₀ (a i) (k i) ≤ 1) ∧
        ‖Ht - ∑ i, k i‖ ≤ ε ∧
        ∃ (e : ℝ) (Ω₀ : EuclideanSpace ℂ (ι → Fin q)), ‖Ω₀‖ = 1 ∧
          Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧ 0 ≤ e ∧ e ≤ ε ∧
          (Ht - (e : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
            (1 - Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))).PosSemidef ∧
          (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) ∧
          let β := fun _ : ι => Fin q
          ∀ X : Finset ι,
            let split := FiniteProduct.splitEquiv β X
            let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ split Ω₀
            ∀ E : Finset (FiniteProduct.Configuration β X),
              0 < ((Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian)
                .spectralRestrictionMass E →
              let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x =>
                Matrix.compressedTypicalPureState ΩX E
                  ((Finset.equivFin E).symm x.2, x.1)
              ∃ ell : (k : ℕ) → PermutationRepresentation.IrrepLabel (Equiv.Perm (Fin k)),
                (∀ k : ℕ, 0 < k →
                  let d := E.card
                  let eₖ := TensorPower.globalReplicaCopiesEquiv β (Fin d) (Fin d) k
                  let ξ := WithLp.toLp 2
                    (TensorPower.replicaPrevector Ω₀ d k (ell k) ∘ eₖ)
                  let L := PermutationRepresentation.labelProj
                    (TensorPower.copyPerm (Fin d) k) (ell k)
                  let I := (1 : Matrix (Fin k → ι → Fin q) (Fin k → ι → Fin q) ℂ)
                  let Pe := PermutationRepresentation.symProj
                    (TensorPower.copyPerm
                      ((v : Option (Option ι)) →
                        TensorPower.addedSiteSpace (TensorPower.addedSiteSpace β (Fin d))
                          (Fin d) v) k)
                  ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 ∧
                    (((((k : ℝ)⁻¹ • Matrix.replicaHamiltonian Ht k) ⊗ₖ
                      (1 : Matrix ((Fin k → Fin d) × (Fin k → Fin d))
                        ((Fin k → Fin d) × (Fin k → Fin d)) ℂ)).submatrix eₖ eₖ) *ᵥ ξ =
                      (e : ℂ) • ξ.ofLp) ∧
                    Pe *ᵥ ξ = ξ.ofLp ∧
                    ((I ⊗ₖ (L ⊗ₖ (1 : Matrix (Fin k → Fin d)
                      (Fin k → Fin d) ℂ))).submatrix eₖ eₖ) *ᵥ ξ = ξ.ofLp ∧
                    ((I ⊗ₖ ((1 : Matrix (Fin k → Fin d)
                      (Fin k → Fin d) ℂ) ⊗ₖ L)).submatrix eₖ eₖ) *ᵥ ξ = ξ.ofLp) ∧
                (∀ᶠ k : ℕ in Filter.atTop,
                  (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
                    ‖WithLp.toLp 2
                      (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
                        (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
                        PermutationRepresentation.labelProj
                          (TensorPower.copyPerm (Fin E.card) k) (ell k)) *ᵥ
                        (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                          (Fin k → Fin E.card) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
                Asymptotics.IsLittleO Filter.atTop
                  (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) *
                    vonNeumannEntropy
                      (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
                      (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
                  (fun k : ℕ => (k : ℝ)) := by
  obtain ⟨C₁, hC₁, htr⟩ := exists_finiteSetTruncation_of_gap R vR b₀ Kg kg
    hJ hΔ hKb hμ hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro q _ ι _ _ κ _ G X a ha h hHerm hSupport hDiam hCard hBudget hGrowth hBall hMult hJh
    E₀ Ω hΩ hHΩ hgap n hn S₀ hS₀n cs g k r₀ ε Ht
  obtain ⟨hSupp, hPos, hErr, e, Ω₀, hΩ₀, hE₀, he0, heε, hGap₀, hPhase, hDist⟩ :=
    htr G X a ha h hHerm hSupport hDiam hCard hBudget hGrowth hBall hMult hJh
      E₀ Ω hΩ hHΩ hgap n hn S₀ hS₀n
  refine ⟨hSupp, hPos, hErr, e, Ω₀, hΩ₀, hE₀, he0, heε, hGap₀, hPhase, hDist, ?_⟩
  intro β X split ΩX E hz ψ
  exact exists_global_schmidtBellPrevector Ht Ω₀ e hΩ₀ hE₀ X E hz

end TNLean.PEPS.AreaLaw
