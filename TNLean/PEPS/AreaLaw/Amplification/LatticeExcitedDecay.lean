/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.LatticeConstraints
import QICLean.Analysis.PoissonContractionDecay
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Excited-state decay for the exact lattice constraints

The fresh exact positive constraints of a finite induced-domain Hamiltonian
annihilate its original ground vector. Their sum has gap `Δ / c_*`, with
`c_*` the normalization of the positive replacement. Chronological products of their
complementary square roots therefore suppress the component orthogonal to
that ground vector in squared-norm expectation, with any finite spectator.
The expectation uses the concrete fixed-time Poisson-word probability law.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `09-amplification.tex`, lines 237–253,
  `eq:amplification-excited-decay`, at revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  The exact positive replacement is `03-quasilocal.tex`, lines 220–246,
  Proposition 4.3. Independently formalized from the manuscript;
  no upstream Lean text is reused.
-/

noncomputable section

open Matrix MeasureTheory SpectralFilter
open scoped Kronecker NNReal MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open TNLean.Lattice

open ManyBody (IsGapped groundSpace)

namespace TNLean.PEPS.AreaLaw

/-- The literal exact lattice constraint product has an integrable squared
excited-component norm and the original full-gap exponential decay rate,
including arbitrary entangled finite spectators.
Source: area law, `09-amplification.tex`, lines 237–253,
`eq:amplification-excited-decay`. -/
theorem latticeConstraintWord_excitedProjection_decay
    {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ} (_hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
    (E₀ : ℝ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.operator E₀ Δ)
    (hspan : groundSpace h.operator E₀ = Submodule.span ℂ {Ω})
    {Aux : Type*} [Fintype Aux] [DecidableEq Aux]
    (ζ : EuclideanSpace ℂ (Configuration Λ q × Aux)) (t : ℝ≥0) :
    let cs := positiveNormalization p (Δ / 2) J
    let k := fun i : AdmissibleSupport Λ R =>
      positiveConstraint cs (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
    let ξ := toEuclideanLin
      ((1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ⊗ₖ
        (1 : Matrix Aux Aux ℂ)) ζ
    Integrable (poissonContractionWordEnergy k ξ)
        (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
      (∫ w, poissonContractionWordEnergy k ξ w
        ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
        Real.exp (-(Δ / cs) * (t : ℝ)) * ‖ξ‖ ^ 2 := by
  have hHΩ := ManyBody.mulVec_eq_of_groundSpace_eq_span hspan
  have hgap := hgap.posSemidef_sub_smul_one h.operator_isHermitian hΩ hspan
  obtain ⟨hk, hsum, hgapk⟩ :=
    positive_replacement hp hΔ hΩ hHΩ hgap h.term h.hermitian h.norm_le rfl
  exact Matrix.poissonContractionWord_excitedProjection_decay _
    (fun i => (hk i).2.1) hΩ
    (fun i => WithLp.ofLp_injective 2 (hk i).2.2)
    (hgapk.trans hsum) ζ t

end TNLean.PEPS.AreaLaw
