/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.LatticeConstraints
import QICLean.Analysis.PoissonContractionDecay

/-!
# Excited-state decay for the exact lattice constraints

The fresh exact positive constraints of a finite induced-domain Hamiltonian
annihilate its original ground vector. Their sum has gap
`Δ / positiveNormalization p (Δ / 2) J`. Chronological products of their
complementary square roots therefore suppress the component orthogonal to
that ground vector in squared-norm expectation, with any finite spectator.
The expectation uses the concrete fixed-time Poisson-word probability law.

## Proof status

The statement and its initial proof step await elaboration. The proof is
unfinished; the physical positive-constraint estimates still have to be
applied to the existing Poisson contraction decay theorem.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `09-amplification.tex`, lines 237–253,
  `eq:amplification-excited-decay`, at revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
  The exact positive replacement is `03-quasilocal.tex`, lines 220–246,
  Proposition 4.3. Independently formalized from the manuscript;
  no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

noncomputable section

open Matrix MeasureTheory SpectralFilter
open scoped Kronecker NNReal MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw

/-- The literal exact lattice constraint product has an integrable squared
excited-component norm and the original full-gap exponential decay rate,
including arbitrary entangled finite spectators.
Source: area law, `09-amplification.tex`, lines 237–253,
`eq:amplification-excited-decay`. -/
theorem latticeConstraintWord_excitedProjection_decay
    {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
    (E₀ : ℝ) (Ω : StateSpace Λ q) (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ)
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
  obtain ⟨hΩ, hHΩ, hgap⟩ := Matrix.isGappedGroundState_iff.mp hgs
  done

end TNLean.PEPS.AreaLaw
