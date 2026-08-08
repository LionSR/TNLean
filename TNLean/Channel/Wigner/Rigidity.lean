/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Wigner.ProjectiveCarrierBridge

/-!
# Wigner rigidity for finite-coordinate rays and pure-state matrices

This module transfers the projective Wigner rigidity theorem adapted from
`zblore/csd-lean4` commit `55ac6758832291c8b0fb94d78e10dc47b1cb8a06`
to TNLean's `Fin d → ℂ` carrier and then states Wolf's Chapter 1 theorem on the
range of normalized pure-state matrices.

The conclusion is a disjunction, not an exclusive alternative. In dimension
zero the domain is empty; in dimension one it is a singleton and the two
alternatives coincide. No uniqueness of the implementing unitary is asserted.
-/

open scoped LinearAlgebra.Projectivization Matrix

namespace Projectivization

variable {d : ℕ}

/-- Wigner rigidity in TNLean's finite-coordinate projective-ray language. -/
theorem wigner_rigidity_fin
    {f : ℙ ℂ (Fin d → ℂ) → ℙ ℂ (Fin d → ℂ)}
    (hf : ∀ p q, transitionProbability (f p) (f q) =
      transitionProbability p q) :
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      ∀ p, f p = unitaryAction U p) ∨
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      ∀ p, f p = unitaryAction U (coordinateConjugation p)) := by
  let fE : ℙ ℂ (EuclideanSpace ℂ (Fin d)) →
      ℙ ℂ (EuclideanSpace ℂ (Fin d)) :=
    fun p ↦ toEuclideanRay (f (fromEuclideanRay p))
  have hfE : TransProbPreserving fE := by
    intro p q
    apply Complex.ofReal_injective
    calc
      ((transProb (fE p) (fE q) : ℝ) : ℂ) =
          transitionProbability (f (fromEuclideanRay p))
            (f (fromEuclideanRay q)) := by
              exact transProb_toEuclideanRay_ofReal_eq _ _
      _ = transitionProbability (fromEuclideanRay p) (fromEuclideanRay q) :=
        hf _ _
      _ = ((transProb p q : ℝ) : ℂ) := by
        rw [← transProb_toEuclideanRay_ofReal_eq]
        simp
  rcases wigner_rigidity_unitaryGroup hfE with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨U, fun p ↦ by
      have h := congrArg fromEuclideanRay (hU (toEuclideanRay p))
      simpa [fE, fromEuclideanRay_unitary_smul] using h⟩
  · exact Or.inr ⟨U, fun p ↦ by
      have h := congrArg fromEuclideanRay (hU (toEuclideanRay p))
      simpa [fE, fromEuclideanRay_unitary_smul,
        fromEuclideanRay_conjProj] using h⟩

/-- Normalized pure-state matrices, represented intrinsically as the range of
the projective pure-state realization. -/
def PureStateMatrix (d : ℕ) :=
  Set.range
    (pureStateMatrix : ℙ ℂ (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ)

/-- Projective rays are equivalent to normalized pure-state matrices in their
range realization. -/
noncomputable def pureStateMatrixEquiv :
    ℙ ℂ (Fin d → ℂ) ≃ PureStateMatrix d where
  toFun p := ⟨pureStateMatrix p, p, rfl⟩
  invFun P := Classical.choose P.property
  left_inv p := pureStateMatrix_injective (Classical.choose_spec (show
    (pureStateMatrix p) ∈ Set.range
      (pureStateMatrix : ℙ ℂ (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ) from
        ⟨p, rfl⟩))
  right_inv P := Subtype.ext (Classical.choose_spec P.property)

/-- The range equivalence sends a ray to its normalized pure-state matrix. -/
@[simp]
theorem pureStateMatrixEquiv_val (p : ℙ ℂ (Fin d → ℂ)) :
    (pureStateMatrixEquiv p).1 = pureStateMatrix p := rfl

/-- The ray corresponding to a matrix in the range realizes that matrix. -/
@[simp]
theorem pureStateMatrix_pureStateMatrixEquiv_symm (P : PureStateMatrix d) :
    pureStateMatrix (pureStateMatrixEquiv.symm P) = P.1 := by
  exact congrArg Subtype.val (pureStateMatrixEquiv.apply_symm_apply P)

/-- Wolf's matrix-facing Wigner theorem for normalized pure states.

The bijectivity hypothesis is retained exactly as in Wolf, Theorem 1.1, although
the adapted projective rigidity theorem proves the classification from
transition-probability preservation alone. -/
theorem wolf_wigner_pureStateMatrix
    (F : PureStateMatrix d → PureStateMatrix d)
    (_hbijective : Function.Bijective F)
    (htransition : ∀ P Q,
      Matrix.trace ((F P).1 * (F Q).1) = Matrix.trace (P.1 * Q.1)) :
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ P,
      (F P).1 = (U : Matrix (Fin d) (Fin d) ℂ) * P.1 *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) ∨
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ P,
      (F P).1 = (U : Matrix (Fin d) (Fin d) ℂ) * P.1ᵀ *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  let e := pureStateMatrixEquiv (d := d)
  let f : ℙ ℂ (Fin d → ℂ) → ℙ ℂ (Fin d → ℂ) := fun p ↦ e.symm (F (e p))
  have hf : ∀ p q, transitionProbability (f p) (f q) =
      transitionProbability p q := by
    intro p q
    rw [← trace_pureStateMatrix_mul_pureStateMatrix,
      ← trace_pureStateMatrix_mul_pureStateMatrix]
    simpa [f, e] using htransition (e p) (e q)
  rcases wigner_rigidity_fin hf with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨U, fun P ↦ by
      let p := e.symm P
      calc
        (F P).1 = pureStateMatrix (f p) := by simp [f, p, e]
        _ = pureStateMatrix (unitaryAction U p) := congrArg pureStateMatrix (hU p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * pureStateMatrix p *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := pureStateMatrix_unitaryAction U p
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * P.1 *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by simp [p, e]⟩
  · exact Or.inr ⟨U, fun P ↦ by
      let p := e.symm P
      calc
        (F P).1 = pureStateMatrix (f p) := by simp [f, p, e]
        _ = pureStateMatrix (unitaryAction U (coordinateConjugation p)) :=
          congrArg pureStateMatrix (hU p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) *
            pureStateMatrix (coordinateConjugation p) *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ :=
          pureStateMatrix_unitaryAction U (coordinateConjugation p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * (pureStateMatrix p)ᵀ *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
          rw [pureStateMatrix_coordinateConjugation]
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * P.1ᵀ *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by simp [p, e]⟩

end Projectivization
