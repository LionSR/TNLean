/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.IndependentBondGap
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Star.StarProjection

/-!
# The parent interaction of a normalized bond vector

For a unit vector `w`, the operator `I - |w⟩⟨w|` is an orthogonal projection
of norm at most one. It varies continuously with `w`, annihilates `w`, and
gives an independent-bond Hamiltonian with ground energy zero and a gap
of at least one at every positive chain length.

Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`, and Section II.F.2, source lines 899–906.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace Matrix.Norms.L2Operator
namespace MPSTensor

/-- The projector onto the orthogonal complement of a unit bond vector,
written as `I - |w⟩⟨w|`. Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`, for a normalized bond vector. -/
noncomputable def bondVectorInteraction {d : ℕ} (w : EuclideanSpace ℂ (Fin d)) :
    Matrix (Fin d) (Fin d) ℂ :=
  1 - Matrix.vecMulVec w.ofLp (star w.ofLp)

/-- A normalized bond vector gives an orthogonal parent-interaction projection.
Source: arXiv:1010.3732, Section II.F.2, source lines 899–906. -/
theorem bondVectorInteraction_isStarProjection {d : ℕ} (w : EuclideanSpace ℂ (Fin d))
    (hw : ‖w‖ = 1) : IsStarProjection (bondVectorInteraction w) := by
  apply IsStarProjection.one_sub
  rw [isStarProjection_iff']
  constructor
  · rw [Matrix.vecMulVec_mul_vecMulVec]
    have hdot : star w.ofLp ⬝ᵥ w.ofLp = (1 : ℂ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        inner_self_eq_norm_sq_to_K, hw]
      norm_num
    simp [hdot]
  · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_vecMulVec, star_star]

/-- The bond vector is annihilated by its parent interaction.
Source: arXiv:1010.3732, Section II.F.2, source lines 899–906. -/
theorem bondVectorInteraction_mulVec {d : ℕ} (w : EuclideanSpace ℂ (Fin d))
    (hw : ‖w‖ = 1) : bondVectorInteraction w *ᵥ w.ofLp = 0 := by
  rw [bondVectorInteraction, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, hw]
  simp

/-- A normalized bond vector gives a parent interaction different from the identity.
Source: arXiv:1010.3732, Section II.F.2, source lines 899–906. -/
theorem bondVectorInteraction_ne_one {d : ℕ} (w : EuclideanSpace ℂ (Fin d))
    (hw : ‖w‖ = 1) : bondVectorInteraction w ≠ 1 := by
  intro h
  have hz := bondVectorInteraction_mulVec w hw
  rw [h, Matrix.one_mulVec] at hz
  have hwzero : w = 0 := by
    apply PiLp.ext
    intro i
    exact congrFun hz i
  simp [hwzero] at hw

/-- The normalized bond interaction has operator norm at most one.
Source: arXiv:1010.3732, Section II.C.1, the bound on interaction strengths. -/
theorem bondVectorInteraction_norm_le_one {d : ℕ} (w : EuclideanSpace ℂ (Fin d))
    (hw : ‖w‖ = 1) : ‖bondVectorInteraction w‖ ≤ 1 := by
  exact IsStarProjection.norm_le _ (bondVectorInteraction_isStarProjection w hw)

/-- The parent interaction depends continuously on the bond vector.
Source: arXiv:1010.3732, Section II.F.2, source lines 904–906. -/
theorem continuous_bondVectorInteraction (d : ℕ) :
    Continuous (bondVectorInteraction (d := d)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [bondVectorInteraction, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  fun_prop

/-- The independent-bond parent Hamiltonian of a unit vector has ground energy
zero and a spectral gap of at least one for every positive chain length.
Source: arXiv:1010.3732, Section II.F.2, source lines 899–906. -/
theorem bondVectorInteraction_independentBond_gap {d N : ℕ} (hN : 1 ≤ N)
    (w : EuclideanSpace ℂ (Fin d)) (hw : ‖w‖ = 1) :
    (0 : ℂ) ∈ spectrum ℂ (independentBondHamiltonian hN (bondVectorInteraction w)) ∧
    ∀ z ∈ spectrum ℂ (independentBondHamiltonian hN (bondVectorInteraction w)),
      0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) :=
  ⟨independentBondHamiltonian_zero_mem_spectrum hN _
      (bondVectorInteraction_isStarProjection w hw) (bondVectorInteraction_ne_one w hw),
    independentBondHamiltonian_spectrum_gap hN _ (bondVectorInteraction_isStarProjection w hw)⟩

end MPSTensor
