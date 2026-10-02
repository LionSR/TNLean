/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargePair
import TNLean.Algebra.UnitaryVectorSwap
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Unitary preparation in the four accessible charge registers

SCP10, arXiv:1001.3807, equation `eq:anyons:create-chargepair-accessible`,
lines 2534–2558, starts from the two uniform diagonal pairs a=c and b=d.
The input is the normalized vectorization of the identity on two group
registers. The output is the normalized vectorization of the printed
charge-pair operator. A reflection exchanges these vectors for a nontrivial
irreducible character; the trivial character requires only the identity.

These are accessible-register statements. No comparison with the original
six-spin contraction or original-spin creation operation is asserted.
-/
noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The normalized four-register vector is the literal diagonal operator's
vectorization. Source: SCP10, `eq:anyons:create-chargepair-accessible`,
lines 2534–2558. Matrix vectorization lists the column pair before the row pair. -/
def normalizedRegularChargeFourRegister (χ : G → ℂ) (p : G) :
    (G × G) × (G × G) → ℂ :=
  Matrix.vec (Matrix.diagonal (normalizedRegularChargePairCoefficient χ p))

/-- The actual diagonal embedding preserves the coefficient inner product.
Source: SCP10, charge-pair accessible-register diagram, lines 2534–2558. -/
theorem normalizedRegularChargeFourRegister_inner (χ ψ : G → ℂ) (p q : G) :
    star (normalizedRegularChargeFourRegister χ p) ⬝ᵥ
      normalizedRegularChargeFourRegister ψ q =
      star (normalizedRegularChargePairCoefficient χ p) ⬝ᵥ
        normalizedRegularChargePairCoefficient ψ q := by
  unfold normalizedRegularChargeFourRegister
  rw [Matrix.star_vec, Matrix.map_diagonal_star, Matrix.vec_dotProduct_vec,
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- The source's actual normalized four-register charge vector has norm one.
Source: SCP10, `eq:anyons:create-chargepair-accessible`, lines 2534–2558. -/
theorem normalizedRegularChargeFourRegister_normSq
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p : G) :
    star (normalizedRegularChargeFourRegister σ.character p) ⬝ᵥ
      normalizedRegularChargeFourRegister σ.character p = 1 := by
  rw [normalizedRegularChargeFourRegister_inner]
  exact normalizedRegularChargePairCoefficient_normSq σ hσ p

/-- An actual unitary prepares the normalized charge pair from the two uniform
pairs. Source: SCP10, accessible preparation, lines 2534–2558. This auxiliary
register operation does not assert an original six-spin physical implementation. -/
theorem exists_unitary_regularChargePairPreparation
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p : G) :
    ∃ Q : Matrix ((G × G) × (G × G)) ((G × G) × (G × G)) ℂ,
      Q ∈ Matrix.unitaryGroup _ ℂ ∧
        Q *ᵥ normalizedRegularChargeFourRegister (fun _ : G => 1) 1 =
          normalizedRegularChargeFourRegister σ.character p := by
  let τ := Representation.trivial ℂ G ℂ
  let : τ.IsIrreducible :=
    Representation.isIrreducible_of_finrank_eq_one τ (by simp)
  have ht : τ.character = fun _ : G => 1 := by
    ext g
    simp [τ, Representation.character, Representation.trivial, LinearMap.trace_one]
  have hτ (g : G) : LinearMap.adjoint (τ g) = τ g⁻¹ := by
    simp [τ, Representation.trivial]
  have hx : star (normalizedRegularChargeFourRegister (fun _ : G => 1) 1) ⬝ᵥ
      normalizedRegularChargeFourRegister (fun _ : G => 1) 1 = 1 := by
    simpa only [ht] using normalizedRegularChargeFourRegister_normSq τ hτ 1
  have hy := normalizedRegularChargeFourRegister_normSq σ hσ p
  by_cases hc : τ.character = σ.character
  · refine ⟨1, one_mem _, ?_⟩
    rw [Matrix.one_mulVec]
    have hs : σ.character = fun _ : G => 1 := hc.symm.trans ht
    simp only [hs, normalizedRegularChargeFourRegister,
      normalizedRegularChargePairCoefficient]
    rfl
  · have hxy : star (normalizedRegularChargeFourRegister (fun _ : G => 1) 1) ⬝ᵥ
        normalizedRegularChargeFourRegister σ.character p = 0 := by
      rw [normalizedRegularChargeFourRegister_inner]
      simpa only [dotProduct, Pi.star_apply, normalizedRegularChargePairCoefficient,
        regularChargePairCoefficient, Pi.smul_apply, smul_eq_mul, mul_one] using
          normalizedRegularChargePairCoefficient_orthogonal_uniform σ hc p
    exact ⟨Matrix.unitaryVectorSwap _ _,
      Matrix.unitaryVectorSwap_mem_unitaryGroup _ _ hx hy hxy,
      Matrix.unitaryVectorSwap_mulVec_left _ _ hx hxy⟩
end TNLean.PEPS
