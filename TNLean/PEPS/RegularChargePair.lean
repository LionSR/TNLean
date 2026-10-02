/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusSite
import TNLean.Algebra.RepresentationTensorProduct
import TNLean.Algebra.TranslatedCharacterOrthogonality

/-!
# The actual diagonal charge-pair operator

The operator of SCP10, arXiv:1001.3807, equation
`eq:anyons:chargeon-pair-state`, lines 2505–2535, is diagonal on two group
registers. Its relative coordinate is unchanged by simultaneous left
translation. This proves the printed conjugation identity directly, and the
character norm gives the normalized coefficient vector. These are auxiliary
accessible-coordinate results; no original six-spin creation is asserted.
-/
open scoped BigOperators Kronecker Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The coefficient of the actual charge-pair operator in the group basis.
Source: SCP10, equation `eq:anyons:chargeon-pair-state`, lines 2505–2535. -/
def regularChargePairCoefficient (χ : G → ℂ) (p : G) (q : G × G) : ℂ :=
  χ (p * q.2⁻¹ * q.1)

/-- The actual diagonal two-register operator from the source charge-pair equation. -/
def regularChargePairOperator (χ : G → ℂ) (p : G) : Matrix (G × G) (G × G) ℂ :=
  Matrix.diagonal (regularChargePairCoefficient χ p)

omit [Fintype G] [DecidableEq G] in
/-- Simultaneous left translation leaves the actual relative-coordinate
coefficient invariant, for every function χ. Source: SCP10, lines 2520–2535. -/
theorem regularChargePairCoefficient_left_invariant (χ : G → ℂ) (p x g h : G) :
    regularChargePairCoefficient χ p (x * g, x * h) =
      regularChargePairCoefficient χ p (g, h) := by
  unfold regularChargePairCoefficient
  congr 1
  group

/-- The actual operator commutes with the Kronecker left-regular action.
Source: SCP10, equation `eq:anyons:Ux-invariance-of-charge-pair`, lines 2520–2535. -/
theorem regularChargePairOperator_commute (χ : G → ℂ) (p x : G) :
    Commute (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x)
      (regularChargePairOperator χ p) := by
  apply Matrix.ext
  rintro ⟨g,h⟩ ⟨g',h'⟩
  rw [regularChargePairOperator, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.kroneckerMap_apply, leftRegularMatrix_apply]
  by_cases hg : g = x * g'
  · by_cases hh : h = x * h'
    · subst g h
      simp [regularChargePairCoefficient_left_invariant]
    · simp [hh]
  · simp [hg]

/-- The source's actual diagonal operator is invariant under conjugation by
Ux⊗Ux; the relative-coordinate identity proves this without an invariance premise.
Source: SCP10, equation `eq:anyons:Ux-invariance-of-charge-pair`, lines 2520–2535. -/
theorem regularChargePairOperator_conjugation (χ : G → ℂ) (p x : G) :
    (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x) *
      regularChargePairOperator χ p *
      (leftRegularMatrix G x ⊗ₖ leftRegularMatrix G x).conjTranspose =
        regularChargePairOperator χ p := by
  have hU : leftRegularMatrix G x ∈ Matrix.unitaryGroup G ℂ := by
    simpa only [leftRegularMatrix, MonoidHom.comp_apply, Matrix.permMatrixHom_apply] using
      ((MulAction.toPermHom G G x)⁻¹).permMatrix_mem_unitaryGroup
  have hUU := Matrix.mem_unitaryGroup_iff.mp (Matrix.kronecker_mem_unitary hU hU)
  rw [Matrix.star_eq_conjTranspose] at hUU
  rw [(regularChargePairOperator_commute χ p x).eq, Matrix.mul_assoc, hUU,
    Matrix.mul_one]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

omit [DecidableEq G] in
/-- The actual pair coefficient vector has squared norm |G|².
Source: SCP10, charge-pair equation, lines 2505–2535; explicit normalization. -/
theorem regularChargePairCoefficient_normSq
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p : G) :
    ∑ q : G × G, star (regularChargePairCoefficient σ.character p q) *
      regularChargePairCoefficient σ.character p q = (Nat.card G : ℂ)^2 := by
  simp only [Fintype.sum_prod_type, regularChargePairCoefficient]
  rw [Finset.sum_comm]
  simp_rw [Representation.sum_star_character_mul_character_self σ hσ]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, pow_two]

/-- The actual normalized pair coefficient vector. Source: SCP10, the charge-pair
creation equation, lines 2505–2535; its normalization is made explicit here. -/
noncomputable def normalizedRegularChargePairCoefficient (χ : G → ℂ) (p : G) : (G × G) → ℂ :=
  (Nat.card G : ℂ)⁻¹ • regularChargePairCoefficient χ p

omit [DecidableEq G] in
/-- The normalized actual charge-pair vector has unit squared norm.
Source: SCP10, lines 2505–2535; auxiliary accessible-coordinate normalization. -/
theorem normalizedRegularChargePairCoefficient_normSq
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p : G) :
    ∑ q : G × G, star (normalizedRegularChargePairCoefficient σ.character p q) *
      normalizedRegularChargePairCoefficient σ.character p q = 1 := by
  change star ((Nat.card G : ℂ)⁻¹ • regularChargePairCoefficient σ.character p) ⬝ᵥ
    ((Nat.card G : ℂ)⁻¹ • regularChargePairCoefficient σ.character p) = 1
  rw [star_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul]
  rw [show star (regularChargePairCoefficient σ.character p) ⬝ᵥ
    regularChargePairCoefficient σ.character p = (Nat.card G : ℂ)^2 from
      regularChargePairCoefficient_normSq σ hσ p]
  simp [pow_two]


omit [DecidableEq G] in
/-- A nontrivial irreducible charge-pair vector is orthogonal to the normalized
uniform pair vector. Source: SCP10, charge creation, lines 2505–2535;
auxiliary accessible-coordinate orthogonality. -/
theorem normalizedRegularChargePairCoefficient_orthogonal_uniform
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hne : (Representation.trivial ℂ G ℂ).character ≠ σ.character) (p : G) :
    ∑ q : G × G, star ((Nat.card G : ℂ)⁻¹) *
      normalizedRegularChargePairCoefficient σ.character p q = 0 := by
  let τ := Representation.trivial ℂ G ℂ
  let : τ.IsIrreducible :=
    Representation.isIrreducible_of_finrank_eq_one τ (by simp)
  have ht (g : G) : τ.character g = 1 := by
    simp [τ, Representation.character, Representation.trivial, LinearMap.trace_one]
  have hz (a : G) : ∑ g : G, σ.character (a * g) = 0 := by
    simpa only [ht, one_mul] using
      Representation.sum_character_inv_mul_character_translate_eq_zero τ σ hne 1 a
  simp only [normalizedRegularChargePairCoefficient, Pi.smul_apply, smul_eq_mul,
    regularChargePairCoefficient, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.mul_sum]
  have hs : ∑ h : G, ∑ g : G, σ.character (p * h⁻¹ * g) = 0 := by
    apply Finset.sum_eq_zero
    intro h _
    exact hz (p * h⁻¹)
  rw [hs, mul_zero]

end TNLean.PEPS
