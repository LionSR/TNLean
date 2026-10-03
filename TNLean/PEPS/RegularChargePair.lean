/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTorusSite
import TNLean.Algebra.RepresentationTensorProduct
import TNLean.Algebra.TranslatedCharacterOrthogonality

/-!
# Charge-pair coefficients and the interferometric return measurement

The operator of SCP10, arXiv:1001.3807, equation
`eq:anyons:chargeon-pair-state`, lines 2505–2535, is diagonal on two group
registers. Its relative coordinate is unchanged by simultaneous left
translation. This proves the printed conjugation identity directly, and the
character norm gives the normalized coefficient vector. Translated character
orthogonality also gives the return amplitude of the literal flux-inserted pair,
independently of its common root translation, and a complete binary measurement.

**Scope restriction (accessible-register interference):** The results concern
the two group registers in SCP10, lines 2582–2615. Realizing this measurement on
the six original physical sites, and obtaining its input from a geometric braid,
requires the corresponding contraction and physical-operation identities. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
open scoped BigOperators Kronecker Matrix ComplexOrder
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

/-- The literal relative-pair weight after the flux insertion. The common root
translation conjugates the flux between the two bond labels; it is not absorbed
into the left parameter. Source: SCP10, interference calculation, lines 2582–2615. -/
def regularBraidedChargePairCoefficient (χ : G → ℂ) (p k x : G) (q : G × G) : ℂ :=
  χ (p * q.2⁻¹ * x * k⁻¹ * x⁻¹ * q.1)

/-- Normalization of the actual braided pair coefficients.
Source: SCP10, interference calculation, lines 2582–2615. -/
noncomputable def normalizedRegularBraidedChargePairCoefficient
    (χ : G → ℂ) (p k x : G) : (G × G) → ℂ :=
  (Nat.card G : ℂ)⁻¹ • regularBraidedChargePairCoefficient χ p k x

/-- The rank-one return projector onto the normalized initial charge pair.
Source: SCP10, the measurement on the four accessible registers, lines 2605–2615. -/
noncomputable def regularChargePairReturnProjection
    (χ : G → ℂ) (p : G) : Matrix (G × G) (G × G) ℂ :=
  Matrix.vecMulVec (normalizedRegularChargePairCoefficient χ p)
    (star (normalizedRegularChargePairCoefficient χ p))

/-- The two outcomes of the accessible charge-pair return measurement. The true
outcome detects the initial pair and the false outcome is its orthogonal
complement. Source: SCP10, interference measurement, lines 2605–2615. -/
noncomputable def regularChargePairReturnMeasurement (χ : G → ℂ) (p : G)
    (b : Bool) : Matrix (G × G) (G × G) ℂ :=
  if b then regularChargePairReturnProjection χ p
    else 1 - regularChargePairReturnProjection χ p

omit [DecidableEq G] in
/-- The overlap of the literal braided and initial pair is independent of the
common root translation. Source: SCP10, interference calculation, lines 2582–2615. -/
theorem regularChargePairCoefficient_braided_overlap
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p k x : G) :
    ∑ q : G × G, star (regularChargePairCoefficient σ.character p q) *
      regularBraidedChargePairCoefficient σ.character p k x q =
        (Nat.card G : ℂ)^2 / Module.finrank ℂ E * σ.character k⁻¹ := by
  classical
  simp only [Fintype.sum_prod_type, regularChargePairCoefficient,
    regularBraidedChargePairCoefficient]
  rw [Finset.sum_comm]
  have hs (h : G) :
      ∑ g : G, star (σ.character (p * h⁻¹ * g)) *
        σ.character (p * h⁻¹ * x * k⁻¹ * x⁻¹ * g) =
          ((Nat.card G : ℂ) / Module.finrank ℂ E) * σ.character k⁻¹ := by
    rw [Representation.sum_star_character_mul_character_translate σ σ hσ,
      ite_eq_left ⟨Representation.Equiv.refl σ⟩]
    have hg : p * h⁻¹ * x * k⁻¹ * x⁻¹ * (p * h⁻¹)⁻¹ =
        (p * h⁻¹ * x) * k⁻¹ * (p * h⁻¹ * x)⁻¹ := by group
    rw [hg, σ.char_conj]
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  ring

omit [DecidableEq G] in
/-- The normalized return amplitude is the dimension-normalized character.
Source: SCP10, interference calculation, lines 2582–2615. -/
theorem normalizedRegularChargePairCoefficient_braided_overlap
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p k x : G) :
    star (normalizedRegularChargePairCoefficient σ.character p) ⬝ᵥ
      normalizedRegularBraidedChargePairCoefficient σ.character p k x =
        σ.character k⁻¹ / Module.finrank ℂ E := by
  rw [normalizedRegularChargePairCoefficient,
    normalizedRegularBraidedChargePairCoefficient, star_smul,
    dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul]
  rw [show star (regularChargePairCoefficient σ.character p) ⬝ᵥ
      regularBraidedChargePairCoefficient σ.character p k x =
      (Nat.card G : ℂ)^2 / Module.finrank ℂ E * σ.character k⁻¹ from
        regularChargePairCoefficient_braided_overlap σ hσ p k x]
  simp [pow_two, ← mul_assoc, div_eq_mul_inv]
  ring

omit [DecidableEq G] in
/-- The literal braided pair has unit norm, for every common root translation.
Source: SCP10, interference calculation, lines 2582–2615. -/
theorem normalizedRegularBraidedChargePairCoefficient_normSq
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p k x : G) :
    ∑ q, star (normalizedRegularBraidedChargePairCoefficient σ.character p k x q) *
      normalizedRegularBraidedChargePairCoefficient σ.character p k x q = 1 := by
  have hn : star (regularBraidedChargePairCoefficient σ.character p k x) ⬝ᵥ
      regularBraidedChargePairCoefficient σ.character p k x = (Nat.card G : ℂ)^2 := by
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type,
      regularBraidedChargePairCoefficient]
    rw [Finset.sum_comm]
    simp_rw [Representation.sum_star_character_mul_character_self σ hσ]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card, pow_two]
  change star ((Nat.card G : ℂ)⁻¹ • regularBraidedChargePairCoefficient σ.character p k x) ⬝ᵥ
    ((Nat.card G : ℂ)⁻¹ • regularBraidedChargePairCoefficient σ.character p k x) = 1
  rw [star_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul]
  rw [hn]
  simp [pow_two]


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

omit [Fintype G] [DecidableEq G] in
/-- The charge-pair return operator is Hermitian. Source: SCP10, measurement of
the four accessible registers, lines 2605–2615. -/
theorem regularChargePairReturnProjection_conjTranspose (χ : G → ℂ) (p : G) :
    (regularChargePairReturnProjection χ p).conjTranspose =
      regularChargePairReturnProjection χ p := by
  simp only [regularChargePairReturnProjection, Matrix.conjTranspose_vecMulVec,
    star_star]

omit [DecidableEq G] in
/-- Irreducible unitary characters give an orthogonal return projector.
Source: SCP10, interference measurement, lines 2582–2615. -/
theorem regularChargePairReturnProjection_mul_self
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p : G) :
    regularChargePairReturnProjection σ.character p *
      regularChargePairReturnProjection σ.character p =
        regularChargePairReturnProjection σ.character p := by
  simp only [regularChargePairReturnProjection, Matrix.vecMulVec_mul_vecMulVec,
    show star (normalizedRegularChargePairCoefficient σ.character p) ⬝ᵥ
      normalizedRegularChargePairCoefficient σ.character p = 1 from
        normalizedRegularChargePairCoefficient_normSq σ hσ p, one_smul]

omit [DecidableEq G] in
/-- The return projector applied to the literal braided pair gives the initial
pair multiplied by the dimension-normalized character. Source: SCP10,
interference calculation and measurement, lines 2582–2615. -/
theorem regularChargePairReturnProjection_mulVec_braided
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p k x : G) :
    regularChargePairReturnProjection σ.character p *ᵥ
      normalizedRegularBraidedChargePairCoefficient σ.character p k x =
        (σ.character k⁻¹ / Module.finrank ℂ E) •
          normalizedRegularChargePairCoefficient σ.character p := by
  rw [regularChargePairReturnProjection, Matrix.vecMulVec_mulVec,
    normalizedRegularChargePairCoefficient_braided_overlap σ hσ]
  ext q
  simp [div_eq_mul_inv, mul_comm]

omit [DecidableEq G] in
/-- The squared norm of the accepted coefficient vector is the probability
printed in the interference calculation. This is a statement about the actual
two-register coefficients. Source: SCP10, lines 2605–2615. -/
theorem regularChargePairReturnProjection_probability
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p k x : G) :
    ∑ q, Complex.normSq
      ((regularChargePairReturnProjection σ.character p *ᵥ
        normalizedRegularBraidedChargePairCoefficient σ.character p k x) q) =
      Complex.normSq (σ.character k / Module.finrank ℂ E) := by
  rw [regularChargePairReturnProjection_mulVec_braided σ hσ]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, ← Finset.mul_sum]
  have hn : ∑ q, Complex.normSq
      (normalizedRegularChargePairCoefficient σ.character p q) = 1 := by
    have h := congrArg Complex.re
      (normalizedRegularChargePairCoefficient_normSq σ hσ p)
    change Complex.reAddGroupHom (∑ q,
      star (normalizedRegularChargePairCoefficient σ.character p q) *
        normalizedRegularChargePairCoefficient σ.character p q) = 1 at h
    rw [map_sum] at h
    simpa [Complex.normSq_apply, Complex.mul_re] using h
  rw [hn, mul_one, Representation.character_inv_of_unitary σ hσ]
  simp

/-- The accessible return measurement is a complete orthogonal projection
family; both outcomes are positive. Source: SCP10, lines 2605–2615. -/
theorem regularChargePairReturnMeasurement_complete
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (p : G) :
    (∀ b, (regularChargePairReturnMeasurement σ.character p b).IsHermitian ∧
      (regularChargePairReturnMeasurement σ.character p b).PosSemidef) ∧
    (∀ b c, regularChargePairReturnMeasurement σ.character p b *
      regularChargePairReturnMeasurement σ.character p c =
        if b = c then regularChargePairReturnMeasurement σ.character p b else 0) ∧
    (∑ b, regularChargePairReturnMeasurement σ.character p b) = 1 := by
  let D := regularChargePairReturnProjection σ.character p
  have hDh : D.IsHermitian := regularChargePairReturnProjection_conjTranspose _ _
  have hDI : D * D = D := regularChargePairReturnProjection_mul_self σ hσ p
  have hCh : (1 - D).IsHermitian := Matrix.isHermitian_one.sub hDh
  have hCI : (1 - D) * (1 - D) = 1 - D := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      hDI, sub_self, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro b
    cases b
    · change (1 - D).IsHermitian ∧ (1 - D).PosSemidef
      refine ⟨hCh, ?_⟩
      have hp := Matrix.posSemidef_self_mul_conjTranspose (1 - D)
      rw [hCh.eq, hCI] at hp
      exact hp
    · change D.IsHermitian ∧ D.PosSemidef
      refine ⟨hDh, ?_⟩
      have hp := Matrix.posSemidef_self_mul_conjTranspose D
      rw [hDh.eq, hDI] at hp
      exact hp
  · intro b c
    cases b <;> cases c <;>
      simp only [regularChargePairReturnMeasurement, Bool.false_eq_true, Bool.true_eq_false,
        ↓reduceIte] <;>
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        regularChargePairReturnProjection_mul_self σ hσ p, sub_self, sub_zero]
  · simp [regularChargePairReturnMeasurement]

end TNLean.PEPS
