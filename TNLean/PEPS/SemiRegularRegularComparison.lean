/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SemiRegularGroupAlgebra
import TNLean.PEPS.BlockMultiplicityRepresentation
import TNLean.PEPS.RegularMatrixEquiv

/-!
# Comparing complete irreducible blocks with the regular representation

A semi-regular family of pairwise inequivalent irreducible matrix representations,
with each block repeated according to its dimension, has the regular character.
The matrix of all block coefficients gives an invertible intertwiner with the
left regular representation. No choice of blocks from a regular decomposition
and no unitary normalization are required.

Source: SCP10, arXiv:1001.3807, Definition 4.5, lines 1010–1013, and the
regular decomposition in Section 7, lines 2947–3019.
-/

noncomputable section
open scoped Matrix Kronecker
namespace TNLean.PEPS

variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

omit [Fintype G] in
/-- The character of a single-copy block representation is the sum of its block
characters. Source: the decomposition in SCP10, Section 4.1. -/
theorem character_blockMatrixRepresentation (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    Representation.character
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) g =
      ∑ i, Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) g := by
  change LinearMap.trace ℂ _ (Matrix.toLin' (blockMatrixRepresentation d D g)) = _
  rw [Matrix.trace_toLin'_eq]
  change (Matrix.blockDiagonal' (fun i => D i g)).trace = _
  rw [Matrix.trace_blockDiagonal']
  apply Finset.sum_congr rfl
  intro i hi
  exact (Matrix.trace_toLin'_eq (D i g)).symm

/-- A complete irreducible block family lists precisely the occurring characters
of its single-copy direct sum. Source: SCP10, Definition 4.5 and Section 7. -/
theorem irreducibleCharacterFinset_blockMatrixRepresentation (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hirr : ∀ i, Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hSemi : Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))) :
    Representation.irreducibleCharacterFinset
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) =
      Finset.univ.image (fun i =>
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) := by
  classical
  let ρ : Representation ℂ G ((Σ i, Fin (d i)) → ℂ) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)
  let σ : ∀ i, Representation ℂ G (Fin (d i) → ℂ) :=
    fun i => Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)
  let : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Representation.natCard_ne_zero_complex (G := G))
  ext χ
  constructor
  · intro hχ
    obtain ⟨S, hS, rfl⟩ := (Representation.mem_irreducibleCharacterFinset ρ).mp hχ
    by_contra hn
    have hne : ∀ i, (σ i).character ≠ S.toRepresentation.character := by
      intro i hi
      exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    apply Representation.characterMultiplicity_ne_zero ρ ⟨S, hS, rfl⟩
    unfold Representation.characterMultiplicity
    simp_rw [show ∀ g, ρ.character g = ∑ i, (σ i).character g from
      character_blockMatrixRepresentation d D, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have := hirr i
    rw [Representation.char_orthonormal]
    apply ite_eq_right
    rintro ⟨e⟩
    exact hne i (Representation.char_iso e).symm
  · rintro hχ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hχ
    apply (Representation.mem_irreducibleCharacterFinset ρ).mpr
    rw [Representation.irreducibleCharacters_eq_leftRegular_of_isSemiRegular ρ hSemi]
    have := hirr i
    obtain ⟨f, hf⟩ := Representation.exists_intertwiningMap_leftRegular_ne_zero (σ i)
    exact Representation.character_mem_irreducibleCharacters_of_ne_zero _ (σ i) f hf

omit [Fintype G] in
/-- Repeating each irreducible block by its dimension multiplies its character by
that dimension. Source: SCP10, Section 7, regular representation decomposition. -/
theorem character_multiplicityRestoredRepresentation (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    Representation.character
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (multiplicityRestoredRepresentation d D)) g =
      ∑ i, (d i : ℂ) *
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) g := by
  change LinearMap.trace ℂ _ (Matrix.toLin' (multiplicityRestoredRepresentation d D g)) = _
  rw [Matrix.trace_toLin'_eq]
  change (Matrix.blockDiagonal' (fun i =>
    D i g ⊗ₖ (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ))).trace = _
  rw [Matrix.trace_blockDiagonal']
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.trace_kronecker, Matrix.trace_one]
  simp only [Fintype.card_fin]
  rw [mul_comm]
  congr 1
  exact (Matrix.trace_toLin'_eq (D i g)).symm

omit [Fintype G] in
/-- A complete distinct irreducible block family, repeated by its dimensions,
has the regular character. Source: SCP10, Definition 4.5 and Section 7. -/
theorem character_multiplicityRestoredRepresentation_eq_regular [Finite G] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hirr : ∀ i, Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hcross : ∀ i j, i ≠ j →
      Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j)))
    (hSemi : Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))) :
    Representation.character
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (multiplicityRestoredRepresentation d D)) =
      (Representation.leftRegular ℂ G).character := by
  classical
  let _ := Fintype.ofFinite G
  funext g
  rw [character_multiplicityRestoredRepresentation, Representation.character_leftRegular]
  have h := Representation.sum_irreducibleCharacters_mul_of_isSemiRegular _ hSemi g
  rw [irreducibleCharacterFinset_blockMatrixRepresentation d D hirr hSemi,
    Finset.sum_image] at h
  · simpa only [Representation.char_one, Module.finrank_pi, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h
  · intro i hi j hj hij
    by_contra hne
    exact hcross i j hne hij

/-- The matrix of all supplied irreducible matrix coefficients. Its rows retain
both matrix indices, and its columns are group elements. Source: the Fourier
coordinates underlying SCP10, Section 7. -/
def irreducibleBlockFourierMatrix (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    Matrix (Σ i, Fin (d i) × Fin (d i)) G ℂ :=
  fun x g => D x.1 g x.2.1 x.2.2

/-- Semi-regularity makes the matrix-coefficient Fourier map injective.
Source: SCP10, Definition 4.5 and the trace-dual identity of Lemma 4.6. -/
theorem irreducibleBlockFourierMatrix_injective [DecidableEq G] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hSemi : Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))) :
    Function.Injective (Matrix.toLin' (irreducibleBlockFourierMatrix d D)) := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro c hc
  have hmat : ∑ g : G, c g • blockMatrixRepresentation d D g = 0 := by
    ext ⟨i, a⟩ ⟨j, b⟩
    change (∑ g : G, c g • Matrix.blockDiagonal' (fun i => D i g))
      ⟨i, a⟩ ⟨j, b⟩ = 0
    simp only [Matrix.sum_apply, Matrix.smul_apply]
    by_cases hij : i = j
    · subst j
      have hv := congrFun hc ⟨i, (a, b)⟩
      simpa only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        irreducibleBlockFourierMatrix, Pi.zero_apply, Matrix.blockDiagonal'_apply_eq,
        smul_eq_mul, mul_comm] using hv
    · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hij, smul_zero,
        Finset.sum_const_zero]
  have hρ : ∑ g : G, c g •
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) g = 0 := by
    change ∑ g : G, c g • Matrix.toLinAlgEquiv' (blockMatrixRepresentation d D g) = 0
    have h := congrArg Matrix.toLinAlgEquiv' hmat
    simpa only [map_sum, map_smul, map_zero] using h
  exact funext ((Fintype.linearIndependent_iff.mp
    (Representation.linearIndependent_of_isSemiRegular _ hSemi)) c hρ)

/-- Left translation of group elements acts on the first matrix index of Fourier
coefficients. Source: SCP10, Section 7, regular representation decomposition. -/
theorem irreducibleBlockFourierMatrix_intertwining [DecidableEq G] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    irreducibleBlockFourierMatrix d D * leftRegularMatrix G g =
      multiplicityRestoredRepresentation d D g * irreducibleBlockFourierMatrix d D := by
  classical
  ext ⟨i, a, b⟩ h
  rw [Matrix.mul_apply]
  simp only [irreducibleBlockFourierMatrix, leftRegularMatrix_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [map_mul, Matrix.mul_apply]
  change (∑ c, D i g a c * D i h c b) =
    ∑ x, Matrix.blockDiagonal'
      (fun j => D j g ⊗ₖ (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ))
        ⟨i, (a, b)⟩ x * D x.1 h x.2.1 x.2.2
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply,
      Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
      ite_mul, zero_mul]
    simp
  · intro j hj hji
    simp only [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hji),
      zero_mul, Finset.sum_const_zero]
  · simp

/-- The dimension-restored block space and the regular space have equal
cardinality, derived from equality of their characters at the identity.
Source: SCP10, Section 7, regular representation decomposition. -/
theorem card_multiplicityRestored_eq (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hirr : ∀ i, Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hcross : ∀ i j, i ≠ j →
      Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j)))
    (hSemi : Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))) :
    Fintype.card (Σ i, Fin (d i) × Fin (d i)) = Fintype.card G := by
  classical
  have h := congrFun (character_multiplicityRestoredRepresentation_eq_regular
    d D hirr hcross hSemi) 1
  rw [Representation.char_one, Representation.character_leftRegular, ite_eq_left rfl] at h
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card, Nat.cast_inj] using h

/-- The explicit Fourier map gives an equivalence between any complete distinct
irreducible block family with dimension multiplicities and the regular representation.
Source: SCP10, Definition 4.5 and Section 7. -/
theorem nonempty_equiv_multiplicityRestored_leftRegular [DecidableEq G] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hirr : ∀ i, Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hcross : ∀ i j, i ≠ j →
      Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j)))
    (hSemi : Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))) :
    Nonempty (Representation.Equiv (Matrix.toLinAlgEquiv'.toMonoidHom.comp
      (multiplicityRestoredRepresentation d D))
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (leftRegularMatrix G))) := by
  classical
  let R := Matrix.toLin' (irreducibleBlockFourierMatrix d D)
  have hdim : Module.finrank ℂ (G → ℂ) =
      Module.finrank ℂ ((Σ i, Fin (d i) × Fin (d i)) → ℂ) := by
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one] using
      (card_multiplicityRestored_eq d D hirr hcross hSemi).symm
  let e := R.linearEquivOfInjective (irreducibleBlockFourierMatrix_injective d D hSemi) hdim
  refine ⟨(Representation.Equiv.mk e fun g => ?_).symm⟩
  change R.comp (Matrix.toLin' (leftRegularMatrix G g)) =
    (Matrix.toLin' (multiplicityRestoredRepresentation d D g)).comp R
  simpa only [R, Matrix.toLin'_mul] using
    congrArg Matrix.toLin' (irreducibleBlockFourierMatrix_intertwining d D g)

/-- Complete distinct irreducible blocks admit mutually inverse rectangular
coordinates conjugating their dimension restoration to the regular matrices.
Source: SCP10, Section 7. -/
theorem exists_invertible_multiplicityRestored_leftRegular [DecidableEq G] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hirr : ∀ i, Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hcross : ∀ i j, i ≠ j →
      Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j)))
    (hSemi : Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))) :
    ∃ (S : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
      (R : Matrix (Σ i, Fin (d i) × Fin (d i)) G ℂ),
      R * S = 1 ∧ S * R = 1 ∧
        ∀ g, leftRegularMatrix G g = S * multiplicityRestoredRepresentation d D g * R := by
  obtain ⟨e⟩ := nonempty_equiv_multiplicityRestored_leftRegular d D hirr hcross hSemi
  let S := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
  let R := LinearMap.toMatrix' e.toLinearEquiv.symm.toLinearMap
  have hRS : R * S = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : e.toLinearEquiv.symm.toLinearMap.comp e.toLinearEquiv.toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.toLinearEquiv.symm_apply_apply x
    rw [hcomp, LinearMap.toMatrix'_id]
  have hSR : S * R = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : e.toLinearEquiv.toLinearMap.comp e.toLinearEquiv.symm.toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.toLinearEquiv.apply_symm_apply x
    rw [hcomp, LinearMap.toMatrix'_id]
  refine ⟨S, R, hRS, hSR, fun g => ?_⟩
  have he : S * multiplicityRestoredRepresentation d D g = leftRegularMatrix G g * S := by
    have h := congrArg LinearMap.toMatrix' (e.isIntertwining' g)
    change LinearMap.toMatrix' (e.toLinearEquiv.toLinearMap.comp
      (Matrix.toLin' (multiplicityRestoredRepresentation d D g))) =
        LinearMap.toMatrix' ((Matrix.toLin' (leftRegularMatrix G g)).comp
          e.toLinearEquiv.toLinearMap) at h
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using h
  rw [he, Matrix.mul_assoc, hSR, Matrix.mul_one]

/-- Normalize the Fourier row of an irreducible block by √(dᵢ/|G|).
Source: the unitary regular decomposition in SCP10, Section 7. -/
def normalizedIrreducibleBlockFourierMatrix (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    Matrix (Σ i, Fin (d i) × Fin (d i)) G ℂ :=
  fun x g => (Real.sqrt ((d x.1 : ℝ) / Fintype.card G) : ℂ) * D x.1 g x.2.1 x.2.2

private theorem normalizedIrreducibleBlockFourierMatrix_intertwining [DecidableEq G]
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (g : G) :
    normalizedIrreducibleBlockFourierMatrix d D * leftRegularMatrix G g =
      multiplicityRestoredRepresentation d D g *
        normalizedIrreducibleBlockFourierMatrix d D := by
  let W : Matrix (Σ i, Fin (d i) × Fin (d i)) (Σ i, Fin (d i) × Fin (d i)) ℂ :=
    Matrix.diagonal (fun x => (Real.sqrt ((d x.1 : ℝ) / Fintype.card G) : ℂ))
  have hW : Commute W (multiplicityRestoredRepresentation d D g) := by
    ext ⟨i, a, b⟩ ⟨j, c, e⟩
    simp only [W, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [multiplicityRestoredRepresentation, MonoidHom.coe_mk, OneHom.coe_mk]
    by_cases hij : i = j
    · subst j
      exact mul_comm _ _
    · simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hij, mul_zero, zero_mul]
  have hR : normalizedIrreducibleBlockFourierMatrix d D =
      W * irreducibleBlockFourierMatrix d D := by
    ext x h
    simp only [W, Matrix.diagonal_mul, normalizedIrreducibleBlockFourierMatrix,
      irreducibleBlockFourierMatrix]
  rw [hR, Matrix.mul_assoc, irreducibleBlockFourierMatrix_intertwining,
    ← Matrix.mul_assoc W, hW.eq, Matrix.mul_assoc]

private theorem normalizedIrreducibleBlockFourierMatrix_isIsometry [DecidableEq G]
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hD : ∀ i g, D i g ∈ Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hirr : ∀ i, Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hcross : ∀ i j, i ≠ j →
      Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j)))
    (hSemi : Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))) :
    (normalizedIrreducibleBlockFourierMatrix d D).IsIsometry := by
  classical
  have hstar : ∀ i g, (D i g)ᴴ = D i g⁻¹ := by
    intro i g
    apply left_inv_eq_right_inv (Matrix.mem_unitaryGroup_iff'.mp (hD i g))
    rw [← map_mul, mul_inv_cancel, map_one]
  have hchar : ∀ g, ∑ i, (d i : ℂ) * (D i g).trace =
      if g = 1 then (Nat.card G : ℂ) else 0 := by
    intro g
    have h := congrFun (character_multiplicityRestoredRepresentation_eq_regular
      d D hirr hcross hSemi) g
    rw [character_multiplicityRestoredRepresentation, Representation.character_leftRegular] at h
    change (∑ i, (d i : ℂ) * LinearMap.trace ℂ _ (Matrix.toLin' (D i g))) = _ at h
    by_cases hg : g = 1 <;>
      simpa only [Matrix.trace_toLin'_eq, hg, ite_true, ite_false] using h
  change _ * _ = 1
  ext g h
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  have hterm : ∀ i, (∑ p : Fin (d i) × Fin (d i),
      (normalizedIrreducibleBlockFourierMatrix d D)ᴴ g ⟨i, p⟩ *
        normalizedIrreducibleBlockFourierMatrix d D ⟨i, p⟩ h) =
      ((d i : ℂ) / Fintype.card G) * (D i (g⁻¹ * h)).trace := by
    intro i
    let w : ℂ := (Real.sqrt ((d i : ℝ) / Fintype.card G) : ℂ)
    have hw : w * w = (d i : ℂ) / Fintype.card G := by
      dsimp only [w]
      rw [← pow_two, Complex.ofReal_sqrt_sq _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      push_cast
      rfl
    change (∑ p : Fin (d i) × Fin (d i), star (w * D i g p.1 p.2) *
      (w * D i h p.1 p.2)) = _
    have hentry : ∀ a b, star (w * D i g a b) * (w * D i h a b) =
        ((d i : ℂ) / Fintype.card G) * (star (D i g a b) * D i h a b) := by
      intro a b
      rw [star_mul, show star w = w by simp [w], ← hw]
      ring
    simp_rw [hentry]
    rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    congr 1
    rw [map_mul, ← hstar]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [hterm]
  have hsum : (∑ i, ((d i : ℂ) / Fintype.card G) * (D i (g⁻¹ * h)).trace) =
      (Fintype.card G : ℂ)⁻¹ * ∑ i, (d i : ℂ) * (D i (g⁻¹ * h)).trace := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, hchar]
  by_cases hgh : g = h
  · subst h
    simp [Nat.card_eq_fintype_card]
  · simp [inv_mul_eq_one, hgh]

/-- A unitary complete distinct irreducible block family admits unitary rectangular
coordinates with the native left regular matrices. The coordinate matrix is the
adjoint of the normalized matrix-coefficient Fourier transform.
Source: SCP10, Definition 4.5 and Section 7, lines 2947–3019. -/
theorem exists_isometry_multiplicityRestored_leftRegular [DecidableEq G] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hD : ∀ i g, D i g ∈ Matrix.unitaryGroup (Fin (d i)) ℂ)
    (hirr : ∀ i, Representation.IsIrreducible
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hcross : ∀ i j, i ≠ j →
      Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j)))
    (hSemi : Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))) :
    ∃ Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ,
      Q.IsIsometry ∧ Q * Qᴴ = 1 ∧
        ∀ g, leftRegularMatrix G g = Q * multiplicityRestoredRepresentation d D g * Qᴴ := by
  let R := normalizedIrreducibleBlockFourierMatrix d D
  have hR : Rᴴ * R = 1 :=
    normalizedIrreducibleBlockFourierMatrix_isIsometry d D hD hirr hcross hSemi
  have hRR : R * Rᴴ = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq G (Σ i, Fin (d i) × Fin (d i)) ℂ
      (card_multiplicityRestored_eq d D hirr hcross hSemi).symm).mp hR
  refine ⟨Rᴴ, ?_, ?_, fun g => ?_⟩
  · simpa only [Matrix.IsIsometry, Matrix.conjTranspose_conjTranspose] using hRR
  · simpa only [Matrix.conjTranspose_conjTranspose] using hR
  · rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← normalizedIrreducibleBlockFourierMatrix_intertwining, ← Matrix.mul_assoc,
      hR, Matrix.one_mul]

end TNLean.PEPS
