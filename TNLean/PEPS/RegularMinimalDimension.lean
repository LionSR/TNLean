/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SemiRegularDimension
import TNLean.PEPS.RegularMinimalRepresentation

/-!
# The smallest semi-regular representation

The finite group determines a unitary direct sum with one copy of each
irreducible representation. Its dimension is no greater than that of any
finite-dimensional complex semi-regular representation, whether or not the
comparison representation carries an invariant inner product.

Source: SCP10, Section 7, lines 2947–3019, where this direct sum is called the
smallest semi-regular representation. The existence data come from the actual
regular Fourier decomposition; the dimension comparison uses Maschke's theorem.
-/

open Module
namespace TNLean.PEPS
open Representation
universe u v w
variable {G : Type u} [Group G]

/-- Distinct irreducible matrix sectors occupy no more dimensions than a
semi-regular representation. Source: SCP10, Definition 4.5 and Section 7,
lines 1010–1013 and 2947–3019. -/
theorem finrank_blockMatrixRepresentation_le_of_isSemiRegular [Finite G]
    {I : Type w} [Finite I] (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hirr : ∀ i, IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hchar : Function.Injective (fun i =>
      character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))))
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : Representation ℂ G V) (hσ : σ.IsSemiRegular) :
    finrank ℂ ((Σ i, Fin (d i)) → ℂ) ≤ finrank ℂ V := by
  let _ := Fintype.ofFinite I
  simpa using sum_finrank_le_of_distinct_irreducibles_of_isSemiRegular σ hσ
    (fun i => Fin (d i) → ℂ)
    (fun i => Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) hirr hchar

/-- Every finite group has a unitary multiplicity-one semi-regular representation
of smallest dimension among all finite-dimensional complex semi-regular
representations. The comparison representations need not be unitary.
Source: SCP10, Section 7, lines 2947–3019. -/
theorem exists_smallestSemiRegular_matrixRepresentation [Fintype G] :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ),
      (∀ i, 0 < d i) ∧
      (∀ i g, D i g ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) ∧
      (∀ i, IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) ∧
      (∀ i j, i ≠ j →
        character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
          character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j))) ∧
      (∀ g, blockMatrixRepresentation d D g ∈
        Matrix.unitaryGroup (Σ i, Fin (d i)) ℂ) ∧
      IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) ∧
      (∀ i, characterMultiplicity
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))
        (character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) = 1) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (σ : Representation ℂ G V), σ.IsSemiRegular →
        finrank ℂ ((Σ i, Fin (d i)) → ℂ) ≤ finrank ℂ V := by
  classical
  obtain ⟨K, d, b, D, hd, hunit, hirr, hcross, hFourier, hUunit, hSemi, hmult⟩ :=
    exists_minimalSemiRegular_leftRegular_fourier (G := G)
  refine ⟨K, d, D, hd, hunit, hirr, hcross, hUunit, hSemi, hmult, ?_⟩
  intro V _ _ _ σ hσ
  exact finrank_blockMatrixRepresentation_le_of_isSemiRegular d D hirr
    (fun i j h => by
      by_contra hne
      exact hcross i j hne h) σ hσ
end TNLean.PEPS
