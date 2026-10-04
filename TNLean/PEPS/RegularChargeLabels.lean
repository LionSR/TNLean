/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargeDetectorMatrix
import TNLean.PEPS.RegularFourier

/-!
# Charge labels derived from the regular representation

Every occurring irreducible character of the regular representation has an
actual unitary irreducible subrepresentation. The charge normalization and
orthogonality therefore require no additional unitarity hypothesis on a chosen
character. Source: SCP10, arXiv:1001.3807, charge detection, lines 2464–2486.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Every irreducible complex character occurs among the actual regular charge labels.
Source: SCP10, charge detection, lines 2464–2486. -/
theorem character_mem_regularChargeLabels {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (σ : Representation ℂ G E) [σ.IsIrreducible] :
    σ.character ∈ Representation.irreducibleCharacterFinset
      (Representation.euclideanMatrixRepresentation (leftRegularMatrix G)) := by
  apply (Representation.mem_irreducibleCharacterFinset _).mpr
  obtain ⟨f, hf⟩ := Representation.exists_intertwiningMap_leftRegular_ne_zero σ
  let e := leftRegularEuclideanMatrixEquiv (G := G)
  apply Representation.character_mem_irreducibleCharacters_of_ne_zero _ σ
    (e.toIntertwiningMap.comp f)
  intro hzero
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply e.toLinearEquiv.injective
  change e (f v) = e 0
  simpa using congrArg (fun f => f v) hzero

/-- A charge character is realized by an actual unitary irreducible subrepresentation
of the regular Hilbert space. Source: SCP10, charge detection, lines 2474–2486. -/
theorem exists_unitary_irreducible_regularChargeLabel (χ : G → ℂ)
    (hχ : χ ∈ Representation.irreducibleCharacterFinset
      (Representation.euclideanMatrixRepresentation (leftRegularMatrix G))) :
    ∃ S : Subrepresentation
        (Representation.euclideanMatrixRepresentation (leftRegularMatrix G)),
      S.toRepresentation.IsIrreducible ∧ χ = S.toRepresentation.character ∧
        ∀ g, LinearMap.adjoint (S.toRepresentation g) = S.toRepresentation g⁻¹ := by
  obtain ⟨S, hS, hχS⟩ := (Representation.mem_irreducibleCharacterFinset _).mp hχ
  exact ⟨S, hS, hχS.symm, Representation.adjoint_subrepresentation_of_unitary _
    leftRegularEuclidean_adjoint S⟩

/-- Actual regular charge labels have the source normalization without a separately
supplied unitary representation. Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeMatrix_normSq_of_mem_irreducibleCharacterFinset (χ : G → ℂ)
    (hχ : χ ∈ Representation.irreducibleCharacterFinset
      (Representation.euclideanMatrixRepresentation (leftRegularMatrix G))) (p x y : G) :
    ∑ r : G, ∑ s : G,
      star (regularChargeMatrix χ p x y r s) * regularChargeMatrix χ p x y r s =
        (Fintype.card G : ℂ) := by
  obtain ⟨S, hS, rfl, hunit⟩ := exists_unitary_irreducible_regularChargeLabel χ hχ
  let := hS
  simpa only [Nat.card_eq_fintype_card] using
    regularChargeMatrix_normSq S.toRepresentation hunit p x y

/-- Distinct actual regular charge labels are distinguished by the same matrix
projection, without a separately supplied unitary representation.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetectorMatrix_other_of_mem_irreducibleCharacterFinset
    (χ ψ : G → ℂ)
    (hχ : χ ∈ Representation.irreducibleCharacterFinset
      (Representation.euclideanMatrixRepresentation (leftRegularMatrix G)))
    (hψ : ψ ∈ Representation.irreducibleCharacterFinset
      (Representation.euclideanMatrixRepresentation (leftRegularMatrix G)))
    (hne : χ ≠ ψ) (p x y : G) :
    regularChargeDetectorMatrix χ *ᵥ
        (fun rs => regularChargeMatrix ψ p x y rs.1 rs.2) = 0 := by
  obtain ⟨S, hS, rfl, hunit⟩ := exists_unitary_irreducible_regularChargeLabel χ hχ
  obtain ⟨T, hT, rfl, _⟩ := exists_unitary_irreducible_regularChargeLabel ψ hψ
  let := hS
  let := hT
  exact regularChargeDetectorMatrix_other_chargeVector
    S.toRepresentation T.toRepresentation hunit hne p x y

end TNLean.PEPS
