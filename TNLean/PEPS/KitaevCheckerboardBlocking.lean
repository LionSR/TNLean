/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FinCases
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.PEPS.SemiRegularBondSupport
import TNLean.PEPS.Examples.QuantumDouble

/-!
# The actual four-site blocking of Kitaev's binary tensor

Source: SCP10, arXiv:1001.3807, equations `eq:ex:kitaev-tens` and
`eq:ex:kitaev-colordiff-rep`, lines 2718–2827. The checkerboard orientations
are those of `figs6/tc-tensor-orientation` and `figs6/tc-2x2-renorm`.
This is an exact open-block contraction, with every external leg retained.
The contraction uses its four literal internal bonds, with physical sites ordered
clockwise from the upper-right corner. Boundary pairs are ordered north, east,
south and west, and each pair is read clockwise along that side. This proves the
coefficient reduction; it does not identify a physical renormalization operation
or a globally blocked lattice state. No Hamiltonian assertion is made.
-/

open scoped BigOperators Matrix
namespace TNLean.PEPS

/-- The binary color group, written additively. Source: SCP10, lines 2718–2748. -/
abbrev KitaevBit := ZMod 2

/-- Top, right, bottom and left legs of the unblocked binary tensor.
Source: SCP10, `eq:ex:kitaev-tens`, lines 2718–2748. -/
def kitaevElementaryTensor (turned : Bool) (η : Fin 4 → KitaevBit)
    (s : KitaevBit) : ℂ :=
  if (if turned then η 0 = η 3 ∧ η 2 = η 1 else η 0 = η 1 ∧ η 2 = η 3) ∧
      s = η 0 + η 2 then 1 else 0

/-- Four boundary pairs in clockwise order, starting with the northern side.
Source: SCP10, the four-site block, lines 2755–2794. -/
abbrev KitaevBlockBoundary := Fin 4 → KitaevBit × KitaevBit

/-- Original physical spins in clockwise order, starting at the upper right.
Source: SCP10, the four-site block, lines 2755–2794. -/
abbrev KitaevBlockSpins := Fin 4 → KitaevBit

private def active (α : KitaevBlockBoundary) : Fin 4 → KitaevBit := fun i => (α i).1

/-- Adjacent binary color differences, in the physical order of the block.
Source: SCP10, `eq:ex:kitaev-colordiff-rep`, lines 2809–2827. -/
def kitaevBlockColorSpins (p : Fin 4 → KitaevBit) : KitaevBlockSpins :=
  ![p 0 + p 1, p 1 + p 2, p 2 + p 3, p 3 + p 0]

private def blockTerm (α : KitaevBlockBoundary) (σ : KitaevBlockSpins)
    (x : Fin 4 → KitaevBit) : ℂ :=
  kitaevElementaryTensor false ![(α 0).1, x 0, x 3, (α 3).2] (σ 3) *
  kitaevElementaryTensor true ![(α 0).2, (α 1).1, x 1, x 0] (σ 0) *
  kitaevElementaryTensor false ![x 1, (α 1).2, (α 2).1, x 2] (σ 1) *
  kitaevElementaryTensor true ![x 3, x 2, (α 2).2, (α 3).1] (σ 2)

/-- Contract precisely the four internal bonds of the actual 2×2 checkerboard
block, retaining its eight external binary legs. Source: SCP10, lines 2755–2794. -/
def kitaevCheckerboardBlock (α : KitaevBlockBoundary) (σ : KitaevBlockSpins) : ℂ :=
  ∑ x : Fin 4 → KitaevBit, blockTerm α σ x

private def blockGuard (α : KitaevBlockBoundary) (σ : KitaevBlockSpins)
    (x : Fin 4 → KitaevBit) : Prop :=
  ((α 0).1 = x 0 ∧ x 3 = (α 3).2 ∧ σ 3 = (α 0).1 + x 3) ∧
  ((α 0).2 = x 0 ∧ x 1 = (α 1).1 ∧ σ 0 = (α 0).2 + x 1) ∧
  (x 1 = (α 1).2 ∧ (α 2).1 = x 2 ∧ σ 1 = x 1 + (α 2).1) ∧
  (x 3 = (α 3).1 ∧ (α 2).2 = x 2 ∧ σ 2 = x 3 + (α 2).2)

private instance blockGuardDecidable (α : KitaevBlockBoundary) (σ : KitaevBlockSpins)
    (x : Fin 4 → KitaevBit) : Decidable (blockGuard α σ x) := by
  unfold blockGuard
  infer_instance

private theorem blockTerm_eq (α : KitaevBlockBoundary) (σ : KitaevBlockSpins)
    (x : Fin 4 → KitaevBit) :
    blockTerm α σ x = if blockGuard α σ x then 1 else 0 := by
  unfold blockTerm kitaevElementaryTensor blockGuard
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Bool.false_eq_true, ite_false, ite_true]
  split_ifs <;> simp_all <;> grind

private theorem blockGuard_iff (α : KitaevBlockBoundary) (σ : KitaevBlockSpins)
    (x : Fin 4 → KitaevBit) :
    blockGuard α σ x ↔ x = active α ∧ (∀ i, (α i).2 = (α i).1) ∧
      σ = kitaevBlockColorSpins (active α) := by
  constructor
  · intro h
    rcases h with ⟨⟨hN, hW, hsW⟩, ⟨hN', hE, hsN⟩,
      ⟨hE', hS, hsE⟩, hW', hS', hsS⟩
    have hx : x = active α := by
      funext i
      fin_cases i <;> simp_all [active]
    refine ⟨hx, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp_all
    · funext i
      fin_cases i <;> simp_all [kitaevBlockColorSpins, active, add_comm]
  · rintro ⟨rfl, hα, rfl⟩
    have h0 := hα 0
    have h1 := hα 1
    have h2 := hα 2
    have h3 := hα 3
    simp [blockGuard, active, kitaevBlockColorSpins, h0, h1, h2, h3, add_comm]

/-- The actual open block has one nonzero coefficient precisely at equal boundary
pairs and the four adjacent color differences. Source: SCP10, lines 2755–2827. -/
theorem kitaevCheckerboardBlock_apply (α : KitaevBlockBoundary) (σ : KitaevBlockSpins) :
    kitaevCheckerboardBlock α σ =
      if (∀ i, (α i).2 = (α i).1) ∧ σ = kitaevBlockColorSpins (fun i => (α i).1)
      then 1 else 0 := by
  classical
  change (∑ x : Fin 4 → KitaevBit, blockTerm α σ x) =
    if (∀ i, (α i).2 = (α i).1) ∧ σ = kitaevBlockColorSpins (active α) then 1 else 0
  simp_rw [blockTerm_eq, blockGuard_iff]
  by_cases h : (∀ i, (α i).2 = (α i).1) ∧ σ = kitaevBlockColorSpins (active α)
  · simp [h]
  · simp [h]

/-- The four boundary CNOTs, each keeping the first color and adding it to the
second. Source: SCP10, lines 2760–2794. -/
def kitaevBoundaryCNOT : Equiv.Perm KitaevBlockBoundary :=
  Equiv.piCongrRight fun _ =>
    Equiv.prodShear (Equiv.refl KitaevBit) fun a => Equiv.addLeft a

/-- The CNOT acts on each doubled boundary pair by (a,b) ↦ (a,a+b).
Source: SCP10, the boundary CNOTs, lines 2760–2794. -/
theorem kitaevBoundaryCNOT_apply (α : KitaevBlockBoundary) (i : Fin 4) :
    kitaevBoundaryCNOT α i = ((α i).1, (α i).1 + (α i).2) := rfl

/-- Applying the boundary CNOTs twice is the identity.
Source: SCP10, the boundary CNOTs, lines 2760–2794. -/
theorem kitaevBoundaryCNOT_involutive : Function.Involutive kitaevBoundaryCNOT := by
  intro α
  funext i
  simp only [kitaevBoundaryCNOT_apply, CharTwo.add_cancel_left]

/-- The exact renormalization identity: the contracted four original tensors
become the color-difference tensor and four zero registers after the four boundary
CNOTs. Source: SCP10, lines 2755–2827. The physical spins are the four original
spins in clockwise order from the upper-right site. -/
theorem kitaevCheckerboardBlock_boundaryCNOT (α : KitaevBlockBoundary)
    (σ : KitaevBlockSpins) :
    kitaevCheckerboardBlock (kitaevBoundaryCNOT α) σ =
      if ∀ i, (α i).2 = 0 then
        (if σ = kitaevBlockColorSpins (fun i => (α i).1) then 1 else 0)
      else 0 := by
  rw [kitaevCheckerboardBlock_apply]
  change (if (∀ i, (α i).1 + (α i).2 = (α i).1) ∧
      σ = kitaevBlockColorSpins (fun i => (α i).1) then (1 : ℂ) else 0) = _
  simp only [add_eq_left, ite_and]

/-- The actual four-site contraction as a linear tensor map from its eight
boundary bits to its four original physical bits. Source: SCP10, lines 2755–2794. -/
def kitaevCheckerboardBlockMatrix :
    Matrix KitaevBlockSpins KitaevBlockBoundary ℂ :=
  fun σ α => kitaevCheckerboardBlock α σ

/-- The color-difference tensor as a matrix. Source: SCP10,
`eq:ex:kitaev-colordiff-rep`, lines 2809–2827. -/
def kitaevBlockColorMatrix : Matrix KitaevBlockSpins (Fin 4 → KitaevBit) ℂ :=
  fun σ p => if σ = kitaevBlockColorSpins p then 1 else 0

/-- Include four color registers by fixing all four other boundary registers
at zero. Source: SCP10, the boundary CNOT reduction, lines 2760–2794. -/
def kitaevBoundaryZeroEmbedding : (Fin 4 → KitaevBit) ↪ KitaevBlockBoundary where
  toFun p := fun i => (p i, 0)
  inj' := by
    intro p q h
    funext i
    exact congrArg Prod.fst (congrFun h i)

/-- The zero-register inclusion retains every active boundary color.
Source: SCP10, the boundary CNOT reduction, lines 2760–2794. -/
theorem kitaevBoundaryZeroEmbedding_apply (p : Fin 4 → KitaevBit) (i : Fin 4) :
    kitaevBoundaryZeroEmbedding p i = (p i, 0) := rfl

/-- The actual boundary CNOT is a unitary on the eight virtual binary legs.
Source: SCP10, the boundary CNOTs, lines 2760–2794. -/
theorem kitaevBoundaryCNOT_permMatrix_mem_unitaryGroup :
    kitaevBoundaryCNOT.permMatrix ℂ ∈ Matrix.unitaryGroup KitaevBlockBoundary ℂ :=
  kitaevBoundaryCNOT.permMatrix_mem_unitaryGroup

/-- Adding the zero registers is an isometry, with no dimensional assumption.
Source: SCP10, the boundary CNOT reduction, lines 2760–2794. -/
theorem kitaevBoundaryZeroEmbedding_isIsometry :
    Matrix.IsIsometry (endpointEmbeddingMatrix kitaevBoundaryZeroEmbedding) :=
  endpointEmbeddingMatrix_isIsometry kitaevBoundaryZeroEmbedding

/-- The actual blocked tensor map factors after a virtual boundary unitary
through the color-difference tensor and the projection onto four zero registers.
Source: SCP10, the CNOT blocking construction, lines 2760–2827. -/
theorem kitaevCheckerboardBlockMatrix_mul_boundaryCNOT :
    kitaevCheckerboardBlockMatrix * kitaevBoundaryCNOT.permMatrix ℂ =
      kitaevBlockColorMatrix * (endpointEmbeddingMatrix kitaevBoundaryZeroEmbedding)ᴴ := by
  ext σ α
  change ((fun β => kitaevCheckerboardBlock β σ) ᵥ*
    kitaevBoundaryCNOT.permMatrix ℂ) α = _
  rw [Matrix.vecMul_permMatrix]
  simp only [Function.comp_apply]
  have hsym : kitaevBoundaryCNOT.symm α = kitaevBoundaryCNOT α :=
    (Equiv.symm_apply_eq _).2 (kitaevBoundaryCNOT_involutive α).symm
  rw [hsym, kitaevCheckerboardBlock_boundaryCNOT]
  by_cases hα : ∀ i, (α i).2 = 0
  · have hzero : α = kitaevBoundaryZeroEmbedding (fun i => (α i).1) := by
      funext i
      exact Prod.ext rfl (hα i)
    rw [hzero]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, endpointEmbeddingMatrix,
      kitaevBoundaryZeroEmbedding.injective.eq_iff, kitaevBlockColorMatrix,
      kitaevBoundaryZeroEmbedding_apply]
    rfl
  · have hne : ∀ p, α ≠ kitaevBoundaryZeroEmbedding p := by
      intro p hp
      apply hα
      intro i
      exact congrArg Prod.snd (congrFun hp i)
    simp [hα, Matrix.mul_apply, Matrix.conjTranspose_apply, endpointEmbeddingMatrix, hne]

/-- The blocked color-difference tensor is the existing toric-code dual tensor,
with the cyclic physical reordering (upper-left, upper-right, lower-right,
lower-left). Source: SCP10, `eq:ex:kitaev-colordiff-rep`, lines 2809–2827,
and the review arXiv:2011.12127, Appendix A, lines 2460–2465. -/
theorem kitaevBlockColorMatrix_eq_quantumDoubleDualTensor
    (σ : KitaevBlockSpins) (p : Fin 4 → KitaevBit) :
    kitaevBlockColorMatrix σ p =
      quantumDoubleDualTensor ToricCodeGroup
        (Multiplicative.ofAdd (p 0)) (Multiplicative.ofAdd (p 1))
        (Multiplicative.ofAdd (p 2)) (Multiplicative.ofAdd (p 3))
        (Multiplicative.ofAdd (σ 3), Multiplicative.ofAdd (σ 0),
          Multiplicative.ofAdd (σ 1), Multiplicative.ofAdd (σ 2)) := by
  have h : σ = kitaevBlockColorSpins p ↔
      (Multiplicative.ofAdd (σ 3), Multiplicative.ofAdd (σ 0),
        Multiplicative.ofAdd (σ 1), Multiplicative.ofAdd (σ 2)) =
      quantumDoubleDualSpins (Multiplicative.ofAdd (p 0), Multiplicative.ofAdd (p 1),
        Multiplicative.ofAdd (p 2), Multiplicative.ofAdd (p 3)) := by
    constructor
    · rintro rfl
      simp [quantumDoubleDualSpins, kitaevBlockColorSpins,
        ← ofAdd_neg, ← ofAdd_add, CharTwo.neg_eq, add_comm]
    · intro h
      simp only [quantumDoubleDualSpins, ← ofAdd_neg,
        ← ofAdd_add, CharTwo.neg_eq, Equiv.apply_eq_iff_eq,
        Prod.mk.injEq] at h
      funext i
      fin_cases i <;> simp_all [kitaevBlockColorSpins, add_comm]
  unfold kitaevBlockColorMatrix quantumDoubleDualTensor
  simp only [← h]

end TNLean.PEPS
