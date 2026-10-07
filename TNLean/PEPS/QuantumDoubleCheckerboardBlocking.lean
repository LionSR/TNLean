/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.FinCases
import TNLean.PEPS.Examples.QuantumDoubleLocalConstraint
import TNLean.PEPS.RegularTorusSite

/-!
# Exact open checkerboard contraction for a finite group

New implementation following arXiv:1001.3807v3, Section 7.2, lines 2890–2911.
All eight external legs and four internal bonds are retained. Reversed lower-left
and upper-left sites give the literal clockwise K tuple without commutativity.
-/

open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G] [DecidableEq G] [Fintype G]

/-- Top, right, bottom and left legs of the unblocked group tensor.
Source: SCP10, `Section 7.2`, lines 2890–2895. -/
def quantumDoubleElementaryTensor (turned reversed : Bool) (η : Fin 4 → G)
    (s : G) : ℂ :=
  if (if turned then η 0 = η 3 ∧ η 2 = η 1 else η 0 = η 1 ∧ η 2 = η 3) ∧
      s = (if reversed then η 2 * (η 0)⁻¹ else η 0 * (η 2)⁻¹) then 1 else 0

/-- Four boundary pairs in clockwise order, starting with the northern side.
Source: SCP10, the four-site block, lines 2896–2911. -/
abbrev QuantumDoubleBlockBoundary := Fin 4 → G × G

/-- Original physical spins in clockwise order, starting at the upper right.
Source: SCP10, the four-site block, lines 2896–2911. -/
abbrev QuantumDoubleBlockSpins := Fin 4 → G

private def active (α : QuantumDoubleBlockBoundary) : Fin 4 → G := fun i => (α i).1

/-- Adjacent group color differences, in the physical order of the block.
Source: SCP10, `eq:ex:doubles-renorm-tensor`, lines 2904–2911. -/
def quantumDoubleBlockColorSpins (p : Fin 4 → G) : QuantumDoubleBlockSpins :=
  ![p 0 * (p 1)⁻¹, p 1 * (p 2)⁻¹, p 2 * (p 3)⁻¹, p 3 * (p 0)⁻¹]

private def blockTerm (α : QuantumDoubleBlockBoundary) (σ : QuantumDoubleBlockSpins)
    (x : Fin 4 → G) : ℂ :=
  quantumDoubleElementaryTensor false true ![(α 0).1, x 0, x 3, (α 3).2] (σ 3) *
  quantumDoubleElementaryTensor true false ![(α 0).2, (α 1).1, x 1, x 0] (σ 0) *
  quantumDoubleElementaryTensor false false ![x 1, (α 1).2, (α 2).1, x 2] (σ 1) *
  quantumDoubleElementaryTensor true true ![x 3, x 2, (α 2).2, (α 3).1] (σ 2)

/-- Contract precisely the four internal bonds of the actual 2×2 checkerboard
block, retaining its eight external group legs. Source: SCP10, lines 2896–2911. -/
def quantumDoubleCheckerboardBlock (α : QuantumDoubleBlockBoundary) (σ : QuantumDoubleBlockSpins) : ℂ :=
  ∑ x : Fin 4 → G, blockTerm α σ x

private def blockGuard (α : QuantumDoubleBlockBoundary) (σ : QuantumDoubleBlockSpins)
    (x : Fin 4 → G) : Prop :=
  ((α 0).1 = x 0 ∧ x 3 = (α 3).2 ∧ σ 3 = x 3 * ((α 0).1)⁻¹) ∧
  ((α 0).2 = x 0 ∧ x 1 = (α 1).1 ∧ σ 0 = (α 0).2 * (x 1)⁻¹) ∧
  (x 1 = (α 1).2 ∧ (α 2).1 = x 2 ∧ σ 1 = x 1 * ((α 2).1)⁻¹) ∧
  (x 3 = (α 3).1 ∧ (α 2).2 = x 2 ∧ σ 2 = (α 2).2 * (x 3)⁻¹)

private instance blockGuardDecidable (α : QuantumDoubleBlockBoundary) (σ : QuantumDoubleBlockSpins)
    (x : Fin 4 → G) : Decidable (blockGuard α σ x) := by
  unfold blockGuard
  infer_instance

private theorem blockTerm_eq (α : QuantumDoubleBlockBoundary) (σ : QuantumDoubleBlockSpins)
    (x : Fin 4 → G) :
    blockTerm α σ x = if blockGuard α σ x then 1 else 0 := by
  unfold blockTerm quantumDoubleElementaryTensor blockGuard
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Bool.false_eq_true, ite_false, ite_true]
  split_ifs <;> simp_all <;> grind

private theorem blockGuard_iff (α : QuantumDoubleBlockBoundary) (σ : QuantumDoubleBlockSpins)
    (x : Fin 4 → G) :
    blockGuard α σ x ↔ x = active α ∧ (∀ i, (α i).2 = (α i).1) ∧
      σ = quantumDoubleBlockColorSpins (active α) := by
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
      fin_cases i <;> simp_all [quantumDoubleBlockColorSpins, active]
  · rintro ⟨rfl, hα, rfl⟩
    have h0 := hα 0
    have h1 := hα 1
    have h2 := hα 2
    have h3 := hα 3
    simp [blockGuard, active, quantumDoubleBlockColorSpins, h0, h1, h2, h3]

/-- The actual open block has one nonzero coefficient precisely at equal boundary
pairs and the four adjacent color differences. Source: SCP10, lines 2890–2911. -/
theorem quantumDoubleCheckerboardBlock_apply (α : QuantumDoubleBlockBoundary) (σ : QuantumDoubleBlockSpins) :
    quantumDoubleCheckerboardBlock α σ =
      if (∀ i, (α i).2 = (α i).1) ∧ σ = quantumDoubleBlockColorSpins (fun i => (α i).1)
      then 1 else 0 := by
  classical
  change (∑ x : Fin 4 → G, blockTerm α σ x) =
    if (∀ i, (α i).2 = (α i).1) ∧ σ = quantumDoubleBlockColorSpins (active α) then 1 else 0
  simp_rw [blockTerm_eq, blockGuard_iff]
  by_cases h : (∀ i, (α i).2 = (α i).1) ∧ σ = quantumDoubleBlockColorSpins (active α)
  · simp [h]
  · simp [h]

/-- The clockwise color-difference tensor of SCP10 equation (7.10). -/
def quantumDoubleBlockColorMatrix : Matrix (Fin 4 → G) (Fin 4 → G) ℂ :=
  fun σ p => if σ = quantumDoubleBlockColorSpins p then 1 else 0

/-- The open block uses exactly the source K tensor, including the order of all
four physical spins. Source: SCP10, equation (7.10), lines 2904–2911. -/
theorem quantumDoubleBlockColorMatrix_eq_KTensor (σ p : Fin 4 → G) :
    quantumDoubleBlockColorMatrix σ p =
      quantumDoubleKTensor G (p 0) (p 1) (p 2) (p 3) (finFourArrowEquiv G σ) := by
  have h : finFourArrowEquiv G (quantumDoubleBlockColorSpins p) =
      quantumDoubleKSpins (p 0, p 1, p 2, p 3) := rfl
  simp only [quantumDoubleBlockColorMatrix, quantumDoubleKTensor, ← h,
    Equiv.apply_eq_iff_eq]

end TNLean.PEPS
