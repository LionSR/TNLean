/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TriangularPaddingDecomposition

/-!
# An exact auxiliary fusion family for operator action

The disjoint union of padded operator labels and padded state labels has
only the original operator/operator and operator/state channels. All
state-left multiplicity spaces are empty. The exact fusion and action maps
therefore assemble into exact pairwise decompositions of this auxiliary
operator family, without introducing a zero tensor as an extra label.

This coordinate construction is used to derive the actual mixed pentagon
of Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `coupledpent`, from
ordinary complete-zipper coherence. It assumes neither pentagon equation.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- The auxiliary bond dimension is the original operator or state bond. -/
abbrev triangularBondDim (χ : Fin r → ℕ) (D : Fin s → ℕ) : Fin r ⊕ Fin s → ℕ :=
  Sum.elim χ D

/-- Operators occupy the upper-left physical corner and states the
upper-right physical column of the same enlarged alphabet. -/
def triangularTensor (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x)) :
    ∀ q : Fin r ⊕ Fin s, MPOTensor (d + 1) (triangularBondDim χ D q)
  | .inl a => operatorPhysicalPadding (O a)
  | .inr x => statePhysicalPadding (A x)

/-- Only operator/operator-to-operator and operator/state-to-state
channels are present in the auxiliary family. -/
def triangularFusionMultiplicity (N : Fin r → Fin r → Fin r → ℕ)
    (M : Fin r → Fin s → Fin s → ℕ) :
    (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℕ
  | .inl a, .inl b, .inl c => N a b c
  | .inl a, .inr x, .inr y => M a x y
  | _, _, _ => 0

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)

/-- Auxiliary analysis maps are literally the original fusion or action
maps on the two populated kinds of channels. -/
def triangularFusionAnalysis : ∀ a b c : Fin r ⊕ Fin s,
    Fin (triangularFusionMultiplicity N M a b c) →
      Matrix (Fin (triangularBondDim χ D c))
        (Fin (triangularBondDim χ D a * triangularBondDim χ D b)) ℂ
  | .inl a, .inl b, .inl c => VF a b c
  | .inl a, .inr x, .inr y => VA a x y
  | .inl _, .inl _, .inr _ => Fin.elim0
  | .inl _, .inr _, .inl _ => Fin.elim0
  | .inr _, _, _ => Fin.elim0

/-- Auxiliary synthesis maps retain the original rectangular matrices,
including any proper ambient support idempotent. -/
def triangularFusionSynthesis : ∀ a b c : Fin r ⊕ Fin s,
    Fin (triangularFusionMultiplicity N M a b c) →
      Matrix (Fin (triangularBondDim χ D a * triangularBondDim χ D b))
        (Fin (triangularBondDim χ D c)) ℂ
  | .inl a, .inl b, .inl c => WF a b c
  | .inl a, .inr x, .inr y => WA a x y
  | .inl _, .inl _, .inr _ => Fin.elim0
  | .inl _, .inr _, .inl _ => Fin.elim0
  | .inr _, _, _ => Fin.elim0

/-- Exact fusion and exact action decompositions give the actual exact
auxiliary family. State-left products have empty channel spaces and zero
letters, rather than a zero-tensor summand. Source: GLM23 `fusiontensors`,
`eq:orthoW`, `fusiontensors2`, `eq:orthoV`, and `rawrels`. -/
theorem isBiorthogonalDecomposition_triangularTensor
    (O : ∀ a, MPOTensor d (χ a)) (A : ∀ x, MPSTensor d (D x))
    (hF : ∀ a b,
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
        (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
    (hA : ∀ a x,
      MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
        (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
        (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))
    (a b : Fin r ⊕ Fin s) :
    MPSTensor.IsBiorthogonalDecomposition
      (mulTensor (triangularTensor O A a) (triangularTensor O A b)).toMPSTensor
      (fun q : (c : Fin r ⊕ Fin s) × Fin (triangularFusionMultiplicity N M a b c) ↦
        (triangularTensor O A q.1).toMPSTensor)
      (fun q ↦ triangularFusionAnalysis VF VA a b q.1 q.2)
      (fun q ↦ triangularFusionSynthesis WF WA a b q.1 q.2) := by
  classical
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨c, μ⟩
        cases c with
        | inl c => exact (hF a b).retract ⟨c, μ⟩
        | inr x => exact Fin.elim0 μ
      · rintro ⟨c, μ⟩ ⟨c', ν⟩ hne
        cases c with
        | inr x => exact Fin.elim0 μ
        | inl c =>
          cases c' with
          | inr x => exact Fin.elim0 ν
          | inl c' =>
            apply (hF a b).orthogonal ⟨c, μ⟩ ⟨c', ν⟩
            intro he
            apply hne
            cases he
            rfl
      · intro p
        have hp : (mulTensor (operatorPhysicalPadding (O a))
            (operatorPhysicalPadding (O b))).toMPSTensor p =
            ∑ q : (c : Fin r) × Fin (N a b c),
              WF a b q.1 q.2 * (operatorPhysicalPadding (O q.1)).toMPSTensor p *
                VF a b q.1 q.2 := by
          rw [mulTensor_operatorPhysicalPadding]
          exact ((hF a b).operatorPhysicalPadding).letter p
        rw [Fintype.sum_sigma, Fintype.sum_sum_type]
        change (mulTensor (operatorPhysicalPadding (O a))
            (operatorPhysicalPadding (O b))).toMPSTensor p =
          (∑ c : Fin r, ∑ mu : Fin (N a b c),
            WF a b c mu * (operatorPhysicalPadding (O c)).toMPSTensor p * VF a b c mu) +
          ∑ x : Fin s, ∑ mu : Fin 0,
            (Fin.elim0 mu : Matrix (Fin (χ a * χ b)) (Fin (D x)) ℂ) *
              (statePhysicalPadding (A x)).toMPSTensor p *
              (Fin.elim0 mu : Matrix (Fin (D x)) (Fin (χ a * χ b)) ℂ)
        simpa only [Fintype.sum_sigma, Finset.univ_eq_empty, Finset.sum_empty,
          Finset.sum_const_zero, add_zero] using hp
    | inr x =>
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨c, μ⟩
        cases c with
        | inl c => exact Fin.elim0 μ
        | inr y => exact (hA a x).retract ⟨y, μ⟩
      · rintro ⟨c, μ⟩ ⟨c', ν⟩ hne
        cases c with
        | inl c => exact Fin.elim0 μ
        | inr y =>
          cases c' with
          | inl c' => exact Fin.elim0 ν
          | inr y' =>
            apply (hA a x).orthogonal ⟨y, μ⟩ ⟨y', ν⟩
            intro he
            apply hne
            cases he
            rfl
      · intro p
        have hp : (mulTensor (operatorPhysicalPadding (O a))
            (statePhysicalPadding (A x))).toMPSTensor p =
            ∑ q : (y : Fin s) × Fin (M a x y),
              WA a x q.1 q.2 * (statePhysicalPadding (A q.1)).toMPSTensor p *
                VA a x q.1 q.2 := by
          rw [mulTensor_operatorPhysicalPadding_statePhysicalPadding]
          exact ((hA a x).statePhysicalPadding).letter p
        rw [Fintype.sum_sigma, Fintype.sum_sum_type]
        change (mulTensor (operatorPhysicalPadding (O a))
            (statePhysicalPadding (A x))).toMPSTensor p =
          (∑ c : Fin r, ∑ mu : Fin 0,
            (Fin.elim0 mu : Matrix (Fin (χ a * D x)) (Fin (χ c)) ℂ) *
              (operatorPhysicalPadding (O c)).toMPSTensor p *
              (Fin.elim0 mu : Matrix (Fin (χ c)) (Fin (χ a * D x)) ℂ)) +
          ∑ y : Fin s, ∑ mu : Fin (M a x y),
            WA a x y mu * (statePhysicalPadding (A y)).toMPSTensor p * VA a x y mu
        simpa only [Fintype.sum_sigma, Finset.univ_eq_empty, Finset.sum_empty,
          Finset.sum_const_zero, zero_add] using hp
  | inr x =>
    have : IsEmpty ((c : Fin r ⊕ Fin s) ×
        Fin (triangularFusionMultiplicity N M (.inr x) b c)) :=
      ⟨fun q ↦ Fin.elim0 q.2⟩
    refine ⟨fun q ↦ isEmptyElim q, fun q _ _ ↦ isEmptyElim q, ?_⟩
    intro p
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    cases b with
    | inl b =>
      change (mulTensor (statePhysicalPadding (A x))
        (operatorPhysicalPadding (O b))).toMPSTensor p = 0
      rw [mulTensor_statePhysicalPadding_operatorPhysicalPadding]
      rfl
    | inr y =>
      change (mulTensor (statePhysicalPadding (A x))
        (statePhysicalPadding (A y))).toMPSTensor p = 0
      rw [mulTensor_statePhysicalPadding_statePhysicalPadding]
      rfl

end MPOTensor
