/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularSpecialization
import TNLean.PEPS.AreaLaw.ZeroBoundary

/-! # Native rectangular consumers, including degenerate dimensions -/

open Matrix TNLean.PEPS TNLean.PEPS.AreaLaw
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

-- All side lengths and q = 1 are accepted by the same quantified theorem.
example (harea : UniformAreaLaw) : RectangularEntropyAreaLaw :=
  harea.rectangularEntropyAreaLaw

example (harea : UniformAreaLaw) : Approximation.SquareEntropyAreaLaw :=
  harea.rectangularEntropyAreaLaw.squareEntropyAreaLaw

-- One single constant applies to 0 × n, n × 0, 1 × 1, 1 × n, n × 1,
-- and all other rectangles. This consumer keeps the constant outside both sides.
example (harea : UniformAreaLaw) (q : ℕ) (hq : 1 ≤ q)
    (J Δ : ℝ) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ width height : ℕ,
      ∀ h : RectangularHamiltonian width height q J,
        ∀ E₀ : ℝ, ∀ Ω : RectangleStateSpace width height q,
          h.IsGappedGroundState E₀ Ω Δ → ∀ A : Finset (SquareLatticeVertex width height),
            FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin q) Ω A ≤
              C * Fintype.card
                {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} := by
  obtain ⟨C, hC, h⟩ := harea.rectangularEntropyAreaLaw q hq J Δ hJ hΔ
  exact ⟨C, hC, fun width height H E₀ Ω hΩ A ↦ (h width height H E₀ Ω hΩ A).1⟩

-- Local dimension one is also checked directly, without assuming the area law.
example {width height : ℕ} (Ω : RectangleStateSpace width height 1) (hΩ : ‖Ω‖ = 1)
    (A : Finset (SquareLatticeVertex width height)) :
    FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin 1) Ω A = 0 := by
  rw [← regionalEntropy_rectangleAreaLawState]
  exact regionalEntropy_eq_zero_of_q_eq_one ((norm_rectangleAreaLawState Ω).trans hΩ) _

example {height q : ℕ} (Ω : RectangleStateSpace 0 height q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (SquareLatticeVertex 0 height)) :
    FiniteProduct.entropy (fun _ : SquareLatticeVertex 0 height ↦ Fin q) Ω A = 0 := by
  have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
  rw [hA, ← regionalEntropy_rectangleAreaLawState]
  exact regionalEntropy_eq_zero_of_card_le_one _ ((norm_rectangleAreaLawState Ω).trans hΩ)
    _ (by simp)

example {width q : ℕ} (Ω : RectangleStateSpace width 0 q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (SquareLatticeVertex width 0)) :
    FiniteProduct.entropy (fun _ : SquareLatticeVertex width 0 ↦ Fin q) Ω A = 0 := by
  have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
  rw [hA, ← regionalEntropy_rectangleAreaLawState]
  exact regionalEntropy_eq_zero_of_card_le_one _ ((norm_rectangleAreaLawState Ω).trans hΩ)
    _ (by simp)

-- A zero native boundary gives zero entropy by the accepted zero-boundary theorem.
private theorem nativeEntropy_of_zero_boundary
    {width height q : ℕ} {J E₀ Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : RectangularHamiltonian width height q J) (Ω : RectangleStateSpace width height q)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (A : Finset (SquareLatticeVertex width height))
    (hA : Fintype.card
      {e : Edge (squareLatticeGraph width height) // IsRegionBoundaryEdge A e} = 0) :
    FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin q) Ω A = 0 := by
  rw [← regionalEntropy_rectangleAreaLawState]
  apply regionalEntropy_eq_zero_of_edgeBoundary_eq_empty (h.toAreaLawHamiltonian hJ) hΔ
    (h.isGappedGroundState_toAreaLawHamiltonian hJ hΩ)
  apply Finset.card_eq_zero.mp
  rw [card_edgeBoundary_rectangular, hA]

-- Empty and full cuts have zero entropy on every native rectangle.
example {width height q : ℕ} {J E₀ Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : RectangularHamiltonian width height q J) (Ω : RectangleStateSpace width height q)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) :
    FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin q) Ω ∅ = 0 := by
  apply nativeEntropy_of_zero_boundary hJ hΔ h Ω hΩ
  simp [Fintype.card_subtype, IsRegionBoundaryEdge]

example {width height q : ℕ} {J E₀ Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : RectangularHamiltonian width height q J) (Ω : RectangleStateSpace width height q)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) :
    FiniteProduct.entropy (fun _ : SquareLatticeVertex width height ↦ Fin q)
      Ω Finset.univ = 0 := by
  apply nativeEntropy_of_zero_boundary hJ hΔ h Ω hΩ
  simp [Fintype.card_subtype, IsRegionBoundaryEdge]

-- The only possible one-site cuts have no crossing edge.
private theorem singleSite_boundary_card_eq_zero
    (A : Finset (SquareLatticeVertex 1 1)) :
    Fintype.card {e : Edge (squareLatticeGraph 1 1) // IsRegionBoundaryEdge A e} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun e ↦ ?_⟩
  exact (squareLatticeGraph 1 1).ne_of_adj e.val.property.2 (Subsingleton.elim _ _)

example {q : ℕ} {J E₀ Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : RectangularHamiltonian 1 1 q J) (Ω : RectangleStateSpace 1 1 q)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (A : Finset (SquareLatticeVertex 1 1)) :
    FiniteProduct.entropy (fun _ : SquareLatticeVertex 1 1 ↦ Fin q) Ω A = 0 :=
  nativeEntropy_of_zero_boundary hJ hΔ h Ω hΩ A (singleSite_boundary_card_eq_zero A)

-- A one-column and a one-row cut each have one original crossing edge.
example : Fintype.card {e : Edge (squareLatticeGraph 1 3) //
    IsRegionBoundaryEdge {(0, 0)} e} = 1 := by decide

example : Fintype.card {e : Edge (squareLatticeGraph 3 1) //
    IsRegionBoundaryEdge {(0, 0)} e} = 1 := by decide

-- Empty native inner and endpoint boundaries really have zero sites.
example (width height : ℕ) :
    rectangleInnerBoundary (∅ : Finset (SquareLatticeVertex width height)) = ∅ := by
  simp [rectangleInnerBoundary]

example (width height : ℕ) :
    rectangleEndpointBoundary (Finset.univ : Finset (SquareLatticeVertex width height)) = ∅ := by
  simp [rectangleEndpointBoundary]

-- Cancelling, individually non-Hermitian site terms satisfy the source model.
private def cancellingSite (v : SquareLatticeVertex 2 1) :
    Matrix (RectangleConfiguration 2 1 1) (RectangleConfiguration 2 1 1) ℂ :=
  if v.1 = 0 then Complex.I • 1 else (-Complex.I) • 1

private def cancellingHamiltonian : RectangularHamiltonian 2 1 1 1 where
  siteTerm := cancellingSite
  edgeTerm _ := 0
  site_supported v := by
    unfold cancellingSite
    split_ifs <;> exact Submodule.smul_mem _ _ (QuantumCircuit.one_mem_supportedOperators _)
  edge_supported _ := Submodule.zero_mem _
  site_norm_le v := by
    unfold cancellingSite
    split_ifs <;> simp [norm_smul]
  edge_norm_le _ := by simp
  hermitian := by
    simp [cancellingSite, Fintype.sum_prod_type, Fin.sum_univ_two]

example : ¬ (cancellingHamiltonian.siteTerm (0, 0)).IsHermitian := by
  intro h
  have hi := congrArg
    (fun M : Matrix (RectangleConfiguration 2 1 1) (RectangleConfiguration 2 1 1) ℂ ↦
      (M (fun _ ↦ 0) (fun _ ↦ 0)).im) h.eq
  norm_num [cancellingHamiltonian, cancellingSite, Matrix.conjTranspose_apply,
    Matrix.smul_apply] at hi

example : cancellingHamiltonian.operator = 0 := by
  simp [RectangularHamiltonian.operator, cancellingHamiltonian, cancellingSite,
    Fintype.sum_prod_type, Fin.sum_univ_two]

example : (cancellingHamiltonian.toAreaLawHamiltonian (by norm_num)).operator = 0 := by
  rw [RectangularHamiltonian.toAreaLawHamiltonian_operator]
  simp [RectangularHamiltonian.operator, cancellingHamiltonian, cancellingSite,
    Fintype.sum_prod_type, Fin.sum_univ_two]
