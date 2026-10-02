/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.PEPS.RegularTwistedRegionProjectorCoordinates

/-!
# Mixed Gram matrices of actual twisted canonical blocks

In spanning-tree coordinates, the mixed Gram matrix sums pairs of translations
whose transported boundary labels and conjugated cycle residuals agree. Distinct
simultaneous conjugacy classes of cycle residuals therefore have orthogonal
physical ranges. All bond insertions, including crossing operators, remain arbitrary.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`Papers/1001.3807/paper_v3.tex`, lines 1935–2072.
These are exact finite-contraction statements, without a supplied mixed Gram identity
or a topological assumption on the region.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

private theorem delta_sum_pairing {H X Y : Type*}
    [Fintype H] [DecidableEq H] [Fintype X] [Fintype Y] (f : X → H) (g : Y → H) :
    (∑ h : H, (∑ x : X, if h = f x then (1 : ℂ) else 0) *
      (∑ y : Y, if h = g y then (1 : ℂ) else 0)) =
        ∑ x : X, ∑ y : Y, if f x = g y then (1 : ℂ) else 0 := by
  classical
  simp_rw [Fintype.sum_mul_sum]
  rw [Fintype.sum_reverse_three]
  simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_comm]

private def coordinatePairEquiv (Y A R Z : Type*) :
    (Y × A × R × Z) ≃ ((Y × Z) × (A × R)) where
  toFun c := ((c.1, c.2.2.2), (c.2.1, c.2.2.1))
  invFun p := (p.1.1, p.2.1, p.2.2, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem delta_sum_pairing_free {H A X Y : Type*}
    [Fintype H] [DecidableEq H] [Fintype A] [Fintype X] [Fintype Y]
    (f : X → H) (g : Y → H) :
    (∑ p : H × A, (∑ x : X, if p.1 = f x then (1 : ℂ) else 0) *
      (∑ y : Y, if p.1 = g y then (1 : ℂ) else 0)) =
        (Fintype.card A : ℂ) * ∑ x : X, ∑ y : Y,
          if f x = g y then (1 : ℂ) else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  change (∑ h : H, ∑ _ : A, (∑ x : X, if h = f x then (1 : ℂ) else 0) *
    (∑ y : Y, if h = g y then (1 : ℂ) else 0)) = _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, delta_sum_pairing]

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

open scoped Classical in
/-- Exact mixed Gram entries of two actual twisted canonical blocks. The common
physical coordinates enforce equality of transported boundary labels and of
simultaneously conjugated cycle residuals. Source: SCP10, lines 1935–2072. -/
theorem regularProjectorTwistedRegionMatrix_crossGram_coordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (u w : Edge Γ → G) (θ ϑ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    ((regularProjectorTwistedRegionMatrix R u).conjTranspose *
      regularProjectorTwistedRegionMatrix R w) θ ϑ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card * (Fintype.card G : ℂ)⁻¹ ^ R.card *
        (Fintype.card (({e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G) ×
          RootedGroupLabels (G := G) o) : ℂ) *
        ∑ x : G, ∑ t : G,
          if x • regularRegionBoundaryTransport R
              (regularRegionTreeGauge R T hT htree o u).1 u θ =
            t • regularRegionBoundaryTransport R
              (regularRegionTreeGauge R T hT htree o w).1 w ϑ ∧
            (fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹) =
              (fun e => t * regularRegionTreeCycleResidual R T hT htree o w e * t⁻¹)
          then 1 else 0 := by
  classical
  let Y := {e : Edge Γ // IsRegionBoundaryEdge R e} → G
  let A := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} → G
  let Q := RootedGroupLabels (G := G) o
  let Z := {e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
    ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G
  let : Fintype Y := inferInstance
  let : Fintype A := inferInstance
  let : Fintype Q := inferInstance
  let : Fintype Z := inferInstance
  let : Fintype (Y × Z) := inferInstance
  let : Fintype (A × Q) := inferInstance
  let e := (regularRegionCoordinatesEquiv (G := G) R T hT htree o).trans
    (coordinatePairEquiv Y A Q Z)
  let Fu (x : G) : Y × Z :=
    (x • regularRegionBoundaryTransport R (regularRegionTreeGauge R T hT htree o u).1 u θ,
      fun f => x * regularRegionTreeCycleResidual R T hT htree o u f * x⁻¹)
  let Fw (x : G) : Y × Z :=
    (x • regularRegionBoundaryTransport R (regularRegionTreeGauge R T hT htree o w).1 w ϑ,
      fun f => x * regularRegionTreeCycleResidual R T hT htree o w f * x⁻¹)
  let β : ℂ := (Fintype.card G : ℂ)⁻¹ ^ R.card
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [← Equiv.sum_comp e.symm]
  have hentry (p : (Y × Z) × (A × Q)) :
      star (regularProjectorTwistedRegionMatrix R u (e.symm p) θ) *
        regularProjectorTwistedRegionMatrix R w (e.symm p) ϑ =
      (β * β) * ((∑ x : G, if p.1 = Fu x then (1 : ℂ) else 0) *
        (∑ t : G, if p.1 = Fw t then (1 : ℂ) else 0)) := by
    change star (regularProjectorTwistedRegionMatrix R u
      ((regularRegionCoordinatesEquiv R T hT htree o).symm
        (p.1.1, p.2.1, p.2.2, p.1.2)) θ) *
      regularProjectorTwistedRegionMatrix R w
        ((regularRegionCoordinatesEquiv R T hT htree o).symm
          (p.1.1, p.2.1, p.2.2, p.1.2)) ϑ = _
    rw [regularProjectorTwistedRegionMatrix_coordinates,
      regularProjectorTwistedRegionMatrix_coordinates]
    simp only [Fu, Fw, Prod.ext_iff, β, star_mul, star_inv₀, star_pow, star_natCast,
      star_sum, apply_ite, star_one, star_zero]
    ring
  simp_rw [hentry]
  rw [← Finset.mul_sum, delta_sum_pairing_free]
  simp only [Fu, Fw, Prod.ext_iff, β, mul_assoc]
  simp only [Fintype.card_eq_nat_card, A, Q]

/-- If the residual cycle tuples are not simultaneously conjugate, two actual
canonical blocks have orthogonal physical ranges. Crossing operators remain
arbitrary. Source: SCP10, coherent closure comparison, lines 1935–2072. -/
theorem regularProjectorTwistedRegionMatrix_crossGram_eq_zero_of_cycles_not_conjugate
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (u w : Edge Γ → G)
    (hno : ¬ ∃ s : G, regularRegionTreeCycleResidual R T hT htree o u =
      fun e => s * regularRegionTreeCycleResidual R T hT htree o w e * s⁻¹) :
    (regularProjectorTwistedRegionMatrix R u).conjTranspose *
      regularProjectorTwistedRegionMatrix R w = 0 := by
  classical
  ext θ ϑ
  rw [regularProjectorTwistedRegionMatrix_crossGram_coordinates R T hT htree o u w θ ϑ]
  have hn (x t : G) : ¬ (fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹) =
      (fun e => t * regularRegionTreeCycleResidual R T hT htree o w e * t⁻¹) := by
    intro h
    apply hno
    refine ⟨x⁻¹ * t, ?_⟩
    funext e
    have he := congrFun h e
    calc
      _ = x⁻¹ * (x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹) * x := by
        group
      _ = x⁻¹ * (t * regularRegionTreeCycleResidual R T hT htree o w e * t⁻¹) * x := by
        rw [he]
      _ = _ := by group
  simp only [hn, and_false, ↓reduceIte, Finset.sum_const_zero, mul_zero,
    Matrix.zero_apply]

end TNLean.PEPS
