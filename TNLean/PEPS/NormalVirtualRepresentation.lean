/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import TNLean.PEPS.NormalPhysicalSymmetry
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Projective bond representations of a normal tensor network

A physical symmetry group determines invertible matrices on every virtual
bond. Uniqueness of the normal Fundamental Theorem identifies their products
up to nonzero scalars. Reversing the group argument gives the usual projective
multiplication law. Their projective classes define homomorphisms into the
projective general linear group, and associativity gives the cocycle identity.

Source: arXiv:1804.04964, Applications, lines 1696–1713 of paper_normal.tex.
The connectedness correction is recorded on the concluding theorem.
-/

noncomputable section

namespace TNLean.PEPS

open TNLean.Lattice
open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

omit [Fintype V] in
/-- The endpoint action is multiplicative in the edge matrix. At the second
endpoint, inverse transpose preserves the multiplication order.
Source: arXiv:1804.04964, the projective bond symmetry assertion at line 1713. -/
theorem edgeGaugeAt_mul (A : Tensor G d)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeGaugeAt A (fun e => X e * Y e) v ie =
      edgeGaugeAt A X v ie * edgeGaugeAt A Y v ie := by
  by_cases h : ie.1.1.1 = v
  · simp only [edgeGaugeAt, ite_eq_left h]
    rfl
  · simp only [edgeGaugeAt, ite_eq_right h, mul_inv_rev, Units.val_mul,
      Matrix.transpose_mul]

/-- Two successive virtual gauge actions compose by multiplying the outer
edge matrices on the left. Source: arXiv:1804.04964, line 1713. -/
theorem gaugeVertex_applyGauge (A : Tensor G d)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d) :
    gaugeVertex (applyGauge A X) Y v η σ =
      gaugeVertex A (fun e => Y e * X e) v η σ := by
  classical
  let MX := fun ie : IncidentEdge G v => edgeGaugeAt A X v ie
  let MY := fun ie : IncidentEdge G v => edgeGaugeAt A Y v ie
  let f : ((ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) → ℂ :=
    fun ξ => A.component v ξ σ
  have h := LinearMap.congr_fun
    (dependentPhysicalProductFamilyMap_comp (Site := IncidentEdge G v) MY MX) f
  have hProd : (fun ie : IncidentEdge G v => MY ie * MX ie) =
      (fun ie : IncidentEdge G v => edgeGaugeAt A (fun e => Y e * X e) v ie) := by
    funext ie
    exact (edgeGaugeAt_mul A Y X v ie).symm
  rw [hProd] at h
  exact congr_fun h η

omit [Fintype V] in
/-- Multiplication of physical matrices is composition of their local actions.
Source: arXiv:1804.04964, Applications, lines 1696–1713. -/
theorem physicalTensorAction_mul_component (A : Tensor G d)
    (U W : Matrix (Fin d) (Fin d) ℂ)
    (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d) :
    (physicalTensorAction (physicalTensorAction A W) U).component v η σ =
      (physicalTensorAction A (U * W)).component v η σ := by
  classical
  change (∑ τ : Fin d, U σ τ * ∑ κ : Fin d, W τ κ * A.component v η κ) =
    ∑ κ : Fin d, (∑ τ : Fin d, U σ τ * W τ κ) * A.component v η κ
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro κ hκ
  refine Finset.sum_congr rfl ?_
  intro τ hτ
  exact (mul_assoc _ _ _).symm

/-- Physical and virtual actions commute on each actual tensor component.
Source: arXiv:1804.04964, Applications, lines 1696–1713. -/
theorem physicalTensorAction_applyGauge_component (A : Tensor G d)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d) :
    (physicalTensorAction (applyGauge A X) U).component v η σ =
      gaugeVertex (physicalTensorAction A U) X v η σ := by
  classical
  change (∑ τ : Fin d, U σ τ *
      ∑ ξ : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
        (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (ξ ie)) *
          A.component v ξ τ) =
    ∑ ξ : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
      (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (ξ ie)) *
        ∑ τ : Fin d, U σ τ * A.component v ξ τ
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro ξ hξ
  refine Finset.sum_congr rfl ?_
  intro τ hτ
  exact mul_left_comm _ _ _

end TNLean.PEPS

namespace TNLean.PEPS

open TNLean.Lattice TNLean.Algebra
open scoped BigOperators Matrix

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Extract the actual edge matrices of a normal physical symmetry in the
unchanged bond coordinates. Source: arXiv:1804.04964, lines 1696–1713. -/
private theorem exists_normalPhysicalSymmetry_gauges
    (A : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hsingle : ∀ e f : Edge G,
      IsCrossingEdge (G := G) A (hA.edgeBlocking.red e)
        (hA.edgeBlocking.blue e) f ↔ f = e)
    (hconn : G.Connected) (M : Matrix (Fin d) (Fin d) ℂ)
    (hSym : dependentPhysicalProductFamilyMap (fun _ : V => M) (stateCoeff A) =
      stateCoeff A) :
    ∃ X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ,
      ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        (physicalTensorAction A M).component v η σ = gaugeVertex A X v η σ := by
  obtain ⟨hDim, X, hX⟩ :=
    gaugeEquiv_physicalTensorAction_of_normal_symmetry A hA hsingle hconn M hSym
  refine ⟨X, ?_⟩
  intro v η σ
  have hη : (fun ie : IncidentEdge G v =>
      Fin.cast (congr_fun hDim ie.1) (η ie)) = η := by
    funext ie
    apply Fin.ext
    rfl
  simpa only [hη] using hX v η σ

variable {H : Type} [Group H]

/-- The reversed product of the chosen gauges implements the product of two
physical symmetry operators. Source: arXiv:1804.04964, line 1713. -/
private theorem normalPhysicalGauge_product
    (A : Tensor G d) (U : H →* Matrix (Fin d) (Fin d) ℂ)
    (X : H → (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (hX : ∀ (g : H) (v : V)
      (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      (physicalTensorAction A (U g)).component v η σ = gaugeVertex A (X g) v η σ)
    (g h : H) (v : V)
    (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d) :
    (physicalTensorAction A (U (g * h))).component v η σ =
      gaugeVertex A (fun e => X h e * X g e) v η σ := by
  classical
  calc
    (physicalTensorAction A (U (g * h))).component v η σ =
        (physicalTensorAction A (U g * U h)).component v η σ :=
      congrArg (fun M : Matrix (Fin d) (Fin d) ℂ =>
        (physicalTensorAction A M).component v η σ) (U.map_mul g h)
    _ = (physicalTensorAction (physicalTensorAction A (U h)) (U g)).component v η σ :=
      (physicalTensorAction_mul_component A (U g) (U h) v η σ).symm
    _ = (physicalTensorAction (applyGauge A (X h)) (U g)).component v η σ := by
      change (∑ τ : Fin d, U g σ τ * (physicalTensorAction A (U h)).component v η τ) =
        ∑ τ : Fin d, U g σ τ * gaugeVertex A (X h) v η τ
      refine Finset.sum_congr rfl ?_
      intro τ hτ
      exact congrArg (fun z : ℂ => U g σ τ * z) (hX h v η τ)
    _ = gaugeVertex (physicalTensorAction A (U g)) (X h) v η σ :=
      physicalTensorAction_applyGauge_component A (U g) (X h) v η σ
    _ = gaugeVertex (applyGauge A (X g)) (X h) v η σ := by
      change (∑ ξ : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
          (∏ ie : IncidentEdge G v, edgeGaugeAt A (X h) v ie (η ie) (ξ ie)) *
            (physicalTensorAction A (U g)).component v ξ σ) =
        ∑ ξ : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
          (∏ ie : IncidentEdge G v, edgeGaugeAt A (X h) v ie (η ie) (ξ ie)) *
            gaugeVertex A (X g) v ξ σ
      refine Finset.sum_congr rfl ?_
      intro ξ hξ
      exact congrArg (fun z : ℂ =>
        (∏ ie : IncidentEdge G v, edgeGaugeAt A (X h) v ie (η ie) (ξ ie)) * z)
        (hX g v ξ σ)
    _ = gaugeVertex A (fun e => X h e * X g e) v η σ :=
      gaugeVertex_applyGauge A (X g) (X h) v η σ

/-- A physical symmetry group of a normal tensor network has a projective
representation on each bond. The tensor relation uses the inverse group
argument, matching the order of successive virtual gauge actions.

Source: arXiv:1804.04964, Applications, the projective-representation assertion
at line 1713. -/
private theorem exists_normal_virtual_lifts
    (A : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hsingle : ∀ e f : Edge G,
      IsCrossingEdge (G := G) A (hA.edgeBlocking.red e)
        (hA.edgeBlocking.blue e) f ↔ f = e)
    (hconn : G.Connected) (U : H →* Matrix (Fin d) (Fin d) ℂ)
    (hSym : ∀ g : H,
      dependentPhysicalProductFamilyMap (fun _ : V => U g) (stateCoeff A) =
        stateCoeff A) :
    ∃ ω : (e : Edge G) → ScalarCocycle H,
      ∃ ρvirt : (e : Edge G) → ProjectiveRepresentation (D := A.bondDim e) (ω e),
        (∀ (g : H) (v : V)
          (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
          (physicalTensorAction A (U g)).component v η σ =
            gaugeVertex A (fun e => (ρvirt e).X (g⁻¹)) v η σ) ∧
        ∀ (e : Edge G) (g h k : H),
          (ω e (g, h) : ℂ) * (ω e (g * h, k) : ℂ) =
            (ω e (g, h * k) : ℂ) * (ω e (h, k) : ℂ) := by
  classical
  have hGauge (g : H) :=
    exists_normalPhysicalSymmetry_gauges A hA hsingle hconn (U g) (hSym g)
  choose X hX using hGauge
  have hState (g : H) : SameState A (physicalTensorAction A (U g)) := by
    intro σ
    exact (congr_fun ((stateCoeff_physicalTensorAction A (U g)).trans (hSym g)) σ).symm
  have hMult (g h : H) : ∃ c : Edge G → ℂˣ,
      ∀ e : Edge G,
        ((X h e * X g e : GL (Fin (A.bondDim e)) ℂ) :
          Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
          (c e : ℂ) • (X (g * h) e :
            Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) := by
    let B := physicalTensorAction A (U (g * h))
    let hAB : NormalPEPSPairHypotheses A B :=
      normalPairHypothesesOfSameStateOfBondDimEq A B hA rfl (hState (g * h))
    have hEach (e : Edge G) : ∃ c : ℂˣ,
        ((X h e * X g e : GL (Fin (A.bondDim e)) ℂ) :
          Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
          (c : ℂ) • (X (g * h) e :
            Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :=
      fundamentalTheorem_normalPEPS_gauge_unique A B hAB rfl
        (X (g * h)) (fun f => X h f * X g f)
        (hX (g * h)) (normalPhysicalGauge_product A U X hX g h) e
    choose c hc using hEach
    exact ⟨c, hc⟩
  choose c hc using hMult
  let ω : (e : Edge G) → ScalarCocycle H := fun e p => c (p.2⁻¹) (p.1⁻¹) e
  let ρvirt : (e : Edge G) → ProjectiveRepresentation (D := A.bondDim e) (ω e) :=
    fun e => {
      X := fun g => X (g⁻¹) e
      map_mul' := fun g h => by
        change (X (g⁻¹) e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) *
            (X (h⁻¹) e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
          (c (h⁻¹) (g⁻¹) e : ℂ) •
            (X ((g * h)⁻¹) e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
        simpa only [mul_inv_rev, Units.val_mul] using hc (h⁻¹) (g⁻¹) e }
  refine ⟨ω, ρvirt, ?_, ?_⟩
  · intro g v η σ
    change (physicalTensorAction A (U g)).component v η σ =
      gaugeVertex A (fun e => X ((g⁻¹)⁻¹) e) v η σ
    simpa only [inv_inv] using hX g v η σ
  · intro e g h k
    exact (ρvirt e).cocycle_of_assoc (D := A.bondDim e) (hA.bondDim_pos_left e) g h k


/-- A physical symmetry group of a normal tensor network acts on every bond
through Mathlib's projective general linear group. Chosen invertible lifts
implement the physical action and have a nonzero scalar factor system
satisfying the cocycle identity.

**Local fix (connectivity):** The scalar-free tensor relation is on a connected
graph so that component scalars can be absorbed into edge gauges, as recorded in
`docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex`.

Source: arXiv:1804.04964, Applications, the projective-representation assertion
at line 1713. -/
theorem exists_virtualRepresentation_of_normal_symmetry
    (A : Tensor G d) (hA : NormalPEPSPairHypotheses A A)
    (hsingle : ∀ e f : Edge G,
      IsCrossingEdge (G := G) A (hA.edgeBlocking.red e)
        (hA.edgeBlocking.blue e) f ↔ f = e)
    (hconn : G.Connected) (U : H →* Matrix (Fin d) (Fin d) ℂ)
    (hSym : ∀ g : H,
      dependentPhysicalProductFamilyMap (fun _ : V => U g) (stateCoeff A) =
        stateCoeff A) :
    ∃ ω : (e : Edge G) → ScalarCocycle H,
      ∃ X : H → (e : Edge G) → GL (Fin (A.bondDim e)) ℂ,
        ∃ R : (e : Edge G) → H →* Matrix.ProjGenLinGroup (Fin (A.bondDim e)) ℂ,
          (∀ (e : Edge G) (g : H), R e g = Matrix.ProjGenLinGroup.mk (X g e)) ∧
          (∀ (g : H) (v : V)
            (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
            (physicalTensorAction A (U g)).component v η σ =
              gaugeVertex A (fun e => X (g⁻¹) e) v η σ) ∧
          (∀ (e : Edge G) (g h : H),
            (X g e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) *
                (X h e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
              (ω e (g, h) : ℂ) •
                (X (g * h) e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)) ∧
          ∀ (e : Edge G) (g h k : H),
            (ω e (g, h) : ℂ) * (ω e (g * h, k) : ℂ) =
              (ω e (g, h * k) : ℂ) * (ω e (h, k) : ℂ) := by
  classical
  obtain ⟨ω, ρ, hTensor, hCocycle⟩ :=
    exists_normal_virtual_lifts A hA hsingle hconn U hSym
  let R (e : Edge G) : H →* Matrix.ProjGenLinGroup (Fin (A.bondDim e)) ℂ :=
    MonoidHom.mk' (fun g => Matrix.ProjGenLinGroup.mk ((ρ e).X g)) fun g h => by
      have hGL : (ρ e).X g * (ρ e).X h =
          Matrix.GeneralLinearGroup.scalar (Fin (A.bondDim e)) (ω e (g, h)) *
            (ρ e).X (g * h) := by
        apply Units.ext
        simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] using (ρ e).map_mul g h
      have hProj := congrArg
        (fun Z : GL (Fin (A.bondDim e)) ℂ => Matrix.ProjGenLinGroup.mk Z) hGL
      simpa only [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul] using hProj.symm
  refine ⟨ω, fun g e => (ρ e).X g, R, ?_, hTensor, ?_, hCocycle⟩
  · intro e g
    rfl
  · intro e g h
    exact (ρ e).map_mul g h

end TNLean.PEPS
