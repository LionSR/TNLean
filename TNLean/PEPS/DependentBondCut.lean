/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondNetwork

/-!
# Arbitrary joint cut boundaries with edge-dependent dimensions

A cut exposes both incidences of every selected labelled edge to one joint
boundary tensor. The other edges carry identities on their own virtual
alphabets. Fixed endpoint columns span the full cut range and are exactly
networks with matrix units on the cut edges.

This provides the dimension-independent cut spaces needed for SCP10,
arXiv:1001.3807, Theorem 5.5, equation `eq:2d:closure-intersection`.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge : Type*} (tail head : Edge → Vertex)
variable (D : Edge → Type*)

/-- Both endpoints of all edges in a cut. -/
abbrev CutEndpoint (C : Finset Edge) := {e // e ∈ C} × Bool

/-- Independent endpoint labels for the whole cut boundary. -/
abbrev CutConfig (C : Finset Edge) (D : Edge → Type*) :=
  (p : CutEndpoint C) → D p.1.1

/-- Restrict a full endpoint configuration to the selected cut edges. -/
def cutRestriction (C : Finset Edge) (β : EndpointConfig D) : CutConfig C D :=
  fun p ↦ β (p.1.1, p.2)

variable [Fintype Vertex] [Fintype Edge] [DecidableEq Edge]
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

/-- Identity matrices on uncut edges and weight one on cut edges. -/
def cutInteriorWeight (C : Finset Edge) (β : EndpointConfig D) : ℂ :=
  ∏ e, if e ∈ C then 1 else (1 : Matrix (D e) (D e) ℂ) (β (e, true)) (β (e, false))

/-- Literal cut contraction against an arbitrary joint boundary tensor. -/
def cutCoeff (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) (M : CutConfig C D → ℂ) (σ : (v : Vertex) → Phys v) : ℂ :=
  ∑ β : EndpointConfig D,
    (M (cutRestriction D C β) * cutInteriorWeight D C β) *
      ∏ v, A v (endpointSiteEquiv tail head D β v) (σ v)

/-- The linear map from all joint boundary tensors to physical vectors. -/
def cutMap (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) : (CutConfig C D → ℂ) →ₗ[ℂ] (((v : Vertex) → Phys v) → ℂ) where
  toFun := cutCoeff tail head D A C
  map_add' M N := by
    funext σ
    simp [cutCoeff, add_mul, Finset.sum_add_distrib]
  map_smul' z M := by
    funext σ
    simp [cutCoeff, mul_assoc, Finset.mul_sum]

@[simp]
theorem cutMap_apply (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) (M : CutConfig C D → ℂ) (σ : (v : Vertex) → Phys v) :
    cutMap tail head D A C M σ = cutCoeff tail head D A C M σ := rfl

/-- The range of actual contractions with arbitrary correlated cut boundaries. -/
def cutSpace (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) : Submodule ℂ (((v : Vertex) → Phys v) → ℂ) :=
  LinearMap.range (cutMap tail head D A C)

/-- Membership in a cut space is coefficientwise realization by one joint boundary. -/
theorem mem_cutSpace_iff
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) (ψ : ((v : Vertex) → Phys v) → ℂ) :
    ψ ∈ cutSpace tail head D A C ↔
      ∃ M, ∀ σ, cutCoeff tail head D A C M σ = ψ σ := by
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨M, fun _ ↦ rfl⟩
  · rintro ⟨M, hM⟩
    exact ⟨M, funext hM⟩

/-- Every joint boundary gives a linear combination of fixed-boundary columns. -/
theorem cutMap_eq_sum_single
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) (M : CutConfig C D → ℂ) :
    cutMap tail head D A C M =
      ∑ η, M η • cutMap tail head D A C (Pi.single η 1) := by
  classical
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext η
  simp [Pi.single_apply]

/-- The whole correlated-boundary cut space is spanned by fixed endpoint columns. -/
theorem cutSpace_eq_span_single
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) :
    cutSpace tail head D A C = Submodule.span ℂ
      (Set.range fun η ↦ cutMap tail head D A C (Pi.single η 1)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    rw [cutMap_eq_sum_single]
    exact Submodule.sum_mem _ fun η _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self η))
  · exact Submodule.span_le.mpr (by rintro _ ⟨η, rfl⟩; exact ⟨Pi.single η 1, rfl⟩)

/-- A product of inserted matrices is one possible joint cut boundary. -/
def cutBondBoundary (C : Finset Edge)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (η : CutConfig C D) : ℂ :=
  ∏ e : {e // e ∈ C}, B e.1 (η (e, true)) (η (e, false))

omit [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)] in
/-- A factorized boundary contains precisely the matrix factors on the cut edges. -/
theorem cutBondBoundary_restriction (C : Finset Edge)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ) (β : EndpointConfig D) :
    cutBondBoundary D C B (cutRestriction D C β) =
      ∏ e, if e ∈ C then B e (β (e, true)) (β (e, false)) else 1 := by
  unfold cutBondBoundary cutRestriction
  rw [← Finset.prod_subtype C (fun _ ↦ Iff.rfl)
    (fun e ↦ B e (β (e, true)) (β (e, false)))]
  simp [Finset.prod_ite_mem]

/-- Closing a cut by a matrix product inserts its matrices exactly on the cut edges. -/
theorem cutCoeff_bondBoundary
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (σ : (v : Vertex) → Phys v) :
    cutCoeff tail head D A C (cutBondBoundary D C B) σ =
      network tail head D A (fun e ↦ if e ∈ C then B e else 1) σ := by
  unfold cutCoeff network
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  congr 1
  rw [cutBondBoundary_restriction, cutInteriorWeight, bondWeight,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ ↦ ?_
  split_ifs <;> simp

/-- Matrix units on cut edges and identities elsewhere for a fixed boundary. -/
def cutBondUnits (C : Finset Edge) (η : CutConfig C D)
    (e : Edge) : Matrix (D e) (D e) ℂ :=
  if h : e ∈ C then Matrix.single (η (⟨e, h⟩, true)) (η (⟨e, h⟩, false)) 1 else 1

omit [Fintype Edge] [∀ e, Fintype (D e)] in
/-- Products of cut matrix units are exactly the coordinate boundary tensors. -/
theorem cutBondBoundary_units (C : Finset Edge) (η : CutConfig C D) :
    cutBondBoundary D C (cutBondUnits D C η) = Pi.single η 1 := by
  classical
  funext θ
  have hcfg : (∀ e : {e // e ∈ C},
      η (e, true) = θ (e, true) ∧ η (e, false) = θ (e, false)) ↔ η = θ := by
    constructor
    · intro h
      funext p
      rcases p with ⟨e, b⟩
      cases b
      · exact (h e).2
      · exact (h e).1
    · rintro rfl
      exact fun _ ↦ ⟨rfl, rfl⟩
  simp only [cutBondBoundary, cutBondUnits, dite_eq_left (Subtype.property _), Matrix.single_apply,
    Fintype.prod_boole, hcfg]
  simp [Pi.single_apply, eq_comm]

/-- Every fixed-boundary cut column is a literal network of matrix units and identities. -/
theorem cutMap_single_eq_network
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (C : Finset Edge) (η : CutConfig C D) (σ : (v : Vertex) → Phys v) :
    cutMap tail head D A C (Pi.single η 1) σ =
      network tail head D A (cutBondUnits D C η) σ := by
  rw [← cutBondBoundary_units D C η, cutMap_apply, cutCoeff_bondBoundary]
  congr 1
  funext e
  by_cases he : e ∈ C <;> simp [cutBondUnits, he]

end TNLean.PEPS.DependentBondNetwork
