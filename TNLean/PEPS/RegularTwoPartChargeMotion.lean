/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryRegisterTransport
import TNLean.PEPS.RegularBoundaryChargeContraction
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Independent original-spin operations on the two parts of a charge-motion block

Source: SCP10, arXiv:1001.3807, the two column swaps in
`eq:anyons:chargeon-move-setting`, lines 2489–2507. The common bonds and the
external boundary are those of the actual graph contraction. The Gram forms
of both physical maps are derived separately from local G-isometry.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

/-- A joining bond is an actual crossing bond of either disjoint part.
Source: SCP10, independent column contractions, lines 2489–2507. -/
def regionJoiningBoundaryEdge (L S R : Finset V) (hd : Disjoint L S)
    (hR : R = L ∨ R = S) (e : RegionJoiningEdge (Γ := Γ) L S) : RB (Γ := Γ) R :=
  by
    refine ⟨e.1,?_⟩
    rcases hR with hR | hR
    · subst R
      exact (regionJoiningEdge_boundary L S hd e).1
    · subst R
      exact (regionJoiningEdge_boundary L S hd e).2

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem joiningBoundary_swap (L S R : Finset V) (hd : Disjoint L S)
    (hR : R = L ∨ R = S) (e f : RegionJoiningEdge (Γ := Γ) L S)
    (μ : RegionJoiningEdge (Γ := Γ) L S → G) (θ : RB (Γ := Γ) (L ∪ S) → G) :
    regionGluingBoundary L S R (fun b => μ (Equiv.swap e f b)) θ =
      fun b => regionGluingBoundary L S R μ θ
        (Equiv.swap (regionJoiningBoundaryEdge L S R hd hR e)
          (regionJoiningBoundaryEdge L S R hd hR f) b) := by
  funext b
  let eb := regionJoiningBoundaryEdge L S R hd hR e
  let fb := regionJoiningBoundaryEdge L S R hd hR f
  by_cases he : b.1 = e.1
  · have hb : b = eb := Subtype.ext he
    subst b
    dsimp only [eb,fb]
    simp only [regionJoiningBoundaryEdge, regionGluingBoundary, regionGluingLabels,
      dite_eq_left e.2, dite_eq_left f.2, Equiv.swap_apply_left]
  · by_cases hf : b.1 = f.1
    · have hb : b = fb := Subtype.ext hf
      subst b
      dsimp only [eb,fb]
      simp only [regionJoiningBoundaryEdge, regionGluingBoundary, regionGluingLabels,
        dite_eq_left e.2, dite_eq_left f.2, Equiv.swap_apply_right]
    · have hbe : b ≠ eb := fun h => he (congrArg Subtype.val h)
      have hbf : b ≠ fb := fun h => hf (congrArg Subtype.val h)
      rw [Equiv.swap_apply_of_ne_of_ne hbe hbf]
      unfold regionGluingBoundary regionGluingLabels
      split_ifs with hj
      · have hje : (⟨b.1,hj⟩ : RegionJoiningEdge (Γ := Γ) L S) ≠ e :=
          fun h => he (congrArg Subtype.val h)
        have hjf : (⟨b.1,hj⟩ : RegionJoiningEdge (Γ := Γ) L S) ≠ f :=
          fun h => hf (congrArg Subtype.val h)
        simp only [Equiv.swap_apply_of_ne_of_ne hje hjf]
      · rfl
      · rfl

private theorem kronecker_mulVec_product {A B : Type*} [Fintype A] [Fintype B]
    (M : Matrix A A ℂ) (N : Matrix B B ℂ) (x : A → ℂ) (y : B → ℂ) :
    (M ⊗ₖ N) *ᵥ (fun s => x s.1 * y s.2) =
      fun s => (M *ᵥ x) s.1 * (N *ᵥ y) s.2 := by
  funext s
  change (∑ t : A × B, M s.1 t.1 * N s.2 t.2 * (x t.1 * y t.2)) =
    (∑ a : A, M s.1 a * x a) * (∑ b : B, N s.2 b * y b)
  simp only [Fintype.sum_prod_type]
  have hm (a : A) (b : B) :
      M s.1 a * N s.2 b * (x a * y b) = (M s.1 a * x a) * (N s.2 b * y b) := by ring
  simp_rw [hm]
  exact (Finset.sum_mul_sum Finset.univ Finset.univ
    (fun a => M s.1 a * x a) (fun b => N s.2 b * y b)).symm


omit [Group G] [DecidableEq G] in
private theorem transport_graphOpen {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (R : Finset V)
    (W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ)
      (τ : Equiv.Perm (RB (Γ := Γ) R))
      (h : ∀ θ : RB (Γ := Γ) R → G,
        W *ᵥ openRegionWeight (groupBondTensor a) R
          (fun b => Fintype.equivFin G (θ b)) =
        openRegionWeight (groupBondTensor a) R
          (fun b => Fintype.equivFin G (θ (τ b)))) (θ : RB (Γ := Γ) R → G) :
      W *ᵥ graphOpenRegionNetwork a R θ =
        graphOpenRegionNetwork a R (fun b => θ (τ b)) := by
    have heq (η : RB (Γ := Γ) R → G) :
        openRegionWeight (groupBondTensor a) R
          (fun b => Fintype.equivFin G (η b)) = graphOpenRegionNetwork a R η := by
      funext σ
      exact openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork a R η σ
    rw [← heq θ, ← heq (fun b => θ (τ b))]
    exact h θ

omit [DecidableEq G] in
/-- Two independent original-spin unitaries move a literal charge between
joining bonds. They precede its character, parameter and all external labels.
No gluing, Gram or state-action identity is assumed.
Source: SCP10, the independent column swaps, lines 2489–2507. -/
theorem exists_unitary_regularTwoPartChargeMotion {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (L S : Finset V) (hd : Disjoint L S)
    (hL : (Γ.induce (L : Set V)).Connected) (hS : (Γ.induce (S : Set V)).Connected)
    (e f : RegionJoiningEdge (Γ := Γ) L S) :
    ∃ (Wₗ : Matrix (RV L → Fin d) (RV L → Fin d) ℂ)
      (Wᵣ : Matrix (RV S → Fin d) (RV S → Fin d) ℂ),
      Wₗ ∈ Matrix.unitaryGroup (RV L → Fin d) ℂ ∧
      Wᵣ ∈ Matrix.unitaryGroup (RV S → Fin d) ℂ ∧
      ∀ (χ : G → ℂ) (p : G) (θ : RB (Γ := Γ) (L ∪ S) → G),
        (Wₗ ⊗ₖ Wᵣ) *ᵥ (fun s => graphOpenRegionNetwork
          (regularEdgeCharacterSite a e.1 χ p) (L ∪ S) θ
          (Equiv.piFinsetUnion (fun _ : V => Fin d) hd s)) =
        (fun s => graphOpenRegionNetwork (regularEdgeCharacterSite a f.1 χ p)
          (L ∪ S) θ (Equiv.piFinsetUnion (fun _ : V => Fin d) hd s)) := by
  classical
  let τL := Equiv.swap (regionJoiningBoundaryEdge L S L hd (Or.inl rfl) e)
    (regionJoiningBoundaryEdge L S L hd (Or.inl rfl) f)
  let τS := Equiv.swap (regionJoiningBoundaryEdge L S S hd (Or.inr rfl) e)
    (regionJoiningBoundaryEdge L S S hd (Or.inr rfl) f)
  obtain ⟨Wₗ,hWₗ,hactL⟩ := exists_unitary_regularBoundaryRegisterTransport a ha L hL τL
  obtain ⟨Wᵣ,hWᵣ,hactS⟩ := exists_unitary_regularBoundaryRegisterTransport a ha S hS τS
  refine ⟨Wₗ,Wᵣ,hWₗ,hWᵣ,?_⟩
  intro χ p θ
  have hglue (b : RegionJoiningEdge (Γ := Γ) L S) :
      (fun s => graphOpenRegionNetwork (regularEdgeCharacterSite a b.1 χ p) (L ∪ S) θ
        (Equiv.piFinsetUnion (fun _ : V => Fin d) hd s)) =
      ∑ μ : RegionJoiningEdge (Γ := Γ) L S → G, χ (p * μ b) •
        (fun s => graphOpenRegionNetwork a L (regionGluingBoundary L S L μ θ) s.1 *
          graphOpenRegionNetwork a S (regionGluingBoundary L S S μ θ) s.2) := by
    funext s
    rw [graphOpenRegionNetwork_regularEdgeCharacterSite_union a L S hd b]
    have hl : (fun v : RV L => (Equiv.piFinsetUnion (fun _ : V => Fin d) hd s)
        ⟨v.1,Finset.mem_union_left _ v.2⟩) = s.1 := by
      funext v
      exact Equiv.piFinsetUnion_left (fun _ : V => Fin d) hd v.2 _
    have hr : (fun v : RV S => (Equiv.piFinsetUnion (fun _ : V => Fin d) hd s)
        ⟨v.1,Finset.mem_union_right _ v.2⟩) = s.2 := by
      funext v
      exact Equiv.piFinsetUnion_right (fun _ : V => Fin d) hd v.2 _
    rw [hl,hr]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hglue e, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, kronecker_mulVec_product]
  simp_rw [transport_graphOpen a L Wₗ τL hactL, transport_graphOpen a S Wᵣ τS hactS]
  have hβL (μ : RegionJoiningEdge (Γ := Γ) L S → G) :
      (fun b => regionGluingBoundary L S L μ θ (τL b)) =
        regionGluingBoundary L S L (fun b => μ (Equiv.swap e f b)) θ :=
    (joiningBoundary_swap L S L hd (Or.inl rfl) e f μ θ).symm
  have hβS (μ : RegionJoiningEdge (Γ := Γ) L S → G) :
      (fun b => regionGluingBoundary L S S μ θ (τS b)) =
        regionGluingBoundary L S S (fun b => μ (Equiv.swap e f b)) θ :=
    (joiningBoundary_swap L S S hd (Or.inr rfl) e f μ θ).symm
  simp_rw [hβL,hβS]
  rw [hglue f]
  let ν := (Equiv.swap e f).arrowCongr (Equiv.refl G)
  rw [← ν.sum_comp]
  apply Finset.sum_congr rfl
  intro μ _
  simp only [ν, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply,
    Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_self]
end TNLean.PEPS
