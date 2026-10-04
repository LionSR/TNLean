/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoCyclePhysicalFluxMove
import TNLean.PEPS.TorusTwoPlaquetteFluxHolonomy
import TNLean.PEPS.RegularTorusEntropy

/-!
# Moving a flux insertion across two native torus plaquettes

The actual six-site region is the 3 by 2 rectangle at the origin. Its fixed
spanning path leaves the leftmost and middle upward vertical bonds outside
the tree. Native four-leg regular G-isometry implies local incident-edge
G-isometry. The physical two-cycle operation therefore yields one unitary
on these six original spins, chosen before the inserted group element and
all crossing labels. It changes the leftmost insertion into insertions on
both selected bonds, preserving every boundary column.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, lines 2271–2305.

**Scope restriction (six-site regular flux movement):** The horizontal period
is at least four and the vertical period at least three; the virtual action is
regular. The actual plaquette holonomies change from (g⁻¹,1) to (1,g⁻¹).
This local column identity does not assert parent-Hamiltonian ground-space
membership or the source's unrestricted geometry; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance twoPlaquetteMoveWidthFact : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance twoPlaquetteMoveWidthOneFact : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance twoPlaquetteMoveHeightOneFact : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev X := TorusVertex width height
private abbrev Γₜ := torusGraph width height
private abbrev R := twoPlaquetteTorusRegion (width := width) (height := height)
private abbrev T := twoPlaquetteTorusTree (width := width) (height := height)

/-- One six-spin unitary extends the literal left vertical insertion to the middle
vertical bond, uniformly in the group element and all crossing labels.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusTwoPlaquettePhysicalFluxMove
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ W : Matrix ({v : X // v ∈ R} → Fin d) ({v : X // v ∈ R} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({v : X // v ∈ R} → Fin d) ℂ ∧
      ∀ (g : G) (θ : {e : Edge Γₜ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusTwoPlaquetteFluxAssignment (width := width) (height := height) false g))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (torusTwoPlaquetteFluxAssignment (width := width) (height := height) true g))) R
          (fun f => Fintype.equivFin G (θ f)) := by
  classical
  obtain ⟨W, hW, hact⟩ := exists_unitary_regularTwoCyclePhysicalFluxMove R T
    (torusIncidentSite (width := width) (height := height) a)
    (fun v => ha.isGIsometric_torusIncidentSite v)
    twoPlaquetteTorusTree_le twoPlaquetteTorusTree_isTree
    (twoPlaquetteTorusVertexEquiv 0)
    (twoPlaquetteTorusCycleBond 0) (twoPlaquetteTorusCycleBond 1)
    ((twoPlaquetteTorusCycleBond_injective (width := width) (height := height)).ne (by decide))
  refine ⟨W, hW, fun g θ => ?_⟩
  have h₀ := torusTwoPlaquetteFluxAssignment_eq_treeCycleAssignment
    (width := width) (height := height) false g
  have h₁ := torusTwoPlaquetteFluxAssignment_eq_treeCycleAssignment
    (width := width) (height := height) true g
  simp only [Bool.false_eq_true, false_and, or_false, true_and] at h₀ h₁
  rw [h₀, h₁]
  exact hact g θ
end TNLean.PEPS
