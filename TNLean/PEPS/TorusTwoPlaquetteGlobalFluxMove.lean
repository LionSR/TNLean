/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove
import TNLean.PEPS.TorusTwoPlaquetteFluxHolonomy
import TNLean.PEPS.RegularTorusEntropy

/-!
# A six-spin flux-moving operation on the globally contracted torus PEPS

The fixed six-site rectangle, spanning path, and two upward cycle bonds yield
one unitary on the original spins of the region. Extending it by the identity
outside the region gives a global unitary which changes the single leftmost
insertion into leftmost and middle insertions. The identity holds for every
group element and every common exterior and crossing assignment. Its local
isometry hypotheses are derived from the native four-leg regular tensor.

Source: SCP10, arXiv:1001.3807, Theorem 6.16, lines 2271–2305.

**Scope restriction (six-site regular flux movement):** The horizontal period
is at least four and the vertical period at least three; the virtual action is
regular. This actual globally contracted state identity does not assert
parent-Hamiltonian ground-space membership or unrestricted lattice geometry;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (3 < width)] [Fact (2 < height)]
local instance twoPlaquetteGlobalMoveWidthFact : Fact (2 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance twoPlaquetteGlobalMoveWidthOneFact : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 3 < width); omega⟩
local instance twoPlaquetteGlobalMoveHeightOneFact : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev X := TorusVertex width height
private abbrev Γₜ := torusGraph width height
private abbrev R := twoPlaquetteTorusRegion (width := width) (height := height)
private abbrev T := twoPlaquetteTorusTree (width := width) (height := height)

/-- A fixed six-spin operation, extended by the identity outside the region,
moves the literal insertion in the actual global contraction for every common
exterior and crossing assignment. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem IsGIsometric.exists_unitary_torusTwoPlaquetteGlobalFluxMove
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a)) :
    ∃ W : Matrix ({v : X // v ∈ R} → Fin d) ({v : X // v ∈ R} → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup ({v : X // v ∈ R} → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (X → Fin d) ℂ ∧
      ∀ (g : G) (u : Edge Γₜ → G),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension R
            (torusTwoPlaquetteFluxAssignment (width := width) (height := height) false g) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite
          (torusIncidentSite (width := width) (height := height) a)
          (regularRegionBondExtension R
            (torusTwoPlaquetteFluxAssignment (width := width) (height := height) true g) u))) := by
  classical
  obtain ⟨W, hW, hglobal, hact⟩ := exists_unitary_regularTwoCycleGlobalFluxMove_bondOperators R T
    (torusIncidentSite (width := width) (height := height) a)
    (fun v => ha.isGIsometric_torusIncidentSite v)
    twoPlaquetteTorusTree_le twoPlaquetteTorusTree_isTree
    (twoPlaquetteTorusVertexEquiv 0)
    (twoPlaquetteTorusCycleBond 0) (twoPlaquetteTorusCycleBond 1)
    ((twoPlaquetteTorusCycleBond_injective (width := width) (height := height)).ne (by decide))
  refine ⟨W, hW, hglobal, fun g u => ?_⟩
  have h₀ := torusTwoPlaquetteFluxAssignment_eq_treeCycleAssignment
    (width := width) (height := height) false g
  have h₁ := torusTwoPlaquetteFluxAssignment_eq_treeCycleAssignment
    (width := width) (height := height) true g
  simp only [Bool.false_eq_true, false_and, or_false, true_and] at h₀ h₁
  rw [h₀, h₁]
  exact hact g u
end TNLean.PEPS
