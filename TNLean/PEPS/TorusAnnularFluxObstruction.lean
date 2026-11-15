/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularWilsonDensityObstruction
import TNLean.PEPS.TorusDualFluxString

/-!
# An endpoint-free annular observation detects a native open flux

In the seven-by-seven torus, observe the twelve physical sites on the
perimeter of the square from zero to three in both coordinates. An actual
four-step eastward dual string runs from plaquette (1,1) inside the hole to
plaquette (5,1) outside the square. Every physical corner of both endpoint
plaquettes is outside the observation. Nevertheless its holonomy on the
observed perimeter is the inverse of the insertion element. The actual
normalized density therefore differs from vacuum for every nonidentity
element of any finite group and every native regular G-isometric tensor.

This is an explicit limitation of endpoint-only vacuum-density wording in
SCP10, arXiv:1001.3807v3, Lemma 6.14, lines 2199–2214, detected by the
closed-walk measurement of Theorem 6.15. It does not change the explicit
geometry hypotheses of the positive native theorem.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

local instance annularPeriodThree : Fact (2 < 7) := ⟨by decide⟩
local instance annularPeriodOne : Fact (1 < 7) := ⟨by decide⟩
local notation "X" => TorusVertex 7 7
local notation "Γ₇" => torusGraph 7 7
local instance annularFluxQuiver : Quiver X := torusDualQuiver 7 7

/-- The counterclockwise twelve-edge physical perimeter of a four-by-four
square in the seven-by-seven torus. Its two-by-two interior is unobserved. -/
def torusAnnularObservationWalk : (Γ₇).Walk (0, 0) (0, 0) :=
  .cons (torusGraph_adj_right 0 0)
    (.cons (torusGraph_adj_right 1 0)
      (.cons (torusGraph_adj_right 2 0)
        (.cons (torusGraph_adj_up 3 0)
          (.cons (torusGraph_adj_up 3 1)
            (.cons (torusGraph_adj_up 3 2)
              (.cons (torusGraph_adj_right 2 3).symm
                (.cons (torusGraph_adj_right 1 3).symm
                  (.cons (torusGraph_adj_right 0 3).symm
                    (.cons (torusGraph_adj_up 0 2).symm
                      (.cons (torusGraph_adj_up 0 1).symm
                        (.cons (torusGraph_adj_up 0 0).symm .nil)))))))))))

/-- The twelve observed perimeter sites; the four interior physical sites
and the sites beyond the square are excluded. -/
def torusAnnularObservationRegion : Finset X := torusAnnularObservationWalk.support.toFinset

/-- An actual native open dual string from inside the observed ring to the
exterior: four labelled east steps from (1,1) to (5,1). -/
def torusAnnularFluxPath : TorusDualPath ((1, 1) : X) (5, 1) := by
  have h5 : (1 : ZMod 7) + 1 + 1 + 1 + 1 = 5 := by norm_num
  simpa only [h5] using
    (((Quiver.Path.nil.cons (TorusDualStep.east (1 : ZMod 7) (1 : ZMod 7))).cons
      (TorusDualStep.east (1 + 1) 1)).cons
        (TorusDualStep.east (1 + 1 + 1) 1)).cons (TorusDualStep.east (1 + 1 + 1 + 1) 1)

/-- All four physical corners of each endpoint plaquette of the explicit
annular string lie outside the observed ring. -/
theorem torusAnnularFluxPath_endpoint_corners_outside :
    ∀ a ∈ ({(1, 1), (5, 1)} : Finset X),
      a ∉ torusAnnularObservationRegion ∧
      (a.1 + 1, a.2) ∉ torusAnnularObservationRegion ∧
      (a.1, a.2 + 1) ∉ torusAnnularObservationRegion ∧
      (a.1 + 1, a.2 + 1) ∉ torusAnnularObservationRegion := by
  decide

private theorem annular_connected :
    ((Γ₇).induce (torusAnnularObservationRegion : Set X)).Connected := by
  have hR : (torusAnnularObservationRegion : Set X) =
      {v | v ∈ torusAnnularObservationWalk.support} := by
    ext v
    simp [torusAnnularObservationRegion]
  rw [hR]
  exact torusAnnularObservationWalk.connected_induce_support

private def annularRoot : {v : X // v ∈ torusAnnularObservationRegion} :=
  ⟨(0, 0), List.mem_toFinset.mpr torusAnnularObservationWalk.start_mem_support⟩

private theorem annular_support : ∀ x ∈ torusAnnularObservationWalk.support,
    x ∈ (torusAnnularObservationRegion : Set X) :=
  fun _ h => List.mem_toFinset.mpr h

private def annularInducedWalk :
    ((Γ₇).induce (torusAnnularObservationRegion : Set X)).Walk annularRoot annularRoot :=
  torusAnnularObservationWalk.induce (torusAnnularObservationRegion : Set X) annular_support

variable {G : Type*} [Group G]

private theorem directed_right (u v : X → G) (x y : ZMod 7)
    (h : (Γ₇).Adj (x, y) (x + 1, y)) :
    regularDirectedTransport (v := (x, y)) (w := (x + 1, y))
      (torusGraphRegularLabels u v) h = u (x, y) :=
  torusNativeRightTransport_torusGraphRegularLabels u v (x, y)

private theorem directed_up (u v : X → G) (x y : ZMod 7)
    (h : (Γ₇).Adj (x, y) (x, y + 1)) :
    regularDirectedTransport (v := (x, y)) (w := (x, y + 1))
      (torusGraphRegularLabels u v) h = (v (x, y))⁻¹ :=
  torusNativeUpTransport_torusGraphRegularLabels u v (x, y)

private theorem directed_left (u v : X → G) (x y : ZMod 7)
    (h : (Γ₇).Adj (x + 1, y) (x, y)) :
    regularDirectedTransport (v := (x + 1, y)) (w := (x, y))
      (torusGraphRegularLabels u v) h = (u (x, y))⁻¹ := by
  simpa only [directed_right] using
    regularDirectedTransport_symm (v := (x, y)) (w := (x + 1, y))
      (torusGraphRegularLabels u v) h.symm

private theorem directed_down (u v : X → G) (x y : ZMod 7)
    (h : (Γ₇).Adj (x, y + 1) (x, y)) :
    regularDirectedTransport (v := (x, y + 1)) (w := (x, y))
      (torusGraphRegularLabels u v) h = v (x, y) := by
  simpa only [directed_up, inv_inv] using
    regularDirectedTransport_symm (v := (x, y)) (w := (x, y + 1))
      (torusGraphRegularLabels u v) h.symm

private theorem annular_holonomy (g : G) :
    regularWalkHolonomy
      (torusGraphRegularLabels (torusDualFluxLabels g torusAnnularFluxPath).1
        (torusDualFluxLabels g torusAnnularFluxPath).2) torusAnnularObservationWalk = g⁻¹ := by
  simp only [torusAnnularObservationWalk, regularWalkHolonomy_cons,
    regularWalkHolonomy_nil, directed_right, directed_up, directed_left, directed_down]
  have h02 : (0 : ZMod 7) ≠ 2 := by decide
  have h03 : (0 : ZMod 7) ≠ 3 := by decide
  have h04 : (0 : ZMod 7) ≠ 4 := by decide
  have h05 : (0 : ZMod 7) ≠ 5 := by decide
  have h21 : (2 : ZMod 7) ≠ 1 := by decide
  have h32 : (3 : ZMod 7) ≠ 2 := by decide
  have h34 : (3 : ZMod 7) ≠ 4 := by decide
  have h35 : (3 : ZMod 7) ≠ 5 := by decide
  norm_num [torusDualFluxLabels, torusFluxPowerLabels, torusAnnularFluxPath,
    torusDualPathCrossings, TorusDualStep.crossings, torusPointMass,
    h02, h03, h04, h05, h21, h32, h34, h35]

private theorem annular_vacuum_holonomy :
    regularWalkHolonomy (torusGraphRegularLabels (1 : X → G) 1)
      torusAnnularObservationWalk = 1 := by
  simp only [torusAnnularObservationWalk, regularWalkHolonomy_cons,
    regularWalkHolonomy_nil, directed_right, directed_up, directed_left, directed_down,
    Pi.one_apply, inv_one, one_mul]

private theorem induced_holonomy (u : Edge (Γ₇) → G) :
    regularWalkHolonomy (regularRegionInternalOperators torusAnnularObservationRegion u)
      annularInducedWalk = regularWalkHolonomy u torusAnnularObservationWalk := by
  unfold annularInducedWalk annularRoot
  rw [regularWalkHolonomy_inducedWalk, SimpleGraph.Walk.map_induce]
  rfl

variable [Fintype G] [DecidableEq G]

/-- An explicit endpoint-free observed ring distinguishes the normalized
density of an actual native open flux string from vacuum. Both cuts are
derived nonzero. Every physical corner of both endpoint plaquettes is
unobserved, as proved above. This gives a rigorous annular limitation of
endpoint-only wording in SCP10, Lemma 6.14, for any nonidentity finite-group
flux and any native regular G-isometric tensor. -/
theorem IsGIsometric.torusAnnularFlux_normalized_density_ne_vacuum {d : ℕ}
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (g : G) (hg : g ≠ 1) :
    let M := torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g torusAnnularFluxPath)
      torusAnnularObservationRegion
    let M₀ := torusBondRegularPhysicalCutMatrix A 1 torusAnnularObservationRegion
    M ≠ 0 ∧ M₀ ≠ 0 ∧
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) ≠
        (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  apply hA.torusBond_normalized_density_ne_of_closedWalk_holonomy
    torusAnnularObservationRegion annular_connected annularRoot annularInducedWalk
    (torusDualFluxLabels g torusAnnularFluxPath) 1
  rw [induced_holonomy, induced_holonomy, annular_holonomy]
  change ConjClasses.mk g⁻¹ ≠ ConjClasses.mk
    (regularWalkHolonomy (torusGraphRegularLabels (1 : X → G) 1) torusAnnularObservationWalk)
  rw [annular_vacuum_holonomy]
  intro hc
  have hi : g⁻¹ = 1 := by
    simpa only [ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] using hc
  exact hg (inv_eq_one.mp hi)

end TNLean.PEPS
