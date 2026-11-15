/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularAnchoredTwistDensity
import TNLean.PEPS.TorusFluxBoundaryComponent
import TNLean.PEPS.TorusDualHomotopyClassification

/-!
# Vacuum normalized density of a native noncentral open flux pair

The actual exterior collar gives the untwisted complementary boundary component
for an avoiding native string. Its derived tree gauge and complementary Gram
calculation yield vacuum normalized density for arbitrary finite groups.
Simple connectedness of the computed forbidden plaquettes constructs such an
avoiding string in the original lifted displacement class. Full-support
homotopy and virtual invariance identify their actual native coefficient cuts.

Source: SCP10, arXiv:1001.3807v3, Theorem 6.9 and Lemma 6.14,
lines 1935–1990 and 2199–2214.

**Scope restriction:** Both torus periods are at least three. The physical
observation graph is connected, its actual closed-cell realization is simply
connected, and the computed four-corner forbidden plaquettes also have simply
connected realization. Both endpoints are outside that computed set. These
conditions are explicit; endpoint exclusion alone does not classify restricted
homotopy or imply vacuum density on annular observations. No centrality, path,
component, gauge, density equality or nonzero cut is supplied to the main
construction. See `docs/paper-gaps/scp10_noncentral_open_flux_density.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance noncentralFluxWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance noncentralFluxHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
local instance noncentralFluxQuiver : Quiver X := torusDualQuiver width height

private theorem graph_labels_one {G : Type*} [Group G] :
    torusGraphRegularLabels (1 : X → G) 1 = fun _ => 1 := by
  funext f
  unfold torusGraphRegularLabels
  cases he : torusEdgeEquiv.symm f <;> simp

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- An actual avoiding flux string with arbitrary insertion element has the
vacuum normalized reduced density on a connected, simply connected physical
region. The exterior collar supplies the untwisted component and all actual
cuts are derived nonzero. Conditional avoiding-path form of SCP10, Lemma 6.14. -/
theorem IsGIsometric.torusAvoidingFlux_normalized_density_eq_vacuum
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (g : G) {a b : X} (p : TorusDualPath a b)
    (hp : ∀ v ∈ (torusDualPathGraphWalk p).support, v ∉ torusIncidentDualPlaquettes R) :
    let M := torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R
    let M₀ := torusBondRegularPhysicalCutMatrix A 1 R
    M ≠ 0 ∧ M₀ ≠ 0 ∧
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
        (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  obtain ⟨U, hU, o, hu, hboundary⟩ :=
    exists_torusFlux_untwisted_boundary_component R hSC p hp g
  have hi := torusDualFlux_graphLabels_eq_one_on_incident_of_avoids R p hp g
  have hd := regularPhysicalCutMatrix_normalized_reduced_eq_of_untwisted_boundary_component
    (torusIncidentSite A) (fun v => hA.isGIsometric_torusIncidentSite v)
    R hR (torusGraph_compl_connected_of_isSimplyConnected R hSC hR)
    (nonempty_torusRegionBoundaryEdge_of_isSimplyConnected R hSC hR)
    U hU o (torusGraphRegularLabels (torusDualFluxLabels g p).1
      (torusDualFluxLabels g p).2) hu hboundary hi
  have hvac : torusBondRegularPhysicalCutMatrix A 1 R =
      regularPhysicalCutMatrix (torusIncidentSite A) R := by
    rw [torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix]
    change regularPhysicalCutMatrix (regularTwistedSite (torusIncidentSite A)
      (torusGraphRegularLabels (1 : X → G) 1)) R = _
    rw [graph_labels_one, regularTwistedSite_one]
  rw [torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix A
    (torusDualFluxLabels g p) R, hvac]
  exact hd

/-- Construct a same-displacement avoiding detour and derive the vacuum
normalized density of the actual original native open or closed flux string.
The insertion is arbitrary, including noncentral elements of nonabelian finite
groups. Physical simple connectedness and simple connectedness of the computed
forbidden dual cells are separate explicit hypotheses. No detour, homotopy,
component, gauge, density or nonzero-cut premise is supplied. Source: SCP10,
Theorem 6.9 and Lemma 6.14 under the stated geometric conditions. -/
theorem IsGIsometric.torusFlux_normalized_density_eq_vacuum_of_isSimplyConnected
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (hBSC : IsSimplyConnected (torusRegionRealization (torusIncidentDualPlaquettes R)))
    (g : G) {a b : X} (p : TorusDualPath a b)
    (ha : a ∉ torusIncidentDualPlaquettes R) (hb : b ∉ torusIncidentDualPlaquettes R) :
    let M := torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R
    let M₀ := torusBondRegularPhysicalCutMatrix A 1 R
    M ≠ 0 ∧ M₀ ≠ 0 ∧
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
        (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  obtain ⟨q, hd, hq⟩ := exists_torusDualPath_avoiding_of_isSimplyConnected
    (torusIncidentDualPlaquettes R) hBSC p ha hb
  have hhom : TorusDualHomotopy Set.univ p q :=
    (torusDualHomotopy_univ_iff_displacement_eq p q).mpr hd.symm
  have hcut : torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g q) R =
      torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R := by
    ext σ τ
    exact hhom.torusBondNetwork_eq (leftRegularMatrix G) (fun _ => A)
      (fun _ _ => hA.invariant) (assembleRegionσ R σ τ) g
  have hresult := hA.torusAvoidingFlux_normalized_density_eq_vacuum R hR hSC g q hq
  simpa only [hcut] using hresult

end TNLean.PEPS
