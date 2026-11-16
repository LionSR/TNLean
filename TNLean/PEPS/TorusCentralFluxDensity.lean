/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCentralTwistDensity
import TNLean.PEPS.TorusDualPhysicalAvoidance
import TNLean.PEPS.TorusDualHomotopyClassification
import TNLean.PEPS.TorusDualFluxDetection

/-!
# Vacuum reduced density of an open central flux pair

The dual corner collar of the physical observation region is computed from
the native incidence geometry. Simple connectedness of that collar gives a
detour with identity insertions on every incident physical bond. Full-support
homotopy completeness identifies its actual state with the original path's
state. For a central insertion element, equality of the complementary local
Gram kernels gives the vacuum reduced matrix, including its scalar.

Source: SCP10, arXiv:1001.3807v3, Definition 6.13 and Lemma 6.14,
source lines 2180–2214, using regular G-isometry from Definition 6.1.

**Scope restriction (central flux and simply connected dual corner collar):**
Both periods are at least three. The insertion element is central, the actual
computed dual corner collar is simply connected, and both endpoints lie outside
it. No path, homotopy, contraction factorization, density equality, or nonzero
cut is supplied. The theorem includes open pairs and arbitrary winding but
does not cover general noncentral flux or endpoint-free annular observations.
See `docs/paper-gaps/scp10_central_open_flux_density.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance centralFluxWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance centralFluxHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
local instance centralFluxQuiver : Quiver X := torusDualQuiver width height

variable {G : Type*} [Group G]

private theorem graph_labels_central (t : TorusBondLabels width height G)
    (hh : ∀ v x, Commute (t.1 v) x) (hv : ∀ v x, Commute (t.2 v) x) :
    ∀ f x, Commute (torusGraphRegularLabels t.1 t.2 f) x := by
  intro f x
  unfold torusGraphRegularLabels
  cases he : torusEdgeEquiv.symm f with
  | inl v =>
    change Commute (if f.1.1 = v then t.1 v else (t.1 v)⁻¹) x
    split_ifs <;> first | exact hh v x | exact (hh v x).inv_left
  | inr v =>
    change Commute (if f.1.1 = v then (t.2 v)⁻¹ else t.2 v) x
    split_ifs <;> first | exact hv v x | exact (hv v x).inv_left

private theorem incident_ofAdj_iff (R : Finset X) {a b : X} (h : (Γₜ).Adj a b) :
    IsRegionIncidentEdge R (Edge.ofAdj h) ↔ a ∈ R ∨ b ∈ R := by
  rcases Edge.ofAdj_endpoints h with h | h
  · simp only [IsRegionIncidentEdge, h.1, h.2]
  · simp only [IsRegionIncidentEdge, h.1, h.2, or_comm]

private theorem graph_labels_incident (R : Finset X) (t : TorusBondLabels width height G)
    (ht : ∀ v : X,
      ((v ∈ R ∨ (v.1 + 1, v.2) ∈ R) → t.1 v = 1) ∧
        ((v ∈ R ∨ (v.1, v.2 + 1) ∈ R) → t.2 v = 1)) :
    ∀ f : Edge (Γₜ), IsRegionIncidentEdge R f → torusGraphRegularLabels t.1 t.2 f = 1 := by
  intro f hf
  obtain ⟨z, rfl⟩ := torusEdgeEquiv.surjective f
  rcases z with v | v
  · change torusGraphRegularLabels t.1 t.2 (torusRightEdge v) = 1
    have hi : v ∈ R ∨ (v.1 + 1, v.2) ∈ R :=
      (incident_ofAdj_iff R (torusGraph_adj_right v.1 v.2)).mp hf
    unfold torusGraphRegularLabels
    rw [show torusEdgeEquiv.symm (torusRightEdge v) = Sum.inl v from
      torusEdgeEquiv.symm_apply_apply (Sum.inl v)]
    simp only [(ht v).1 hi, inv_one, ite_self]
  · change torusGraphRegularLabels t.1 t.2 (torusUpEdge v) = 1
    have hi : v ∈ R ∨ (v.1, v.2 + 1) ∈ R :=
      (incident_ofAdj_iff R (torusGraph_adj_up v.1 v.2)).mp hf
    unfold torusGraphRegularLabels
    rw [show torusEdgeEquiv.symm (torusUpEdge v) = Sum.inr v from
      torusEdgeEquiv.symm_apply_apply (Sum.inr v)]
    simp only [(ht v).2 hi, inv_one, ite_self]

private theorem graph_labels_one :
    torusGraphRegularLabels (1 : X → G) 1 = fun _ ↦ 1 := by
  funext f
  unfold torusGraphRegularLabels
  cases he : torusEdgeEquiv.symm f <;> simp

variable [Fintype G] [DecidableEq G] {d : ℕ}

/-- An actual finite open or closed central flux string has the vacuum reduced
matrix on a physical region whose computed dual corner collar is simply
connected and excludes both endpoints. Both physical cuts are derived nonzero,
and their normalized densities agree. No avoiding path or density premise is
supplied. Source: SCP10, Definition 6.13 and Lemma 6.14. -/
theorem IsGIsometric.torusCentralFlux_normalized_density_eq_vacuum
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (R : Finset X)
    (hSC : IsSimplyConnected (torusRegionRealization (torusIncidentDualPlaquettes R)))
    (g : G) (hg : ∀ x, Commute g x) {a b : X} (p : TorusDualPath a b)
    (ha : a ∉ torusIncidentDualPlaquettes R) (hb : b ∉ torusIncidentDualPlaquettes R) :
    let M := torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R
    let M₀ := torusBondRegularPhysicalCutMatrix A 1 R
    M ≠ 0 ∧ M₀ ≠ 0 ∧ M * M.conjTranspose = M₀ * M₀.conjTranspose ∧
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
        (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  obtain ⟨q, hd, hq⟩ := exists_torusDualPath_trivial_on_incident R hSC p ha hb g
  have hhom : TorusDualHomotopy Set.univ p q :=
    (torusDualHomotopy_univ_iff_displacement_eq p q).mpr hd.symm
  have hcut : torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g q) R =
      torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R := by
    ext σ τ
    exact hhom.torusBondNetwork_eq (leftRegularMatrix G) (fun _ ↦ A)
      (fun _ _ ↦ hA.invariant) (assembleRegionσ R σ τ) g
  have hc := graph_labels_central (torusDualFluxLabels g q)
    (fun _ x ↦ (hg x).zpow_left _) (fun _ x ↦ (hg x).zpow_left _)
  have hi := graph_labels_incident R (torusDualFluxLabels g q) hq
  have hred := regularPhysicalCutMatrix_reduced_eq_of_central (torusIncidentSite A)
    (fun v ↦ hA.isGIsometric_torusIncidentSite v)
    (torusGraphRegularLabels (torusDualFluxLabels g q).1 (torusDualFluxLabels g q).2) hc R hi
  have hvac : torusBondRegularPhysicalCutMatrix A 1 R =
      regularPhysicalCutMatrix (torusIncidentSite A) R := by
    rw [torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix]
    change regularPhysicalCutMatrix (regularTwistedSite (torusIncidentSite A)
      (torusGraphRegularLabels (1 : X → G) 1)) R = _
    rw [graph_labels_one, regularTwistedSite_one]
  have hn : torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g q) R *
        (torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g q) R).conjTranspose =
      torusBondRegularPhysicalCutMatrix A 1 R *
        (torusBondRegularPhysicalCutMatrix A 1 R).conjTranspose := by
    rw [torusBondRegularPhysicalCutMatrix_eq_regularPhysicalCutMatrix A
      (torusDualFluxLabels g q) R, hvac]
    exact hred
  rw [hcut] at hn
  have hnil : torusDualFluxLabels (1 : G) (.nil : TorusDualPath a a) = 1 := by
    ext v <;> simp [torusDualFluxLabels, torusFluxPowerLabels]
  have hzero := hA.torusDualFlux_cutMatrix_ne_zero 1 (.nil : TorusDualPath a a) R
  rw [hnil] at hzero
  refine ⟨hA.torusDualFlux_cutMatrix_ne_zero g p R, hzero, hn, ?_⟩
  rw [hn]

end TNLean.PEPS
