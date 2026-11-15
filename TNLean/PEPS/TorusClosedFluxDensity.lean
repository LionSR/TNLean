/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualFluxDetection
import TNLean.PEPS.TorusSimplyConnectedPhysicalDensity

/-!
# Vacuum reduced densities of closed flux strings

A closed dual path has trivial plaquette holonomy, including when it winds
around the torus. Flat-connection classification and virtual invariance turn
its actual state into a commuting seam closure. The common physical density
of those closures therefore identifies its normalized regional density with
the vacuum density on every connected, simply connected observation region.
Nonvanishing of the actual cut is derived from regular G-isometry.

Source: SCP10, arXiv:1001.3807v3, Lemma 6.14 and Theorem 6.7,
local source lines 1995–2025 and 2199–2214.

**Scope restriction (closed strings and simply connected regions):** Both
torus periods are at least three, the tensor is regular G-isometric, and the
occupied observation graph is connected with simply connected closed-cell
realization. This does not prove the open flux-pair vacuum-density claim on
general endpoint-free regions or equate global winding states with the vacuum.
See `docs/paper-gaps/scp10_closed_flux_density.tex`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
local notation "X" => TorusVertex width height
local instance : Quiver X := torusDualQuiver width height

omit [NeZero width] [NeZero height] [Fintype G] [DecidableEq G] in
private theorem loop_labels_flat (g : G) {a : X} (p : TorusDualPath a a) :
    IsTorusBondFlat (torusDualFluxLabels g p) := by
  intro v
  have h := torusBondPlaquetteHolonomy_torusDualFluxLabels_loop g p v
  unfold torusBondPlaquetteHolonomy at h
  have he := congrArg (fun z ↦ (torusDualFluxLabels g p).1 v * z *
    (torusDualFluxLabels g p).2 v) h
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one, one_mul] using he

private theorem flat_cut_eq_closure
    [Fact (2 < width)] [Fact (2 < height)]
    (A : G → G → G → G → Fin d → ℂ)
    (hA : ∀ g, siteMap A ∘ₗ torusLegRep (leftRegularMatrix G) g = siteMap A)
    (t : TorusBondLabels width height G) (ht : IsTorusBondFlat t) (R : Finset X) :
    ∃ u v : G, Commute u v ∧ torusBondRegularPhysicalCutMatrix A t R =
      fun σ τ ↦ torusGClosure (leftRegularMatrix G) A u v (assembleRegionσ R σ τ) := by
  obtain ⟨k, u, v, huv, hk⟩ := exists_torusBondGauge_eq_closure t ht
  refine ⟨u, v, huv, ?_⟩
  ext σ τ
  have h := torusBondNetwork_torusBondGauge (leftRegularMatrix G) (fun _ ↦ A)
    (fun _ ↦ hA) (assembleRegionσ R σ τ) k t
  rw [hk] at h
  dsimp only [torusBondRegularPhysicalCutMatrix, torusGClosure,
    torusHorizontalClosure, torusVerticalClosure]
  simpa only [torusBondClosureLabels, apply_ite, map_one] using h.symm

variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "Γₜ" => torusGraph width height

/-- Every closed flux string has the vacuum normalized reduced density on a
connected, simply connected physical region. This includes winding loops;
nonzero normalization is derived from regular G-isometry. The two global
states are not asserted equal. Source: SCP10, Lemma 6.14 and Theorem 6.7. -/
theorem IsGIsometric.torusClosedFlux_normalized_density_eq_vacuum
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    (g : G) {a : X} (p : TorusDualPath a a) :
    let M := torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R
    let M₀ := torusBondRegularPhysicalCutMatrix A 1 R
    (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
      (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  classical
  obtain ⟨ρ, hρ⟩ := hA.exists_torusPhysicalCut_common_density_of_isSimplyConnected R hR hSC
  have hloop (s : G) {b : X} (q : TorusDualPath b b) :
      let M := torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels s q) R
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) = ρ := by
    obtain ⟨u, v, huv, hcut⟩ := flat_cut_eq_closure A hA.invariant
      (torusDualFluxLabels s q) (loop_labels_flat s q) R
    let pairs : Unit → G × G := fun _ ↦ (u, v)
    let μ : Unit → ℂ := fun _ ↦ 1
    have hM : (fun σ τ ↦ torusClosureSuperpositionCut A pairs μ R (σ, τ)) =
        torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels s q) R := by
      rw [hcut]
      ext σ τ
      simp [torusClosureSuperpositionCut, pairs, μ]
    have hne : torusClosureSuperpositionCut A pairs μ R ≠ 0 := by
      intro hz
      apply hA.torusDualFlux_cutMatrix_ne_zero s q R
      rw [← hM, hz]
      rfl
    have hd := hρ pairs (fun _ ↦ huv) μ hne
    simpa only [hM] using hd.2.1
  have hvac := hloop 1 (.nil : TorusDualPath a a)
  exact (hloop g p).trans (by
    simpa [torusDualFluxLabels, torusFluxPowerLabels] using hvac.symm)

end TNLean.PEPS
