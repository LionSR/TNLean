/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusNoncentralFluxDensity
import TNLean.PEPS.RegionPhysicalCutMarginal

/-!
# Vacuum flux density inside an admissible envelope

Every subregion of an admissible simply connected physical envelope has
the vacuum normalized density. The smaller observation may be disconnected,
have holes or be empty; all geometric hypotheses remain on the envelope.
The proof is the actual finite-product partial trace of the already derived
native density, and both smaller coefficient cuts are proved nonzero.

Source: SCP10, arXiv:1001.3807v3, Theorem 6.9 and Lemma 6.14,
lines 1935–1990 and 2199–2214, under explicit envelope conditions.
This does not cover an annulus surrounding an endpoint merely because its
own sites avoid that endpoint. See
`docs/paper-gaps/scp10_flux_envelope_density.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance envelopeWidthOne : Fact (1 < width) :=
  ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance envelopeHeightOne : Fact (1 < height) :=
  ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height
local instance envelopeFluxQuiver : Quiver X := torusDualQuiver width height

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- Every subregion of an admissible simply connected envelope has the actual
native vacuum normalized flux density. The subregion has no connectedness or
topology hypothesis; the envelope retains both explicit simple connectedness
conditions and endpoint exclusions. Both cuts are derived nonzero.
Source: SCP10, Theorem 6.9 and Lemma 6.14, under these envelope conditions. -/
theorem IsGIsometric.torusFlux_normalized_density_eq_vacuum_of_subset_isSimplyConnected
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (R S : Finset X) (hRS : R ⊆ S)
    (hS : ((Γₜ).induce (S : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization S))
    (hBSC : IsSimplyConnected (torusRegionRealization (torusIncidentDualPlaquettes S)))
    (g : G) {a b : X} (p : TorusDualPath a b)
    (ha : a ∉ torusIncidentDualPlaquettes S) (hb : b ∉ torusIncidentDualPlaquettes S) :
    let M := torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R
    let M₀ := torusBondRegularPhysicalCutMatrix A 1 R
    M ≠ 0 ∧ M₀ ≠ 0 ∧
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) =
        (M₀ * M₀.conjTranspose).trace⁻¹ • (M₀ * M₀.conjTranspose) := by
  let ψ : (X → Fin d) → ℂ := fun σ => torusBondNetwork
    (fun x c => A c.1 c.2.1 c.2.2.1 c.2.2.2 (σ x))
    (fun x => leftRegularMatrix G ((torusDualFluxLabels g p).1 x))
    (fun x => leftRegularMatrix G ((torusDualFluxLabels g p).2 x))
  let φ : (X → Fin d) → ℂ := fun σ => torusBondNetwork
    (fun x c => A c.1 c.2.1 c.2.2.1 c.2.2.2 (σ x))
    (fun _ => leftRegularMatrix G 1) (fun _ => leftRegularMatrix G 1)
  obtain ⟨hψ, hφ, hd⟩ :=
    hA.torusFlux_normalized_density_eq_vacuum_of_isSimplyConnected S hS hSC hBSC g p ha hb
  have hnψ : regionPhysicalCutMatrix ψ R ≠ 0 :=
    (regionPhysicalCutMatrix_ne_zero_iff ψ R).mpr
      ((regionPhysicalCutMatrix_ne_zero_iff ψ S).mp hψ)
  have hnφ : regionPhysicalCutMatrix φ R ≠ 0 :=
    (regionPhysicalCutMatrix_ne_zero_iff φ R).mpr
      ((regionPhysicalCutMatrix_ne_zero_iff φ S).mp hφ)
  exact ⟨hnψ, hnφ, regionPhysicalCutMatrix_normalized_reduced_eq_of_subset ψ φ hRS hd⟩

end TNLean.PEPS
