/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusComplementPathReplacement
import TNLean.PEPS.TorusPhysicalLocalEquivalence
import TNLean.PEPS.TorusSimplyConnectedComplement

/-!
# Physical densities and local equivalence from simple connectedness

The complementary winding loops are constructed from the actual simply
connected closed-cell realization of the region. The resulting physical
reduced density is common to all nonzero coherent closure states; local
expectations agree and a complementary physical unitary relates any two.

**Scope restriction (regular native torus):** Both torus dimensions are at
least three. The induced occupied graph is connected, expressing the contiguous
block required by SCP10, lines 1931–1933 and 1349–1354. This condition is separate
from simple connectedness of the closed-cell union, which may admit diagonal
contacts between otherwise disconnected occupied components. Spanning trees,
roots, boundary enumerations, and exterior loops are derived internally.
The smaller torus regimes and the width-one stripe construction remain separate;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: SCP10, arXiv:1001.3807, Theorem 6.7, Corollary 6.8, and
Theorem 6.9, local source lines 1935–2072.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

/-- Choose trees and roots in the contiguous region and its complement, number
the actual boundary, and choose exterior loops with the boundary-route winding.
Source: SCP10, proof of Theorem 6.9, lines 1931–1990. -/
private theorem exists_torusRegionBoundaryCoordinates_of_isSimplyConnected
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R)) :
    ∃ (TR : SimpleGraph {v : X // v ∈ R})
      (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
      (hTR : TR ≤ (Γₜ).induce (R : Set X))
      (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
      (htreeR : TR.IsTree) (htreeS : TS.IsTree)
      (_oR : {v : X // v ∈ R}) (oS : {v : X // v ∈ Finset.univ \ R})
      (e : {f : Edge Γₜ // IsRegionBoundaryEdge R f} ≃
        Fin (Fintype.card {f : Edge Γₜ // IsRegionBoundaryEdge R f} - 1 + 1))
      (p : {f : Edge Γₜ // IsRegionBoundaryEdge R f} →
        ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk oS oS),
      ∀ f, torusWalkWinding
          ((p f).map (SimpleGraph.Embedding.induce
            ((Finset.univ \ R : Finset X) : Set X)).toHom) =
        torusWalkWinding
          (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS (e.symm 0) f) := by
  classical
  have hS := torusGraph_compl_connected_of_isSimplyConnected R hSC hR
  obtain ⟨TR, hTR, htreeR⟩ := hR.exists_isTree_le
  obtain ⟨TS, hTS, htreeS⟩ := hS.exists_isTree_le
  obtain ⟨oR⟩ := hR.nonempty
  obtain ⟨oS⟩ := hS.nonempty
  let β := {f : Edge Γₜ // IsRegionBoundaryEdge R f}
  let : Nonempty β := nonempty_torusRegionBoundaryEdge_of_isSimplyConnected R hSC hR
  have hcard : 1 ≤ Fintype.card β := Fintype.card_pos
  let e : β ≃ Fin (Fintype.card β - 1 + 1) :=
    Fintype.equivFinOfCardEq (Nat.sub_add_cancel hcard).symm
  obtain ⟨p, hp⟩ := exists_complementBoundaryLoops_of_isSimplyConnected
    R hSC TR TS hTR hTS htreeR htreeS oS (e.symm 0)
  exact ⟨TR, TS, hTR, hTS, htreeR, htreeS, oR, oS, e, p, hp⟩

/-- The genuine simply connected region has one common physical reduced
density for every nonzero coherent closure state. Its rank is the boundary
power, its spectrum is flat, and all nonnegative finite Rényi entropies have
the boundary value. Source: SCP10, Theorem 6.9, lines 2027–2072. -/
theorem IsGIsometric.exists_torusPhysicalCut_common_density_of_isSimplyConnected
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R)) :
    let b := Fintype.card {f : Edge Γₜ // IsRegionBoundaryEdge R f}
    ∃ ρ : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ,
      ∀ {I : Type*} [Fintype I] (pairs : I → G × G)
        (_hcomm : ∀ i, Commute (pairs i).1 (pairs i).2) (μ : I → ℂ),
        torusClosureSuperpositionCut a pairs μ R ≠ 0 →
        let M : Matrix (RegionPhysicalConfig (d := d) R)
            (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
          fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)
        0 < (M * M.conjTranspose).trace ∧
          (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) = ρ ∧
          ρ.PosSemidef ∧ ρ.trace = 1 ∧ ρ.rank = Fintype.card G ^ (b - 1) ∧
          ρ * ρ = ((Fintype.card G : ℂ) ^ (b - 1))⁻¹ • ρ ∧
          ∃ hρ : ρ.IsHermitian,
            vonNeumannEntropy ρ hρ = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) ∧
              ∀ α : ℝ, 0 ≤ α →
                renyiEntropy ρ hρ α = (b - 1 : ℕ) * Real.log (Fintype.card G : ℝ) := by
  obtain ⟨TR, TS, hTR, hTS, htreeR, htreeS, oR, oS, e, p, hwind⟩ :=
    exists_torusRegionBoundaryCoordinates_of_isSimplyConnected R hR hSC
  exact ha.exists_torusPhysicalCut_common_density_of_isSimplyConnected_and_winding
    R hSC TR TS hTR hTS htreeR htreeS oR oS e p hwind

/-- Simple connectedness gives equality of all local expectations and a unitary
acting on the complementary physical factor, in the coefficient convention
`M₂ = M₁ * U.transpose`. Source: SCP10, Theorem 6.7 and Corollary 6.8,
lines 1995–2025. -/
theorem IsGIsometric.torusPhysicalCut_local_equivalence_of_isSimplyConnected
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset X) (hR : ((Γₜ).induce (R : Set X)).Connected)
    (hSC : IsSimplyConnected (torusRegionRealization R))
    {I J : Type*} [Fintype I] [Fintype J]
    (pairs : I → G × G) (pairs' : J → G × G)
    (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2)
    (hcomm' : ∀ j, Commute (pairs' j).1 (pairs' j).2)
    (μ : I → ℂ) (μ' : J → ℂ)
    (hne : torusClosureSuperpositionCut a pairs μ R ≠ 0)
    (hne' : torusClosureSuperpositionCut a pairs' μ' R ≠ 0) :
    let A : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)
    let B : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => torusClosureSuperpositionCut a pairs' μ' R (σ, τ)
    (∀ O : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) R) ℂ,
      (O * (normalizedPureCutMatrix B * (normalizedPureCutMatrix B).conjTranspose)).trace =
        (O * (normalizedPureCutMatrix A * (normalizedPureCutMatrix A).conjTranspose)).trace) ∧
      ∃ U : Matrix.unitaryGroup (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ,
        normalizedPureCutMatrix B = normalizedPureCutMatrix A *
          (U : Matrix (RegionPhysicalConfig (d := d) (Finset.univ \ R))
            (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ).transpose := by
  obtain ⟨TR, TS, hTR, hTS, htreeR, htreeS, oR, oS, e, p, hwind⟩ :=
    exists_torusRegionBoundaryCoordinates_of_isSimplyConnected R hR hSC
  exact ha.torusPhysicalCut_local_equivalence_of_isSimplyConnected_and_winding
    R hSC TR TS hTR hTS htreeR htreeS oR oS e p hwind
    pairs pairs' hcomm hcomm' μ μ' hne hne'

end TNLean.PEPS
