/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.PureCutLocalEquivalence
import TNLean.PEPS.TorusPhysicalCutDensity

/-!
# Local equivalence of original torus closure superpositions

Every normalized coherent closure state has the same reduced density on the
region. Consequently, all expectations of operators supported on that region
agree, and any two normalized states are related by a unitary on its complement.

**Scope restriction (geometric winding data):** The region has an actually
simply connected closed-cell realization, and fixed complementary loops realize
the boundary-route winding. Both torus dimensions are at least three. The full
disk argument and the width-one stripe construction of SCP10, Theorem 6.7,
remain separate; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: SCP10, arXiv:1001.3807, Theorem 6.7 and Corollary 6.8,
local source lines 1995–2025.

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

/-- All local expectations agree between normalized original coherent closure
states, and a unitary on the complementary physical factor relates any two
through right multiplication by its transpose.
The reduced density is derived from local G-isometry and geometric winding,
rather than supplied as a hypothesis. Source: SCP10, Theorem 6.7 and
Corollary 6.8, lines 1995–2025. -/
theorem IsGIsometric.torusPhysicalCut_local_equivalence_of_isSimplyConnected_and_winding
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    (TR : SimpleGraph {v : X // v ∈ R})
    (TS : SimpleGraph {v : X // v ∈ Finset.univ \ R})
    (hTR : TR ≤ (Γₜ).induce (R : Set X))
    (hTS : TS ≤ (Γₜ).induce ((Finset.univ \ R : Finset X) : Set X))
    (htreeR : TR.IsTree) (htreeS : TS.IsTree)
    (oR : {v : X // v ∈ R}) (oS : {v : X // v ∈ Finset.univ \ R})
    {n : ℕ} (e : {f : Edge Γₜ // IsRegionBoundaryEdge R f} ≃ Fin (n + 1))
    (p : {f : Edge Γₜ // IsRegionBoundaryEdge R f} →
      ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Walk oS oS)
    (hwind : ∀ f, torusWalkWinding
        ((p f).map (SimpleGraph.Embedding.induce
          ((Finset.univ \ R : Finset X) : Set X)).toHom) =
      torusWalkWinding (torusBoundaryTreeRoute R TR TS hTR hTS htreeR htreeS oS (e.symm 0) f))
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
  classical
  obtain ⟨ρ, hρ⟩ := ha.exists_torusPhysicalCut_common_density_of_isSimplyConnected_and_winding
    R hSC TR TS hTR hTS htreeR htreeS oR oS e p hwind
  let pairsA : I ⊕ J → G × G := Sum.elim pairs (fun _ => (1, 1))
  let pairsB : I ⊕ J → G × G := Sum.elim (fun _ => (1, 1)) pairs'
  let μA : I ⊕ J → ℂ := Sum.elim μ (fun _ => 0)
  let μB : I ⊕ J → ℂ := Sum.elim (fun _ => 0) μ'
  have hcommA : ∀ i, Commute (pairsA i).1 (pairsA i).2 := by
    intro i
    cases i with
    | inl i => exact hcomm i
    | inr j => exact Commute.refl 1
  have hcommB : ∀ i, Commute (pairsB i).1 (pairsB i).2 := by
    intro i
    cases i with
    | inl i => exact Commute.refl 1
    | inr j => exact hcomm' j
  have hcutA : torusClosureSuperpositionCut a pairsA μA R =
      torusClosureSuperpositionCut a pairs μ R := by
    ext q
    simp [torusClosureSuperpositionCut, pairsA, μA, Fintype.sum_sum_type]
  have hcutB : torusClosureSuperpositionCut a pairsB μB R =
      torusClosureSuperpositionCut a pairs' μ' R := by
    ext q
    simp [torusClosureSuperpositionCut, pairsB, μB, Fintype.sum_sum_type]
  have hA := hρ pairsA hcommA μA (by simpa only [hcutA] using hne)
  have hB := hρ pairsB hcommB μB (by simpa only [hcutB] using hne')
  simp only [hcutA, hcutB] at hA hB
  have heq := hB.2.1.trans hA.2.1.symm
  constructor
  · intro O
    exact congrArg (fun D => (O * D).trace)
      ((normalizedPureCutMatrix_mul_conjTranspose _).trans
        (heq.trans (normalizedPureCutMatrix_mul_conjTranspose _).symm))
  · exact exists_unitary_normalizedPureCutMatrix_eq_of_reducedMatrix_eq _ _ heq

end TNLean.PEPS
