/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondLocalInverse
import TNLean.PEPS.TorusLabelledBondGeometry

/-!
# The four source cut spaces with independently sized bonds and sites

This is the literal four-block model of SCP10, Theorem 5.5. Every one of the
eight labelled native bonds has its own finite virtual alphabet, and every
one of the four sites has its own finite physical alphabet. Each cut accepts
one arbitrary joint tensor on its eight exposed endpoint incidences.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.DependentTorus

abbrev Vertex := TorusVertex 2 2
abbrev Bond := TorusLabelledBond 2 2

/-- The actual four incident virtual indices at one site, with their own types. -/
abbrev LocalConfig (D : Bond → Type*) (v : Vertex) :=
  DependentBondNetwork.LocalConfig torusLabelledBondTail torusLabelledBondHead D v

variable (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys Out : Vertex → Type*}

/-- The cut with the selected column and row as its two seam positions. -/
def cutBonds (v : Vertex) : Finset Bond := torusSeamCutBonds v.1 v.2

/-- The source's intersection of four actual correlated-boundary ranges. -/
def fourCutSpace (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) :
    Submodule ℂ (((v : Vertex) → Phys v) → ℂ) :=
  ⨅ v, DependentBondNetwork.cutSpace torusLabelledBondTail torusLabelledBondHead D A (cutBonds v)

/-- Membership keeps the four actual cut-range conditions, without changing
the physical configuration type or restricting boundary correlations. -/
theorem mem_fourCutSpace_iff
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (ψ : ((v : Vertex) → Phys v) → ℂ) :
    ψ ∈ fourCutSpace D A ↔ ∀ v, ψ ∈ DependentBondNetwork.cutSpace
      torusLabelledBondTail torusLabelledBondHead D A (cutBonds v) :=
  Submodule.mem_iInf _

/-- Every native bond is contracted internally by at least one of the four cuts. -/
theorem cutBonds_cover : ∀ e : Bond, ∃ v : Vertex, e ∉ cutBonds v :=
  fun e ↦ ⟨e.1, torusLabelledBond_not_mem_own_cut e⟩

variable {G : Type*} [Group G]

/-- Close each individual bond with its own representation of the source seam labels. -/
def closure
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) (g h : G) :
    ((v : Vertex) → Phys v) → ℂ :=
  DependentBondNetwork.network torusLabelledBondTail torusLabelledBondHead D A
    (fun e ↦ U e (torusLabelledClosure g h e))

/-- The span of actual closures with commuting seam labels. -/
def commutingClosureSpan
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) :
    Submodule ℂ (((v : Vertex) → Phys v) → ℂ) :=
  Submodule.span ℂ (Set.range fun p : {p : G × G // Commute p.1 p.2} ↦
    closure D U A p.1.1 p.1.2)

/-- Physical maps retain every independently sized bond's closure matrix. -/
theorem physicalMap_closure [∀ v, Fintype (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) (g h : G) :
    dependentPhysicalProductFamilyMap F (closure D U A g h) =
      closure D U (DependentBondNetwork.physicalMapSite
        torusLabelledBondTail torusLabelledBondHead D F A) g h :=
  DependentBondNetwork.physicalMap_network torusLabelledBondTail torusLabelledBondHead D F A _

/-- The entire actual closure span is transported by the physical product map. -/
theorem map_commutingClosureSpan [∀ v, Fintype (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) :
    (commutingClosureSpan D U A).map (dependentPhysicalProductFamilyMap F) =
      commutingClosureSpan D U (DependentBondNetwork.physicalMapSite
        torusLabelledBondTail torusLabelledBondHead D F A) := by
  simp only [commutingClosureSpan, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext p
  exact physicalMap_closure D U F A p.1.1 p.1.2

variable [Fintype G]

/-- A common local inverse transports all four actual ranges, with no common
virtual or physical alphabet assumption. -/
theorem fourCutSpace_eq_map_averagingSite [∀ v, Finite (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective
      (DependentBondNetwork.incidentRepresentation
        torusLabelledBondTail torusLabelledBondHead D U v)
      (DependentBondNetwork.localSiteMap torusLabelledBondTail torusLabelledBondHead D A v)) :
    fourCutSpace D A =
      (fourCutSpace D (DependentBondNetwork.averagingSite
        torusLabelledBondTail torusLabelledBondHead D U)).map
        (dependentPhysicalProductFamilyMap (fun v ↦ LinearMap.toMatrix'
          (DependentBondNetwork.localSiteMap
            torusLabelledBondTail torusLabelledBondHead D A v))) :=
  DependentBondNetwork.iInf_cutSpace_eq_map_representationAveragingSite
    torusLabelledBondTail torusLabelledBondHead D (0, 0) _ A hA cutBonds

/-- The same local recovery maps carry canonical commuting closures back to
the original independent physical tensors. -/
theorem map_commutingClosureSpan_recover
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v g, DependentBondNetwork.localSiteMap
      torusLabelledBondTail torusLabelledBondHead D A v ∘ₗ
        DependentBondNetwork.incidentRepresentation
          torusLabelledBondTail torusLabelledBondHead D U v g =
      DependentBondNetwork.localSiteMap torusLabelledBondTail torusLabelledBondHead D A v) :
    (commutingClosureSpan D U (DependentBondNetwork.averagingSite
      torusLabelledBondTail torusLabelledBondHead D U)).map
        (dependentPhysicalProductFamilyMap (fun v ↦ LinearMap.toMatrix'
          (DependentBondNetwork.localSiteMap
            torusLabelledBondTail torusLabelledBondHead D A v))) =
      commutingClosureSpan D U A := by
  rw [map_commutingClosureSpan]
  congr 1
  exact DependentBondNetwork.physicalMap_recover_representationAveragingSite
    torusLabelledBondTail torusLabelledBondHead D _ A hA

end TNLean.PEPS.DependentTorus
