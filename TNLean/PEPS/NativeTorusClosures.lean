/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphDependentCutCoordinates
import TNLean.PEPS.DependentBondLocalInverse
import TNLean.PEPS.RegularTorusCut

/-!
# Native torus closures with independently sized bonds and sites

Every ordered edge of the actual torus graph retains its own virtual alphabet
and representation. Every vertex retains its own physical alphabet and tensor.
The source closure convention puts the inverse horizontal element on the
ordered horizontal seam and the vertical element on the ordered vertical seam.

Source: SCP10, arXiv:1001.3807, Theorems 5.7 and 5.9. Both periods are at least
three so that the four virtual legs are distinct edges of the native graph.
-/

noncomputable section
namespace TNLean.PEPS.NativeTorus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

local notation "Vertex" => TorusVertex width height
local notation "Bond" => Edge (torusGraph width height)
local notation "tail" => (graphEdgeTail (Γ := torusGraph width height))
local notation "head" => (graphEdgeHead (Γ := torusGraph width height))

/-- The actual incident virtual coordinates, with each bond's own alphabet. -/
abbrev LocalConfig (D : Bond → Type*) (v : Vertex) :=
  DependentBondNetwork.LocalConfig tail head D v

variable (D : Edge (torusGraph width height) → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys Out : TorusVertex width height → Type*}
variable {G : Type*} [Group G]

/-- Contract the actual native torus with the source's two closure seams. -/
def closure
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) (g h : G) :
    ((v : Vertex) → Phys v) → ℂ :=
  DependentBondNetwork.network tail head D A
    (fun e ↦ U e (torusClosureEdgeAssignment g h e))

/-- The span of actual closures with commuting seam labels. -/
def commutingClosureSpan
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) :
    Submodule ℂ (((v : Vertex) → Phys v) → ℂ) :=
  Submodule.span ℂ (Set.range fun p : {p : G × G // Commute p.1 p.2} ↦
    closure D U A p.1.1 p.1.2)

/-- Physical maps retain every independently sized native bond's closure matrix. -/
theorem physicalMap_closure [∀ v, Fintype (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) (g h : G) :
    dependentPhysicalProductFamilyMap F (closure D U A g h) =
      closure D U (DependentBondNetwork.physicalMapSite tail head D F A) g h :=
  DependentBondNetwork.physicalMap_network tail head D F A _

/-- The closure span is transported by the actual product of physical maps. -/
theorem map_commutingClosureSpan [∀ v, Fintype (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (F : (v : Vertex) → Matrix (Out v) (Phys v) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ) :
    (commutingClosureSpan D U A).map (dependentPhysicalProductFamilyMap F) =
      commutingClosureSpan D U (DependentBondNetwork.physicalMapSite tail head D F A) := by
  simp only [commutingClosureSpan, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext p
  exact physicalMap_closure D U F A p.1.1 p.1.2

variable [Fintype G]

/-- The actual local invariant-projector family for all native torus bonds. -/
abbrev canonicalSites (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ) :=
  DependentBondNetwork.averagingSite tail head D U

/-- The product of all native local invariant projectors. -/
abbrev canonicalProjector (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ) :=
  DependentBondNetwork.averagingProjector tail head D
    (DependentBondNetwork.incidentRepresentation tail head D U)

/-- The product of the original invariant site maps recovers the actual
commuting closure span from the canonical projector tensors. -/
theorem map_commutingClosureSpan_recover
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v g, DependentBondNetwork.localSiteMap tail head D A v ∘ₗ
      DependentBondNetwork.incidentRepresentation tail head D U v g =
        DependentBondNetwork.localSiteMap tail head D A v) :
    (commutingClosureSpan D U (canonicalSites D U)).map
      (dependentPhysicalProductFamilyMap (fun v ↦ LinearMap.toMatrix'
        (DependentBondNetwork.localSiteMap tail head D A v))) = commutingClosureSpan D U A := by
  rw [map_commutingClosureSpan]
  rw [show DependentBondNetwork.physicalMapSite tail head D
      (fun v ↦ LinearMap.toMatrix' (DependentBondNetwork.localSiteMap tail head D A v))
      (canonicalSites D U) = A from
    DependentBondNetwork.physicalMap_recover_representationAveragingSite tail head D _ A hA]

end TNLean.PEPS.NativeTorus
