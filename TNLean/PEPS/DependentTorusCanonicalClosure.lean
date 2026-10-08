/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentTorusCutSpaces
import TNLean.PEPS.DependentBondCoefficients

/-!
# Canonical closures with arbitrary bond dimensions

Commuting closure matrices provide actual boundary witnesses on every one of
the four cuts, after a pure group-valued seam change. Conversely, the product
of the local invariant projectors sends every flat bare bond product to an
actual commuting closure. Both constructions preserve each edge's own virtual
alphabet and each site's actual incidence coordinates.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.DependentTorus

local notation "tail" => (torusLabelledBondTail (width := 2) (height := 2))
local notation "head" => (torusLabelledBondHead (width := 2) (height := 2))

variable {G : Type*} [Group G] [Fintype G]
variable (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- The actual canonical tensor family with separately sized virtual edges. -/
abbrev canonicalSites (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ) :=
  DependentBondNetwork.averagingSite tail head D U

/-- The product of the four canonical local invariant projectors. -/
abbrev canonicalProjector (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ) :=
  DependentBondNetwork.averagingProjector tail head D
    (DependentBondNetwork.incidentRepresentation tail head D U)

/-- A commuting native closure has an explicit boundary tensor on any of the
four cuts, with each cut bond's own representation matrix. -/
theorem canonicalClosure_mem_cutSpace
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (g h : G) (hgh : Commute g h) (v : Vertex) :
    closure D U (canonicalSites D U) g h ∈
      DependentBondNetwork.cutSpace tail head D (canonicalSites D U) (cutBonds v) := by
  let B : (e : Bond) → Matrix (D e) (D e) ℂ :=
    fun e ↦ U e (torusLabelledClosureAt g h v.1 v.2 e)
  refine ⟨DependentBondNetwork.cutBondBoundary D (cutBonds v) B, ?_⟩
  funext σ
  rw [DependentBondNetwork.cutMap_apply, DependentBondNetwork.cutCoeff_bondBoundary]
  have hB : (fun e ↦ if e ∈ cutBonds v then B e else 1) = B := by
    funext e
    by_cases he : e ∈ cutBonds v
    · simp [he]
    · simp only [he, ↓reduceIte, B,
        torusLabelledClosureAt_eq_one_of_not_mem g h v.1 v.2 e he, map_one]
  rw [hB]
  obtain ⟨q, hq⟩ := exists_torusLabelledClosureGauge g h hgh v.1 v.2
  have hnet := DependentBondNetwork.network_averagingSite_vertexGauge tail head D U
    (torusLabelledClosure g h) q σ
  simp_rw [hq] at hnet
  exact hnet

/-- The actual commuting closure span is contained in all four canonical cut ranges. -/
theorem commutingClosureSpan_le_fourCutSpace_canonical
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ) :
    commutingClosureSpan D U (canonicalSites D U) ≤ fourCutSpace D (canonicalSites D U) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact (mem_fourCutSpace_iff D _ _).mpr fun v ↦
    canonicalClosure_mem_cutSpace D U p.1.1 p.1.2 p.2 v

/-- Canonical averaging turns a bare bond product into the actual network with
those same independently represented group labels. -/
theorem canonicalProjector_bondProduct
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ) (p : Bond → G) :
    canonicalProjector D U (DependentBondNetwork.representationBondProduct tail head D U p) =
      DependentBondNetwork.network tail head D (canonicalSites D U) (fun e ↦ U e (p e)) := by
  have hbare : DependentBondNetwork.representationBondProduct tail head D U p =
      DependentBondNetwork.network tail head D (DependentBondNetwork.identitySite tail head D)
        (fun e ↦ U e (p e)) := by
    funext σ
    rw [DependentBondNetwork.network_identitySite]
    rfl
  rw [hbare]
  exact DependentBondNetwork.averagingProjector_network_identitySite tail head D _ _

/-- Every projected flat bond product is an actual commuting closure, with
no restriction on the dimensions of individual virtual edges. -/
theorem exists_canonicalProjector_bondProduct_eq_closure
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (p : Bond → G) (hp : IsTorusBondFlat (torusLabelledBondPair p)) :
    ∃ g h : G, Commute g h ∧
      canonicalProjector D U (DependentBondNetwork.representationBondProduct tail head D U p) =
        closure D U (canonicalSites D U) g h := by
  obtain ⟨q, g, h, hgh, hq⟩ := exists_torusLabelledBondGauge_eq_closure p hp
  refine ⟨g, h, hgh, ?_⟩
  rw [canonicalProjector_bondProduct]
  funext σ
  have hnet := DependentBondNetwork.network_averagingSite_vertexGauge tail head D U p q σ
  simp_rw [hq] at hnet
  exact hnet.symm

/-- Projected flat bond products lie in the source's actual commuting closure span. -/
theorem canonicalProjector_bondProduct_mem_closureSpan
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (p : Bond → G) (hp : IsTorusBondFlat (torusLabelledBondPair p)) :
    canonicalProjector D U (DependentBondNetwork.representationBondProduct tail head D U p) ∈
      commutingClosureSpan D U (canonicalSites D U) := by
  obtain ⟨g, h, hgh, heq⟩ := exists_canonicalProjector_bondProduct_eq_closure D U p hp
  rw [heq]
  apply Submodule.subset_span
  exact ⟨⟨(g, h), hgh⟩, rfl⟩

end TNLean.PEPS.DependentTorus
