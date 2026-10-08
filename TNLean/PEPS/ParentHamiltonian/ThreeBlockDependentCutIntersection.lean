/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentOpenCutIntersection
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Independently sized three-block open cut intersections

There are three four-legged core vertices, two internal bonds, and eight
separately labelled exterior bonds. Local group averages act only at the core;
the exterior endpoints carry trivial actions. Every edge has its own finite
virtual alphabet and every vertex its own physical alphabet. The two internal
labels can always be removed by a tree gauge, without any flatness hypothesis.

These cut ranges apply the chosen local tensors at every vertex. The separate
lifted-region statement additionally leaves the omitted core physical factor
unrestricted, as required in SCP10, Theorem 5.4.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.ThreeBlockDependent
open DependentBondNetwork

/-- Three core vertices followed by eight distinct exterior endpoints. -/
abbrev Vertex := Fin 11

/-- Two internal bonds followed by eight independently sized exterior bonds. -/
abbrev Bond := Fin 10

/-- Directed tails in the three-four-leg source geometry. -/
def tail : Bond → Vertex := ![0, 1, 0, 0, 0, 1, 1, 2, 2, 2]

/-- Directed heads; the exterior endpoints are pairwise distinct. -/
def head : Bond → Vertex := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- The eight uncontracted exterior bonds of the whole three-block region. -/
def exteriorBonds : Finset Bond := Finset.univ \ {0, 1}

/-- The left two-core contraction leaves only the first internal bond uncut. -/
def leftCut : Finset Bond := Finset.univ \ {0}

/-- The right two-core contraction leaves only the second internal bond uncut. -/
def rightCut : Finset Bond := Finset.univ \ {1}

/-- The core consists of precisely the three physical tensors of the source picture. -/
def coreVertices : Finset Vertex := {0, 1, 2}

/-- All three core tensors have four independent virtual incidences. -/
theorem core_degree (v : Vertex) (hv : v ∈ coreVertices) :
    Fintype.card (IncidentEndpoint tail head v) = 4 := by
  revert v
  decide

/-- The union retains eight distinct exterior bonds. -/
theorem exteriorBonds_card : exteriorBonds.card = 8 := by decide

variable {G : Type*} [Group G]

/-- Core vertices carry the group action; exterior endpoints have trivial action. -/
def coreAction (v : Vertex) : G →* G :=
  if v ∈ coreVertices then MonoidHom.id G else 1

/-- The two independent internal group labels can always be removed on the path. -/
theorem exists_remove_internal_labels (p : Bond → G) :
    ∃ q : Vertex → G, ∀ e, e ∉ exteriorBonds →
      coreAction (head e) (q (head e)) * p e *
        (coreAction (tail e) (q (tail e)))⁻¹ = 1 := by
  refine ⟨![1, (p 0)⁻¹, (p 0)⁻¹ * (p 1)⁻¹, 1, 1, 1, 1, 1, 1, 1, 1], ?_⟩
  intro e he
  have he' : e = 0 ∨ e = 1 := by
    have h : ¬e = 0 → e = 1 := by simpa [exteriorBonds] using he
    exact or_iff_not_imp_left.mpr h
  rcases he' with rfl | rfl <;> simp [coreAction, coreVertices, tail, head, mul_assoc]

variable (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

/-- Every local virtual alphabet keeps the four incident edge dimensions independent. -/
abbrev LocalConfig (v : Vertex) := DependentBondNetwork.LocalConfig tail head D v

/-- The actual local group action, trivial only at exterior endpoints. -/
abbrev localRepresentation
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ) (v : Vertex) :=
  partialIncidentRepresentation tail head D U coreAction v

/-- The all-site cut intersection equals the eight-exterior-leg cut range for
arbitrary G-injective tensors and independently sized matched edge actions.
No semi-regularity or unitarity assumption is needed for this tree identity. -/
theorem cutSpace_left_inf_right [Finite G] [∀ v, Finite (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (localRepresentation D U v)
      (localSiteMap tail head D A v)) :
    cutSpace tail head D A leftCut ⊓ cutSpace tail head D A rightCut =
      cutSpace tail head D A exteriorBonds := by
  have hsub : ∀ b : Bool, exteriorBonds ⊆ if b then rightCut else leftCut := by
    intro b
    cases b <;> decide
  have hcover : ∀ e, e ∉ exteriorBonds →
      ∃ b : Bool, e ∉ (if b then rightCut else leftCut) := by
    decide
  have h := iInf_cutSpace_eq_of_remove_labels tail head D U coreAction A hA
    exteriorBonds false (fun b : Bool ↦ if b then rightCut else leftCut)
    hsub hcover exists_remove_internal_labels
  simpa only [iInf_bool_eq, Bool.false_eq_true, ↓reduceIte, inf_comm] using h

end TNLean.PEPS.ThreeBlockDependent
