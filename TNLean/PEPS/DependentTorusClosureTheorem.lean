/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentTorusCanonicalClosure
import TNLean.PEPS.DependentCutCoefficientSupport

/-!
# The four-block closure theorem with arbitrary bond and physical dimensions

For four independently chosen G-injective tensors, the intersection of the
four actual edge-cut boundary ranges is the span of their commuting native
closures. Every one of the eight bonds may have its own finite virtual
alphabet and its own matching semi-regular representation. Every physical
alphabet may also differ.

The proof first derives a coherent bond expansion from the genuine cut
conditions. Trace-dual extraction forces plaquette flatness coefficientwise.
Projecting its flat terms then gives commuting closures, and a common product
of actual local inverses transfers the equality to the original tensors.
No parent-kernel classification, G-isometry, or supplied spanning statement
is used.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Theorem 5.5,
`Papers/1001.3807/paper_v3.tex`, lines 1421–1513. Unitarity in the source's
semi-regular representation convention is unnecessary for this algebraic result.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.DependentTorus

local notation "tail" => (torusLabelledBondTail (width := 2) (height := 2))
local notation "head" => (torusLabelledBondHead (width := 2) (height := 2))

variable {G : Type*} [Group G] [Fintype G]
variable (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- Each nonflat coherent coefficient vanishes on the actual four-cut intersection,
with no equality assumptions on the dimensions of the eight bonds. -/
theorem coefficient_eq_zero_of_mem_fourCutSpace_not_flat
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p : Bond → G) (hp : ¬IsTorusBondFlat (torusLabelledBondPair p))
    {ψ : ((v : Vertex) → LocalConfig D v) → ℂ}
    (hψ : ψ ∈ fourCutSpace D (canonicalSites D U)) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U p ψ = 0 := by
  classical
  obtain ⟨v, hv⟩ := not_forall.mp hp
  by_contra hn
  obtain ⟨q, hq⟩ :=
    DependentBondNetwork.exists_vertexLabels_of_bondCoefficientExtraction_ne_zero
      tail head D U hU (cutBonds v) p ((mem_fourCutSpace_iff D _ _).mp hψ v) hn
  exact hv (torusPlaquette_flat_of_uncut_relative p q v.1 v.2 hq)

/-- All actual canonical four-cut vectors are sums of commuting closures:
bond support, coefficient extraction, and local averaging are all derived. -/
theorem fourCutSpace_canonical_le_commutingClosureSpan
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e))) :
    fourCutSpace D (canonicalSites D U) ≤ commutingClosureSpan D U (canonicalSites D U) := by
  classical
  intro ψ hψ
  have hcuts := (mem_fourCutSpace_iff D _ _).mp hψ
  obtain ⟨M, hM⟩ := hcuts (0, 0)
  have hfixed : canonicalProjector D U ψ = ψ := by
    rw [← hM]
    exact DependentBondNetwork.averagingProjector_cutMap tail head D _ _ M
  have hexpand := DependentBondNetwork.eq_sum_extracted_bondProducts_of_mem_cutSpaces
    tail head D U hU cutBonds cutBonds_cover hcuts
  rw [← hfixed, hexpand, map_sum]
  apply Submodule.sum_mem
  intro p _
  rw [map_smul]
  by_cases hp : IsTorusBondFlat (torusLabelledBondPair p)
  · exact Submodule.smul_mem _ _ (canonicalProjector_bondProduct_mem_closureSpan D U p hp)
  · rw [coefficient_eq_zero_of_mem_fourCutSpace_not_flat D U hU p hp hψ, zero_smul]
    exact Submodule.zero_mem _

/-- The actual canonical four-cut intersection equals the commuting closure span. -/
theorem fourCutSpace_canonical_eq_commutingClosureSpan
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e))) :
    fourCutSpace D (canonicalSites D U) = commutingClosureSpan D U (canonicalSites D U) :=
  le_antisymm (fourCutSpace_canonical_le_commutingClosureSpan D U hU)
    (commutingClosureSpan_le_fourCutSpace_canonical D U)

omit [Fintype G] in
/-- SCP10 Theorem 5.5: the four actual cut ranges of arbitrary G-injective
blocks intersect in precisely their commuting closure span. All eight bond
alphabets and all four physical alphabets may differ; each actual bond carries
its own matching semi-regular representation. The proof has no additional
geometric, isometric, parent-kernel, or spanning hypothesis. -/
theorem fourCutSpace_eq_commutingClosureSpan [Finite G]
    {Phys : Vertex → Type*} [∀ v, Finite (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (DependentBondNetwork.incidentRepresentation tail head D U v)
      (DependentBondNetwork.localSiteMap tail head D A v)) :
    fourCutSpace D A = commutingClosureSpan D U A := by
  let := Fintype.ofFinite G
  rw [fourCutSpace_eq_map_averagingSite D U A hA,
    fourCutSpace_canonical_eq_commutingClosureSpan D U hU,
    map_commutingClosureSpan_recover D U A (fun v ↦ (hA v).invariant)]

end TNLean.PEPS.DependentTorus
