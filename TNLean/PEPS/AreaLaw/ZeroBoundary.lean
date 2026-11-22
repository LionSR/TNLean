/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
import TNLean.Lattice.MarginalTails
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import QICLean.ManyBody.Entropy.ZeroEntropy
import TNLean.Lattice.RegionEntropyInequalities
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# A cut with no crossing edge

Lemma 2.2 (`lem:zero-boundary`) of the area-law preprint: under the hypotheses of
Theorem 1.1, if no edge of the induced domain graph crosses the cut `A | Aᶜ`,
then the regional entropy `S_Ω(A)` vanishes.

A walk inside the domain cannot leave `A` without crossing an edge of `∂_Λ A`.
Every admissible support is joined by such walks, so it lies in one connected
component and in particular inside `A` or inside `Aᶜ`. In the split
coordinates the Hamiltonian is therefore `H_A ⊗ 1 + 1 ⊗ H_{Aᶜ}`, and the
gapped ground vector is a product vector across the cut, whose reduced state has
zero entropy. This last step holds on any finite set of sites and is the shared
lemma `ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint`.

The same argument covers the degenerate cases of Section 2: range `R = 0`
(every support is a single site, so no cut divides a support and
`H = H_A ⊗ 1 + 1 ⊗ H_{Aᶜ}` for every cut), the
empty and full regions, and every union of connected components of a
disconnected domain. For `q = 1` or an empty domain every regional entropy
vanishes for every unit vector.

## Main results

* `regionEntropy_eq_zero_of_forall_subset_or_disjoint`: the cut does not
  split any support.
* `regionEntropy_eq_zero_of_edgeBoundary_eq_empty`: Lemma 2.2.
* `regionEntropy_eq_zero_of_range_eq_zero`: the range-zero case.
* `regionEntropy_eq_zero_of_q_eq_one`, `regionEntropy_eq_zero_of_domain_eq_empty`.
* `edgeBoundary_connectedComponent_eq_empty`: a component has no crossing edge.

The graph facts are QICLean's: `ManyBody.subset_or_disjoint_of_edgeBoundary_eq_empty` (a region
without crossing edges splits no set of mutually reachable sites),
`ManyBody.edgeBoundary_filter_connectedComponentMk_mem` (unions of components have no crossing
edge) and `ManyBody.IsAdmissibleSupport.reachable` (supports lie in one component).

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 2, `build/sections/01-preliminaries.tex`,
  lines 116–134 (degenerate cases and Lemma 2.2).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix

open ManyBody (IsGapped groundSpace PlaneInteraction)
open scoped ComplexOrder Kronecker
open TNLean.Lattice

open ManyBody (AdmissibleSupport IsAdmissibleSupport isAdmissibleSupport_zero_iff planeDomainGraph)

open ManyBody (edgeBoundary)

namespace TNLean.PEPS.AreaLaw

/-! ### Walks, components and crossing edges -/

section Graph

variable {Λ : Finset (ℤ × ℤ)}

open scoped Classical in
/-- **A connected component has no crossing edge.** -/
theorem edgeBoundary_connectedComponent_eq_empty
    (c : (planeDomainGraph Λ).ConnectedComponent) :
    edgeBoundary (planeDomainGraph Λ)
        (Finset.univ.filter fun x ↦ (planeDomainGraph Λ).connectedComponentMk x = c) = ∅ := by
  simpa using ManyBody.edgeBoundary_filter_connectedComponentMk_mem (G := planeDomainGraph Λ) {c}

end Graph

/-! ### Lemma 2.2 -/

section ZeroBoundary

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- **Zero entropy for a cut that splits no support.** Under the gapped
ground-state hypothesis of Theorem 1.1, if every admissible support lies inside
`A` or is disjoint from it, then `S_Ω(A) = 0`. -/
theorem regionEntropy_eq_zero_of_forall_subset_or_disjoint (h : PlaneInteraction Λ q R)
    (hh : ∀ X, (h.term X).IsHermitian)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (Site Λ))
    (hsplit : ∀ X : AdmissibleSupport Λ R, X.1 ⊆ A ∨ Disjoint X.1 A) :
    ManyBody.regionEntropy Ω A = 0 := by
  exact ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint (Φ := h) hh hΔ hΩ hgap
    hspan (B := A) hsplit

/-- **A cut with no crossing edge** (area-law preprint, Lemma 2.2,
`lem:zero-boundary`, `01-preliminaries.tex` lines 123–134). Under the
hypotheses of Theorem 1.1, if `∂_Λ A = ∅`, then `S_Ω(A) = 0`.

Only the gapped ground-state hypothesis with `Δ > 0` is used; the bound `J`,
the range `R` and the local dimension `q` are arbitrary. -/
theorem regionEntropy_eq_zero_of_edgeBoundary_eq_empty (h : PlaneInteraction Λ q R)
    (hh : ∀ X, (h.term X).IsHermitian)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) {A : Finset (Site Λ)}
    (hA : edgeBoundary (planeDomainGraph Λ) A = ∅) : ManyBody.regionEntropy Ω A = 0 :=
  regionEntropy_eq_zero_of_forall_subset_or_disjoint h hh hΔ hΩ hgap hspan A fun X ↦
    ManyBody.subset_or_disjoint_of_edgeBoundary_eq_empty hA fun _ hx _ hy ↦ X.2.reachable hx hy

/-- **Range zero** (area-law preprint, `01-preliminaries.tex` lines 118–120). For
`R = 0` the Hamiltonian is a sum of on-site terms and every regional entropy of
the gapped ground vector vanishes. -/
theorem regionEntropy_eq_zero_of_range_eq_zero (h : PlaneInteraction Λ q 0)
    (hh : ∀ X, (h.term X).IsHermitian)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (Site Λ)) :
    ManyBody.regionEntropy Ω A = 0 := by
  refine regionEntropy_eq_zero_of_forall_subset_or_disjoint h hh hΔ hΩ hgap hspan A fun X ↦ ?_
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp ((isAdmissibleSupport_zero_iff Λ X.1).mp X.2)
  rw [hx]
  by_cases hxA : x ∈ A
  · exact Or.inl (Finset.singleton_subset_iff.mpr hxA)
  · exact Or.inr (Finset.disjoint_singleton_left.mpr hxA)

/-- A regional entropy vanishes when the regional configuration space has at
most one element. -/
theorem regionEntropy_eq_zero_of_card_le_one (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (hcard : Fintype.card ({x : Site Λ // x ∈ A} → Fin q) ≤ 1) :
    ManyBody.regionEntropy Ω A = 0 := by
  classical
  exact vonNeumannEntropy_eq_zero_of_rank_le_one (ManyBody.regionState_posSemidef A Ω)
    (ManyBody.trace_regionState_eq_one hΩ (D := A)) ((rank_le_card_width _).trans hcard)

/-- **Local dimension one** (area-law preprint, `01-preliminaries.tex`,
line 116): for `q = 1` every regional entropy of every unit vector vanishes. -/
theorem regionEntropy_eq_zero_of_q_eq_one {Ω : StateSpace Λ 1} (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) : ManyBody.regionEntropy Ω A = 0 := by
  exact TNLean.Lattice.regionEntropy_eq_zero_of_localDimension_one hΩ A

/-- **Empty domain** (area-law preprint, `01-preliminaries.tex`, line 116): on
the empty domain every regional entropy of every unit vector vanishes. -/
theorem regionEntropy_eq_zero_of_domain_eq_empty {Ω : StateSpace ∅ q} (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site ∅)) : ManyBody.regionEntropy Ω A = 0 :=
  regionEntropy_eq_zero_of_card_le_one Ω hΩ A (by
    rw [Fintype.card_fun]
    simp)

open scoped Classical in
/-- **Unions of connected components** (area-law preprint, proof of Lemma 2.2):
the regional entropy of the gapped ground vector vanishes on every union of
connected components of the induced domain graph, in particular on each
component of a disconnected domain. -/
theorem regionEntropy_connectedComponents_eq_zero (h : PlaneInteraction Λ q R)
    (hh : ∀ X, (h.term X).IsHermitian)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (s : Set (planeDomainGraph Λ).ConnectedComponent) :
    ManyBody.regionEntropy Ω
      (Finset.univ.filter fun x ↦ (planeDomainGraph Λ).connectedComponentMk x ∈ s) = 0 :=
  regionEntropy_eq_zero_of_edgeBoundary_eq_empty h hh hΔ hΩ hgap hspan
    (ManyBody.edgeBoundary_filter_connectedComponentMk_mem s)

end ZeroBoundary

end TNLean.PEPS.AreaLaw
