/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
import TNLean.Lattice.RegionalEntropyBridge
import TNLean.Lattice.ZeroEntropy
import TNLean.Lattice.RegionEntropyInequalities

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
lemma `TNLean.Lattice.regionEntropy_eq_zero_of_forall_subset_or_disjoint`, read
on the domain through `regionalEntropy_eq_regionEntropy`.

The same argument covers the degenerate cases of Section 2: range `R = 0`
(every support is a single site, so no cut divides a support and
`H = H_A ⊗ 1 + 1 ⊗ H_{Aᶜ}` for every cut), the
empty and full regions, and every union of connected components of a
disconnected domain. For `q = 1` or an empty domain every regional entropy
vanishes for every unit vector.

## Main results

* `regionalEntropy_eq_zero_of_forall_subset_or_disjoint`: the cut does not
  split any support.
* `regionalEntropy_eq_zero_of_edgeBoundary_eq_empty`: Lemma 2.2.
* `regionalEntropy_eq_zero_of_range_eq_zero`: the range-zero case.
* `regionalEntropy_eq_zero_of_q_eq_one`, `regionalEntropy_eq_zero_of_domain_eq_empty`.
* `IsAdmissibleSupport.reachable`, `edgeBoundary_connectedComponent_eq_empty`:
  supports lie in one component, and components have no crossing edge.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 2, `build/sections/01-preliminaries.tex`,
  lines 116–134 (degenerate cases and Lemma 2.2).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped ComplexOrder Kronecker
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-! ### Walks, components and crossing edges -/

section Graph

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}

/-- Without crossing edges, adjacent sites are on the same side of the cut. -/
theorem mem_iff_of_adj_of_edgeBoundary_eq_empty (hA : edgeBoundary Λ A = ∅) {x y : Site Λ}
    (hxy : (domainGraph Λ).Adj x y) : x ∈ A ↔ y ∈ A := by
  classical
  have key : ∀ {a b : Site Λ}, (domainGraph Λ).Adj a b → a ∈ A → b ∉ A → False := by
    intro a b hab ha hb
    have hmem : s(a, b) ∈ edgeBoundary Λ A := by
      simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact ⟨hab, a, ha, b, hb, rfl⟩
    rw [hA] at hmem
    simp at hmem
  constructor
  · intro hx; by_contra hy; exact key hxy hx hy
  · intro hy; by_contra hx; exact key hxy.symm hy hx

/-- Without crossing edges, the two ends of a walk are on the same side of the
cut. -/
theorem mem_iff_of_walk_of_edgeBoundary_eq_empty (hA : edgeBoundary Λ A = ∅) {x y : Site Λ}
    (w : (domainGraph Λ).Walk x y) : x ∈ A ↔ y ∈ A := by
  induction w with
  | nil => rfl
  | cons h _ ih => exact (mem_iff_of_adj_of_edgeBoundary_eq_empty hA h).trans ih

/-- **A cut with no crossing edge splits no support.** Every admissible support
lies inside `A` or is disjoint from it. -/
theorem subset_or_disjoint_of_edgeBoundary_eq_empty (hA : edgeBoundary Λ A = ∅) {R : ℕ}
    (X : AdmissibleSupport Λ R) : X.1 ⊆ A ∨ Disjoint X.1 A := by
  obtain ⟨⟨x₀, hx₀⟩, hwalk⟩ := X.2
  by_cases h : x₀ ∈ A
  · left
    intro y hy
    obtain ⟨w, -⟩ := hwalk x₀ hx₀ y hy
    exact (mem_iff_of_walk_of_edgeBoundary_eq_empty hA w).mp h
  · right
    rw [Finset.disjoint_left]
    intro y hy hyA
    obtain ⟨w, -⟩ := hwalk x₀ hx₀ y hy
    exact h ((mem_iff_of_walk_of_edgeBoundary_eq_empty hA w).mpr hyA)

/-- **Every admissible support lies in one connected component.** -/
theorem _root_.TNLean.Lattice.IsAdmissibleSupport.reachable {R : ℕ} {X : Finset (Site Λ)}
    (hX : IsAdmissibleSupport Λ R X) {x y : Site Λ} (hx : x ∈ X) (hy : y ∈ X) :
    (domainGraph Λ).Reachable x y :=
  let ⟨w, _⟩ := hX.2 x hx y hy
  ⟨w⟩

open scoped Classical in
/-- **A union of connected components has no crossing edge.** For a set `s` of
components of the induced domain graph, the set of sites in components of `s`
has empty edge boundary. -/
theorem edgeBoundary_connectedComponents_eq_empty
    (s : Set (domainGraph Λ).ConnectedComponent) :
    edgeBoundary Λ (Finset.univ.filter fun x ↦ (domainGraph Λ).connectedComponentMk x ∈ s) =
      ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset, Finset.mem_univ,
    true_and] at he
  obtain ⟨hadj, x, hx, y, hy, rfl⟩ := he
  rw [SimpleGraph.mem_edgeSet] at hadj
  have hxy : (domainGraph Λ).connectedComponentMk x = (domainGraph Λ).connectedComponentMk y :=
    SimpleGraph.ConnectedComponent.eq.mpr ⟨SimpleGraph.Walk.cons hadj .nil⟩
  exact hy (hxy ▸ hx)

open scoped Classical in
/-- **A connected component has no crossing edge.** -/
theorem edgeBoundary_connectedComponent_eq_empty
    (c : (domainGraph Λ).ConnectedComponent) :
    edgeBoundary Λ (Finset.univ.filter fun x ↦ (domainGraph Λ).connectedComponentMk x = c) =
      ∅ := by
  simpa using edgeBoundary_connectedComponents_eq_empty (Λ := Λ) {c}

end Graph

/-! ### Lemma 2.2 -/

section ZeroBoundary

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- **Zero entropy for a cut that splits no support.** Under the gapped
ground-state hypothesis of Theorem 1.1, if every admissible support lies inside
`A` or is disjoint from it, then `S_Ω(A) = 0`. -/
theorem regionalEntropy_eq_zero_of_forall_subset_or_disjoint (h : LocalHamiltonian Λ q R J)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : IsGappedGroundState Λ q h.operator E₀ Ω Δ) (A : Finset (Site Λ))
    (hsplit : ∀ X : AdmissibleSupport Λ R, X.1 ⊆ A ∨ Disjoint X.1 A) :
    regionalEntropy Λ q Ω A = 0 := by
  rw [regionalEntropy_eq_regionEntropy]
  exact regionEntropy_eq_zero_of_forall_subset_or_disjoint
    (fun X ↦ QuantumCircuit.isSupportedOn_of_mem_supportedOperators (h.supported X))
    h.hermitian hΔ hΩ A hsplit

/-- **A cut with no crossing edge** (area-law preprint, Lemma 2.2,
`lem:zero-boundary`, `01-preliminaries.tex` lines 123–134). Under the
hypotheses of Theorem 1.1, if `∂_Λ A = ∅`, then `S_Ω(A) = 0`.

Only the gapped ground-state hypothesis with `Δ > 0` is used; the bound `J`,
the range `R` and the local dimension `q` are arbitrary. -/
theorem regionalEntropy_eq_zero_of_edgeBoundary_eq_empty (h : LocalHamiltonian Λ q R J)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : IsGappedGroundState Λ q h.operator E₀ Ω Δ) {A : Finset (Site Λ)}
    (hA : edgeBoundary Λ A = ∅) : regionalEntropy Λ q Ω A = 0 :=
  regionalEntropy_eq_zero_of_forall_subset_or_disjoint h hΔ hΩ A
    (subset_or_disjoint_of_edgeBoundary_eq_empty hA)

/-- **Range zero** (area-law preprint, `01-preliminaries.tex` lines 118–120). For
`R = 0` the Hamiltonian is a sum of on-site terms and every regional entropy of
the gapped ground vector vanishes. -/
theorem regionalEntropy_eq_zero_of_range_eq_zero (h : LocalHamiltonian Λ q 0 J)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : IsGappedGroundState Λ q h.operator E₀ Ω Δ) (A : Finset (Site Λ)) :
    regionalEntropy Λ q Ω A = 0 := by
  refine regionalEntropy_eq_zero_of_forall_subset_or_disjoint h hΔ hΩ A fun X ↦ ?_
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp ((isAdmissibleSupport_zero_iff Λ X.1).mp X.2)
  rw [hx]
  by_cases hxA : x ∈ A
  · exact Or.inl (Finset.singleton_subset_iff.mpr hxA)
  · exact Or.inr (Finset.disjoint_singleton_left.mpr hxA)

/-- The reduced state of a unit vector has unit trace. -/
theorem trace_reducedState (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ)) :
    (reducedState Λ q Ω A).trace = 1 := by
  rw [reducedState_eq_regionState]
  exact Entropy.trace_regionState_eq_one hΩ

/-- A regional entropy vanishes when the regional configuration space has at
most one element. -/
theorem regionalEntropy_eq_zero_of_card_le_one (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (hcard : Fintype.card ({x : Site Λ // x ∈ A} → Fin q) ≤ 1) :
    regionalEntropy Λ q Ω A = 0 := by
  classical
  exact vonNeumannEntropy_eq_zero_of_rank_le_one (reducedState_posSemidef Λ q Ω A)
    (trace_reducedState Ω hΩ A) ((rank_le_card_width _).trans hcard)

/-- **Local dimension one** (area-law preprint, `01-preliminaries.tex`,
line 116): for `q = 1` every regional entropy of every unit vector vanishes. -/
theorem regionalEntropy_eq_zero_of_q_eq_one {Ω : StateSpace Λ 1} (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) : regionalEntropy Λ 1 Ω A = 0 := by
  rw [regionalEntropy_eq_regionEntropy]
  exact TNLean.Lattice.regionEntropy_eq_zero_of_localDimension_one hΩ A

/-- **Empty domain** (area-law preprint, `01-preliminaries.tex`, line 116): on
the empty domain every regional entropy of every unit vector vanishes. -/
theorem regionalEntropy_eq_zero_of_domain_eq_empty {Ω : StateSpace ∅ q} (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site ∅)) : regionalEntropy ∅ q Ω A = 0 :=
  regionalEntropy_eq_zero_of_card_le_one Ω hΩ A (by
    rw [Fintype.card_fun]
    simp)

open scoped Classical in
/-- **Unions of connected components** (area-law preprint, proof of Lemma 2.2):
the regional entropy of the gapped ground vector vanishes on every union of
connected components of the induced domain graph, in particular on each
component of a disconnected domain. -/
theorem regionalEntropy_connectedComponents_eq_zero (h : LocalHamiltonian Λ q R J)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : IsGappedGroundState Λ q h.operator E₀ Ω Δ)
    (s : Set (domainGraph Λ).ConnectedComponent) :
    regionalEntropy Λ q Ω
      (Finset.univ.filter fun x ↦ (domainGraph Λ).connectedComponentMk x ∈ s) = 0 :=
  regionalEntropy_eq_zero_of_edgeBoundary_eq_empty h hΔ hΩ
    (edgeBoundary_connectedComponents_eq_empty s)

end ZeroBoundary

end TNLean.PEPS.AreaLaw
