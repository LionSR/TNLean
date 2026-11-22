/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Defs
import TNLean.Lattice.FiniteDomain
import QICLean.ManyBody.Entropy.SupportedMarginalTails

/-!
# Exact nearest-neighbor crossing budgets

An unordered edge crossing a cut has exactly one endpoint inside. Its inside
configuration space therefore has dimension q, and its squared dimension is q².
On-site terms do not cross. The generic crossing sum is exactly the unordered
boundary cardinality times q² J. No Hamiltonian or energy conclusion is assumed.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
`03-patches.tex`, lines 302–336, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

open ManyBody (Edge)

open scoped BigOperators
open TNLean.Lattice

open ManyBody (planeDomainGraph edgeBoundary)

namespace TNLean.PEPS.AreaLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- An on-site designated support never meets both sides of a cut. -/
theorem not_mem_crossingTerms_singleton (A : Finset V) (v : V) :
    v ∉ ManyBody.crossingTerms (fun w : V ↦ {w}) A := by
  classical
  simp [ManyBody.crossingTerms]

omit [Fintype V] in
/-- The inside portion of a crossing two-site support is a singleton. -/
theorem pair_inter_eq_singleton_of_crossing {x y : V} {A : Finset V}
    (h : (∃ v ∈ ({x, y} : Finset V), v ∈ A) ∧
      ∃ v ∈ ({x, y} : Finset V), v ∉ A) :
    ∃ v, ({x, y} : Finset V) ∩ A = {v} := by
  classical
  by_cases hx : x ∈ A
  · have hy : y ∉ A := by simpa [hx] using h.2
    exact ⟨x, by ext v; simp [hy, hx]⟩
  · have hy : y ∈ A := by simpa [hx] using h.1
    exact ⟨y, by ext v; simp [hy, hx]⟩

omit [Fintype V] in
/-- Only the inside endpoint contributes to the configuration dimension. -/
theorem card_pair_insideConfig_of_crossing (q : ℕ) {x y : V} {A : Finset V}
    (h : (∃ v ∈ ({x, y} : Finset V), v ∈ A) ∧
      ∃ v ∈ ({x, y} : Finset V), v ∉ A) :
    Fintype.card (↥(({x, y} : Finset V) ∩ A) → Fin q) = q := by
  obtain ⟨v, hv⟩ := pair_inter_eq_singleton_of_crossing h
  simp [hv]

variable {Λ : Finset (ℤ × ℤ)} [siteOrder : LinearOrder (Site Λ)]

/-- The physical on-site and nearest-neighbor supports, with each edge counted once. -/
noncomputable def nearestNeighborSupport :
    Site Λ ⊕ Edge (planeDomainGraph Λ) → Finset (Site Λ) := by
  classical
  exact Sum.elim (fun v ↦ {v}) (fun e ↦ {e.1.1, e.1.2})

/-- The combined interaction list has no crossing on-site terms. -/
theorem inl_not_mem_crossingTerms (A : Finset (Site Λ))
    (v : Site Λ) : Sum.inl v ∉ ManyBody.crossingTerms nearestNeighborSupport A := by
  classical
  intro h
  have h' := h
  simp only [ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at h'
  change (∃ w ∈ ({v} : Finset (Site Λ)), w ∈ A) ∧
    (∃ w ∈ ({v} : Finset (Site Λ)), w ∉ A) at h'
  simp only [Finset.mem_singleton, exists_eq_left, and_not_self] at h'

/-- Crossing of the edge support is precisely membership in the unordered boundary. -/
theorem inr_mem_crossingTerms_iff (A : Finset (Site Λ))
    (e : Edge (planeDomainGraph Λ)) :
    Sum.inr e ∈ ManyBody.crossingTerms nearestNeighborSupport A ↔
      s(e.1.1, e.1.2) ∈ edgeBoundary (planeDomainGraph Λ) A := by
  classical
  constructor
  · intro h
    have h' := h
    simp only [ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at h'
    change (∃ v ∈ ({e.1.1, e.1.2} : Finset (Site Λ)), v ∈ A) ∧
      (∃ v ∈ ({e.1.1, e.1.2} : Finset (Site Λ)), v ∉ A) at h'
    obtain ⟨⟨x, hx, hxA⟩, y, hy, hyA⟩ := h'
    rw [ManyBody.mk_mem_edgeBoundary_iff]
    refine ⟨e.2.2, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | exact absurd hxA hyA | exact Or.inl ⟨hxA, hyA⟩ | exact Or.inr ⟨hxA, hyA⟩
  · intro h
    obtain ⟨x, hxA, y, hyA, hxy⟩ := (ManyBody.mem_edgeBoundary.mp h).2
    simp only [ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]
    change (∃ v ∈ ({e.1.1, e.1.2} : Finset (Site Λ)), v ∈ A) ∧
      (∃ v ∈ ({e.1.1, e.1.2} : Finset (Site Λ)), v ∉ A)
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨⟨_, by simp, hxA⟩, _, by simp, hyA⟩

/-- Every crossing term has one inside site, including in the presence of on-site terms. -/
theorem card_nearestNeighbor_insideConfig (q : ℕ)
    (A : Finset (Site Λ)) {i : Site Λ ⊕ Edge (planeDomainGraph Λ)}
    (hi : i ∈ ManyBody.crossingTerms nearestNeighborSupport A) :
    Fintype.card (↥(nearestNeighborSupport i ∩ A) → Fin q) = q := by
  classical
  cases i with
  | inl v => exact False.elim (inl_not_mem_crossingTerms A v hi)
  | inr e =>
    apply card_pair_insideConfig_of_crossing
    simp only [ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi

/-- Forgetting the canonical endpoint order counts each unordered boundary edge once. -/
theorem card_crossingTerms_nearestNeighbor
    (A : Finset (Site Λ)) :
    (ManyBody.crossingTerms nearestNeighborSupport A).card =
      (edgeBoundary (planeDomainGraph Λ) A).card := by
  classical
  let f : Site Λ ⊕ Edge (planeDomainGraph Λ) → Sym2 (Site Λ) :=
    Sum.elim (fun v ↦ s(v, v)) (fun e ↦ s(e.1.1, e.1.2))
  apply Finset.card_bij (fun i _ ↦ f i)
  · intro i hi
    cases i with
    | inl v => exact False.elim (inl_not_mem_crossingTerms A v hi)
    | inr e => exact (inr_mem_crossingTerms_iff A e).mp hi
  · intro i hi k hk hik
    cases i with
    | inl v => exact False.elim (inl_not_mem_crossingTerms A v hi)
    | inr e =>
      cases k with
      | inl v => exact False.elim (inl_not_mem_crossingTerms A v hk)
      | inr d =>
        congr 1
        apply Subtype.ext
        have h := Sym2.eq_iff.mp hik
        rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Prod.ext h₁ h₂
        · have he := e.2.1
          rw [h₁, h₂] at he
          exact False.elim (@lt_asymm (Site Λ) siteOrder.toPreorder _ _ d.2.1 he)
  · intro b hb
    obtain ⟨x, y⟩ := b
    have hxy : (planeDomainGraph Λ).Adj x y :=
      (ManyBody.mem_edgeBoundary.mp hb).1
    let e := ManyBody.Edge.ofAdj hxy
    have he : s(e.1.1, e.1.2) = s(x, y) := by
      rcases ManyBody.Edge.ofAdj_endpoints hxy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact congrArg₂ (fun x y ↦ s(x, y)) h₁ h₂
      · exact (congrArg₂ (fun x y ↦ s(x, y)) h₁ h₂).trans Sym2.eq_swap
    exact ⟨Sum.inr e, (inr_mem_crossingTerms_iff A e).mpr (he.symm ▸ hb), he⟩

/-- The exact generic crossing budget for on-site and nearest-neighbor terms. -/
theorem nearestNeighbor_crossing_budget (q : ℕ) (J : ℝ)
    {m : ℕ} (regions : Fin m → Finset (Site Λ)) (a : Fin m → ℝ) :
    (∑ j : Fin m, a j ^ 2 * ∑ i ∈ ManyBody.crossingTerms nearestNeighborSupport (regions j),
      (Fintype.card (↥(nearestNeighborSupport i ∩ regions j) → Fin q) : ℝ) ^ 2 * J) =
      (q : ℝ) ^ 2 * J * ∑ j : Fin m, a j ^ 2 *
        (edgeBoundary (planeDomainGraph Λ) (regions j)).card := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hsum :
      (∑ i ∈ ManyBody.crossingTerms nearestNeighborSupport (regions j),
        (Fintype.card (↥(nearestNeighborSupport i ∩ regions j) → Fin q) : ℝ) ^ 2 * J) =
      ∑ _i ∈ ManyBody.crossingTerms nearestNeighborSupport (regions j), (q : ℝ) ^ 2 * J := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [card_nearestNeighbor_insideConfig q _ hi]
  rw [hsum]
  simp only [Finset.sum_const, nsmul_eq_mul, card_crossingTerms_nearestNeighbor]
  ring

end TNLean.PEPS.AreaLaw
