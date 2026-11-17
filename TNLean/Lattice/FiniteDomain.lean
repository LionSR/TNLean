/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Plane
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite induced square-lattice domains

A domain is an arbitrary finite subset of the integer lattice. Interaction
range is measured by walks that remain in the domain. Ambient coordinate
neighborhoods, used in the geometric argument, are defined separately.
Neither connectedness nor the absence of holes is assumed. The induced nearest-neighbor graph
`ManyBody.planeDomainGraph` and the admissible supports `ManyBody.IsAdmissibleSupport` are
QICLean's.

## Main definitions

* `Site`: the sites of a finite domain.
* `edgeBoundary`: the unordered edges crossing a cut, each counted once.
* `ambientDilation`: the integer sup-norm dilation of an ambient finite set.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1, `eq:hamiltonian`, and Section 2.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (planeDomainGraph)

namespace TNLean.Lattice

/-- Sites of a finite induced domain. Source: area-law Theorem 1.1. -/
abbrev Site (Λ : Finset (ℤ × ℤ)) := ↥Λ

/-- Configurations of a domain with local dimension `q`.
Source: area-law Section 1, the tensor product of the site spaces. -/
abbrev Configuration (Λ : Finset (ℤ × ℤ)) (q : ℕ) := Site Λ → Fin q

/-- Closed graph neighborhood of a region, measured by walks in the induced
finite domain. Source: area-law Section 2, induced-graph distance conventions. -/
noncomputable def graphNeighborhood (Λ : Finset (ℤ × ℤ)) (R : ℕ)
    (X : Finset (Site Λ)) : Finset (Site Λ) := by
  classical
  exact Finset.univ.filter fun y ↦ ∃ x ∈ X, ∃ p : (planeDomainGraph Λ).Walk x y, p.length ≤ R

/-- Unordered edges with one endpoint in `A` and the other outside `A`.
Source: area-law Section 1, definition of `∂Λ A`. -/
noncomputable def edgeBoundary (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    Finset (Sym2 (Site Λ)) := by
  classical
  exact (planeDomainGraph Λ).edgeFinset.filter fun e ↦
    ∃ x ∈ A, ∃ y ∉ A, e = s(x, y)

/-- Integer sup-norm dilation of an ambient finite set, independent of walks
in a domain. Source: area-law Definition 9.3 and the sets `T_j`. -/
def ambientDilation (T : Finset (ℤ × ℤ)) (r : ℕ) : Finset (ℤ × ℤ) :=
  T.biUnion fun x ↦
    (Finset.Icc (x.1 - (r : ℤ)) (x.1 + r)).product
      (Finset.Icc (x.2 - (r : ℤ)) (x.2 + r))

/-- Membership in an ambient integer dilation, in coordinate inequalities. -/
theorem mem_ambientDilation_iff {S : Finset (ℤ × ℤ)} {r : ℕ} {x : ℤ × ℤ} :
    x ∈ ambientDilation S r ↔ ∃ p ∈ S,
      p.1 - r ≤ x.1 ∧ x.1 ≤ p.1 + r ∧ p.2 - r ≤ x.2 ∧ x.2 ≤ p.2 + r := by
  simp only [ambientDilation, Finset.mem_biUnion, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  tauto

/-- Configuration decomposition into a region and its complement. This is
Mathlib's finite product decomposition, with no ordering of the sites chosen.
Source: area-law Section 1, the regional tensor factors. -/
def configurationSplit (Λ : Finset (ℤ × ℤ)) (q : ℕ) (A : Finset (Site Λ)) :
    Configuration Λ q ≃
      ({x : Site Λ // x ∈ A} → Fin q) × ({x : Site Λ // x ∉ A} → Fin q) :=
  Equiv.piEquivPiSubtypeProd (· ∈ A) (fun _ ↦ Fin q)

/-- The number of configurations is exactly the tensor-product dimension.
Source: area-law Section 1, the site Hilbert spaces. -/
@[simp] theorem card_configuration (Λ : Finset (ℤ × ℤ)) (q : ℕ) :
    Fintype.card (Configuration Λ q) = q ^ Λ.card := by
  simp [Configuration, Site]

/-- Empty cuts have no crossing edges. -/
@[simp] theorem edgeBoundary_empty (Λ : Finset (ℤ × ℤ)) :
    edgeBoundary Λ ∅ = ∅ := by
  classical
  simp [edgeBoundary]

/-- The whole domain has no crossing edges. -/
@[simp] theorem edgeBoundary_univ (Λ : Finset (ℤ × ℤ)) :
    edgeBoundary Λ Finset.univ = ∅ := by
  classical
  simp [edgeBoundary]

/-- A walk in the induced domain from a site of `A` to a site outside `A` crosses an edge
`{u, v}` of the cut with `u ∈ A` and `v ∉ A`, and its initial segment joins the starting
site to `u` in at most as many steps. Source: area-law Section 1, definition of `∂Λ A`. -/
theorem exists_edgeBoundary_of_walk {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    {x y : Site Λ} (p : (planeDomainGraph Λ).Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ u v, u ∈ A ∧ v ∉ A ∧ s(u, v) ∈ edgeBoundary Λ A ∧
      ∃ p' : (planeDomainGraph Λ).Walk x u, p'.length ≤ p.length := by
  classical
  obtain ⟨d, hd, hdA, hdA'⟩ := p.exists_boundary_dart (A : Set (Site Λ)) hx hy
  have hsupp := p.dart_fst_mem_support_of_mem_darts hd
  refine ⟨d.fst, d.snd, hdA, hdA', ?_, p.takeUntil d.fst hsupp,
    p.length_takeUntil_le_length hsupp⟩
  simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet]
  exact ⟨d.adj, d.fst, hdA, d.snd, hdA', rfl⟩

/-- Zero ambient dilation changes no lattice points. -/
@[simp] theorem ambientDilation_zero (T : Finset (ℤ × ℤ)) : ambientDilation T 0 = T := by
  simp [ambientDilation]

end TNLean.Lattice
