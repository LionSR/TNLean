/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Int.Interval

/-!
# Finite induced square-lattice domains

A domain is an arbitrary finite subset of the integer lattice. Interaction
range is measured by walks that remain in the domain. Ambient coordinate
neighborhoods, used in the geometric argument, are defined separately.
Neither connectedness nor the absence of holes is assumed.

## Main definitions

* `Site`: the sites of a finite domain.
* `domainGraph`: the induced nearest-neighbor graph.
* `IsAdmissibleSupport`: a nonempty support of bounded induced-graph diameter.
* `edgeBoundary`: the unordered edges crossing a cut, each counted once.
* `ambientDilation`: the integer sup-norm dilation of an ambient finite set.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1, `eq:hamiltonian`, and Section 2.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Sites of a finite induced domain. Source: area-law Theorem 1.1. -/
abbrev Site (Λ : Finset (ℤ × ℤ)) := ↥Λ

/-- Configurations of a domain with local dimension `q`.
Source: area-law Section 1, the tensor product of the site spaces. -/
abbrev Configuration (Λ : Finset (ℤ × ℤ)) (q : ℕ) := Site Λ → Fin q

/-- The nearest-neighbor graph induced on the domain.
Source: area-law Section 1, before `eq:hamiltonian`. -/
def domainGraph (Λ : Finset (ℤ × ℤ)) : SimpleGraph (Site Λ) where
  Adj x y :=
    (x.1.2 = y.1.2 ∧ (x.1.1 + 1 = y.1.1 ∨ y.1.1 + 1 = x.1.1)) ∨
    (x.1.1 = y.1.1 ∧ (x.1.2 + 1 = y.1.2 ∨ y.1.2 + 1 = x.1.2))
  symm := ⟨by intros; omega⟩
  loopless := ⟨by intros; omega⟩

instance (Λ : Finset (ℤ × ℤ)) : DecidableRel (domainGraph Λ).Adj := by
  unfold domainGraph
  infer_instance

/-- A support is nonempty and every pair of its sites is joined inside the
induced domain by a walk of length at most `R`.
Source: area-law `eq:hamiltonian`. -/
def IsAdmissibleSupport (Λ : Finset (ℤ × ℤ)) (R : ℕ) (X : Finset (Site Λ)) : Prop :=
  X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X, ∃ p : (domainGraph Λ).Walk x y, p.length ≤ R

/-- The finite index of supports in the Hamiltonian sum, with one index per
nonempty support. Source: area-law `eq:hamiltonian`. -/
abbrev AdmissibleSupport (Λ : Finset (ℤ × ℤ)) (R : ℕ) :=
  {X : Finset (Site Λ) // IsAdmissibleSupport Λ R X}

noncomputable instance (Λ : Finset (ℤ × ℤ)) (R : ℕ) :
    Fintype (AdmissibleSupport Λ R) := Fintype.ofFinite _

/-- Closed graph neighborhood of a region, measured by walks in the induced
finite domain. Source: area-law Section 2, induced-graph distance conventions. -/
noncomputable def graphNeighborhood (Λ : Finset (ℤ × ℤ)) (R : ℕ)
    (X : Finset (Site Λ)) : Finset (Site Λ) := by
  classical
  exact Finset.univ.filter fun y ↦ ∃ x ∈ X, ∃ p : (domainGraph Λ).Walk x y, p.length ≤ R

/-- Unordered edges with one endpoint in `A` and the other outside `A`.
Source: area-law Section 1, definition of `∂Λ A`. -/
noncomputable def edgeBoundary (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    Finset (Sym2 (Site Λ)) := by
  classical
  exact (domainGraph Λ).edgeFinset.filter fun e ↦
    ∃ x ∈ A, ∃ y ∉ A, e = s(x, y)

/-- Integer sup-norm dilation of an ambient finite set, independent of walks
in a domain. Source: area-law Definition 9.3 and the sets `T_j`. -/
def ambientDilation (T : Finset (ℤ × ℤ)) (r : ℕ) : Finset (ℤ × ℤ) :=
  T.biUnion fun x ↦
    (Finset.Icc (x.1 - (r : ℤ)) (x.1 + r)).product
      (Finset.Icc (x.2 - (r : ℤ)) (x.2 + r))

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

/-- A singleton is an admissible support at every range.
Source: area-law `eq:hamiltonian`, including range zero. -/
theorem isAdmissibleSupport_singleton (Λ : Finset (ℤ × ℤ)) (R : ℕ) (x : Site Λ) :
    IsAdmissibleSupport Λ R {x} := by
  refine ⟨Finset.singleton_nonempty x, ?_⟩
  simp only [Finset.mem_singleton]
  rintro y rfl z rfl
  exact ⟨.nil, Nat.zero_le R⟩

/-- The walk condition agrees with Mathlib's extended graph metric.
Disconnected pairs have distance infinity, so cannot satisfy a finite range. -/
theorem exists_walk_length_le_iff_edist_le (Λ : Finset (ℤ × ℤ)) (R : ℕ)
    (x y : Site Λ) :
    (∃ p : (domainGraph Λ).Walk x y, p.length ≤ R) ↔
      (domainGraph Λ).edist x y ≤ R := by
  constructor
  · rintro ⟨p, hp⟩
    exact p.edist_le.trans (by exact_mod_cast hp)
  · intro h
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
      (ne_top_of_le_ne_top (by simp) h)
    exact ⟨p, by exact_mod_cast hp ▸ h⟩

/-- At range zero, admissible supports are exactly the one-site supports.
Source: area-law Section 2, the range-zero Hamiltonian. -/
theorem isAdmissibleSupport_zero_iff (Λ : Finset (ℤ × ℤ)) (X : Finset (Site Λ)) :
    IsAdmissibleSupport Λ 0 X ↔ X.card = 1 := by
  simp only [IsAdmissibleSupport]
  simp_rw [exists_walk_length_le_iff_edist_le]
  simp only [Nat.cast_zero, le_zero_iff, SimpleGraph.edist_eq_zero_iff]
  rw [← Finset.card_le_one, ← Finset.card_pos]
  omega

/-- Adjacent sites form an admissible range-one support.
Source: area-law Corollary 1.2, nearest-neighbor interactions. -/
theorem isAdmissibleSupport_pair_of_adj {Λ : Finset (ℤ × ℤ)}
    {x y : Site Λ} (h : (domainGraph Λ).Adj x y) :
    IsAdmissibleSupport Λ 1 {x, y} := by
  simp only [IsAdmissibleSupport]
  simp_rw [exists_walk_length_le_iff_edist_le]
  simp [SimpleGraph.edist_le_one_iff_adj_or_eq, h, h.symm]

/-- Zero ambient dilation changes no lattice points. -/
@[simp] theorem ambientDilation_zero (T : Finset (ℤ × ℤ)) : ambientDilation T 0 = T := by
  simp [ambientDilation]

end TNLean.PEPS.AreaLaw
