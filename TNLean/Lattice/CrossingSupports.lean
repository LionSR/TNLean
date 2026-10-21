/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.FiniteDomain
import QICLean.Entropy.SupportedMarginalTails

/-!
# Sites of the supports crossing a region

Let `Λ` be a finite domain, `R` an interaction range and `A` a set of sites. The supports of
range `R` crossing `A` are those that meet both `A` and its complement; they are the crossing
terms `Entropy.crossingTerms` of the admissible supports at the cut `A`. This file defines the
set of their sites and shows that each such site is within walk distance `R` of a site of `A`
and of a site outside `A`.

## Main statements

* `TNLean.Lattice.crossingSites`: the sites of the supports of range `R` crossing `A`.
* `TNLean.Lattice.exists_walks_of_mem_crossingSites`: every site of a crossing support is
  joined by walks of length at most `R` to a site of `A` and to a site outside `A`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `02-information.tex`, lines 416–424 and 498–564, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `02-initial.tex`, lines 47–48 (the terms crossing a cut).

Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

namespace TNLean.Lattice

variable {Λ : Finset (ℤ × ℤ)} {R : ℕ}

/-- The sites of the supports of range `R` crossing `A`, that is, of the admissible supports
meeting both `A` and its complement. At range one these are the endpoints of the edges
crossing `A`. Source: polynomial-PEPS `02-information.tex`, lines 416–424 and 513–524, at
range `R`. -/
noncomputable def crossingSites (Λ : Finset (ℤ × ℤ)) (R : ℕ) (A : Finset (Site Λ)) :
    Finset (Site Λ) := by
  classical
  exact (Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).biUnion fun X ↦ X.1

/-- **Every site of a crossing support is near both sides of `A`.** It is joined by walks of
length at most `R` to a site of `A` and to a site outside `A`. -/
theorem exists_walks_of_mem_crossingSites {A : Finset (Site Λ)} {z : Site Λ}
    (hz : z ∈ crossingSites Λ R A) :
    ∃ x ∈ A, ∃ y ∉ A, (∃ p : (domainGraph Λ).Walk z x, p.length ≤ R) ∧
      ∃ p : (domainGraph Λ).Walk z y, p.length ≤ R := by
  classical
  simp only [crossingSites, Entropy.crossingTerms, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and] at hz
  obtain ⟨X, ⟨⟨x, hxX, hxA⟩, y, hyX, hyA⟩, hzX⟩ := hz
  exact ⟨x, hxA, y, hyA, X.2.2 z hzX x hxX, X.2.2 z hzX y hyX⟩

end TNLean.Lattice
