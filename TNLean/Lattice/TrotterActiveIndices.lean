/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.FiniteDomain

/-!
# Active factor occurrences in a Trotter product

A sweep contains one term per centre. Only those occurrences whose support
contains a site contribute an index component there. This file first records
the count used in Hastings, arXiv:cond-mat/0508554v3, lines 1069–1075.
-/

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Factor occurrences acting at a site in `n` sweeps, each with one term per
centre. Source: Hastings, arXiv:cond-mat/0508554v3, lines 1069–1075. -/
def trotterActiveOccurrences (X : ι → Finset ι) (n : ℕ) (j : ι) :
    Finset (Fin n × ι) :=
  Finset.univ.filter fun a ↦ j ∈ X a.2

/-- Each centre whose support contains `j` contributes exactly `n` occurrences.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1073–1075. -/
theorem card_trotterActiveOccurrences (X : ι → Finset ι) (n : ℕ) (j : ι) :
    (trotterActiveOccurrences X n j).card =
      n * (Finset.univ.filter fun i ↦ j ∈ X i).card := by
  have heq : trotterActiveOccurrences X n j =
      (Finset.univ : Finset (Fin n)).product (Finset.univ.filter fun i ↦ j ∈ X i) := by
    ext a
    simp [trotterActiveOccurrences]
  rw [heq]
  simp

/-- One pair of physical indices is attached to each active occurrence at a site.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1069–1075. The local physical
dimension `d` may be chosen separately at each site. -/
theorem card_trotterActiveIndices (X : ι → Finset ι) (n : ℕ) (j : ι) (d : ℕ) :
    Fintype.card ((trotterActiveOccurrences X n j) → Fin d × Fin d) =
      (d * d) ^ (n * (Finset.univ.filter fun i ↦ j ∈ X i).card) := by
  simp [card_trotterActiveOccurrences]

variable {Λ : Finset (ℤ × ℤ)}

/-- Radius locality bounds the number of active occurrences by `n` times the
number of sites in the radius ball. Source: Hastings, arXiv:cond-mat/0508554v3,
lines 1073–1075, on the finite planar domain. -/
theorem card_trotterActiveOccurrences_le {R : ℕ}
    (X : Site Λ → Finset (Site Λ))
    (hX : ∀ i j, j ∈ X i → ∃ p : (domainGraph Λ).Walk i j, p.length ≤ R)
    (n : ℕ) (j : Site Λ) :
    (trotterActiveOccurrences X n j).card ≤
      n * (graphNeighborhood Λ R {j}).card := by
  classical
  rw [card_trotterActiveOccurrences]
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro i hi
  obtain ⟨p, hp⟩ := hX i j (Finset.mem_filter.mp hi).2
  simp only [graphNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, exists_eq_left]
  exact ⟨p.reverse, by simpa using hp⟩

end TNLean.Lattice
