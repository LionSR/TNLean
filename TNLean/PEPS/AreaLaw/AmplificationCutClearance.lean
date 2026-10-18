/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheorem
import TNLean.PEPS.AreaLaw.GraphNeighborhoodCutClearance

/-!
# The cut-clearance clause of the amplification proposition

The last assertion of Proposition 10.2 says that the graph neighborhood
`N_{2r}(S₀)` of the collar `S₀ = A ∩ T_L` stays inside the cut `A` once the ambient
target `T` is far from the cut endpoints `Z`. A walk of length at most `2r` from
`S₀` that leaves `A` crosses the cut at an endpoint within ambient distance
`L + 2r` of `T`; with the explicit clearance `L + 2r < dist_∞(T, Z)` this is
`graphNeighborhood_subset_of_cut_clearance`. This module derives the clause from the
source clearance `L + n^β` at all large scales, uniformly in the domain, the cut and
the target. Consequently the amplification proposition reduces to its radius and
information bounds.

## Main statements

* `exists_threshold_graphNeighborhood_collar_subset`: the cut-clearance clause of
  Proposition 10.2 for every radius obeying `eq:amplification-radius`.
* `amplificationBound_of_radius_output`: the radius and output bounds of
  Proposition 10.2 imply `AmplificationBound`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Proposition 10.2 (`prop:amplification`),
  `09-amplification.tex` lines 289–295, `eq:amplification-cut-clearance`, and
  the last paragraph of its proof, lines 563–575.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- **The cut-clearance clause of Proposition 10.2.** For every radius constant `C` there
is a threshold `N` such that, at every scale `n ≥ N` and for every radius
`r ≤ C n^((1-ε)/α)`, the clearance `dist_∞(T, Z) > L + n^β` of
`eq:amplification-cut-clearance` gives `N_{2r}(S₀) ⊆ A`, where `L = ⌊n^(1-ε)⌋` and
`S₀ = A ∩ T_L`. The threshold depends only on `C`, not on the domain, the cut or the
target. Source: `09-amplification.tex`, lines 289–295 and 563–575. -/
theorem exists_threshold_graphNeighborhood_collar_subset (C : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : ℕ,
      (r : ℝ) ≤ C * (n : ℝ) ^ (Exponents.radiusExponent : ℝ) →
      ∀ (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (T : Finset (ℤ × ℤ)),
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
          (⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ : ℝ) +
              (n : ℝ) ^ (Exponents.beta : ℝ) <
            (Scan.ambientSupDistance t z : ℝ)) →
        graphNeighborhood Λ (2 * r)
            (A.filter fun x ↦ x.val ∈ ambientDilation T
              ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) ⊆ A := by
  obtain ⟨N, -, hN⟩ := Exponents.exists_collar_radius_threshold C 1 one_pos
  refine ⟨N, fun n hn r hr Λ A T hclear ↦
    (graphNeighborhood_subset_of_cut_clearance Λ T A _ (2 * r) ?_).trans
      (Finset.filter_subset _ _)⟩
  intro t ht z hz
  have hsmall := hN n hn r hr
  have hL : (0 : ℝ) ≤
      (⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ : ℝ) := Nat.cast_nonneg _
  have hlt : ((⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ + 2 * r : ℕ) : ℝ) <
      (Scan.ambientSupDistance t z : ℝ) := by
    push_cast
    linarith only [hclear t ht z hz, hsmall, hL]
  exact_mod_cast hlt

/-- **Reduction of Proposition 10.2 to its radius and output bounds.** If, under the
hypotheses of Proposition 10.2, every large scale admits a radius obeying
`eq:amplification-radius` with the output bound `eq:amplification-output` for every
subset of `X = A ∩ T`, then `AmplificationBound` holds: its cut-clearance clause follows
from `exists_threshold_graphNeighborhood_collar_subset`. This does not prove
Proposition 10.2. Source: `09-amplification.tex`, lines 261–296 and 563–575. -/
theorem amplificationBound_of_radius_output {q R : ℕ} {J Δ : ℝ}
    (h : ∀ C₀ : ℝ, 0 < C₀ → ∀ M : ℕ, 1 ≤ M →
      ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, 2 ≤ n → N ≤ n →
        ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
          ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            ∀ (A : Finset (Site Λ)) (T : Finset (ℤ × ℤ)),
              ((A.filter fun x ↦ x.val ∈ ambientDilation T
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
                C₀ * (n : ℝ) ^ 2 →
              ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
              ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                  A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
              ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
                C₀ * n →
              FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                  (A.filter fun x ↦ x.val ∈ T)
                  (A.filter fun x ↦ x.val ∈ ambientDilation T
                    ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
                C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) →
              ∃ r : ℕ, (r : ℝ) ≤ C * (n : ℝ) ^ (Exponents.radiusExponent : ℝ) ∧
                ∀ X ⊆ A.filter (fun x ↦ x.val ∈ T), ∀ Jset : Finset (Site Λ),
                  Disjoint Jset (graphNeighborhood Λ (2 * r)
                    (A.filter fun x ↦ x.val ∈ ambientDilation T
                      ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)) →
                  FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X Jset ≤
                    C * ((n : ℝ) ^ M)⁻¹) :
    AmplificationBound q R J Δ := by
  intro C₀ hC₀ M hM
  obtain ⟨C, N₁, hC⟩ := h C₀ hC₀ M hM
  obtain ⟨N₂, hN₂⟩ := exists_threshold_graphNeighborhood_collar_subset C
  refine ⟨C, max N₁ N₂, fun n hn2 hn Λ hH E₀ Ω hΩ A T hcard hX hY hS hI ↦ ?_⟩
  obtain ⟨r, hr, hout⟩ :=
    hC n hn2 (le_of_max_le_left hn) Λ hH E₀ Ω hΩ A T hcard hX hY hS hI
  exact ⟨r, hr, hout, hN₂ n (le_of_max_le_right hn) r hr Λ A T⟩

end TNLean.PEPS.AreaLaw
