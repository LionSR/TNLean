/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheorem

/-!
# The cut-clearance clause of the amplification proposition

The last assertion of Proposition 10.2 says that the graph neighborhood
`N_{2r}(S₀)` of the collar `S₀ = A ∩ T_L` stays inside the cut `A` once the ambient
target `T` is far from the cut endpoints `Z`. A walk of length at most `2r` from
`S₀` that leaves `A` crosses the cut at an endpoint within ambient distance
`L + 2r` of `T`. This module proves that clause, first with the explicit clearance
`L + 2r < dist_∞(T, Z)` and then with the source clearance `L + n^β` at all large
scales, uniformly in the domain, the cut and the target. Consequently the
amplification proposition reduces to its radius and information bounds.

## Main statements

* `graphNeighborhood_collar_subset_of_clearance`: the explicit clearance gives
  `N_k(A ∩ T_L) ⊆ A`.
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

namespace TNLean.PEPS.AreaLaw

/-- A graph neighborhood of radius `k` of the collar `A ∩ T_L` lies inside `A` when every
cut endpoint is at ambient sup-distance more than `L + k` from `T`. A walk of length at
most `k` from the collar that leaves `A` crosses the cut at an endpoint within distance
`L + k` of `T`. Source: `09-amplification.tex`, lines 569–575. -/
theorem graphNeighborhood_collar_subset_of_clearance {Λ T : Finset (ℤ × ℤ)}
    {A : Finset (Site Λ)} {L k : ℕ}
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((L + k : ℕ) : ℤ) < Scan.ambientSupDistance t z) :
    graphNeighborhood Λ k (A.filter fun x ↦ x.val ∈ ambientDilation T L) ⊆ A := by
  classical
  intro y hy
  by_contra hyA
  obtain ⟨x, hxS, p, hp⟩ := (Finset.mem_filter.mp hy).2
  obtain ⟨hxA, hxT⟩ := Finset.mem_filter.mp hxS
  have hT : T.Nonempty := by
    obtain ⟨t, ht, -⟩ := Finset.mem_biUnion.mp hxT
    exact ⟨t, ht⟩
  obtain ⟨u, v, -, -, he, p', hp'⟩ := exists_edgeBoundary_of_walk p hxA hyA
  have hu : u ∈ graphNeighborhood Λ k (A.filter fun x ↦ x.val ∈ ambientDilation T L) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxS, p', hp'.trans hp⟩
  obtain ⟨t, ht, htu⟩ := exists_ambientSupDistance_le_of_mem_graphNeighborhood hT
    (fun x hx ↦ (Finset.mem_filter.mp hx).2) hu
  have hz := hclear t ht u.val
    (Geometry.mem_boundaryEndpoints_of_mem_edgeBoundary he (Sym2.mem_mk_left u v))
  push_cast at hz
  omega

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
  refine ⟨N, fun n hn r hr Λ A T hclear ↦ graphNeighborhood_collar_subset_of_clearance ?_⟩
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
