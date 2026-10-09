/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.LatticeDyadicRect
import TNLean.PEPS.AreaLaw.EntropyDimension

/-!
# Entropy subadditivity on the actual capped dyadic partition

The selected lattice squares induce disjoint physical rectangle regions,
whose union is the physical intersection with the finite lattice set.
An estimate on each safe rectangle therefore bounds the entropy by
the sum of its scale weights.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, Lemma 9.4, 08-scanner.tex, lines 641–667,
at openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The existing manuscript proofs are extracted from TemplateBoxEntropy.lean,
with the weighted-cover lemma made public for rectangle shells.
This auxiliary lemma assumes a pointwise safe-box bound and does not derive it.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The physical rectangle regions of the actual capped partition cover exactly
the physical intersection, including holes and disconnected domains. -/
theorem biUnion_rectRegion_cappedDyadicPartition {Λ : Finset (ℤ × ℤ)}
    (A : Finset (Site Λ)) (S : Finset (ℤ × ℤ)) (K : ℕ) :
    (cappedDyadicPartition S K).biUnion (fun c ↦ rectRegion A (latticeDyadicRect c.1 c.2)) =
      A.filter (fun x ↦ x.1 ∈ S) := by
  classical
  ext x
  simp only [Finset.mem_biUnion, rectRegion_latticeDyadicRect, Finset.mem_filter]
  constructor
  · rintro ⟨c, hc, hxA, hx⟩
    exact ⟨hxA, ((mem_cappedDyadicPartition _ _ _ _).mp hc).2.1 hx⟩
  · rintro ⟨hxA, hx⟩
    obtain ⟨c, hc, hxc⟩ := exists_mem_cappedDyadicPartition S K hx
    exact ⟨c, hc, hxA, hxc⟩

/-- Filtering the disjoint ambient cells preserves their disjointness. -/
theorem pairwiseDisjoint_rectRegion_cappedDyadicPartition {Λ : Finset (ℤ × ℤ)}
    (A : Finset (Site Λ)) (S : Finset (ℤ × ℤ)) (K : ℕ) :
    (cappedDyadicPartition S K : Set (ℕ × (ℤ × ℤ))).PairwiseDisjoint
      (fun c ↦ rectRegion A (latticeDyadicRect c.1 c.2)) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  change x ∈ rectRegion A (latticeDyadicRect a.1 a.2) at hxa
  change x ∈ rectRegion A (latticeDyadicRect b.1 b.2) at hxb
  rw [rectRegion_latticeDyadicRect] at hxa hxb
  exact Finset.disjoint_left.mp (pairwiseDisjoint_cappedDyadicPartition S K ha hb hab)
    (Finset.mem_filter.mp hxa).2 (Finset.mem_filter.mp hxb).2

/-- Subadditivity on the actual physical dyadic partition. -/
theorem regionalEntropy_filter_le_sum_rectRegion (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ))
    (S : Finset (ℤ × ℤ)) (K : ℕ) :
    regionalEntropy Λ q Ω (A.filter fun x ↦ x.1 ∈ S) ≤
      ∑ c ∈ cappedDyadicPartition S K,
        regionalEntropy Λ q Ω (rectRegion A (latticeDyadicRect c.1 c.2)) := by
  classical
  simp only [regionalEntropy_eq_finiteProduct]
  have h := Entropy.OrderedSetFunction.union_biUnion_le_sum
    (FiniteProduct.entropy (fun _ : Site Λ ↦ Fin q) Ω)
    (FiniteProduct.entropy_union_le _ Ω hΩ) ∅
    (fun c : ℕ × (ℤ × ℤ) ↦ rectRegion A (latticeDyadicRect c.1 c.2))
    (cappedDyadicPartition S K) (by intros; simp)
    (pairwiseDisjoint_rectRegion_cappedDyadicPartition A S K)
  simpa only [Finset.empty_union, FiniteProduct.entropy_empty _ Ω hΩ, zero_add,
    biUnion_rectRegion_cappedDyadicPartition] using h

/-- Entropy of the physical intersection is bounded by the weighted sum of
the actual selected squares under a pointwise safe-box estimate.
Source: Lemma 9.4, 08-scanner.tex, lines 651–664. -/
theorem regionalEntropy_filter_le_weighted_cover
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (S : Finset (ℤ × ℤ)) (K : ℕ) (e C : ℝ)
    (hsafe : ∀ c ∈ cappedDyadicPartition S K, IsSafe Λ A D₀ (latticeDyadicRect c.1 c.2))
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    regionalEntropy Λ q Ω (A.filter fun x ↦ x.1 ∈ S) ≤
      C * ∑ c ∈ cappedDyadicPartition S K, ((2 : ℝ) ^ c.1) ^ (1 + e) := by
  classical
  refine (regionalEntropy_filter_le_sum_rectRegion Λ q Ω hΩ A S K).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  simpa only [size_latticeDyadicRect, Nat.cast_pow, Nat.cast_ofNat] using
    hbox (latticeDyadicRect c.1 c.2) (hsafe c hc)

end TNLean.PEPS.AreaLaw.Geometry
