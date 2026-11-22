/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.WeightedLowRestriction
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian
import TNLean.MPS.AreaLaw.NearestNeighbourImaginaryTime

/-!
# Residual estimates for regional energy truncation

The original nearest-neighbour bond sum supplies boundary exponential estimates. With them,
the conjugation-bound form of the weighted Sylvester argument in
`QICLean.Analysis.WeightedLowRestriction` controls the regional truncation excess on the
specified low-energy space.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

open ManyBody (interval)

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The sum of supplied original nearest-neighbour boundary bonds has
short-time conjugation norm at most twice their number, even after a scalar
energy shift: the bond case of `ManyBody.Interaction.norm_exp_conjugation_shift_sum_le`.
Supporting AKL14, arXiv:1406.3898, low70.tex, lines 795–880.
No conjugation or residual estimate is supplied as a hypothesis. -/
theorem norm_exp_conjugation_nearestNeighbour_boundary_sum_le
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ Φ.term i) (h1 : ∀ i ∈ I ∪ J, Φ.term i ≤ 1)
    (z : ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.partialHamiltonian I
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * (Φ.partialHamiltonian J) *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * (J.card : ℝ) := by
  classical
  intro H
  have hI : H = ∑ i ∈ I, (Φ.restrict (· ∈ I ∪ J)).term i :=
    (ManyBody.Interaction.partialHamiltonian_restrict_of_forall fun _ hi ↦
      Finset.mem_union_left J hi).symm
  have hJ : Φ.partialHamiltonian J = ∑ j ∈ J, (Φ.restrict (· ∈ I ∪ J)).term j :=
    (ManyBody.Interaction.partialHamiltonian_restrict_of_forall fun _ hj ↦
      Finset.mem_union_right I hj).symm
  rw [hI, hJ]
  exact (Φ.restrict (· ∈ I ∪ J)).norm_exp_conjugation_shift_sum_le I J (k := 2) (g := 2)
    (fun i ↦ by
      rw [ManyBody.Interaction.restrict_term]
      split_ifs with hi
      exacts [h0 i hi, le_rfl])
    (fun i ↦ by
      rw [ManyBody.Interaction.restrict_term]
      split_ifs with hi
      exacts [h1 i hi, zero_le_one])
    (fun i ↦ by simpa using ManyBody.card_interval_le (L := L) i.val (i.val + 2))
    (card_filter_mem_bond_le_two I) z ht0 (by push_cast; linarith)

/-- The actual exponential weight on the original regional sum has a small
restriction from the actual low spectral span to the original high projection
range. All commutations, range memberships, quadratic bounds and boundary norms
are derived. The structural commutation and matrix order must be established
from the spatial decomposition in a physical application.

This is an auxiliary weighted spectral estimate for ALVV,
arXiv:1602.08828v2, Theorem t:ais, lines 1010--1024, and AKL14,
arXiv:1406.3898, Theorem lowspec, lines 1102--1168. It is not the full physical
truncation-error or subspace-closeness theorem. -/
theorem exists_nearestNeighbour_weighted_low_restriction
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ Φ.term i) (h1 : ∀ i ∈ I ∪ J, Φ.term i ≤ 1)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (r u e s : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 8)
    (hXA : Commute X (Φ.partialHamiltonian I))
    (horder : u • Matrix.spectralProjectionGE (Φ.partialHamiltonian I) (r + u) ≤ X)
    (b : OrthonormalBasis (Fin L → Fin q) ℂ
      (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ)
    (hEigen : ∀ j, Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (X + Φ.partialHamiltonian J) (b j) = (a j : ℂ) • b j)
    (hgap : 2 * (J.card : ℝ) < u - e) :
    let A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.partialHamiltonian I
    let Q := Matrix.spectralProjectionGE A (r + u)
    let W := NormedSpace.exp (s • (A - (r + u) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)))
    let T := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a e
    let U := (T Q).range
    ∃ Z : G →L[ℂ] U,
      U.subtypeL ∘L Z = (T W * T Q).domRestrict G ∧
      ‖Z‖ ≤ (2 * (J.card : ℝ)) / (u - e - 2 * (J.card : ℝ)) := by
  intro A Q W T G U
  have hA : A.IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i hi ↦
      h0 i (Finset.mem_union_left J hi))).isHermitian
  have hconj := norm_exp_conjugation_nearestNeighbour_boundary_sum_le
    I J Φ h0 h1 ((r + u : ℝ) : ℂ) s hs0.le hs1
  simp only [Complex.coe_smul] at hconj
  exact Matrix.exists_weighted_low_restriction_of_conjugation_le A X _ hA r u e s _ hs0
    hXA horder b a hEigen hconj hgap

/-- The single-region tail bound for a literal partially clipped consecutive
regional sum. Original bond supports imply commutation, and the original
regional lower bounds imply the required order. No current-commutation,
current-order or norm estimate is supplied. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005. -/
theorem norm_consecutive_regional_truncation_low_le
    {L q m : ℕ} (k : Fin (m + 1) → ℕ) (hk : Monotone k)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (e : Fin m → ℝ) (T : Finset (Fin m)) (j : Fin m)
    (J : Finset (Fin (L - 1))) (u ε s t : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 8) (hu : 0 ≤ u) (hut : u ≤ t)
    (b : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ) :
    let A : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun i ↦
      ∑ r ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun r ↦ k i.castSucc ≤ r.val ∧ r.val + 1 < k i.succ), Φ.term r
    let X := ∑ i, ((if i ∈ T then cfc (fun x : ℝ ↦ min x (e i + t)) (A i)
      else A i) - (e i : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a ε
    (∀ i, (e i : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A i) →
    (∀ v, ι (X + Φ.partialHamiltonian J) (b v) = (a v : ℂ) • b v) →
    2 * (J.card : ℝ) < u - ε →
    ‖(ι (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict G‖ ≤
      (Real.exp (-s * (t - u) - 1) / s) *
        ((2 * (J.card : ℝ)) / (u - ε - 2 * (J.card : ℝ))) := by
  intro A X ι G he hEigen hgap
  have hA (i : Fin m) : (A i).IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun r _ ↦ h0 r)).isHermitian
  have hconj := norm_exp_conjugation_nearestNeighbour_boundary_sum_le
    ((Finset.univ : Finset (Fin (L - 1))).filter
      (fun r ↦ k j.castSucc ≤ r.val ∧ r.val + 1 < k j.succ)) J Φ
    (fun r _ ↦ h0 r) (fun r _ ↦ h1 r) ((e j + u : ℝ) : ℂ) s hs0.le hs1
  simp only [Complex.coe_smul] at hconj
  exact Matrix.norm_partially_clipped_truncation_low_le A hA
    (pairwise_commute_sum_internal_consecutive_regions k hk Φ) e he T j _ u ε s t _
    hs0 hu hut b a hEigen hconj hgap

end TNLean.MPS.AreaLaw
