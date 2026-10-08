/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BeltMarks
import TNLean.PEPS.AreaLaw.Geometry.PolynomialBudget
import TNLean.PEPS.AreaLaw.Geometry.FineMarkSeparation
import Mathlib.Data.Set.Finite.Basic

/-!
# A finite family of initial marks

Choose a sparse pair of belt residues in every dyadic layer. The selected
cell counts are bounded by a summable geometric sequence. Since these counts
are natural numbers, they vanish at every sufficiently large scale. Thus the
selected cell families have finite support, including when the boundary is
empty.

For any lower scale, the union of their actual nine-point mark sets is finite.
Its cardinality is bounded by one constant times the boundary size and the
square of the layer-width factor. The constant is chosen before the domain,
cut, origin, width and lower scale.

Above the fixed lower-scale threshold, each mark is assigned the smallest
side length of a selected cell incident to it. This scale is positive and is
realized by an actual cell. Distinct marks are separated by at least a quarter
of the larger of their assigned scales.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:belt-count`, lines 220–233, and
`geometry:initial-stars`, lines 325–339 and 352–363.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open Filter Topology

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem finite_support_of_summable_nat_counts (c : ℕ → ℕ)
    (hc : Summable (fun k => (c k : ℝ))) : Set.Finite {k | c k ≠ 0} := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (hc.tendsto_atTop_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  apply (Set.finite_lt_nat K).subset
  intro k hk
  by_contra h
  have hreal := hK k (Nat.le_of_not_gt h)
  have hnat : c k < 1 := by exact_mod_cast hreal
  exact hk (by omega)

/-- Sparse residues can be chosen at every scale so that the actual selected belt
cell families have finite support.
Source: area-law Section 11, `geometry:belt-count`, lines 220–233. -/
theorem exists_finitely_supported_sparse_belt_shifts (o : ℝ × ℝ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C : ℕ) :
    ∃ a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)),
      let F := fun k => beltCellIndices
        (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
        (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
      (∀ k, ((F k).card : ℝ) ≤
        64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) ∧
      Set.Finite {k | (F k).Nonempty} := by
  classical
  choose a b hab using fun k => exists_sparse_dyadic_belt_shift o k Λ A C
  let F := fun k => beltCellIndices
    (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
    (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
  refine ⟨a, b, hab, ?_⟩
  have hdecay : Summable (fun k : ℕ =>
      (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) := by
    simpa using summable_polynomial_dyadic_decay 0
  have hcounts : Summable (fun k => ((F k).card : ℝ)) :=
    Summable.of_nonneg_of_le (fun k => Nat.cast_nonneg _) hab
      (hdecay.mul_left (64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card))
  simpa [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty, F] using
    finite_support_of_summable_nat_counts (fun k => (F k).card) hcounts

/-- One uniform boundary bound controls the finite union of actual marks from
chosen sparse belt cells above any lower scale. The shifts satisfy the sparse
cell estimates, and the selected cell families have finite support.
Source: area-law Section 11, `geometry:belt-count`, lines 220–233, and
`geometry:initial-stars`, lines 325–330. -/
theorem exists_uniform_initial_mark_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
      (A : Finset (Site Λ)) (C k₀ : ℕ),
      ∃ a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)),
        let F := fun k => beltCellIndices
          (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
          (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
        (∀ k, ((F k).card : ℝ) ≤
          64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
            (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) ∧
        Set.Finite {k | (F k).Nonempty} ∧
        ∃ M : Finset (ℝ × ℝ),
          (∀ x, x ∈ M ↔ ∃ k, k₀ ≤ k ∧ x ∈ beltMarks o (fineScaleIndex k) (F k)) ∧
          (M.card : ℝ) ≤ B * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  classical
  obtain ⟨B₀, hB₀, hsum⟩ := exists_uniform_polynomial_dyadic_sum_bound 0
  refine ⟨576 * B₀, mul_pos (by norm_num) hB₀, ?_⟩
  intro o Λ A C k₀
  obtain ⟨a, b, hcells, hfinite⟩ := exists_finitely_supported_sparse_belt_shifts o Λ A C
  let F := fun k => beltCellIndices
    (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
    (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
  let K := hfinite.toFinset.filter (fun k => k₀ ≤ k)
  let M := K.biUnion (fun k => beltMarks o (fineScaleIndex k) (F k))
  have hK (k : ℕ) : k ∈ K ↔ k₀ ≤ k ∧ (F k).Nonempty := by
    simp [K, hfinite.mem_toFinset, and_comm, F]
  refine ⟨a, b, hcells, hfinite, M, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
      exact ⟨k, (hK k).mp hk |>.1, hxk⟩
    · rintro ⟨k, hk, hxk⟩
      have hFk : (F k).Nonempty := by
        obtain ⟨z, hz, _⟩ := Finset.mem_biUnion.mp hxk
        exact ⟨z, hz⟩
      exact Finset.mem_biUnion.mpr ⟨k, (hK k).mpr ⟨hk, hFk⟩, hxk⟩
  · let W : ℝ := (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card
    have hW : 0 ≤ W := by dsimp [W]; positivity
    have hmarks (k : ℕ) : ((beltMarks o (fineScaleIndex k) (F k)).card : ℝ) ≤
        576 * W * (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) := by
      have hmarkcard : ((beltMarks o (fineScaleIndex k) (F k)).card : ℝ) ≤
          9 * ((F k).card : ℝ) := by
        exact_mod_cast card_beltMarks_le o (fineScaleIndex k) (F k)
      calc
        _ ≤ 9 * ((F k).card : ℝ) := hmarkcard
        _ ≤ 9 * (64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
            (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hcells k) (by norm_num)
        _ = _ := by dsimp [W]; ring
    have hM : (M.card : ℝ) ≤
        ∑ k ∈ K, ((beltMarks o (fineScaleIndex k) (F k)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have hsumK : ∑ k ∈ K,
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) ≤ B₀ := by
      simpa using hsum K
    calc
      _ ≤ ∑ k ∈ K, ((beltMarks o (fineScaleIndex k) (F k)).card : ℝ) := hM
      _ ≤ ∑ k ∈ K, 576 * W *
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) :=
        Finset.sum_le_sum (fun k _ => hmarks k)
      _ = 576 * W * ∑ k ∈ K,
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) := by
        rw [Finset.mul_sum]
      _ ≤ 576 * W * B₀ := mul_le_mul_of_nonneg_left hsumK (by positivity)
      _ = _ := by dsimp [W]; ring

private theorem exists_least_incident_scales (o : ℝ × ℝ)
    (F : ℕ → Finset (ℤ × ℤ)) (k₀ : ℕ) (M : Finset (ℝ × ℝ))
    (hM : ∀ x, x ∈ M ↔ ∃ k, k₀ ≤ k ∧ x ∈ beltMarks o (fineScaleIndex k) (F k)) :
    ∃ S : M → ℝ,
      (∀ v, 0 < S v ∧ ∃ k z, k₀ ≤ k ∧ z ∈ F k ∧
        v.val ∈ beltCellMarks o (fineScaleIndex k) z ∧ S v = (2 : ℝ) ^ fineScaleIndex k) ∧
      (∀ v k z, k₀ ≤ k → z ∈ F k → v.val ∈ beltCellMarks o (fineScaleIndex k) z →
        S v ≤ (2 : ℝ) ^ fineScaleIndex k) := by
  classical
  let incident (v : M) := (hM v.val).mp v.property
  let m (v : M) := Nat.find (incident v)
  let S (v : M) : ℝ := (2 : ℝ) ^ fineScaleIndex (m v)
  refine ⟨S, ?_, ?_⟩
  · intro v
    have hinc := Nat.find_spec (incident v)
    obtain ⟨z, hz, hvz⟩ := Finset.mem_biUnion.mp hinc.2
    exact ⟨pow_pos zero_lt_two _, m v, z, hinc.1, hz, hvz, rfl⟩
  · intro v k z hk hz hvz
    have hinc : v.val ∈ beltMarks o (fineScaleIndex k) (F k) :=
      Finset.mem_biUnion.mpr ⟨z, hz, hvz⟩
    exact pow_le_pow_right₀ (by norm_num)
      (fineScaleIndex_mono (Nat.find_min' (incident v) ⟨hk, hinc⟩))

/-- Sparse initial marks have their actual smallest incident cell side as a
positive scale, and distinct marks are separated by a quarter of the larger
of their scales. The boundary bound is uniform in all the geometric data.
Source: area-law Section 11, `geometry:belt-count`, lines 220–233, and
`geometry:initial-stars`, lines 325–339 and 352–363. -/
theorem exists_uniform_separated_initial_marks :
    ∃ B : ℝ, 0 < B ∧ ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ))
      (A : Finset (Site Λ)) (C k₀ : ℕ), 2 ≤ C → 50000000 ≤ k₀ →
      ∃ a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)),
        let F := fun k => beltCellIndices
          (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
          (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
        (∀ k, ((F k).card : ℝ) ≤
          64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
            (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) ∧
        Set.Finite {k | (F k).Nonempty} ∧
        ∃ M : Finset (ℝ × ℝ),
          (∀ x, x ∈ M ↔ ∃ k, k₀ ≤ k ∧ x ∈ beltMarks o (fineScaleIndex k) (F k)) ∧
          (M.card : ℝ) ≤ B * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card ∧
          ∃ S : M → ℝ,
            (∀ v, 0 < S v ∧ ∃ k z, k₀ ≤ k ∧ z ∈ F k ∧
              v.val ∈ beltCellMarks o (fineScaleIndex k) z ∧
              S v = (2 : ℝ) ^ fineScaleIndex k) ∧
            (∀ v k z, k₀ ≤ k → z ∈ F k →
              v.val ∈ beltCellMarks o (fineScaleIndex k) z →
              S v ≤ (2 : ℝ) ^ fineScaleIndex k) ∧
            (∀ v w, v ≠ w → max (S v) (S w) / 4 ≤ dist v.val w.val) := by
  classical
  obtain ⟨B, hB, hinitial⟩ := exists_uniform_initial_mark_bound
  refine ⟨B, hB, ?_⟩
  intro o Λ A C k₀ hC hk₀
  obtain ⟨a, b, hcells, hfinite, M, hM, hcard⟩ := hinitial o Λ A C k₀
  let F := fun k => beltCellIndices
    (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
    (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
  obtain ⟨S, hincident, hminimal⟩ := exists_least_incident_scales o F k₀ M hM
  refine ⟨a, b, hcells, hfinite, M, hM, hcard, S, hincident, hminimal, ?_⟩
  intro v w hvw
  obtain ⟨_, k, z, hk, hz, hv, hSv⟩ := hincident v
  obtain ⟨_, h, t, hh, ht, hw, hSw⟩ := hincident w
  have hz' : z ∈ fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C :=
    (Finset.mem_filter.mp hz).1
  have ht' : t ∈ fineLayerIndices o h (fineScaleIndex h) (boundaryEndpoints Λ A) C :=
    (Finset.mem_filter.mp ht).1
  have hne : v.val ≠ w.val := fun he => hvw (Subtype.ext he)
  rw [hSv, hSw]
  exact fineLayer_marks_dist_ge o k h (boundaryEndpoints Λ A) C z t v.val w.val
    hC (hk₀.trans hk) (hk₀.trans hh) hz' ht' hv hw hne

end TNLean.PEPS.AreaLaw.Geometry
