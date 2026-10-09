/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.ClosedSquare
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Separated nested square patches

The source-selected radii `u + 2 * j`, with `j < ⌊u / 2⌋₊ + 1`, are between
`u` and `2 * u` when `u ≥ 0`. A nearest-neighbor edge crosses at most one selected patch.
At any crossing its support misses all earlier patches and is contained in
all later patches. The resulting boundary-weighted quadratic sum is at most
`36 * κ²` when `u ≥ 4`.

These are geometry and scalar arithmetic statements, not the energy estimate
or Proposition 4.1: no Hamiltonian, unitary, or state is involved.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `03-patches.tex`, lines 53–66, 213–228, 323–336.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

open scoped BigOperators

/-- The number of nested patches. Source: polynomial-PEPS `03-patches.tex`, lines 60–66. -/
noncomputable def nestedPatchCount (u : ℝ) : ℕ := ⌊u / 2⌋₊ + 1

/-- The zero-based selected radius. Source: polynomial-PEPS `03-patches.tex`, lines 60–66. -/
def nestedPatchRadius (u : ℝ) (j : ℕ) : ℝ := u + 2 * j

/-- The sampled patch at the selected radius.
Source: polynomial-PEPS `03-patches.tex`, lines 60–66. -/
noncomputable def nestedPatch (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) (u : ℝ) (j : ℕ) :
    Finset (Site Λ) := closedSquareSample Λ c (nestedPatchRadius u j)

/-- There is at least one selected radius. -/
theorem nestedPatchCount_pos (u : ℝ) : 0 < nestedPatchCount u := by
  simp [nestedPatchCount]

/-- The source choice provides more than `u / 2` patches. -/
theorem half_lt_nestedPatchCount (u : ℝ) : u / 2 < (nestedPatchCount u : ℝ) := by
  simpa [nestedPatchCount] using Nat.lt_floor_add_one (u / 2)

/-- Each selected radius is at least the base radius. -/
theorem le_nestedPatchRadius (u : ℝ) (j : ℕ) : u ≤ nestedPatchRadius u j := by
  unfold nestedPatchRadius
  exact le_add_of_nonneg_right (by positivity)

/-- Every radius in the selected finite family is at most twice the base radius. -/
theorem nestedPatchRadius_le_two_mul {u : ℝ} (hu : 0 ≤ u)
    {j : ℕ} (hj : j < nestedPatchCount u) : nestedPatchRadius u j ≤ 2 * u := by
  have hj' : j ≤ ⌊u / 2⌋₊ := by simpa [nestedPatchCount] using hj
  have hjr : (j : ℝ) ≤ (⌊u / 2⌋₊ : ℝ) := by exact_mod_cast hj'
  have hf := Nat.floor_le (show 0 ≤ u / 2 by positivity)
  unfold nestedPatchRadius
  linarith

/-- Distinct successive selected radii are separated by at least two. -/
theorem nestedPatchRadius_add_two_le {u : ℝ} {i j : ℕ} (hij : i < j) :
    nestedPatchRadius u i + 2 ≤ nestedPatchRadius u j := by
  have h : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  unfold nestedPatchRadius
  linarith

/-- Selected patches are nested, even when clipping makes some of them equal. -/
theorem nestedPatch_mono (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) (u : ℝ)
    {i j : ℕ} (hij : i ≤ j) : nestedPatch Λ c u i ⊆ nestedPatch Λ c u j := by
  apply closedSquareSample_mono
  unfold nestedPatchRadius
  have h : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

/-- A crossing edge's support misses a square whose radius is smaller by at least one. -/
theorem edgeBoundary_support_disjoint_of_add_one_le {Λ : Finset (ℤ × ℤ)}
    {c : ℝ × ℝ} {r s : ℝ} {e : Sym2 (Site Λ)}
    (he : e ∈ edgeBoundary Λ (closedSquareSample Λ c r)) (hsr : s + 1 ≤ r) :
    Disjoint e.toFinset (closedSquareSample Λ c s) := by
  classical
  obtain ⟨hedge, x, hx, y, hy, rfl⟩ := Finset.mem_filter.mp he
  have hxy : (domainGraph Λ).Adj x y := by simpa using hedge
  rw [Sym2.toFinset_mk_eq, Finset.disjoint_left]
  intro z hz hzs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hy (closedSquareSample_mono Λ c hsr (mem_closedSquareSample_of_adj hxy hzs))
  · exact hy (closedSquareSample_mono Λ c (by linarith) hzs)

/-- A crossing edge's support lies in every square enlarged by at least one. -/
theorem edgeBoundary_support_subset_of_add_one_le {Λ : Finset (ℤ × ℤ)}
    {c : ℝ × ℝ} {r s : ℝ} {e : Sym2 (Site Λ)}
    (he : e ∈ edgeBoundary Λ (closedSquareSample Λ c r)) (hrs : r + 1 ≤ s) :
    e.toFinset ⊆ closedSquareSample Λ c s := by
  classical
  obtain ⟨hedge, x, hx, y, hy, rfl⟩ := Finset.mem_filter.mp he
  have hxy : (domainGraph Λ).Adj x y := by simpa using hedge
  rw [Sym2.toFinset_mk_eq]
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact ⟨closedSquareSample_mono Λ c (by linarith) hx,
    closedSquareSample_mono Λ c hrs (mem_closedSquareSample_of_adj hxy hx)⟩

/-- A crossing support misses every earlier selected patch.
Source: polynomial-PEPS `03-patches.tex`, lines 222–228. -/
theorem nestedPatch_crossing_disjoint_earlier {Λ : Finset (ℤ × ℤ)}
    {c : ℝ × ℝ} {u : ℝ} {i j : ℕ} {e : Sym2 (Site Λ)}
    (he : e ∈ edgeBoundary Λ (nestedPatch Λ c u j)) (hij : i < j) :
    Disjoint e.toFinset (nestedPatch Λ c u i) := by
  apply edgeBoundary_support_disjoint_of_add_one_le he
  linarith [nestedPatchRadius_add_two_le (u := u) hij]

/-- A crossing support is contained in every later selected patch.
Source: polynomial-PEPS `03-patches.tex`, lines 222–228. -/
theorem nestedPatch_crossing_subset_later {Λ : Finset (ℤ × ℤ)}
    {c : ℝ × ℝ} {u : ℝ} {i j : ℕ} {e : Sym2 (Site Λ)}
    (he : e ∈ edgeBoundary Λ (nestedPatch Λ c u i)) (hij : i < j) :
    e.toFinset ⊆ nestedPatch Λ c u j := by
  apply edgeBoundary_support_subset_of_add_one_le he
  linarith [nestedPatchRadius_add_two_le (u := u) hij]

/-- No unordered edge crosses two distinct selected patches.
Source: polynomial-PEPS `03-patches.tex`, lines 218–228. -/
theorem nestedPatch_crossing_unique {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ}
    {u : ℝ} {i j : ℕ} {e : Sym2 (Site Λ)}
    (hi : e ∈ edgeBoundary Λ (nestedPatch Λ c u i))
    (hj : e ∈ edgeBoundary Λ (nestedPatch Λ c u j)) : i = j := by
  classical
  wlog hij : i < j generalizing i j
  · rcases lt_trichotomy i j with h | h | h
    · exact this hi hj h
    · exact h
    · exact (this hj hi h).symm
  have hs := nestedPatch_crossing_subset_later hi hij
  obtain ⟨_, x, _, y, hy, rfl⟩ := Finset.mem_filter.mp hj
  exact False.elim (hy (hs (by simp [Sym2.toFinset_mk_eq])))

/-- The crossing-edge sets of distinct selected patches are disjoint. -/
theorem disjoint_edgeBoundary_nestedPatch (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ)
    (u : ℝ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (edgeBoundary Λ (nestedPatch Λ c u i))
      (edgeBoundary Λ (nestedPatch Λ c u j)) := by
  classical
  exact Finset.disjoint_left.mpr fun _ hi hj ↦ hij (nestedPatch_crossing_unique hi hj)

/-- Each selected patch has at most `16 * u + 4` crossing edges.
Source: polynomial-PEPS `03-patches.tex`, lines 323–326. -/
theorem card_edgeBoundary_nestedPatch_le (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ)
    {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : j < nestedPatchCount u) :
    ((edgeBoundary Λ (nestedPatch Λ c u j)).card : ℝ) ≤ 16 * u + 4 := by
  have h := card_edgeBoundary_closedSquareSample_le Λ c
    (hu.trans (le_nestedPatchRadius u j))
  have hr := nestedPatchRadius_le_two_mul hu hj
  change ((edgeBoundary Λ (closedSquareSample Λ c (nestedPatchRadius u j))).card : ℝ) ≤ _
  linarith

/-- The scalar budget of the source-selected family is at most `36 * κ²`.
Source: polynomial-PEPS `eq:patch-energy-bound`, lines 323–336. This is only the
numerical coefficient, with no Hamiltonian or energy conclusion. -/
theorem nestedPatch_quadratic_budget {u : ℝ} (hu : 4 ≤ u) (κ : ℝ) :
    (16 * u + 4) * ∑ _j : Fin (nestedPatchCount u),
      (κ / (nestedPatchCount u : ℝ)) ^ 2 ≤ 36 * κ ^ 2 := by
  have hm : (0 : ℝ) < nestedPatchCount u := by exact_mod_cast nestedPatchCount_pos u
  have hbound : 16 * u + 4 ≤ 36 * (nestedPatchCount u : ℝ) := by
    linarith [half_lt_nestedPatchCount u]
  have hsum : (∑ _j : Fin (nestedPatchCount u), (κ / (nestedPatchCount u : ℝ)) ^ 2) =
      κ ^ 2 / (nestedPatchCount u : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum]
  calc
    (16 * u + 4) * (κ ^ 2 / (nestedPatchCount u : ℝ)) =
        ((16 * u + 4) / (nestedPatchCount u : ℝ)) * κ ^ 2 := by ring
    _ ≤ 36 * κ ^ 2 :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ hm).mpr hbound) (sq_nonneg κ)

/-- The actual boundary-weighted sum satisfies the source's geometric coefficient.
Source: polynomial-PEPS `eq:patch-energy-bound`, lines 323–336. This theorem
supplies the counting and arithmetic only, not the analytic energy argument. -/
theorem sum_card_edgeBoundary_nestedPatch_mul_sq_le (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ)
    {u : ℝ} (hu : 4 ≤ u) (κ : ℝ) :
    ∑ j : Fin (nestedPatchCount u),
      ((edgeBoundary Λ (nestedPatch Λ c u j)).card : ℝ) *
        (κ / (nestedPatchCount u : ℝ)) ^ 2 ≤ 36 * κ ^ 2 := by
  calc
    _ ≤ ∑ _j : Fin (nestedPatchCount u),
        (16 * u + 4) * (κ / (nestedPatchCount u : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (card_edgeBoundary_nestedPatch_le Λ c (by linarith) j.isLt) (sq_nonneg _)
    _ = (16 * u + 4) * ∑ _j : Fin (nestedPatchCount u),
        (κ / (nestedPatchCount u : ℝ)) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := nestedPatch_quadratic_budget hu κ

end TNLean.PEPS.AreaLaw.Geometry
