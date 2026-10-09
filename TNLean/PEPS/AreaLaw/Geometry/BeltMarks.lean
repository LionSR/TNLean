/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FineBelts
import TNLean.PEPS.AreaLaw.Geometry.DyadicClosure

/-!
# The nine initial marks of each belt cell

Each belt cell marks its center, four corners and four side midpoints. The
mark set of a finite family of cells at one scale is their finite union,
so coincident marks are counted only once. The number of marks is at most nine times the
number of belt cells. Combining this count with the sparse-belt estimate
gives a uniform geometrically decaying bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 325–330;
the sparse-belt count is `geometry:belt-count`, lines 220–228.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.

The minimum incident scale of a coincident mark, the fan coloring and the
isolated-star properties are not part of these definitions or estimates.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The center, four corners and four side midpoints of a dyadic belt cell.
Source: area-law Section 11, `geometry:initial-stars`, lines 325–330. -/
def beltCellMarks (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) : Finset (ℝ × ℝ) := by
  classical
  exact Finset.univ.image (fun i : Fin 3 × Fin 3 ↦
    (o.1 + (2 : ℝ) ^ ℓ * z.1 + (2 : ℝ) ^ ℓ * i.1.val / 2,
      o.2 + (2 : ℝ) ^ ℓ * z.2 + (2 : ℝ) ^ ℓ * i.2.val / 2))

/-- The deduplicated finite union of the nine marks from each indicated belt cell.
Source: area-law Section 11, `geometry:initial-stars`, lines 325–330. -/
def beltMarks (o : ℝ × ℝ) (ℓ : ℕ) (F : Finset (ℤ × ℤ)) : Finset (ℝ × ℝ) := by
  classical
  exact F.biUnion (beltCellMarks o ℓ)

/-- Every cell mark lies in the closure of its actual dyadic cell.
Source: area-law Section 11, `geometry:initial-stars`, lines 325–330. -/
theorem beltCellMarks_subset_closure_dyadicCell (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    (beltCellMarks o ℓ z : Set (ℝ × ℝ)) ⊆ closure (dyadicCell o ℓ z) := by
  classical
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  rw [closure_dyadicCell]
  have ht : 0 ≤ (2 : ℝ) ^ ℓ := pow_nonneg zero_le_two ℓ
  have h (v : ℝ) (j : ℤ) (a : Fin 3) :
      v + (2 : ℝ) ^ ℓ * j + (2 : ℝ) ^ ℓ * a.val / 2 ∈
        Set.Icc (v + (2 : ℝ) ^ ℓ * j) (v + (2 : ℝ) ^ ℓ * (j + 1)) := by
    have ha : (a.val : ℝ) ≤ 2 := by exact_mod_cast (show a.val ≤ 2 by omega)
    have hlo := mul_nonneg ht (Nat.cast_nonneg (α := ℝ) a.val)
    have hhi := mul_le_mul_of_nonneg_left ha ht
    constructor <;> nlinarith
  exact ⟨h _ _ _, h _ _ _⟩

/-- A belt cell has exactly nine distinct marked points.
Source: area-law Section 11, `geometry:initial-stars`, lines 325–330. -/
theorem card_beltCellMarks (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ) :
    (beltCellMarks o ℓ z).card = 9 := by
  classical
  have ht : (2 : ℝ) ^ ℓ ≠ 0 := (pow_pos zero_lt_two ℓ).ne'
  have hcoord {a b : Fin 3} {v : ℝ}
      (h : v + (2 : ℝ) ^ ℓ * a.val / 2 = v + (2 : ℝ) ^ ℓ * b.val / 2) : a = b := by
    apply Fin.ext
    have hm : (2 : ℝ) ^ ℓ * (a.val : ℝ) = (2 : ℝ) ^ ℓ * (b.val : ℝ) := by linarith
    exact_mod_cast (mul_left_cancel₀ ht hm)
  unfold beltCellMarks
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact Prod.ext (hcoord (congrArg Prod.fst h)) (hcoord (congrArg Prod.snd h))

/-- Coincident marks from different belt cells contribute only once to the total count.
Source: area-law Section 11, `geometry:initial-stars`, lines 325–330. -/
theorem card_beltMarks_le (o : ℝ × ℝ) (ℓ : ℕ) (F : Finset (ℤ × ℤ)) :
    (beltMarks o ℓ F).card ≤ 9 * F.card := by
  classical
  exact Finset.card_biUnion_le.trans (by simp [card_beltCellMarks, Nat.mul_comm])

/-- Sparse residue shifts give a geometrically decaying count for the actual marked points.
Source: area-law Section 11, `geometry:belt-count`, lines 220–228, and
`geometry:initial-stars`, lines 325–330. -/
theorem exists_sparse_dyadic_belt_marks_shift (o : ℝ × ℝ) (k : ℕ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C : ℕ) :
    ∃ a b : Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)),
      ((beltMarks o (fineScaleIndex k)
        (beltCellIndices (fineLayerIndices o k (fineScaleIndex k)
          (boundaryEndpoints Λ A) C) (2 ^ (pitchScaleIndex k - fineScaleIndex k))
          a b)).card : ℝ) ≤
        576 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) := by
  obtain ⟨a, b, hab⟩ := exists_sparse_dyadic_belt_shift o k Λ A C
  refine ⟨a, b, ?_⟩
  let F := beltCellIndices (fineLayerIndices o k (fineScaleIndex k)
    (boundaryEndpoints Λ A) C) (2 ^ (pitchScaleIndex k - fineScaleIndex k)) a b
  have hmarks : ((beltMarks o (fineScaleIndex k) F).card : ℝ) ≤ 9 * (F.card : ℝ) := by
    exact_mod_cast card_beltMarks_le o (fineScaleIndex k) F
  calc
    _ ≤ 9 * (F.card : ℝ) := hmarks
    _ ≤ 9 * (64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hab (by norm_num)
    _ = _ := by ring

end TNLean.PEPS.AreaLaw.Geometry
