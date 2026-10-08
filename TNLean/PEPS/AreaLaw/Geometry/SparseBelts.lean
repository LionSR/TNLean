/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.ModEq

/-!
# Sparse selection of coordinate residue classes

For a finite set of integer cell indices and a positive modulus, two residue
classes can be chosen so that the union of the corresponding horizontal and
vertical strips contains at most twice the average number of cells.

This is the finite averaging step used for `geometry:belt-count` in OpenAI,
*A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 11, source lines 210–237. The estimate below does not include the
layer-cell count or its conversion to the displayed dyadic decay estimate.

Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Two coordinate residue classes select at most `2 / m` of a finite cell set.
The integer formulation avoids division and includes empty cell sets and `m = 1`.
Source: `geometry:belt-count`, Section 11, lines 210–237 of the area-law manuscript.
The layer-cell and dyadic-scale estimates are separate conclusions. -/
theorem exists_sparse_belt_shift (F : Finset (ℤ × ℤ)) (m : ℕ) (hm : 0 < m) :
    ∃ a b : Fin m,
      m * (F.filter fun z ↦
        z.1 % (m : ℤ) = (a.val : ℤ) ∨ z.2 % (m : ℤ) = (b.val : ℤ)).card ≤
          2 * F.card := by
  have small_fiber (f : ℤ × ℤ → Fin m) :
      ∃ a, m * (F.filter fun z ↦ f z = a).card ≤ F.card := by
    obtain ⟨a, _, ha⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul
      (s := F) (t := Finset.univ) (f := f)
      (by simpa using Nat.lt_mul_div_succ F.card hm)
    exact ⟨a, (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ ha)).trans (Nat.mul_div_le _ _)⟩
  let residue (x : ℤ) : Fin m :=
    ⟨(x % (m : ℤ)).toNat,
      (Int.toNat_lt (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hm.ne'))).mpr
        (Int.emod_lt_of_pos _ (Int.natCast_pos.mpr hm))⟩
  have residue_val (x : ℤ) : ((residue x).val : ℤ) = x % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr hm.ne'))
  obtain ⟨a, ha⟩ := small_fiber (fun z ↦ residue z.1)
  obtain ⟨b, hb⟩ := small_fiber (fun z ↦ residue z.2)
  simp only [Fin.ext_iff, ← Int.natCast_inj, residue_val] at ha hb
  refine ⟨a, b, ?_⟩
  rw [Finset.filter_or]
  exact (Nat.mul_le_mul_left m (Finset.card_union_le _ _)).trans
    (by simpa only [Nat.mul_add, two_mul] using Nat.add_le_add ha hb)

end TNLean.PEPS.AreaLaw.Geometry
