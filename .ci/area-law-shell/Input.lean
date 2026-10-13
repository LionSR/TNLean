/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finset.Prod
import Lean.Elab.Tactic.Omega

/-!
# Positive scan prefixes as ambient collars

Let T be a nonempty finite lattice target, and let A be the chosen color in
a finite physical domain. The positive-depth prefix of A is precisely the
part of A in the ambient collar outside T. For a negative integer threshold
both sets are empty; for a nonnegative threshold the dilation radius is its
natural value.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
08-scanner.tex, lines 21–29, at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

namespace TNLean.PEPS.AreaLaw

/-- Sites of a finite induced domain. Source: area-law Theorem 1.1. -/
abbrev Site (Λ : Finset (ℤ × ℤ)) := ↥Λ

/-- Integer sup-norm dilation of an ambient finite set, independent of walks
in a domain. Source: area-law Definition 9.3 and the sets `T_j`. -/
def ambientDilation (T : Finset (ℤ × ℤ)) (r : ℕ) : Finset (ℤ × ℤ) :=
  T.biUnion fun x ↦
    (Finset.Icc (x.1 - (r : ℤ)) (x.1 + r)).product
      (Finset.Icc (x.2 - (r : ℤ)) (x.2 + r))

/-- Zero ambient dilation changes no lattice points. -/
@[simp] theorem ambientDilation_zero (T : Finset (ℤ × ℤ)) : ambientDilation T 0 = T := by
  simp [ambientDilation]

end TNLean.PEPS.AreaLaw

namespace TNLean.PEPS.AreaLaw.Scan

/-- Integer sup-norm distance in the ambient lattice. Source: `08-scanner.tex`, lines 13–18. -/
def ambientSupDistance (x y : ℤ × ℤ) : ℤ :=
  max |x.1 - y.1| |x.2 - y.2|

/-- Actual depth relative to the finite nonempty target, independent of the physical graph.
Source: `08-scanner.tex`, lines 13–18 and the sets `T_j` in lines 21–24. -/
def ambientDepth (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x : ℤ × ℤ) : ℤ :=
  T.inf' hT (ambientSupDistance x)

/-- Ambient depth is nonnegative. -/
theorem ambientDepth_nonneg (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x : ℤ × ℤ) :
    0 ≤ ambientDepth T hT x := by
  exact Finset.le_inf' hT _ fun _ _ ↦ (abs_nonneg _).trans (le_max_left _ _)

/-- The depth sublevel set is exactly the manuscript's ambient dilation.
Source: `08-scanner.tex`, lines 21–24. -/
theorem ambientDepth_le_iff_mem_dilation (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (x : ℤ × ℤ) (r : ℕ) :
    ambientDepth T hT x ≤ r ↔ x ∈ ambientDilation T r := by
  rw [ambientDepth, Finset.inf'_le_iff]
  simp only [ambientSupDistance, max_le_iff, abs_le, ambientDilation,
    Finset.mem_biUnion, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  constructor <;> rintro ⟨y, hy, h⟩ <;> exact ⟨y, hy, by omega⟩

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- A full positive-depth prefix, excluding the fixed target. -/
def positiveDepthPrefix (A : Finset V) (depth : V → ℤ) (j : ℤ) : Finset V :=
  A.filter fun x ↦ 0 < depth x ∧ depth x ≤ j

/-- The positive-depth prefix is the chosen color restricted to the ambient
collar. Source: OpenAI, A two-dimensional area law from a global spectral gap,
08-scanner.tex, lines 21–29, at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem positiveDepthPrefix_eq_filter_ambientDilation
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset (Site Λ)) (j : ℤ) :
    positiveDepthPrefix A (fun x ↦ ambientDepth T hT x.val) j =
      A.filter fun x ↦ x.val ∈ (ambientDilation T j.toNat \ T) := by
  simp only [Finset.ext_iff, positiveDepthPrefix, Finset.mem_filter, Finset.mem_sdiff]
  by_cases hj : 0 ≤ j
  · simp only [← ambientDepth_le_iff_mem_dilation T hT, Int.toNat_of_nonneg hj]
    have hzero (x : ℤ × ℤ) : ambientDepth T hT x ≤ 0 ↔ x ∈ T :=
      (ambientDepth_le_iff_mem_dilation T hT x 0).trans
        (Iff.of_eq (congrArg (fun U : Finset (ℤ × ℤ) ↦ x ∈ U) (ambientDilation_zero T)))
    simp [← hzero, not_le, and_comm]
  · simp [Int.toNat_of_nonpos (le_of_lt (lt_of_not_ge hj)),
      fun x : ℤ × ℤ ↦ not_le.mpr
        ((lt_of_not_ge hj).trans_le (ambientDepth_nonneg T hT x))]

/-- The fixed positive-depth comparison prefixes exclude the chosen-color target.
Source: OpenAI, A two-dimensional area law from a global spectral gap,
08-scanner.tex, lines 21–24, at
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem disjoint_target_positiveDepthPrefix
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (A : Finset (Site Λ)) (j : ℤ) :
    Disjoint (A.filter fun x ↦ x.val ∈ T)
      (positiveDepthPrefix A (fun x ↦ ambientDepth T hT x.val) j) := by
  simp +contextual [Finset.disjoint_left, positiveDepthPrefix_eq_filter_ambientDilation hT A j]
  done

#print axioms positiveDepthPrefix_eq_filter_ambientDilation

end TNLean.PEPS.AreaLaw.Scan
