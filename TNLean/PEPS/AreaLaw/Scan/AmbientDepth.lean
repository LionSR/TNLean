/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteDomain
import TNLean.PEPS.AreaLaw.Scan.PhysicalPartition
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Group.Abs

/-!
# Ambient depth of the actual scan rows

Depth is the minimum integer sup-norm distance to the nonempty ambient target.
It varies by at most the length of a graph walk when adjacent coordinates differ
by at most one. Hence every graph ball has the required depth variation, even
when the physical graph has holes or disconnected components. Positive-depth
rows inject into the corresponding difference of ambient dilations, so the
manuscript's ambient row bound applies to the fixed physical row lists.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 13–18, 43–59, 83–137, and 331–337, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The manuscript's nonempty core `X = A ∩ T` supplies target nonemptiness by
`Finset.Nonempty.mono Finset.inter_subset_right`. The accepted polygonal
`Geometry.Template` also requires its whole point set to be nonempty, while
allowing individual sampled pieces to be empty. No empty-target distance
convention is needed for the scanner.
These are the geometric inputs to the scan, not the full histories lemma.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- Integer sup-norm distance in the ambient lattice. Source: `08-scanner.tex`, lines 13–18. -/
def ambientSupDistance (x y : ℤ × ℤ) : ℤ :=
  max |x.1 - y.1| |x.2 - y.2|

/-- Actual depth relative to the finite nonempty target, independent of the physical graph.
Source: `08-scanner.tex`, lines 13–18 and the sets `T_j` in lines 21–24. -/
def ambientDepth (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x : ℤ × ℤ) : ℤ :=
  T.inf' hT (ambientSupDistance x)

private theorem ambientSupDistance_comm (x y : ℤ × ℤ) :
    ambientSupDistance x y = ambientSupDistance y x := by
  simp only [ambientSupDistance, abs_sub_comm]

private theorem ambientSupDistance_triangle (x y z : ℤ × ℤ) :
    ambientSupDistance x z ≤ ambientSupDistance x y + ambientSupDistance y z := by
  unfold ambientSupDistance
  exact max_le
    ((abs_sub_le _ _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
    ((abs_sub_le _ _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _)))

/-- Ambient depth is nonnegative. -/
theorem ambientDepth_nonneg (T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (x : ℤ × ℤ) :
    0 ≤ ambientDepth T hT x := by
  exact Finset.le_inf' hT _ fun _ _ ↦ (abs_nonneg _).trans (le_max_left _ _)

private theorem ambientDepth_le_add (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (x y : ℤ × ℤ) :
    ambientDepth T hT x ≤ ambientSupDistance x y + ambientDepth T hT y := by
  obtain ⟨z, hz, hmin⟩ := T.exists_mem_eq_inf' hT (ambientSupDistance y)
  calc
    ambientDepth T hT x ≤ ambientSupDistance x z := Finset.inf'_le _ hz
    _ ≤ ambientSupDistance x y + ambientSupDistance y z :=
      ambientSupDistance_triangle _ _ _
    _ = ambientSupDistance x y + ambientDepth T hT y := by rw [ambientDepth, hmin]

/-- Distance to the target changes by no more than the ambient displacement.
Source: the depth comparison used in `08-scanner.tex`, lines 331–337. -/
theorem abs_ambientDepth_sub_le (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (x y : ℤ × ℤ) :
    |ambientDepth T hT x - ambientDepth T hT y| ≤ ambientSupDistance x y := by
  have hxy := ambientDepth_le_add T hT x y
  have hyx := ambientDepth_le_add T hT y x
  rw [ambientSupDistance_comm y x] at hyx
  rw [abs_le]
  omega

/-- The depth sublevel set is exactly the manuscript's ambient dilation.
Source: `08-scanner.tex`, lines 21–24. -/
theorem ambientDepth_le_iff_mem_dilation (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (x : ℤ × ℤ) (r : ℕ) :
    ambientDepth T hT x ≤ r ↔ x ∈ ambientDilation T r := by
  rw [ambientDepth, Finset.inf'_le_iff]
  simp only [ambientSupDistance, max_le_iff, abs_le, ambientDilation,
    Finset.mem_biUnion, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  constructor <;> rintro ⟨y, hy, h⟩ <;> exact ⟨y, hy, by omega⟩

/-- A positive-depth row is exactly one ambient dilation layer.
Source: the row hypothesis in `08-scanner.tex`, lines 43–48. -/
theorem ambientDepth_eq_iff_mem_dilation_sdiff (T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (x : ℤ × ℤ) {d : ℕ} (hd : 0 < d) :
    ambientDepth T hT x = d ↔ x ∈ ambientDilation T d \ ambientDilation T (d - 1) := by
  rw [Finset.mem_sdiff, ← ambientDepth_le_iff_mem_dilation T hT,
    ← ambientDepth_le_iff_mem_dilation T hT]
  omega

variable {V : Type*} {G : SimpleGraph V}

/-- Graph walks control actual ambient depth without any connectedness or convexity assumption.
Source: `08-scanner.tex`, graph balls in lines 125–137 and the use in lines 331–337. -/
theorem abs_ambientDepth_sub_le_walk_length (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (coord : V → ℤ × ℤ)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → ambientSupDistance (coord x) (coord y) ≤ 1)
    {x y : V} (p : G.Walk x y) :
    |ambientDepth T hT (coord x) - ambientDepth T hT (coord y)| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
      calc
        |ambientDepth T hT (coord x) - ambientDepth T hT (coord z)| ≤
            |ambientDepth T hT (coord x) - ambientDepth T hT (coord y)| +
              |ambientDepth T hT (coord y) - ambientDepth T hT (coord z)| :=
          abs_sub_le _ _ _
        _ ≤ 1 + (p.length : ℤ) :=
          add_le_add ((abs_ambientDepth_sub_le T hT _ _).trans (hstep hxy)) ih
        _ = (SimpleGraph.Walk.cons hxy p).length := by simp [add_comm]

/-- Every site in a graph `r₀`-ball has ambient depth within `r₀` of the anchor's depth.
The extended graph metric excludes disconnected pairs from finite-radius balls.
Source: the sampling-window argument in `08-scanner.tex`, lines 331–337. -/
theorem abs_ambientDepth_sub_le_of_edist_le (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (coord : V → ℤ × ℤ)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → ambientSupDistance (coord x) (coord y) ≤ 1)
    {x anchor : V} {r₀ : ℕ} (hx : G.edist x anchor ≤ (r₀ : ℕ∞)) :
    |ambientDepth T hT (coord x) - ambientDepth T hT (coord anchor)| ≤ r₀ := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (by simp) hx)
  have hlength : p.length ≤ r₀ := ENat.natCast_le_natCast.mp (hp.le.trans hx)
  exact (abs_ambientDepth_sub_le_walk_length T hT coord hstep p).trans
    (Int.ofNat_le.mpr hlength)

/-- Ambient coordinate steps in the actual induced domain graph have sup norm at most one.
Source: the induced nearest-neighbor domain and `08-scanner.tex`, lines 13–18. -/
theorem ambientSupDistance_le_one_of_domainGraph_adj {Λ : Finset (ℤ × ℤ)}
    {x y : Site Λ} (hxy : (domainGraph Λ).Adj x y) :
    ambientSupDistance x.val y.val ≤ 1 := by
  simp only [domainGraph] at hxy
  simp only [ambientSupDistance, max_le_iff, abs_le]
  rcases hxy with ⟨h₁, h₂ | h₂⟩ | ⟨h₁, h₂ | h₂⟩ <;> omega

/-- The actual induced-domain graph ball satisfies the scanner's depth estimate.
No Lipschitz estimate or coordinate-step certificate is an input to this specialization.
Source: `08-scanner.tex`, lines 13–18, 125–137, and 331–337. -/
theorem abs_ambientDepth_sub_le_domainGraph (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    {Λ : Finset (ℤ × ℤ)} {x anchor : Site Λ} {r₀ : ℕ}
    (hx : (domainGraph Λ).edist x anchor ≤ (r₀ : ℕ∞)) :
    |ambientDepth T hT x.val - ambientDepth T hT anchor.val| ≤ r₀ :=
  abs_ambientDepth_sub_le_of_edist_le T hT Subtype.val
    (fun _ _ ↦ ambientSupDistance_le_one_of_domainGraph_adj) hx

variable [Fintype V]

/-- The actual fixed physical row has at most as many entries as its ambient dilation layer.
The injective coordinates are the inclusion of the physical domain in the lattice.
Source: `08-scanner.tex`, lines 43–48 and 83–87. -/
theorem depthRow_ambientDepth_length_le (T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
    (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord) {d : ℕ} (hd : 0 < d) :
    (depthRow (fun x ↦ ambientDepth T hT (coord x)) d).length ≤
      (ambientDilation T d \ ambientDilation T (d - 1)).card := by
  classical
  rw [depthRow, Finset.length_toList]
  apply Finset.card_le_card_of_injOn coord _ hcoord.injOn
  intro x hx
  exact (ambientDepth_eq_iff_mem_dilation_sdiff T hT (coord x) hd).mp
    (Finset.mem_filter.mp hx).2

/-- The ambient row assumption supplies the scanner's fixed padding bound on every physical row.
Source: `scanner:test-geometry` and fixed row padding, `08-scanner.tex`, lines 43–48 and 83–87. -/
theorem depthRow_ambientDepth_length_le_of_row_bound (T : Finset (ℤ × ℤ))
    (hT : T.Nonempty) (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    {n L : ℕ}
    (hrow : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ n)
    {d : ℕ} (hd : 1 ≤ d) (hdL : d ≤ L) :
    (depthRow (fun x ↦ ambientDepth T hT (coord x)) d).length ≤ n :=
  (depthRow_ambientDepth_length_le T hT coord hcoord hd).trans (hrow d hd hdL)

end TNLean.PEPS.AreaLaw.Scan
