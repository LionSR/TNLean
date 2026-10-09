/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateRows
import TNLean.PEPS.AreaLaw.Geometry.CellCounting
import TNLean.PEPS.AreaLaw.Geometry.MixedDyadicSquares

/-!
# Strict clearance of dyadic cells in separated templates

Every point of the radius-`j` dilation retains strict sup-norm clearance
`4 D₀ s₀ - j` from the cut endpoints. If `j ≤ s₀` and `D₀ ≥ 1`, each
contained dyadic cell of side at most `s₀` therefore has clearance greater
than `D₀` times its side. The integer inequality uses the endpoints of actual
physical crossing edges, including domains with holes or several components.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4, `08-scanner.tex`, lines 650–655.
Revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A lattice dyadic cell is literally a product of closed integer intervals.
Source: Lemma 9.4, dyadic squares in the template covering. -/
theorem latticeDyadicCell_eq_Icc_product (k : ℕ) (z : ℤ × ℤ) :
    latticeDyadicCell k z =
      Finset.Icc (z.1 * 2 ^ k) (z.1 * 2 ^ k + 2 ^ k - 1) ×ˢ
        Finset.Icc (z.2 * 2 ^ k) (z.2 * 2 ^ k + 2 ^ k - 1) := by
  ext p
  simp only [mem_latticeDyadicCell_iff_bounds, Finset.mem_product, Finset.mem_Icc]
  omega

/-- The two integer intervals defining a dyadic cell are nonempty and each
has exactly `2^k` sites. Source: Lemma 9.4, side lengths of covering squares. -/
theorem latticeDyadicCell_interval_length (k : ℕ) (a : ℤ) :
    a * 2 ^ k ≤ a * 2 ^ k + 2 ^ k - 1 ∧
      (a * 2 ^ k + 2 ^ k - 1 + 1 - a * 2 ^ k).toNat = 2 ^ k := by
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  constructor
  · omega
  · have h : a * 2 ^ k + 2 ^ k - 1 + 1 - a * 2 ^ k = 2 ^ k := by omega
    rw [h]
    norm_cast

/-- Dilation by `j` reduces strict template clearance by at most `j`.
Source: Lemma 9.4, lines 652–654. No upper bound on `j` is needed here. -/
theorem Template.IsSeparated.lt_dist_of_mem_ambientDilation
    {Ctpl D₀ : ℝ} {n s₀ j : ℕ} {T : Template Ctpl n s₀}
    {Z : Finset (ℤ × ℤ)} (hsep : T.IsSeparated D₀ Z)
    {x z : ℤ × ℤ} (hx : x ∈ ambientDilation T.points j) (hz : z ∈ Z) :
    4 * D₀ * s₀ - j < max |(x.1 : ℝ) - z.1| |(x.2 : ℝ) - z.2| := by
  obtain ⟨p, hp, hcoord⟩ := mem_ambientDilation_iff.mp hx
  have hcoord' : |(p.1 : ℝ) - x.1| ≤ j ∧ |(p.2 : ℝ) - x.2| ≤ j := by
    rw [abs_le, abs_le]
    exact_mod_cast (show (-(j : ℤ) ≤ p.1 - x.1 ∧ p.1 - x.1 ≤ j) ∧
      (-(j : ℤ) ≤ p.2 - x.2 ∧ p.2 - x.2 ≤ j) by omega)
  have hbound : max |(p.1 : ℝ) - z.1| |(p.2 : ℝ) - z.2| ≤
      j + max |(x.1 : ℝ) - z.1| |(x.2 : ℝ) - z.2| := by
    apply max_le
    · exact (abs_sub_le _ _ _).trans
        (add_le_add hcoord'.1 (le_max_left _ _))
    · exact (abs_sub_le _ _ _).trans
        (add_le_add hcoord'.2 (le_max_right _ _))
  have h := hsep p hp z hz
  linarith

/-- A permitted dilation has more than `D₀ u` clearance for every side
`u ≤ s₀`. Source: Lemma 9.4, lines 650–655; the standing `D₀ > 2R+10`
implies the sufficient condition `1 ≤ D₀`. -/
theorem Template.IsSeparated.side_lt_dist_of_mem_ambientDilation
    {Ctpl D₀ : ℝ} {n s₀ j u : ℕ} {T : Template Ctpl n s₀}
    {Z : Finset (ℤ × ℤ)} (hsep : T.IsSeparated D₀ Z) (hD : 1 ≤ D₀)
    (hj : j ≤ s₀) (hu : u ≤ s₀)
    {x z : ℤ × ℤ} (hx : x ∈ ambientDilation T.points j) (hz : z ∈ Z) :
    D₀ * u < max |(x.1 : ℝ) - z.1| |(x.2 : ℝ) - z.2| := by
  have hclear := hsep.lt_dist_of_mem_ambientDilation hx hz
  have hj' : (j : ℝ) ≤ s₀ := by exact_mod_cast hj
  have hu' : (u : ℝ) ≤ s₀ := by exact_mod_cast hu
  have hs : (0 : ℝ) < s₀ := by exact_mod_cast T.s₀_pos
  have hmul := mul_le_mul_of_nonneg_left hu' (by linarith : 0 ≤ D₀)
  have hscale := mul_le_mul_of_nonneg_right hD hs.le
  nlinarith

/-- Every site of a contained dyadic cell has the strict integer clearance
required at every endpoint of a physical crossing edge.
Source: Lemma 9.4, lines 650–655. -/
theorem Template.IsSeparated.dyadicCell_clearance
    {Ctpl : ℝ} {n s₀ D₀ j k : ℕ} {T : Template Ctpl n s₀}
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    (hsep : T.IsSeparated (D₀ : ℝ) (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (hj : j ≤ s₀) (hk : 2 ^ k ≤ s₀) {c : ℤ × ℤ}
    (hcell : latticeDyadicCell k c ⊆ ambientDilation T.points j) :
    ∀ e ∈ edgeBoundary Λ A, ∀ z ∈ e, ∀ p ∈ latticeDyadicCell k c,
      D₀ * 2 ^ k < max (p.1 - z.1.1).natAbs (p.2 - z.1.2).natAbs := by
  intro e he z hz p hp
  have h := hsep.side_lt_dist_of_mem_ambientDilation
    (by exact_mod_cast hD) hj hk (hcell hp)
    (mem_boundaryEndpoints_of_mem_edgeBoundary he hz)
  have hcast : ((D₀ * 2 ^ k : ℕ) : ℝ) <
      ((max (p.1 - z.1.1).natAbs (p.2 - z.1.2).natAbs : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_max,
      Nat.cast_natAbs, Int.cast_abs, Int.cast_sub] using h
  exact_mod_cast hcast

end TNLean.PEPS.AreaLaw.Geometry
