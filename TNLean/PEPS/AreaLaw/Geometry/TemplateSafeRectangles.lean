/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicPartition
import TNLean.PEPS.AreaLaw.Geometry.TemplateCutBoundary

/-!
# Safe native rectangles in template coverings

The existing lattice dyadic cells are exactly integer rectangles of size `2^k`.
For a separated template, every rectangle of size at most `s₀` contained in a
permitted dilation is safe. In particular, the actual capped core and shell
partitions consist of safe rectangles. The physical regions are the existing
`rectRegion`, including holes and disconnected domains.

Original proofs from OpenAI, *A two-dimensional area law from a global spectral
gap*, September 24, 2026, Definition 9.3 and Lemma 9.4, `08-scanner.tex`,
lines 546–564 and 641–664, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The sufficient condition `D₀ ≥ 1` follows from the standing `D₀ > 2R + 10`
in `02-initial.tex`, line 225. No upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The native integer rectangle of a lattice dyadic cell, with closed integer
endpoints. Source: Lemma 9.4, the maximal contained dyadic square covering. -/
def latticeDyadicRect (k : ℕ) (z : ℤ × ℤ) : IntRect where
  x₀ := z.1 * (2 : ℤ) ^ k
  x₁ := z.1 * (2 : ℤ) ^ k + (2 : ℤ) ^ k - 1
  y₀ := z.2 * (2 : ℤ) ^ k
  y₁ := z.2 * (2 : ℤ) ^ k + (2 : ℤ) ^ k - 1
  hx := by
    have : 0 < (2 : ℤ) ^ k := by positivity
    omega
  hy := by
    have : 0 < (2 : ℤ) ^ k := by positivity
    omega

/-- The adapter preserves every lattice point, including negative coordinates.
Source: Lemma 9.4, lines 641–649. -/
@[simp] theorem toFinset_latticeDyadicRect (k : ℕ) (z : ℤ × ℤ) :
    (latticeDyadicRect k z).toFinset = latticeDyadicCell k z := by
  rcases z with ⟨a, b⟩
  ext p
  rw [IntRect.mem_toFinset, mem_latticeDyadicCell]
  simp only [latticeDyadicRect, dyadicAncestor, Prod.mk.injEq,
    Int.ediv_eq_iff_of_pos (by positivity : 0 < (2 : ℤ) ^ k)]
  omega

/-- Rectangle size counts sites along an axis, so a side-`2^k` cell has size
exactly `2^k`, rather than its coordinate diameter `2^k - 1`. -/
@[simp] theorem size_latticeDyadicRect (k : ℕ) (z : ℤ × ℤ) :
    (latticeDyadicRect k z).size = 2 ^ k := by
  have h (a : ℤ) : (a + (2 : ℤ) ^ k - 1 + 1 - a).toNat = 2 ^ k := by
    have he : a + (2 : ℤ) ^ k - 1 + 1 - a = (2 : ℤ) ^ k := by omega
    rw [he, Int.toNat_pow_of_nonneg (by norm_num)]
    rfl
  simp only [IntRect.size, latticeDyadicRect, h, max_self]

/-- Physical intersections use the same native rectangle region as the safe-box
entropy interface; no ambient sites outside the domain are added. -/
theorem rectRegion_latticeDyadicRect {Λ : Finset (ℤ × ℤ)}
    (A : Finset (Site Λ)) (k : ℕ) (z : ℤ × ℤ) :
    rectRegion A (latticeDyadicRect k z) = A.filter (fun x ↦ x.1 ∈ latticeDyadicCell k z) := by
  simp only [rectRegion, toFinset_latticeDyadicRect]

private theorem cast_supDist (p z : ℤ × ℤ) :
    (supDist p z : ℝ) = max |(p.1 : ℝ) - z.1| |(p.2 : ℝ) - z.2| := by
  simp only [supDist, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]

private theorem supDist_triangle (p x z : ℤ × ℤ) :
    supDist p z ≤ supDist p x + supDist x z := by
  have hx := Int.natAbs_add_le (p.1 - x.1) (x.1 - z.1)
  have hy := Int.natAbs_add_le (p.2 - x.2) (x.2 - z.2)
  simp only [sub_add_sub_cancel] at hx hy
  exact max_le
    (hx.trans (Nat.add_le_add (le_max_left _ _) (le_max_left _ _)))
    (hy.trans (Nat.add_le_add (le_max_right _ _) (le_max_right _ _)))

/-- Ambient clearance after dilation, for the source's real separation constant.
This is Lemma 9.4, lines 651–655. No integrality of `D₀` is required. -/
theorem Template.IsSeparated.clearance_ambientDilation {Ctpl D₀ : ℝ} {n s₀ : ℕ}
    {T : Template Ctpl n s₀} {Z : Finset (ℤ × ℤ)}
    (hsep : T.IsSeparated D₀ Z) (hD : 1 ≤ D₀)
    (j : ℕ) (hj : j ≤ s₀) {x z : ℤ × ℤ}
    (hx : x ∈ ambientDilation T.points j) (hz : z ∈ Z) :
    D₀ * s₀ < max |(x.1 : ℝ) - z.1| |(x.2 : ℝ) - z.2| := by
  obtain ⟨p, hp, hcoord⟩ := mem_ambientDilation_iff.mp hx
  have hnear : supDist p x ≤ j := by
    simp only [supDist]
    omega
  have hsep' := hsep p hp z hz
  rw [← cast_supDist] at hsep' ⊢
  have htri : (supDist p z : ℝ) ≤ j + (supDist x z : ℝ) := by
    exact_mod_cast (supDist_triangle p x z).trans (Nat.add_le_add_right hnear _)
  have hscale : (s₀ : ℝ) ≤ D₀ * s₀ := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg s₀ : (0 : ℝ) ≤ s₀)
  have hj' : (j : ℝ) ≤ s₀ := by exact_mod_cast hj
  nlinarith

/-- Every sufficiently small native rectangle contained in a permitted dilation
is safe, with safety derived from template separation. This is the clearance
step of Lemma 9.4, lines 651–655, and uses no geometric regularity premise. -/
theorem Template.IsSeparated.isSafe_of_subset_ambientDilation
    {Ctpl : ℝ} {n s₀ D₀ : ℕ} {T : Template Ctpl n s₀}
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j : ℕ) (hj : j ≤ s₀) (Q : IntRect)
    (hQ : Q.toFinset ⊆ ambientDilation T.points j) (hsize : Q.size ≤ s₀) :
    IsSafe Λ A D₀ Q := by
  intro e he z hz p hp
  have hclear := hsep.clearance_ambientDilation (by exact_mod_cast hD) j hj (hQ hp)
    (mem_boundaryEndpoints_of_mem_edgeBoundary he hz)
  rw [← cast_supDist] at hclear
  have hdist : D₀ * s₀ < supDist p z.1 := by exact_mod_cast hclear
  exact (Nat.mul_le_mul_left D₀ hsize).trans_lt hdist

/-- Every cell of the actual capped core partition is a safe native rectangle.
Containment and size are derived from selection, not assumed of the cover.
Source: Lemma 9.4, lines 651–664. -/
theorem Template.IsSeparated.isSafe_cappedDyadicPartition_core
    {Ctpl : ℝ} {n s₀ D₀ : ℕ} {T : Template Ctpl n s₀}
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (K k : ℕ) (z : ℤ × ℤ) (hcap : 2 ^ K ≤ s₀)
    (hcell : (k, z) ∈ cappedDyadicPartition T.points K) :
    IsSafe Λ A D₀ (latticeDyadicRect k z) := by
  obtain ⟨hk, hsub, _⟩ := (mem_cappedDyadicPartition _ _ _ _).mp hcell
  apply hsep.isSafe_of_subset_ambientDilation hD 0 (Nat.zero_le s₀)
  · simpa only [toFinset_latticeDyadicRect, ambientDilation_zero] using hsub
  · rw [size_latticeDyadicRect]
    exact (Nat.pow_le_pow_right (by decide) hk).trans hcap

/-- Every cell of the actual capped shell partition is a safe native rectangle,
including cap zero and disconnected shells. Source: Lemma 9.4, lines 651–655. -/
theorem Template.IsSeparated.isSafe_cappedDyadicPartition_shell
    {Ctpl : ℝ} {n s₀ D₀ : ℕ} {T : Template Ctpl n s₀}
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j K k : ℕ) (z : ℤ × ℤ) (hj : j ≤ s₀) (hcap : 2 ^ K ≤ s₀)
    (hcell : (k, z) ∈ cappedDyadicPartition (ambientDilation T.points j \ T.points) K) :
    IsSafe Λ A D₀ (latticeDyadicRect k z) := by
  obtain ⟨hk, hsub, _⟩ := (mem_cappedDyadicPartition _ _ _ _).mp hcell
  apply hsep.isSafe_of_subset_ambientDilation hD j hj
  · simpa only [toFinset_latticeDyadicRect] using hsub.trans Finset.sdiff_subset
  · rw [size_latticeDyadicRect]
    exact (Nat.pow_le_pow_right (by decide) hk).trans hcap

end TNLean.PEPS.AreaLaw.Geometry
