/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.LatticeDyadicRect
import TNLean.PEPS.AreaLaw.Geometry.TemplateCutBoundary

/-!
# Safe native rectangles in template coverings

The lattice dyadic cells are integer rectangles of size `2^k`
(`TNLean.PEPS.AreaLaw.Geometry.LatticeDyadicRect`).
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

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem cast_supDist (p z : ℤ × ℤ) :
    (supDist p z : ℝ) = max |(p.1 : ℝ) - z.1| |(p.2 : ℝ) - z.2| := by
  simp only [supDist, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]

/-- Every sufficiently small native rectangle contained in a permitted dilation
is safe, with safety derived from template separation. This is the clearance
step of Lemma 9.4, lines 651–655, and uses no geometric regularity premise.
For separation bounds written as real literals, specify `(T := T) (D₀ := D₀)`
when applying this theorem or its core and shell consequences. -/
theorem Template.IsSeparated.isSafe_of_subset_ambientDilation
    {Ctpl : ℝ} {n s₀ D₀ : ℕ} {T : Template Ctpl n s₀}
    {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j : ℕ) (hj : j ≤ s₀) (Q : IntRect)
    (hQ : Q.toFinset ⊆ ambientDilation T.points j) (hsize : Q.size ≤ s₀) :
    IsSafe Λ A D₀ Q := by
  intro e he z hz p hp
  have hclear := hsep.side_lt_dist_of_mem_ambientDilation
    (by exact_mod_cast hD) hj hsize (hQ hp)
    (mem_boundaryEndpoints_of_mem_edgeBoundary he hz)
  rw [← cast_supDist] at hclear
  exact_mod_cast hclear

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
