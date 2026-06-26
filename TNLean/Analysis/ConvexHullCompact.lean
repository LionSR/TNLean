/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The convex hull of a compact set is compact in finite dimension

In a finite-dimensional real normed space the convex hull of a compact set is
itself compact.  This is a standard consequence of Carathéodory's convexity
theorem: every point of the convex hull is a convex combination of at most
`finrank ℝ E + 1` points of the set, so the convex hull is the continuous image
of a compact set of weighted families.

The argument realises `convexHull ℝ s` as the image of the compact set
`stdSimplex ℝ (Fin N) ×ˢ {g | ∀ i, g i ∈ s}` (with `N = finrank ℝ E + 1`) under
the continuous barycentric map `(w, g) ↦ ∑ i, w i • g i`.  The forward inclusion
is Carathéodory's theorem with the affine-independence cardinality bound; the
reverse inclusion holds because each such weighted sum is a convex combination of
points of `s`.

This is a general convex-geometry foundation lemma.  It underlies the
compactness of the set of states of bounded Schmidt number, used in Wolf's
Chapter 3 study of finite-dimensional quantum channels.
-/

open Set FiniteDimensional Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace TNLean

/-- The barycentric map sending a weight vector `w` on the standard simplex and a
family `g` of points to the convex combination `∑ i, w i • g i`. -/
private noncomputable def baryMap (N : ℕ) (p : (Fin N → ℝ) × (Fin N → E)) : E :=
  ∑ i, p.1 i • p.2 i

omit [FiniteDimensional ℝ E] in
private theorem continuous_baryMap (N : ℕ) : Continuous (baryMap (E := E) N) := by
  unfold baryMap
  fun_prop

/-- **The convex hull of a compact set is compact** in a finite-dimensional real
normed space.

Every point of `convexHull ℝ s` is, by Carathéodory's theorem, a convex
combination of at most `finrank ℝ E + 1` points of `s`.  Hence `convexHull ℝ s`
is the image, under the continuous barycentric map, of the product of the
standard simplex on `Fin (finrank ℝ E + 1)` with the (compact) set of families of
points in `s`, and is therefore compact. -/
theorem IsCompact.convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (_root_.convexHull ℝ s) := by
  -- Handle the empty set separately; otherwise we have a base point to pad with.
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp only [convexHull_empty]; exact isCompact_empty
  set N : ℕ := finrank ℝ E + 1 with hN
  -- The compact domain: simplex weights paired with families of points in `s`.
  set K : Set ((Fin N → ℝ) × (Fin N → E)) :=
    stdSimplex ℝ (Fin N) ×ˢ {g : Fin N → E | ∀ i, g i ∈ s} with hK
  have hKpi : {g : Fin N → E | ∀ i, g i ∈ s} = univ.pi (fun _ : Fin N => s) := by
    ext g; simp
  have hKcompact : IsCompact K := by
    rw [hK]
    refine (isCompact_stdSimplex ℝ (Fin N)).prod ?_
    rw [hKpi]
    exact isCompact_univ_pi fun _ => hs
  -- It suffices to identify the convex hull with the image of `K`.
  suffices h : _root_.convexHull ℝ s = baryMap N '' K by
    rw [h]
    exact hKcompact.image (continuous_baryMap N)
  apply Set.Subset.antisymm
  · -- Forward inclusion: Carathéodory plus padding to exactly `N` indices.
    intro x hx
    obtain ⟨ι, _, z, w, hzs, hzindep, hwpos, hwsum, hwx⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    -- The affinely independent family has at most `N` points.
    have hcard : Fintype.card ι ≤ N := by
      calc Fintype.card ι ≤ finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
            AffineIndependent.card_le_finrank_succ hzindep
        _ ≤ finrank ℝ E + 1 := by gcongr; exact (vectorSpan ℝ (Set.range z)).finrank_le
        _ = N := hN.symm
    -- Embed the index type into `Fin N`.
    obtain ⟨e⟩ : Nonempty (ι ↪ Fin N) :=
      Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin]; exact hcard)
    -- Pad the weights with `0` and the points with the base point `x₀`.
    set w' : Fin N → ℝ := Function.extend e w 0 with hw'
    set g' : Fin N → E := Function.extend e z (fun _ => x₀) with hg'
    have hwe : ∀ i, w' (e i) = w i := fun i => e.injective.extend_apply w 0 i
    have hge : ∀ i, g' (e i) = z i := fun i => e.injective.extend_apply z _ i
    have hwoff : ∀ j ∉ Set.range e, w' j = 0 := fun j hj => by
      simp [hw', Function.extend_apply' _ _ _ (by simpa using hj)]
    -- The padded weight vector lies in the standard simplex.
    have hw'mem : w' ∈ stdSimplex ℝ (Fin N) := by
      refine ⟨fun j => ?_, ?_⟩
      · by_cases hj : j ∈ Set.range e
        · obtain ⟨i, rfl⟩ := hj; rw [hwe]; exact (hwpos i).le
        · rw [hwoff j hj]
      · rw [← Fintype.sum_of_injective e e.injective w w' (fun j hj => hwoff j hj)
          (fun i => (hwe i).symm), hwsum]
    -- The padded family takes values in `s`.
    have hg'mem : ∀ j, g' j ∈ s := by
      intro j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj; rw [hge]; exact hzs ⟨i, rfl⟩
      · simp [hg', Function.extend_apply' _ _ _ (by simpa using hj), hx₀]
    -- The barycentric value matches `x`.
    have hval : baryMap N (w', g') = x := by
      unfold baryMap
      have : ∑ j, w' j • g' j = ∑ i, w i • z i := by
        refine (Fintype.sum_of_injective e e.injective (fun i => w i • z i)
          (fun j => w' j • g' j) (fun j hj => ?_) (fun i => ?_)).symm
        · rw [hwoff j hj, zero_smul]
        · rw [hwe, hge]
      rw [this, hwx]
    exact ⟨(w', g'), ⟨hw'mem, hg'mem⟩, hval⟩
  · -- Reverse inclusion: each weighted sum is a convex combination of points of `s`.
    rintro x ⟨⟨w, g⟩, ⟨hw, hg⟩, rfl⟩
    exact mem_convexHull_of_exists_fintype w g hw.1 hw.2 hg rfl

end TNLean
