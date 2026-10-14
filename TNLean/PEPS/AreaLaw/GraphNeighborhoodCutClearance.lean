/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.AmbientDepth
import TNLean.PEPS.AreaLaw.Geometry.CellCounting

/-!
# Graph neighborhoods separated from physical cuts

A graph neighborhood of the part of an ambient target collar inside a cut
stays inside the cut and the enlarged collar whenever every cut endpoint is
farther from the target than the sum of the two radii. The estimate applies
to arbitrary finite induced domains, including holes and disconnected parts.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`10-geometry.tex`, lines 815–838, at immutable revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proof is independently written from the manuscript; no upstream Lean
proof text is reused. The ordered two-family construction and separation
from the earlier pieces are further geometric inputs.
-/

namespace TNLean.PEPS.AreaLaw

/-- A graph neighborhood of the part of an ambient target collar inside a cut
remains inside that cut and inside the enlarged ambient collar, provided every
physical cut endpoint is farther from the target than the two radii together.
No connectedness, convexity or target-nonemptiness assumption is required.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`10-geometry.tex`, lines 815–838, immutable revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the cut-exclusion and ambient-distance implication; the ordered
partition and the earlier-family clearance estimates are separate results. -/
theorem graphNeighborhood_subset_of_cut_clearance
    (Λ T : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (L R : ℕ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((L + R : ℕ) : ℤ) < Scan.ambientSupDistance t z) :
    graphNeighborhood Λ R (A.filter fun x ↦ x.val ∈ ambientDilation T L) ⊆
      A.filter (fun x ↦ x.val ∈ ambientDilation T (L + R)) := by
  classical
  intro x hx
  obtain ⟨y, hy, p, hp⟩ := (Finset.mem_filter.mp hx).2
  rcases Finset.mem_filter.mp hy with ⟨hyA, hyDil⟩
  have hT : T.Nonempty :=
    let ⟨t, ht, _⟩ := Finset.mem_biUnion.mp hyDil
    ⟨t, ht⟩
  have hydepth := (Scan.ambientDepth_le_iff_mem_dilation T hT y.val L).mpr hyDil
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · by_contra hxA
    obtain ⟨u, w, -, -, hcut, p', hp'⟩ := exists_edgeBoundary_of_walk p hyA hxA
    have hz : u.val ∈ Geometry.boundaryEndpoints Λ A :=
      Geometry.mem_boundaryEndpoints_of_mem_edgeBoundary hcut (by simp)
    have hvariation := (Scan.abs_ambientDepth_sub_le_walk_length T hT Subtype.val
      (fun _ _ ↦ Scan.ambientSupDistance_le_one_of_domainGraph_adj) p').trans
        (Int.ofNat_le.mpr (hp'.trans hp))
    obtain ⟨t, ht, hmin⟩ := T.exists_mem_eq_inf' hT (Scan.ambientSupDistance u.val)
    have hdeep : ((L + R : ℕ) : ℤ) < Scan.ambientDepth T hT u.val := by
      simpa only [Scan.ambientDepth, hmin, Scan.ambientSupDistance, abs_sub_comm]
        using hclear t ht u.val hz
    rw [abs_le] at hvariation
    omega
  · apply (Scan.ambientDepth_le_iff_mem_dilation T hT x.val (L + R)).mp
    have hvariation := (Scan.abs_ambientDepth_sub_le_walk_length T hT Subtype.val
      (fun _ _ ↦ Scan.ambientSupDistance_le_one_of_domainGraph_adj) p).trans
        (Int.ofNat_le.mpr hp)
    rw [abs_le] at hvariation
    omega

/-- Clearance from physical cut endpoints and from an entire remote set excludes
both the exterior and that remote set from the graph neighborhood of the target
collar inside the region. In the area-law application, the remote set is the
whole union of the earlier actual regions of the same geometric family.

Source: OpenAI, proof of Theorem 1.1, `10-geometry.tex`, lines 825–838,
immutable revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This auxiliary geometric implication assumes the two clearance estimates;
it does not construct the ordered partition or prove its clearance estimates.
The proof is independently written from the manuscript; no upstream Lean
proof text is reused. -/
theorem exterior_union_subset_graphNeighborhood_compl_of_clearance
    (Λ T : Finset (ℤ × ℤ)) (A J : Finset (Site Λ)) (L R : ℕ)
    (hcut : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
      ((L + R : ℕ) : ℤ) < Scan.ambientSupDistance t z)
    (hremote : ∀ t ∈ T, ∀ x ∈ J,
      ((L + R : ℕ) : ℤ) < Scan.ambientSupDistance t x.val) :
    Aᶜ ∪ J ⊆
      (graphNeighborhood Λ R (A.filter fun x ↦ x.val ∈ ambientDilation T L))ᶜ := by
  have hN := graphNeighborhood_subset_of_cut_clearance Λ T A L R hcut
  simp_all only [Finset.subset_iff, Finset.mem_compl, Finset.mem_union, Finset.mem_filter,
    mem_ambientDilation_iff, Scan.ambientSupDistance, lt_max_iff, lt_abs]
  grind


end TNLean.PEPS.AreaLaw
