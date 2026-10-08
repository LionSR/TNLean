/-
Original formalization from the cited manuscript;
no upstream Lean proof text reused.
Manuscript: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026.
Pinned source: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Manuscript path:
preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex

Provenance-ID: 8758-tnlean.peps.arealaw.geometry.unique_initial_open_region_lattice
Downstream declaration:
TNLean.PEPS.AreaLaw.Geometry.exists_unique_initialOpenRegion_integerPoint
Source labels: prop:two-families
Source: Section 11, lines 154–177, 212–218, 299–323 and 545–559.

OpenAI Codex (GPT-6) assistance was used in this formalization.
-/
/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionBoundaries
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInteriors

/-!
# Unique initial regions at integer lattice points

The actual closed birth regions cover the plane for a nonempty endpoint set.
At the prescribed translated origin, no lattice point lies on a birth-region
boundary. Closed membership therefore gives membership in the open interior,
and pairwise disjointness gives a unique initial region at each lattice point.
The initial ambient family is retained before stars and recursive repairs.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 154–177,
212–218, 299–323 and 545–559.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Every integer lattice point belongs to exactly one actual initial open
region at the prescribed origin, for a nonempty endpoint set.
Source: area-law Section 11, `prop:two-families`, lines 154–177,
212–218, 299–323 and 545–559. -/
theorem exists_unique_initialOpenRegion_integerPoint (k₀ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (hZ : Z.Nonempty) (v : ℤ × ℤ) :
    ∃! i : InitialRegionIndex dyadicOrigin k₀ Z C a b hC h₀,
      integerPoint v ∈ initialOpenRegion dyadicOrigin k₀ Z C a b hC h₀ i := by
  have hcover := initialBirthRegions_cover dyadicOrigin k₀ Z C a b hC h₀ hZ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
    (hcover.symm ▸ Set.mem_univ (integerPoint v))
  have hiopen := (initialBirthRegion_lattice_mem_iff_initialOpenRegion
    k₀ Z C a b hC h₀ i v).mp hi
  refine ⟨i, hiopen, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp
    (initialOpenRegion_pairwise_disjoint dyadicOrigin k₀ Z C a b hC h₀ hji) hj hiopen

end TNLean.PEPS.AreaLaw.Geometry
