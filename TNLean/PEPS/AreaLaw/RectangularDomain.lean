/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteDomain
import TNLean.PEPS.SquareLatticeGraph

/-!
# Open rectangular domains in integer coordinates

The native open rectangular graph is identified with its induced integer
lattice domain. The embedding uses coordinates starting at zero; translating
both coordinates by one gives the convention of the polynomial-PEPS manuscript.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Corollary 1.2.
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Section 1, the open grid `Λ_L`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- The integer-coordinate embedding of the native rectangular vertices.
Source: area-law Corollary 1.2 and polynomial-PEPS Section 1. -/
def rectangleEmbedding {width height : ℕ} (v : SquareLatticeVertex width height) : ℤ × ℤ :=
  ((v.1.val : ℤ), (v.2.val : ℤ))

/-- Integer embedding preserves distinct native vertices. -/
theorem rectangleEmbedding_injective (width height : ℕ) :
    Function.Injective (rectangleEmbedding (width := width) (height := height)) :=
  fun _ _ h ↦ Prod.ext (Fin.ext (Int.ofNat.inj (congrArg Prod.fst h)))
    (Fin.ext (Int.ofNat.inj (congrArg Prod.snd h)))

/-- The finite integer domain of an open rectangle, also when a side is zero.
Source: area-law Corollary 1.2. -/
def rectangularDomain (width height : ℕ) : Finset (ℤ × ℤ) :=
  Finset.univ.image (rectangleEmbedding (width := width) (height := height))

/-- Native vertices and the sites of the induced integer domain are equivalent.
Source: area-law Corollary 1.2 and polynomial-PEPS Section 1. -/
noncomputable def rectangleSiteEquiv (width height : ℕ) :
    SquareLatticeVertex width height ≃ Site (rectangularDomain width height) :=
  (Equiv.ofInjective rectangleEmbedding (rectangleEmbedding_injective width height)).trans
    (Equiv.subtypeEquivRight (by simp [rectangularDomain, Set.mem_range]))

/-- The integer coordinates of a transported native vertex. -/
@[simp] theorem rectangleSiteEquiv_val (width height : ℕ)
    (v : SquareLatticeVertex width height) :
    (rectangleSiteEquiv width height v).val = rectangleEmbedding v := rfl

/-- The open rectangular graph is exactly the induced lattice graph on its domain.
Source: area-law Corollary 1.2 and polynomial-PEPS Section 1. -/
noncomputable def rectangleGraphIso (width height : ℕ) :
    squareLatticeGraph width height ≃g domainGraph (rectangularDomain width height) where
  toEquiv := rectangleSiteEquiv width height
  map_rel_iff' := by
    intro v w
    simp only [domainGraph, rectangleSiteEquiv_val, rectangleEmbedding,
      squareLatticeGraph_adj, squareLatticeHorizontalNeighbor, squareLatticeVerticalNeighbor]
    norm_cast
    simp only [Fin.ext_iff]

/-- Configuration coordinates transported from the native rectangle to its
integer domain. Source: area-law Corollary 1.2 and polynomial-PEPS Section 1. -/
noncomputable def rectangleConfigurationEquiv (width height q : ℕ) :
    (SquareLatticeVertex width height → Fin q) ≃
      Configuration (rectangularDomain width height) q :=
  Equiv.arrowCongr (rectangleSiteEquiv width height) (Equiv.refl (Fin q))

/-- A native nearest-neighbor interaction has the same range-one support in
the induced integer domain. Source: area-law Corollary 1.2. -/
theorem isAdmissibleSupport_rectangle_pair_of_adj {width height : ℕ}
    {v w : SquareLatticeVertex width height} (h : (squareLatticeGraph width height).Adj v w) :
    IsAdmissibleSupport (rectangularDomain width height) 1
      {rectangleSiteEquiv width height v, rectangleSiteEquiv width height w} :=
  isAdmissibleSupport_pair_of_adj ((rectangleGraphIso width height).map_rel_iff.mpr h)

end TNLean.PEPS.AreaLaw
