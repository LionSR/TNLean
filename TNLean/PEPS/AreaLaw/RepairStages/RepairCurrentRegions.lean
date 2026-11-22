/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RepairStages.RepairDescendantCounts
import TNLean.PEPS.AreaLaw.RepairStages.RepairStageSites
import TNLean.PEPS.AreaLaw.Layers.DummyContacts

/-!
# Current regions and closed removal sets

At each repair generation, the current region of an identifier lies in its
remembered closed birth. Initially and for fresh replacements, the current
region is the interior of that birth. An old current region only loses the
closed removal squares, while its remembered birth is retained. A finite
mark family gives a closed union of removal squares. Finiteness of the actual
mark families therefore preserves openness of every current region.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, initial regions, lines 172–177, 212–218 and
313–316; replacement instructions, lines 393–417; and remembered closed
births and current open regions, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Counting the surviving dummy sites

The current dummy region is contained in its initial closed birth. Every
lattice site in that birth lies within sup distance (C + 1) 2^k₀ of a boundary
endpoint. Counting these integer neighborhoods bounds the surviving dummy
sites uniformly over all repair generations. Restriction to the finite cut
can only decrease their number.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, initial dummy region, lines 172–177, and
`geometry:bad-sites`, lines 694–707.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The removal set of a finite family of marks is closed.
Source: area-law Section 11, `geometry:trim-radius`, lines 393–399. -/
theorem isClosed_repairRemovalSet {K : Type*} [Finite K]
    (v : K → ℝ × ℝ) (S : K → ℝ) : IsClosed (repairRemovalSet v S) := by
  exact isClosed_iUnion_of_finite (fun _ ↦ Metric.isClosed_closedBall)

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- Every actual current region is contained in its remembered birth.
Source: area-law Section 11, lines 172–177, 212–218, 313–316,
393–417 and 558–561. -/
theorem repairStage_current_subset_birth (j : ℕ) (i : (𝔇 j).regionIndex) :
    (𝔇 j).current i ⊆ (𝔇 j).birth i := by
  exact Nat.rec
    (motive := fun j ↦ ∀ i : (𝔇 j).regionIndex, (𝔇 j).current i ⊆ (𝔇 j).birth i)
    (fun _ ↦ interior_subset)
    (fun j ih i ↦ Sum.casesOn i
      (fun x ↦ fun _ hx ↦ ih x hx.1)
      (fun _ ↦ interior_subset)) j i

/-- Every actual current region is open. Old open regions lose a closed
finite union of removal squares; fresh current regions are interiors.
Source: area-law Section 11, initial regions, lines 172–177, 212–218 and
313–316, and replacement instructions, lines 393–417. -/
theorem isOpen_repairStage_current (j : ℕ) (i : (𝔇 j).regionIndex) :
    IsOpen ((𝔇 j).current i) := by
  exact Nat.rec
    (motive := fun j ↦ ∀ i : (𝔇 j).regionIndex, IsOpen ((𝔇 j).current i))
    (fun _ ↦ isOpen_interior)
    (fun j ih i ↦
      letI := finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar j
      Sum.casesOn i
        (fun x ↦ (ih x).sdiff (isClosed_repairRemovalSet (𝔇 j).location (𝔇 j).scale))
        (fun _ ↦ isOpen_interior)) j i

end TNLean.PEPS.AreaLaw.Geometry
end

end

section

noncomputable section

open TNLean.Lattice
open ManyBody (ambientDilation edgeBoundary mem_ambientDilation_iff planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The surviving dummy sites have a bound proportional to the edge boundary,
with a coefficient depending only on the fixed initial scale and dilation.
Source: area-law Section 11, `geometry:bad-sites`, lines 694–707. -/
theorem card_repairStage_dummySites_le (j : ℕ) :
    ((𝔇 j).regionSites Λ A (𝔇 j).dummy).card ≤
      2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 * (edgeBoundary (planeDomainGraph Λ) A).card := by
  classical
  refine (Finset.card_le_card_of_injOn
    (t := ambientDilation (boundaryEndpoints Λ A) ((C + 1) * 2 ^ k₀))
    Subtype.val ?_ (fun _ _ _ _ h ↦ Subtype.ext h)).trans ?_
  · intro x hx
    have hb : ∀ t, (𝔇 t).birth (𝔇 t).dummy =
        closure (dyadicNeighborhood o k₀ (boundaryEndpoints Λ A) C) :=
      Nat.rec rfl (fun _ ih ↦ ih)
    have hbirth := repairStage_current_subset_birth o Λ A C k₀ hC h₀ Sstar
      j (𝔇 j).dummy (Finset.mem_filter.mp hx).2
    obtain ⟨z, hz, hd⟩ := dyadicNeighborhood_exists_dist_le o k₀
      (boundaryEndpoints Λ A) C (integerPoint x.val) ((hb j) ▸ hbirth)
    simp only [integerPoint, Prod.dist_eq, Real.dist_eq, max_le_iff] at hd
    have hi : |x.val.1 - z.1| ≤ (((C + 1) * 2 ^ k₀ : ℕ) : ℤ) ∧
        |x.val.2 - z.2| ≤ (((C + 1) * 2 ^ k₀ : ℕ) : ℤ) := by
      exact_mod_cast hd
    refine mem_ambientDilation_iff.mpr ⟨z, hz, ?_⟩
    simp only [abs_le] at hi
    omega
  · refine (card_ambientDilation_le (boundaryEndpoints Λ A) ((C + 1) * 2 ^ k₀)).trans ?_
    simpa only [Nat.mul_assoc, Nat.mul_left_comm] using
      Nat.mul_le_mul_left ((2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2)
        (card_boundaryEndpoints_le Λ A)

end TNLean.PEPS.AreaLaw.Geometry
end

end
