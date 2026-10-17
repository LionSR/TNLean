/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairCurrentRegions
import TNLean.PEPS.AreaLaw.Geometry.RepairStageSites
import TNLean.PEPS.AreaLaw.Geometry.DummyContacts

/-!
# Counting the surviving dummy sites

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

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- The surviving dummy sites have a bound proportional to the edge boundary,
with a coefficient depending only on the fixed initial scale and dilation.
Source: area-law Section 11, `geometry:bad-sites`, lines 694–707. -/
theorem card_repairStage_dummySites_le (j : ℕ) :
    ((𝔇 j).regionSites Λ A (𝔇 j).dummy).card ≤
      2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 * (edgeBoundary Λ A).card := by
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
