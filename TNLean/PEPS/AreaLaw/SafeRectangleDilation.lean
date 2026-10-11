/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles

/-!
# Safety inside a dilated parent rectangle

A safe parent controls every smaller rectangle contained in its dilation,
provided the smaller rectangle's safety radius plus the dilation radius
fits inside the parent's safety radius.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, proof of Proposition 9.5 (`prop:small-box`),
`08-scanner.tex`, lines 707–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the geometric clearance step for the rectangle bootstrap.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Safety passes from a parent to a rectangle in its dilation when the two
radii fit inside the parent's safety radius. Source: `08-scanner.tex`,
lines 723–729, in the proof of Proposition 9.5 (`prop:small-box`). -/
theorem IsSafe.of_subset_dilate {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    {D₀ j : ℕ} {Q Q' : IntRect} (hsafe : IsSafe Λ A D₀ Q)
    (hsub : Q'.toFinset ⊆ (Q.dilate j).toFinset)
    (hbudget : D₀ * Q'.size + j ≤ D₀ * Q.size) : IsSafe Λ A D₀ Q' := by
  intro e he z hz p hp
  by_contra! hnear
  have hzparent : z.1 ∈ (Q.dilate (D₀ * Q.size)).toFinset :=
    Q.toFinset_dilate_mono (d := j + D₀ * Q'.size) (by omega)
      (IntRect.mem_dilate_of_supDist_le (hsub hp) hnear)
  rw [IntRect.toFinset_dilate] at hzparent
  obtain ⟨v, hv, hvz⟩ := Finset.mem_biUnion.mp hzparent
  have hfar := hsafe e he z hz v hv
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hvz
  simp only [Finset.mem_Icc, supDist] at hx hy hfar
  omega

end TNLean.PEPS.AreaLaw
