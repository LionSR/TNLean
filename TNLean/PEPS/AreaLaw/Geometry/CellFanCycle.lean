/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.FanRunContacts
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Perimeter order of midpoint-subdivided cell fans

Numbering the two halves of each of the four whole sides in perimeter order
transports the rotation of eight positions to the existing fan slots. Final
perimeter endpoints are distinct even for an arbitrary optional midpoint
subdivision: a repeated endpoint would force two distinct fan triangles to
share both their center and that endpoint, contradicting their contact
classification and elementary-side nondegeneracy. In the all-midpoint fan,
ordered endpoint adjacency is exactly the successor relation.

## References

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 361–370.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Manuscript file:
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/`
`build/sections/10-geometry.tex`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- Final perimeter endpoints are distinct for the actual optional fan.
Source: Section 11, `prop:two-families`, lines 299–323, and
`geometry:initial-stars`, lines 361–370. -/
theorem cellFanEnd_injective (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (split : Fin 4 → Bool) : Function.Injective (cellFanEnd o ℓ z split) := by
  intro i j he
  by_contra hij
  have hn := norm_sub_cellFanCenter_of_mem_base o ℓ z split i
    (right_mem_segment ℝ (cellFanStart o ℓ z split i) (cellFanEnd o ℓ z split i))
  have hce : cellFanEnd o ℓ z split i ≠ cellFanCenter o ℓ z :=
    sub_ne_zero.mp (norm_pos_iff.mp
      (hn.symm ▸ div_pos (pow_pos zero_lt_two ℓ) zero_lt_two))
  have hvertices (s : CellFanSlot split) :
      cellFanCenter o ℓ z ∈ (cellFanPolygon o ℓ z split s).region ∧
        cellFanEnd o ℓ z split s ∈ (cellFanPolygon o ℓ z split s).region :=
    ⟨subset_convexHull ℝ _ (Or.inl rfl),
      subset_convexHull ℝ _ (Or.inr (Or.inr rfl))⟩
  have hcontact : ((cellFanPolygon o ℓ z split i).region ∩
      (cellFanPolygon o ℓ z split j).region).Nontrivial :=
    Set.nontrivial_of_mem_mem_ne
      ⟨(hvertices i).2, Set.mem_of_eq_of_mem he (hvertices j).2⟩
      ⟨(hvertices i).1, (hvertices j).1⟩ hce
  rcases cellFanPolygons_nontrivial_inter_cases o ℓ z split i j hij hcontact with
    ⟨hadj, _⟩ | ⟨hadj, _⟩
  · exact (cellFan_elementary_geometry o ℓ z split j).1 (hadj.symm.trans he)
  · exact (cellFan_elementary_geometry o ℓ z split i).1 (hadj.symm.trans he.symm)


/-- Number the actual all-midpoint slots in perimeter order.
Source: area-law Section 11, lines 308–310 and 361–370. -/
private def number : CellFanSlot (fun _ : Fin 4 ↦ true) ≃ Fin 8 :=
  (Equiv.sigmaEquivProd (Fin 4) (Fin 2)).trans finProdFinEquiv

/-- Rotate the eight actual midpoint slots by one perimeter position.
Source: area-law Section 11, lines 361–370. -/
def cellFanNext : Equiv.Perm (CellFanSlot (fun _ : Fin 4 ↦ true)) :=
  (number.trans (finRotate 8)).trans number.symm

/-- The perimeter numbering conjugates the successor to finite rotation.
Source: area-law Section 11, lines 361–370. -/
private theorem number_next (i : CellFanSlot (fun _ : Fin 4 ↦ true)) :
    number (cellFanNext i) = finRotate 8 (number i) := by
  simp only [cellFanNext, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The first half of a side is followed by its second half.
Source: area-law Section 11, lines 308–310 and 361–370. -/
private theorem next_first (s : Fin 4) :
    cellFanNext ⟨s, 0⟩ = ⟨s, 1⟩ := by
  apply number.injective
  rw [number_next]
  fin_cases s <;>
    norm_num [number, Equiv.trans_apply, Equiv.sigmaEquivProd_apply,
      finProdFinEquiv, finRotate_apply]

/-- The last half of a side is followed by the first half of the next side.
Source: area-law Section 11, lines 308–310 and 361–370. -/
private theorem next_last (s : Fin 4) :
    cellFanNext ⟨s, 1⟩ = ⟨s + 1, 0⟩ := by
  apply number.injective
  rw [number_next]
  fin_cases s <;>
    norm_num [number, Equiv.trans_apply, Equiv.sigmaEquivProd_apply,
      finProdFinEquiv, finRotate_apply]

/-- Consecutive whole sides share their oriented corner.
Source: area-law Section 11, lines 299–310. -/
private theorem whole_end_eq_next_start (o : ℝ × ℝ) (ℓ : ℕ)
    (z : ℤ × ℤ) (s : Fin 4) :
    cellFanEnd o ℓ z (fun _ ↦ false) ⟨s, 0⟩ =
      cellFanStart o ℓ z (fun _ ↦ false) ⟨s + 1, 0⟩ := by
  have he := congrArg Prod.snd
    (cellFan_unsplit_endpoints_coordinates o ℓ z s)
  have hs := congrArg Prod.fst
    (cellFan_unsplit_endpoints_coordinates o ℓ z (s + 1))
  fin_cases s <;> norm_num at he hs <;> exact he.trans hs.symm

/-- The final endpoint of a midpoint slot starts the next perimeter slot.
Source: area-law Section 11, lines 308–310 and 361–370. -/
theorem cellFanEnd_eq_cellFanStart_next (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (i : CellFanSlot (fun _ : Fin 4 ↦ true)) :
    cellFanEnd o ℓ z (fun _ ↦ true) i =
      cellFanStart o ℓ z (fun _ ↦ true) (cellFanNext i) := by
  rcases i with ⟨s, h⟩
  fin_cases h
  · change cellFanEnd o ℓ z (fun _ ↦ true) ⟨s, 0⟩ =
      cellFanStart o ℓ z (fun _ ↦ true) (cellFanNext ⟨s, 0⟩)
    rw [next_first]
    have h := And.intro
      (cellFan_elementary_endpoints_lineMap o ℓ z (fun _ ↦ true) ⟨s, 0⟩).2
      (cellFan_elementary_endpoints_lineMap o ℓ z (fun _ ↦ true) ⟨s, 1⟩).1
    norm_num at h
    exact h.1.trans h.2.symm
  · change cellFanEnd o ℓ z (fun _ ↦ true) ⟨s, 1⟩ =
      cellFanStart o ℓ z (fun _ ↦ true) (cellFanNext ⟨s, 1⟩)
    rw [next_last]
    have h := And.intro
      (cellFan_elementary_endpoints_lineMap o ℓ z (fun _ ↦ true) ⟨s, 1⟩).2
      (cellFan_elementary_endpoints_lineMap o ℓ z (fun _ ↦ true) ⟨s + 1, 0⟩).1
    norm_num at h
    exact h.1.trans ((whole_end_eq_next_start o ℓ z s).trans h.2.symm)

/-- Endpoint adjacency is exactly the perimeter successor relation.
Source: area-law Section 11, lines 308–310 and 361–370. -/
theorem cellFanEnd_eq_cellFanStart_iff (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)
    (i j : CellFanSlot (fun _ : Fin 4 ↦ true)) :
    cellFanEnd o ℓ z (fun _ ↦ true) i =
        cellFanStart o ℓ z (fun _ ↦ true) j ↔
      j = cellFanNext i := by
  constructor
  · intro he
    have hp : cellFanEnd o ℓ z (fun _ ↦ true) (cellFanNext.symm j) =
        cellFanStart o ℓ z (fun _ ↦ true) j := by
      simpa only [Equiv.apply_symm_apply] using
        cellFanEnd_eq_cellFanStart_next o ℓ z (cellFanNext.symm j)
    have hi := cellFanEnd_injective o ℓ z (fun _ ↦ true) (he.trans hp.symm)
    simpa only [Equiv.apply_symm_apply] using (congrArg cellFanNext hi).symm
  · rintro rfl
    exact cellFanEnd_eq_cellFanStart_next o ℓ z i

end TNLean.PEPS.AreaLaw.Geometry
