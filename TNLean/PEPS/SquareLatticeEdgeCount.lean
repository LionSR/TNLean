/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import TNLean.PEPS.SquareLatticeGraph

/-!
# Number of edges in an open square lattice

An edge is determined by its initial vertex and its horizontal or vertical
orientation. The resulting bound includes the empty and one-vertex squares.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: the finite edge count
  used in the bound for the doubled Hamiltonian boundary perturbation.
-/

namespace TNLean.PEPS

/-- An open square of side length `L` has at most `2 * L ^ 2` edges,
including `L = 0` and `L = 1`.

Source: polynomial-PEPS manuscript, the boundary perturbation estimate in
`02-information.tex`, lines 416–424 and 513–524. -/
theorem card_squareLatticeEdges_le (L : ℕ) :
    Fintype.card (Edge (squareLatticeGraph L L)) ≤ 2 * L ^ 2 := by
  classical
  suffices hinj : Function.Injective
      (fun e : Edge (squareLatticeGraph L L) ↦
        (e.1.1, decide (IsHorizontalSquareLatticeEdge e))) by
    simpa [SquareLatticeVertex, pow_two, Nat.mul_comm] using
      Fintype.card_le_of_injective _ hinj
  intro e e' h
  simp only [Prod.mk.injEq, decide_eq_decide] at h
  obtain ⟨hvertex, hiff⟩ := h
  have hfst : e.1.1.1 = e'.1.1.1 := congrArg Prod.fst hvertex
  have hsnd : e.1.1.2 = e'.1.1.2 := congrArg Prod.snd hvertex
  have hsnd2 : e.1.2 = e'.1.2 := by
    by_cases hH : IsHorizontalSquareLatticeEdge e
    · have hH' : IsHorizontalSquareLatticeEdge e' := hiff.1 hH
      obtain ⟨hcy, hcx⟩ := horizontalSquareLatticeEdge_coords e hH
      obtain ⟨hcy', hcx'⟩ := horizontalSquareLatticeEdge_coords e' hH'
      refine Prod.ext_iff.mpr ⟨Fin.ext ?_, ?_⟩
      · have hv : e.1.1.1.1 = e'.1.1.1.1 := congrArg Fin.val hfst
        omega
      · rw [← hcy, ← hcy']; exact hsnd
    · have hV : IsVerticalSquareLatticeEdge e :=
        (squareLatticeEdge_horizontal_or_vertical e).resolve_left hH
      have hH' : ¬ IsHorizontalSquareLatticeEdge e' := fun c => hH (hiff.2 c)
      have hV' : IsVerticalSquareLatticeEdge e' :=
        (squareLatticeEdge_horizontal_or_vertical e').resolve_left hH'
      obtain ⟨hcx, hcy⟩ := verticalSquareLatticeEdge_coords e hV
      obtain ⟨hcx', hcy'⟩ := verticalSquareLatticeEdge_coords e' hV'
      refine Prod.ext_iff.mpr ⟨?_, Fin.ext ?_⟩
      · rw [← hcx, ← hcx']; exact hfst
      · have hv : e.1.1.2.1 = e'.1.1.2.1 := congrArg Fin.val hsnd
        omega
  exact Subtype.ext (Prod.ext_iff.mpr ⟨hvertex, hsnd2⟩)

end TNLean.PEPS
