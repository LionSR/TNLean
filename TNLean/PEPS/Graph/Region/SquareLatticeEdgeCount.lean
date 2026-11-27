/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import QICLean.ManyBody.Sites.Lattice.Square

/-!
# Number of edges in an open square lattice

An edge is determined by its initial vertex and its horizontal or vertical
orientation. The resulting bound includes the empty and one-vertex squares.

The coordinate rectangles of the open square lattice (`squareLatticeRectangle`,
`squareLatticeContiguousRectangle`) are recorded here as well.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: the finite edge count
  used in the bound for the doubled Hamiltonian boundary perturbation.
-/

open ManyBody (Edge IsHorizontalSquareLatticeEdge IsVerticalSquareLatticeEdge SquareLatticeVertex
  horizontalSquareLatticeEdge_coords squareLatticeEdge_horizontal_or_vertical squareLatticeGraph
  verticalSquareLatticeEdge_coords)

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

/-! ### Coordinate rectangles of the open square lattice -/

section CoordinateRectangles

open ManyBody (SquareLatticeVertex)

/-- A coordinate rectangle in a finite square lattice, specified by its
horizontal and vertical coordinate sets.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the regions \(R\), \(S\), and
\(T\) are assembled from rectangular \(2\times3\) and \(3\times2\) blocks. -/
def squareLatticeRectangle {width height : ℕ}
    (xs : Finset (Fin width)) (ys : Finset (Fin height)) :
    Finset (SquareLatticeVertex width height) :=
  xs ×ˢ ys

@[simp] theorem mem_squareLatticeRectangle {width height : ℕ}
    (xs : Finset (Fin width)) (ys : Finset (Fin height))
    (v : SquareLatticeVertex width height) :
    v ∈ squareLatticeRectangle xs ys ↔ v.1 ∈ xs ∧ v.2 ∈ ys := by
  simp [squareLatticeRectangle]

@[simp] theorem card_squareLatticeRectangle {width height : ℕ}
    (xs : Finset (Fin width)) (ys : Finset (Fin height)) :
    (squareLatticeRectangle xs ys).card = xs.card * ys.card := by
  simp [squareLatticeRectangle]

/-- A contiguous interval of coordinates in one axis of a finite square lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the normal square-lattice theorem
uses contiguous \(2\times3\) and \(3\times2\) rectangular blocks. -/
def squareLatticeCoordinateInterval {size : ℕ} (start length : ℕ) : Finset (Fin size) :=
  Finset.univ.filter fun i ↦ start ≤ i.1 ∧ i.1 < start + length

@[simp] theorem mem_squareLatticeCoordinateInterval {size : ℕ}
    (start length : ℕ) (i : Fin size) :
    i ∈ squareLatticeCoordinateInterval start length ↔
      start ≤ i.1 ∧ i.1 < start + length := by
  simp [squareLatticeCoordinateInterval]

/-- A contiguous coordinate rectangle in a finite square lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`, where the regions \(R\), \(S\), and
\(T\) are assembled from contiguous \(2\times3\) and \(3\times2\) rectangles. -/
def squareLatticeContiguousRectangle {width height : ℕ}
    (xStart yStart xLength yLength : ℕ) :
    Finset (SquareLatticeVertex width height) :=
  squareLatticeRectangle
    (squareLatticeCoordinateInterval xStart xLength)
    (squareLatticeCoordinateInterval yStart yLength)

@[simp] theorem mem_squareLatticeContiguousRectangle {width height : ℕ}
    (xStart yStart xLength yLength : ℕ)
    (v : SquareLatticeVertex width height) :
    v ∈ squareLatticeContiguousRectangle xStart yStart xLength yLength ↔
      xStart ≤ v.1.1 ∧ v.1.1 < xStart + xLength ∧
        yStart ≤ v.2.1 ∧ v.2.1 < yStart + yLength := by
  simp [squareLatticeContiguousRectangle, and_assoc]

end CoordinateRectangles

end TNLean.PEPS
