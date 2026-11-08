/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularDomain
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Rev

/-!
# Snake ordering and its prefix boundaries on an open square grid

Rows are visited in increasing order, with the second coordinate reversed on odd rows.
Every prefix has at most one crossing edge within a row and at most one crossing edge
between rows in each column. Hence its edge boundary has at most `L + 1` edges.

The result includes empty grids, one-site grids, and prefixes beyond the last site.

## References

* The square-grid comparison in *Polynomial PEPS approximation of gapped
  square-grid ground states*, September 24, 2026, Section 1.
* TNLean note, `docs/notes/one_dimensional_note/part2a_mps_information.tex`,
  `sec:shortcut`, `thm:Bshort`, lines 73–92, for the threshold and sequential
  truncation argument used after this geometry.
-/

open TNLean.Lattice TNLean.PEPS TNLean.PEPS.AreaLaw

namespace TNLean.MPS.AreaLaw

private def snakeRowFlip (L : ℕ) (p : Fin L × Fin L) : Fin L × Fin L :=
  (p.1, if p.1.val % 2 = 0 then p.2 else p.2.rev)

private def snakeRowEquiv (L : ℕ) : (Fin L × Fin L) ≃ (Fin L × Fin L) :=
  (show Function.Involutive (snakeRowFlip L) from by
    intro p
    simp [snakeRowFlip]
    split_ifs <;> simp).toPerm

/-- The boustrophedon ordering: even rows run forward and odd rows run backward. -/
def snakeNativeEquiv (L : ℕ) : Fin (L * L) ≃ (Fin L × Fin L) :=
  finProdFinEquiv.symm.trans (snakeRowEquiv L)

/-- The position of a native grid vertex in the snake ordering. -/
def snakeIndex (L : ℕ) (p : Fin L × Fin L) : Fin (L * L) :=
  (snakeNativeEquiv L).symm p

/-- The snake position in row and column coordinates. -/
theorem snakeIndex_val (L : ℕ) (p : Fin L × Fin L) :
    (snakeIndex L p).val = (if p.1.val % 2 = 0 then p.2.val else L - 1 - p.2.val) +
      L * p.1.val := by
  simp [snakeIndex, snakeNativeEquiv, snakeRowEquiv, snakeRowFlip, finProdFinEquiv,
    Function.Involutive.toPerm, Fin.rev]
  split_ifs <;> simp [Nat.sub_sub, Nat.add_comm]

private theorem snakeIndex_row_lt {L : ℕ} {p p' : Fin L × Fin L} (h : p.1.val < p'.1.val) :
    (snakeIndex L p).val < (snakeIndex L p').val := by
  have hoff (p : Fin L × Fin L) :
      (if p.1.val % 2 = 0 then p.2.val else L - 1 - p.2.val) < L := by
    split_ifs <;> omega
  rw [snakeIndex_val, snakeIndex_val]
  have hmul : L * (p.1.val + 1) ≤ L * p'.1.val := Nat.mul_le_mul_left _ h
  have := hoff p
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

private theorem snakeIndex_adj_same_row {L : ℕ} {p p' : Fin L × Fin L}
    (hrow : p.1 = p'.1) (hadj : (squareLatticeGraph L L).Adj p p') :
    (snakeIndex L p).val + 1 = (snakeIndex L p').val ∨
      (snakeIndex L p').val + 1 = (snakeIndex L p).val := by
  rcases hadj with ⟨_, h | h⟩ | ⟨_, h | h⟩
  · have := congrArg Fin.val hrow
    omega
  · have := congrArg Fin.val hrow
    omega
  all_goals
    rw [snakeIndex_val, snakeIndex_val, hrow]
    split_ifs <;> omega

private noncomputable def snakeBoundaryPairs (L k : ℕ) :
    Finset ((Fin L × Fin L) × (Fin L × Fin L)) := by
  classical
  exact Finset.univ.filter fun p ↦ (squareLatticeGraph L L).Adj p.1 p.2 ∧
    (snakeIndex L p.1).val < k ∧ k ≤ (snakeIndex L p.2).val

private theorem boundaryPair_row_lt {L k : ℕ} {p : (Fin L × Fin L) × (Fin L × Fin L)}
    (hp : p ∈ snakeBoundaryPairs L k) (hrow : p.1.1 ≠ p.2.1) :
    p.1.1.val < p.2.1.val := by
  classical
  obtain ⟨_, hadj, hlt, hge⟩ := Finset.mem_filter.mp hp
  by_contra h
  have heq : p.1.1.val ≠ p.2.1.val := fun heq ↦ hrow (Fin.ext heq)
  have hrev := snakeIndex_row_lt (p := p.2) (p' := p.1) (by omega)
  omega

private theorem boundaryPair_same_row_index {L k : ℕ} {p : (Fin L × Fin L) × (Fin L × Fin L)}
    (hp : p ∈ snakeBoundaryPairs L k) (hrow : p.1.1 = p.2.1) :
    (snakeIndex L p.1).val + 1 = k ∧ (snakeIndex L p.2).val = k := by
  classical
  obtain ⟨_, hadj, hlt, hge⟩ := Finset.mem_filter.mp hp
  have h := snakeIndex_adj_same_row hrow hadj
  omega

private theorem boundaryPair_diff_row_column {L k : ℕ} {p : (Fin L × Fin L) × (Fin L × Fin L)}
    (hp : p ∈ snakeBoundaryPairs L k) (hrow : p.1.1 ≠ p.2.1) :
    p.1.2 = p.2.2 ∧ p.1.1.val + 1 = p.2.1.val := by
  classical
  obtain ⟨_, hadj, hlt, hge⟩ := Finset.mem_filter.mp hp
  rcases hadj with ⟨hcol, hadj⟩ | ⟨hrow', _⟩
  · have h := boundaryPair_row_lt hp hrow
    exact ⟨hcol, by omega⟩
  · exact (hrow hrow').elim

private theorem boundaryPairs_diff_row_inj {L k : ℕ} {p p' : (Fin L × Fin L) × (Fin L × Fin L)}
    (hp : p ∈ snakeBoundaryPairs L k) (hp' : p' ∈ snakeBoundaryPairs L k)
    (hrow : p.1.1 ≠ p.2.1) (hrow' : p'.1.1 ≠ p'.2.1)
    (hcol : p.1.2 = p'.1.2) : p = p' := by
  classical
  obtain ⟨hc, hr⟩ := boundaryPair_diff_row_column hp hrow
  obtain ⟨hc', hr'⟩ := boundaryPair_diff_row_column hp' hrow'
  obtain ⟨_, _, hlt, hge⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, _, hlt', hge'⟩ := Finset.mem_filter.mp hp'
  have hrows : p.1.1 = p'.1.1 := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hle : (snakeIndex L p.2).val ≤ (snakeIndex L p'.1).val := by
        rcases lt_or_eq_of_le (show p.2.1.val ≤ p'.1.1.val by omega) with hlt | heq
        · exact (snakeIndex_row_lt hlt).le
        · have he : p.2 = p'.1 := Prod.ext (Fin.ext heq) (hc.symm.trans hcol)
          rw [he]
      omega
    · have hle : (snakeIndex L p'.2).val ≤ (snakeIndex L p.1).val := by
        rcases lt_or_eq_of_le (show p'.2.1.val ≤ p.1.1.val by omega) with hlt | heq
        · exact (snakeIndex_row_lt hlt).le
        · have he : p'.2 = p.1 := Prod.ext (Fin.ext heq) (hc'.symm.trans hcol.symm)
          rw [he]
      omega
  exact Prod.ext (Prod.ext hrows hcol)
    (Prod.ext (Fin.ext (by have := congrArg Fin.val hrows; omega)) (hc.symm.trans (hcol.trans hc')))

private theorem card_snakeBoundaryPairs_le (L k : ℕ) :
    (snakeBoundaryPairs L k).card ≤ L + 1 := by
  classical
  let f : ((Fin L × Fin L) × (Fin L × Fin L)) → Fin (L + 1) := fun p ↦
    if p.1.1 = p.2.1 then ⟨L, by omega⟩ else ⟨p.1.2.val, by omega⟩
  have hf : Set.InjOn f (snakeBoundaryPairs L k : Set _) := by
    intro p hp p' hp' heq
    by_cases hrow : p.1.1 = p.2.1 <;> by_cases hrow' : p'.1.1 = p'.2.1
    · obtain ⟨hu, hv⟩ := boundaryPair_same_row_index hp hrow
      obtain ⟨hu', hv'⟩ := boundaryPair_same_row_index hp' hrow'
      apply Prod.ext
      · apply (snakeNativeEquiv L).symm.injective
        apply Fin.ext
        change (snakeIndex L p.1).val = (snakeIndex L p'.1).val
        omega
      · apply (snakeNativeEquiv L).symm.injective
        apply Fin.ext
        change (snakeIndex L p.2).val = (snakeIndex L p'.2).val
        omega
    · have hval := congrArg Fin.val heq
      simp only [f, hrow, hrow', ↓reduceIte] at hval
      omega
    · have hval := congrArg Fin.val heq
      simp only [f, hrow, hrow', ↓reduceIte] at hval
      omega
    · exact boundaryPairs_diff_row_inj hp hp' hrow hrow' (by
        have hval := congrArg Fin.val heq
        simp only [f, hrow, hrow', ↓reduceIte] at hval
        exact Fin.ext hval)
  simpa using Finset.card_le_card_of_injOn f (t := Finset.univ) (by simp [Set.MapsTo]) hf

/-- The snake ordering of the sites of the actual open integer square domain. -/
noncomputable def snakeGridEquiv (L : ℕ) :
    Fin (L * L) ≃ Site (rectangularDomain L L) :=
  (snakeNativeEquiv L).trans (rectangleSiteEquiv L L)

/-- The first `k` sites in the snake ordering. -/
noncomputable def snakeGridPrefix (L k : ℕ) : Finset (Site (rectangularDomain L L)) := by
  classical
  exact Finset.univ.filter fun v ↦ ((snakeGridEquiv L).symm v).val < k

/-- Membership in a snake prefix is the inequality on its actual ordering position. -/
@[simp] theorem mem_snakeGridPrefix {L k : ℕ} {v : Site (rectangularDomain L L)} :
    v ∈ snakeGridPrefix L k ↔ ((snakeGridEquiv L).symm v).val < k := by
  classical
  simp [snakeGridPrefix]

/-- A prefix is exactly the image of the corresponding initial interval of chain sites. -/
theorem snakeGridPrefix_eq_map (L k : ℕ) :
    snakeGridPrefix L k =
      (Finset.univ.filter fun i : Fin (L * L) ↦ i.val < k).map
        (snakeGridEquiv L).toEmbedding := by
  classical
  ext v
  simp

/-- Every snake-prefix cut of the open square grid has at most `L + 1` edges.
Rows changing across an edge are charged to their common column, at most once per
column; the remaining edges are consecutive positions in one row, so at most one
can cross the prefix. Source: the square-grid cutwidth comparison in
*Polynomial PEPS approximation of gapped square-grid ground states*, Section 1. -/
theorem card_edgeBoundary_snakeGridPrefix_le (L k : ℕ) :
    (edgeBoundary (rectangularDomain L L) (snakeGridPrefix L k)).card ≤ L + 1 := by
  classical
  let f : ((Fin L × Fin L) × (Fin L × Fin L)) →
      Sym2 (Site (rectangularDomain L L)) := fun p ↦
    s(rectangleSiteEquiv L L p.1, rectangleSiteEquiv L L p.2)
  have hcover : edgeBoundary (rectangularDomain L L) (snakeGridPrefix L k) ⊆
      (snakeBoundaryPairs L k).image f := by
    intro e he
    obtain ⟨he, x, hx, y, hy, rfl⟩ := Finset.mem_filter.mp he
    obtain ⟨a, rfl⟩ := (rectangleSiteEquiv L L).surjective x
    obtain ⟨b, rfl⟩ := (rectangleSiteEquiv L L).surjective y
    have hadj : (domainGraph (rectangularDomain L L)).Adj
        (rectangleSiteEquiv L L a) (rectangleSiteEquiv L L b) := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have ha : (snakeIndex L a).val < k := by
      simpa only [mem_snakeGridPrefix, snakeGridEquiv, Equiv.symm_trans_apply,
        Equiv.trans_apply, Equiv.symm_apply_apply, snakeIndex] using hx
    have hb : k ≤ (snakeIndex L b).val := by
      have : ¬ (snakeIndex L b).val < k := by
        simpa only [mem_snakeGridPrefix, snakeGridEquiv, Equiv.symm_trans_apply,
          Equiv.trans_apply, Equiv.symm_apply_apply, snakeIndex] using hy
      omega
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (rectangleGraphIso L L).map_rel_iff.mp hadj, ha, hb⟩, rfl⟩
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_image_le).trans (card_snakeBoundaryPairs_le L k))

end TNLean.MPS.AreaLaw
