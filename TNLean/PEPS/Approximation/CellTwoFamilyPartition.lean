/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CellColouredRecursion

/-!
# The two-family partition of a cell

This module assembles the recursive coloured partition in the proof of the
conditional information bound for one cell into an ordered two-family partition
of the lattice sample of the cell, as pure geometry.

Fix `γ < 1`. The plane is tiled by half-open squares of side `s ≥ 1`; one cell is
chosen and every other cell receives a forbidden colour. Running the recursion with
`t₀ = u ^ γ` until the side drops below a fixed threshold `u_*` gives the tiles of
all generations, in creation order, and the remaining allowed sites as the
remainder. `cell_twoFamily_partition` proves, with the named stopping scale
`u_* = cellStopScale γ u₀`, prefactor `C = cellPartitionConstant γ u₀` and exponent
`K = cellPartitionExponent γ u₀` (`exists_cell_twoFamily_partition` is its existential form):

* every tile has a scale `u` with `u_* ≤ u ≤ s`, is a union of at most `66 ^ 2`
  closed lattice rectangles, and has sup diameter at most `u`;
* every point of a tile of family `i` is at distance greater than `u ^ γ` from
  every exterior site of colour `i` and from every earlier tile of family `i`;
* the numbers of tiles and of remainder sites together are at most
  `C (1 + log s) ^ K`.

The threshold `u_*` can be taken above any prescribed value, as required to apply
the coarse information estimate to the tiles. That estimate, and with it the tile
cost and the information bound of the cell, are not part of this module.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`,
  lines 181–196 and 224–311.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.Approximation.CellPartition

open TNLean.PEPS.AreaLaw.Geometry

/-- The intermediate exponent `γ' = (max γ 0 + 1) / 2` of the cell recursion: for `γ < 1`
it satisfies `γ < γ'`, `0 < γ' < 1`, and children of side `8 u ^ γ` shrink below `u ^ γ'`.
Source: Lemma 3.2, `02-information.tex`, lines 224–227. -/
def cellIntermediateExponent (γ : ℝ) : ℝ := (max γ 0 + 1) / 2

/-- The stopping scale `u_* = max (max U₁ U₂) (max u₀ 2)` of the cell recursion for the
lower bound `u₀`, where `U₁ = cellPowerThreshold 1000 γ 1` makes `1000 u ^ γ ≤ u` and
`U₂ = cellPowerThreshold 8 γ γ'`, `γ' = cellIntermediateExponent γ`, makes
`8 u ^ γ ≤ u ^ γ'` for `u ≥ u_*`. Source: Lemma 3.2, `02-information.tex`, lines 238–240
and 302–307. -/
def cellStopScale (γ u₀ : ℝ) : ℝ :=
  max (max (cellPowerThreshold 1000 γ 1) (cellPowerThreshold 8 γ (cellIntermediateExponent γ)))
    (max u₀ 2)

/-- The exponent `K = cellGenerationCountConstant γ' u_* 25` of the two-family partition
count, the tile-count constant of the cell recursion at the intermediate exponent
`γ' = cellIntermediateExponent γ`, the stopping scale `u_* = cellStopScale γ u₀` and
branching bound `25`. Source: Lemma 3.2, `02-information.tex`, lines 302–311. -/
def cellPartitionExponent (γ u₀ : ℝ) : ℝ :=
  cellGenerationCountConstant (cellIntermediateExponent γ) (cellStopScale γ u₀) 25

/-- The prefactor `C = (2 + (u_* + 1) ^ 2) K` of the two-family partition count, with
`u_* = cellStopScale γ u₀` and `K = cellPartitionExponent γ u₀`: each active square carries
two tiles and each terminal square at most `(u_* + 1) ^ 2` remainder sites.
Source: Lemma 3.2, `02-information.tex`, lines 302–311. -/
def cellPartitionConstant (γ u₀ : ℝ) : ℝ :=
  (2 + (cellStopScale γ u₀ + 1) ^ 2) * cellPartitionExponent γ u₀

/-- The stopping scale is at least the prescribed lower bound. -/
theorem le_cellStopScale (γ u₀ : ℝ) : u₀ ≤ cellStopScale γ u₀ :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- The stopping scale exceeds one. -/
theorem one_lt_cellStopScale (γ u₀ : ℝ) : 1 < cellStopScale γ u₀ :=
  lt_of_lt_of_le one_lt_two ((le_max_right _ _).trans (le_max_right _ _))

/-- The intermediate exponent lies strictly between `max γ 0` and `1` for `γ < 1`. -/
theorem cellIntermediateExponent_bounds {γ : ℝ} (hγ : γ < 1) :
    γ < cellIntermediateExponent γ ∧ 0 < cellIntermediateExponent γ ∧
      cellIntermediateExponent γ < 1 := by
  unfold cellIntermediateExponent
  have h1 := le_max_left γ 0
  have h2 := le_max_right γ 0
  have h3 : max γ 0 < 1 := max_lt hγ one_pos
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The exponent of the partition count is positive. -/
theorem cellPartitionExponent_pos (γ u₀ : ℝ) :
    0 < cellPartitionExponent γ u₀ :=
  cellGenerationCountConstant_pos _ _ (by norm_num)

/-- The prefactor of the partition count is positive. -/
theorem cellPartitionConstant_pos (γ u₀ : ℝ) :
    0 < cellPartitionConstant γ u₀ :=
  mul_pos (by positivity) (cellPartitionExponent_pos γ u₀)

/-- **The two-family partition of a cell, with named constants.** Fix `γ < 1` and a lower
bound `u₀`, and put `u_* = cellStopScale γ u₀`, `C = cellPartitionConstant γ u₀` and
`K = cellPartitionExponent γ u₀`. For every grid of squares of side `s ≥ 1` with origin `o`,
every chosen cell `m₀` and every colouring `c` of the other cells, the lattice sample of the
chosen cell has an ordered two-family partition in which every piece `i` has a scale
`u_i ∈ [u_*, s]` with

* the piece a union of at most `66 ^ 2` closed lattice rectangles, of sup
  diameter at most `u_i`;
* every point of the piece at sup distance greater than `u_i ^ γ` from every
  lattice site of an exterior cell of colour equal to the family of the piece;
* the same clearance from every earlier piece of the same family;

and the pieces and remainder sites number at most `C (1 + log s) ^ K` in total.
The stopping scale is fixed by the two power thresholds and `u₀`; the exponent `K` by the
generation count of the recursion at that scale; the prefactor `C` by the tile and
remainder count per generation.
Source: Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`, lines 181–196
(colours and families) and 224–311 (the recursion and its count). -/
theorem cell_twoFamily_partition {γ : ℝ} (hγ : γ < 1) (u₀ : ℝ) :
    ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (c : ℤ × ℤ → Fin 2),
      ∃ (P : OrderedTwoFamilyPartition (cellSample o s m₀))
        (scale : Fin P.pieceCount → ℝ),
        (∀ i, cellStopScale γ u₀ ≤ scale i ∧ scale i ≤ s) ∧
        (∀ i, IsRectUnion (66 * 66) (P.piece i)) ∧
        (∀ i, ∀ x ∈ P.piece i, ∀ y ∈ P.piece i,
          dist (integerPoint x) (integerPoint y) ≤ scale i) ∧
        (∀ i, ∀ x ∈ P.piece i, ∀ y : ℤ × ℤ, cellIndex o s (integerPoint y) ≠ m₀ →
          c (cellIndex o s (integerPoint y)) = P.family i →
            scale i ^ γ < dist (integerPoint x) (integerPoint y)) ∧
        (∀ i, ∀ x ∈ P.piece i, ∀ y ∈ P.earlierSameFamily i,
          scale i ^ γ < dist (integerPoint x) (integerPoint y)) ∧
        (P.pieceCount : ℝ) + P.residual.card ≤
          cellPartitionConstant γ u₀ * (1 + Real.log s) ^ cellPartitionExponent γ u₀ := by
  classical
  unfold cellPartitionConstant
  -- exponents and the stopping threshold
  set γ' : ℝ := cellIntermediateExponent γ
  obtain ⟨hγγ', hγ'0, hγ'1⟩ := cellIntermediateExponent_bounds hγ
  set ustar := cellStopScale γ u₀
  have hone : 1 < ustar := one_lt_cellStopScale γ u₀
  have hlarge : ∀ u, ustar ≤ u → 1000 * u ^ γ ≤ u := fun u hu ↦ by
    simpa using const_mul_rpow_le_rpow_of_cellPowerThreshold_le (K := 1000) (by norm_num) hγ
      (((le_max_left _ _).trans (le_max_left _ _)).trans hu)
  have hthr : ∀ u, ustar ≤ u → cellChildSide γ u ≤ u ^ γ' := fun u hu ↦
    const_mul_rpow_le_rpow_of_cellPowerThreshold_le (by norm_num) hγγ'
      (((le_max_right _ _).trans (le_max_left _ _)).trans hu)
  obtain ⟨Cg, -, hgen⟩ := exists_cell_generation_bound hγ'0 hγ'1 hone hthr
  have hcount := cell_generation_count_bound hγ'0 hγ'1 hone hthr (b := 25) (by norm_num)
  set Cc := cellPartitionExponent γ u₀
  intro s hs o m₀ c
  have hs0 : 0 < s := by linarith
  set S₀ := initialGeneration o s m₀ c with hS₀def
  have hS₀ : S₀.IsValid := initialGeneration_isValid hs0 m₀ c
  have hside : ∀ g, (gen γ S₀ g).side = (cellChildSide γ)^[g] s := gen_side
  -- the first terminal generation
  have hex : ∃ m, (gen γ S₀ m).side < ustar := by
    by_contra hcon
    push Not at hcon
    set b := Cg + Cg * Real.log (Real.log (s + Real.exp 1))
    have hM := hgen s hs0 (⌈b⌉₊ + 1) fun i _ ↦ hside i ▸ hcon i
    push_cast at hM
    linarith [Nat.le_ceil b]
  set m := Nat.find hex with hmdef
  have hm : ∀ i < m, ustar ≤ (gen γ S₀ i).side := fun i hi ↦ not_lt.mp (Nat.find_min hex hi)
  have hmterm : (gen γ S₀ m).side < ustar := Nat.find_spec hex
  have hval := gen_isValid hS₀ hlarge hm
  have hdec : ∀ g ≤ m, (gen γ S₀ g).side ≤ s := by
    intro g hg
    induction g with
    | zero => exact le_rfl
    | succ g ih =>
      rw [gen_succ]
      have hpos := (hval g (by omega)).rpow_side_pos γ
      have := hlarge _ (hm g (by omega))
      change 8 * (gen γ S₀ g).side ^ γ ≤ s
      linarith [ih (by omega)]
  set L := pieceList γ S₀ m with hLdef
  have hpw : L.Pairwise (PieceRel γ) := pairwise_pieceList hS₀ hlarge hm
  have hmemL : ∀ i, ∃ g < m, ∃ Q ∈ (gen γ S₀ g).squares, ∃ f : Fin 2,
      L.get i = (tileSample (gen γ S₀ g).colour Q (gen γ S₀ g).side ((gen γ S₀ g).side ^ γ) f,
        f, (gen γ S₀ g).side) := fun i ↦ by
    obtain ⟨g, hg, he⟩ := mem_pieceList.mp (List.get_mem L i)
    exact ⟨g, hg, mem_genPieces.mp he⟩
  have hcell : ∀ x : ℤ × ℤ, (gen γ S₀ 0).colour (integerPoint x) = none →
      x ∈ cellSample o s m₀ := by
    intro x hx
    simp only [gen_zero, hS₀def, initialGeneration, initialColouring] at hx
    split_ifs at hx with h
    exact (mem_cellSample hs0).mpr h
  have hsub : ∀ i, (L.get i).1 ⊆ cellSample o s m₀ := by
    intro i x hx
    obtain ⟨g, -, Q, -, f, he⟩ := hmemL i
    rw [he] at hx
    exact hcell x (gen_colour_eq_none_of_le (Nat.zero_le g) (mem_tileSample.mp hx).2.2.1)
  set R := (cellSample o s m₀).filter fun x ↦ (gen γ S₀ m).colour (integerPoint x) = none
    with hRdef
  let P : OrderedTwoFamilyPartition (cellSample o s m₀) :=
    { pieceCount := L.length
      family := fun i ↦ (L.get i).2.1
      piece := fun i ↦ (L.get i).1
      residual := R
      disjoint := fun i j hij ↦ by
        rcases lt_or_gt_of_ne hij with h | h
        · exact (hpw.rel_get_of_lt h).1
        · exact (hpw.rel_get_of_lt h).1.symm
      residual_disjoint := fun i ↦ by
        obtain ⟨g, hg, Q, hQ, f, he⟩ := hmemL i
        refine Finset.disjoint_left.mpr fun x hxR hxi ↦ ?_
        rw [he] at hxi
        have h1 := gen_colour_of_mem_tile hg (hval g hg.le) hQ (mem_tileSample.mp hxi).2
        rw [(Finset.mem_filter.mp hxR).2] at h1
        exact absurd h1 (by simp)
      cover := by
        ext x
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · intro hx
          by_cases hxm : (gen γ S₀ m).colour (integerPoint x) = none
          · exact Or.inl (Finset.mem_filter.mpr ⟨hx, hxm⟩)
          · right
            have hex' : ∃ g, (gen γ S₀ g).colour (integerPoint x) ≠ none := ⟨m, hxm⟩
            have hg0 : Nat.find hex' ≠ 0 := by
              intro h0
              have := Nat.find_spec hex'
              rw [h0] at this
              apply this
              simp [gen_zero, hS₀def, initialGeneration, initialColouring,
                (mem_cellSample hs0).mp hx]
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hg0
            have hgm : Nat.find hex' ≤ m := Nat.find_min' hex' hxm
            have hknone : (gen γ S₀ k).colour (integerPoint x) = none := by
              by_contra h
              exact Nat.find_min hex' (by omega : k < Nat.find hex') h
            have hk1 : (gen γ S₀ (k + 1)).colour (integerPoint x) ≠ none := by
              have := Nat.find_spec hex'
              rwa [hk] at this
            have htile : ∃ Q ∈ (gen γ S₀ k).squares, ∃ f,
                integerPoint x ∈ tile (gen γ S₀ k).colour Q (gen γ S₀ k).side
                  ((gen γ S₀ k).side ^ γ) f := by
              by_contra hno
              push Not at hno
              apply hk1
              rw [gen_succ, Generation.next_colour_of_forall_not_mem_tile hno]
              exact hknone
            obtain ⟨Q, hQ, f, hxt⟩ := htile
            have he : (tileSample (gen γ S₀ k).colour Q (gen γ S₀ k).side
                ((gen γ S₀ k).side ^ γ) f, f, (gen γ S₀ k).side) ∈ L :=
              mem_pieceList.mpr ⟨k, by omega, mem_genPieces.mpr ⟨Q, hQ, f, rfl⟩⟩
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
            exact ⟨i, by rw [hi]; exact mem_tileSample.mpr ⟨mem_latticeBox.mpr hxt.1, hxt⟩⟩
        · rintro (hx | ⟨i, hx⟩)
          · exact (Finset.mem_filter.mp hx).1
          · exact hsub i hx }
  refine ⟨P, fun i ↦ (L.get i).2.2, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_,
    fun i x hx y hy ↦ ?_, ?_⟩
  · obtain ⟨g, hg, Q, hQ, f, he⟩ := hmemL i
    beta_reduce
    rw [he]
    exact ⟨hm g hg, hdec g hg.le⟩
  · obtain ⟨g, hg, Q, hQ, f, he⟩ := hmemL i
    change IsRectUnion _ (L.get i).1
    rw [he]
    exact ((hval g hg.le).chamber Q hQ).isRectUnion_tileSample
      ((hval g hg.le).rpow_side_pos γ) (hlarge _ (hm g hg)) f
  · obtain ⟨g, hg, Q, hQ, f, he⟩ := hmemL i
    intro x hx y hy
    change x ∈ (L.get i).1 at hx
    change y ∈ (L.get i).1 at hy
    beta_reduce
    rw [he] at hx hy ⊢
    exact dist_le_of_mem_box (mem_tileSample.mp hx).2.1 (mem_tileSample.mp hy).2.1
  · obtain ⟨g, hg, Q, hQ, f, he⟩ := hmemL i
    intro x hx y hy hcy
    change x ∈ (L.get i).1 at hx
    change c _ = (L.get i).2.1 at hcy
    beta_reduce
    rw [he] at hx hcy ⊢
    have h0 : (gen γ S₀ 0).colour (integerPoint y) = some f := by
      simp [gen_zero, hS₀def, initialGeneration, initialColouring, hy, hcy]
    have hg' := gen_colour_of_ne_none (Nat.zero_le g) (h0 ▸ Option.some_ne_none f)
    rw [h0] at hg'
    exact ((hval g hg.le).chamber Q hQ).lt_dist_of_mem_tile
      ((hval g hg.le).rpow_side_pos γ) (hlarge _ (hm g hg))
      (mem_tileSample.mp hx).2 hg'
  · simp only [OrderedTwoFamilyPartition.earlierSameFamily, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨j, ⟨hji, hfam⟩, hy⟩ := hy
    exact (hpw.rel_get_of_lt hji).2 hfam x hx y hy
  · -- the count of pieces and remainder sites
    have hlen : ((L.length : ℕ) : ℝ) ≤ ∑ j ∈ Finset.range m, 2 * (25 : ℝ) ^ j := by
      have := length_pieceList_le hS₀ (by simp [hS₀def, initialGeneration]) hlarge hm m le_rfl
      exact_mod_cast this
    have hsq := length_gen_squares_le hS₀ (by simp [hS₀def, initialGeneration]) hlarge hm m le_rfl
    have hRsub : R ⊆ (gen γ S₀ m).squares.toFinset.biUnion
        fun Q ↦ latticeBox Q.corner (gen γ S₀ m).side := by
      intro x hx
      obtain ⟨Q, hQ, hxQ⟩ := (hval m le_rfl).allowed _ (Finset.mem_filter.mp hx).2
      exact Finset.mem_biUnion.mpr ⟨Q, List.mem_toFinset.mpr hQ, mem_latticeBox.mpr hxQ⟩
    have hpos := (hval m le_rfl).side_pos
    have hbox : ∀ Q : ActiveSquare,
        ((latticeBox Q.corner (gen γ S₀ m).side).card : ℝ) ≤ (ustar + 1) ^ 2 := fun Q ↦
      (card_latticeBox_le _ hpos.le).trans (pow_le_pow_left₀ (by linarith) (by linarith) 2)
    have hR : (R.card : ℝ) ≤ (25 : ℝ) ^ m * (ustar + 1) ^ 2 := by
      calc (R.card : ℝ) ≤ ((gen γ S₀ m).squares.toFinset.biUnion
            fun Q ↦ latticeBox Q.corner (gen γ S₀ m).side).card := by
            exact_mod_cast Finset.card_le_card hRsub
        _ ≤ ∑ Q ∈ (gen γ S₀ m).squares.toFinset,
            ((latticeBox Q.corner (gen γ S₀ m).side).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _Q ∈ (gen γ S₀ m).squares.toFinset, (ustar + 1) ^ 2 :=
            Finset.sum_le_sum fun Q _ ↦ hbox Q
        _ = ((gen γ S₀ m).squares.toFinset.card : ℝ) * (ustar + 1) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (25 : ℝ) ^ m * (ustar + 1) ^ 2 := by
            gcongr
            exact_mod_cast (List.toFinset_card_le _).trans hsq
    have hC : ∑ j ∈ Finset.range (m + 1), (25 : ℝ) ^ j ≤ Cc * (1 + Real.log s) ^ Cc :=
      hcount s hs m fun i hi ↦ hside i ▸ hm i hi
    have hsum : ∑ j ∈ Finset.range m, 2 * (25 : ℝ) ^ j + (25 : ℝ) ^ m * (ustar + 1) ^ 2 ≤
        (2 + (ustar + 1) ^ 2) * ∑ j ∈ Finset.range (m + 1), (25 : ℝ) ^ j := by
      rw [Finset.sum_range_succ, ← Finset.mul_sum]
      have h1 : 0 ≤ ∑ j ∈ Finset.range m, (25 : ℝ) ^ j :=
        Finset.sum_nonneg fun j _ ↦ by positivity
      have h2 : 0 ≤ (25 : ℝ) ^ m := by positivity
      have h3 : 0 ≤ (ustar + 1) ^ 2 := by positivity
      nlinarith
    change ((L.length : ℕ) : ℝ) + (R.card : ℝ) ≤ _
    calc ((L.length : ℕ) : ℝ) + (R.card : ℝ)
        ≤ ∑ j ∈ Finset.range m, 2 * (25 : ℝ) ^ j + (25 : ℝ) ^ m * (ustar + 1) ^ 2 :=
          add_le_add hlen hR
      _ ≤ (2 + (ustar + 1) ^ 2) * ∑ j ∈ Finset.range (m + 1), (25 : ℝ) ^ j := hsum
      _ ≤ (2 + (ustar + 1) ^ 2) * (Cc * (1 + Real.log s) ^ Cc) := by gcongr
      _ = (2 + (ustar + 1) ^ 2) * Cc * (1 + Real.log s) ^ Cc := by ring

/-- **The two-family partition of a cell.** Fix `γ < 1` and a lower bound `u₀`.
There are a threshold `u_* ≥ u₀` and constants `C, K` such that, for every grid of
squares of side `s ≥ 1` with origin `o`, every chosen cell `m₀` and every colouring
`c` of the other cells, the lattice sample of the chosen cell has an ordered
two-family partition in which every piece `i` has a scale `u_i ∈ [u_*, s]` with

* the piece a union of at most `66 ^ 2` closed lattice rectangles, of sup
  diameter at most `u_i`;
* every point of the piece at sup distance greater than `u_i ^ γ` from every
  lattice site of an exterior cell of colour equal to the family of the piece;
* the same clearance from every earlier piece of the same family;

and the pieces and remainder sites number at most `C (1 + log s) ^ K` in total.
The constants are `u_* = cellStopScale γ u₀`, `C = cellPartitionConstant γ u₀` and
`K = cellPartitionExponent γ u₀` (`cell_twoFamily_partition`).
Source: Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`, lines 181–196
(colours and families) and 224–311 (the recursion and its count). -/
theorem exists_cell_twoFamily_partition {γ : ℝ} (hγ : γ < 1) (u₀ : ℝ) :
    ∃ ustar : ℝ, u₀ ≤ ustar ∧ 1 < ustar ∧ ∃ C K : ℝ, 0 < C ∧
      ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (c : ℤ × ℤ → Fin 2),
        ∃ (P : OrderedTwoFamilyPartition (cellSample o s m₀))
          (scale : Fin P.pieceCount → ℝ),
          (∀ i, ustar ≤ scale i ∧ scale i ≤ s) ∧
          (∀ i, IsRectUnion (66 * 66) (P.piece i)) ∧
          (∀ i, ∀ x ∈ P.piece i, ∀ y ∈ P.piece i,
            dist (integerPoint x) (integerPoint y) ≤ scale i) ∧
          (∀ i, ∀ x ∈ P.piece i, ∀ y : ℤ × ℤ, cellIndex o s (integerPoint y) ≠ m₀ →
            c (cellIndex o s (integerPoint y)) = P.family i →
              scale i ^ γ < dist (integerPoint x) (integerPoint y)) ∧
          (∀ i, ∀ x ∈ P.piece i, ∀ y ∈ P.earlierSameFamily i,
            scale i ^ γ < dist (integerPoint x) (integerPoint y)) ∧
          (P.pieceCount : ℝ) + P.residual.card ≤ C * (1 + Real.log s) ^ K :=
  ⟨cellStopScale γ u₀, le_cellStopScale γ u₀, one_lt_cellStopScale γ u₀,
    cellPartitionConstant γ u₀, cellPartitionExponent γ u₀, cellPartitionConstant_pos γ u₀,
    cell_twoFamily_partition hγ u₀⟩

end TNLean.PEPS.Approximation.CellPartition
