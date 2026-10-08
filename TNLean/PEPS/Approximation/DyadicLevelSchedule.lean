/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import TNLean.PEPS.Approximation.DyadicRepaintingSchedule

/-!
# Repainting the squares of one level of the dyadic hierarchy

At level `n` of the padded dyadic hierarchy the main guide passes from the assignment by
`2n`-squares to the assignment by `n`-squares, one `n`-square at a time. At the beginning and end
of each repainting every `n`-square carries a single label, its old `2n`-square label or its final
`n`-square label, and the exterior of the root square carries the placeholder. This file:

* describes these guides by labels of the `n`-blocks, `p ↦ lab (⌊p₁ / n⌋, ⌊p₂ / n⌋)`, and places
  the schedule of `TNLean.PEPS.Approximation.DyadicRepaintingSchedule` on the block
  `S = (n r, n s) + [0, n] ^ 2` by translation;
* proves Lemma 7.2 (`lem:geometry-angular`) for every elementary birth, death and lens exchange
  of the repainting of every block, with `a₀ = 1/5000`, in the source's form: the changed region
  has diameter at most `n`, and its closure is at sup distance at least `a₀ min(n, d_V(y))` from
  the closure of the positions of the other labels;
* proves that the repainting leaves, off the boundary of the block, the guide of the next
  repainting, that the guide at the end
  of level `2n` is the guide at the start of level `n`, and the part of the active-label invariant
  `eq:geometry-active-labels` that concerns guides: at the start of a level only old labels and
  the placeholder occur, during it only old and new labels and the placeholder, and at its end
  only new labels and the placeholder;
* proves that no lattice site, a cell center `(i + 1/2, j + 1/2)`, lies on the curves off which
  the schedule's two changes of labelling are identities (the curves `x = 0`, `x = 1` of a band
  and the boundary of a block), so that the labels at the lattice sites do not change there.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the hierarchy and the
  repainting by levels (lines 62–100), the edge construction (lines 142–241), Lemma 7.2
  `lem:geometry-angular` (lines 243–319), and the active-label invariant (lines 597–618).
-/

namespace TNLean.PEPS.Approximation

open Set Metric SquareEdge

/-! ### Translation -/

/-- The guide `g` of the square at the origin, moved to the square with lower-left corner `o`. -/
def shiftGuide {ι : Type*} (o : ℝ × ℝ) (g : ℝ × ℝ → ι) : ℝ × ℝ → ι := fun p => g (p - o)

theorem sub_mem_closure {o y : ℝ × ℝ} {s : Set (ℝ × ℝ)}
    (hy : y ∈ closure ((fun p => p - o) ⁻¹' s)) : y - o ∈ closure s := by
  have h := (Homeomorph.subRight o).preimage_closure s
  have : y ∈ (Homeomorph.subRight o) ⁻¹' closure s := by rw [h]; exact hy
  exact this

theorem sub_mem_frontier {o z : ℝ × ℝ} {s : Set (ℝ × ℝ)}
    (hz : z ∈ frontier ((fun p => p - o) ⁻¹' s)) : z - o ∈ frontier s := by
  have h := (Homeomorph.subRight o).preimage_frontier s
  have : z ∈ (Homeomorph.subRight o) ⁻¹' frontier s := by rw [h]; exact hz
  exact this

theorem mem_closure_shift {ι : Type*} {f g : ℝ × ℝ → ι} (o : ℝ × ℝ) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | shiftGuide o f p ≠ shiftGuide o g p}) :
    y - o ∈ closure {p | f p ≠ g p} :=
  sub_mem_closure (s := {p | f p ≠ g p}) hy

/-- **Transport of a clearance estimate.** Translating all guides by `o` translates the estimate:
sup distances are translation invariant.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–145`. -/
theorem clearance_shift {ι : Type*} {f g h : ℝ × ℝ → ι} {P : ι} {Φ : ℝ × ℝ → ℝ} (o : ℝ × ℝ)
    (H : ∀ y ∈ closure {p | f p ≠ g p}, ∀ z, h z ≠ P → Φ y ≤ dist y z) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | shiftGuide o f p ≠ shiftGuide o g p}) {z : ℝ × ℝ}
    (hz : shiftGuide o h z ≠ P) : Φ (y - o) ≤ dist y z := by
  have := H _ (mem_closure_shift o hy) (z - o) hz
  rwa [dist_sub_right] at this

/-- Transport of a diameter bound along a translation. -/
theorem dist_le_shift {ι : Type*} {f g : ℝ × ℝ → ι} {c : ℝ} (o : ℝ × ℝ)
    (H : ∀ y ∈ closure {p | f p ≠ g p}, ∀ z ∈ closure {p | f p ≠ g p}, dist y z ≤ c)
    {y z : ℝ × ℝ} (hy : y ∈ closure {p | shiftGuide o f p ≠ shiftGuide o g p})
    (hz : z ∈ closure {p | shiftGuide o f p ≠ shiftGuide o g p}) : dist y z ≤ c := by
  have := H _ (mem_closure_shift o hy) _ (mem_closure_shift o hz)
  rwa [dist_sub_right] at this

/-- The corner distance of a translated square: the distance from its four corners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:157–160, 246–248`. -/
theorem cornerMarkDist_sub (n : ℝ) (y o : ℝ × ℝ) :
    cornerMarkDist n (y - o) = min (min (dist y o) (dist y (o + (n, 0))))
      (min (dist y (o + (0, n))) (dist y (o + (n, n)))) := by
  have h (v : ℝ × ℝ) : dist (y - o) v = dist y (o + v) := by
    rw [← dist_sub_right y (o + v) o, add_sub_cancel_left]
  simp only [cornerMarkDist, h, Prod.mk_zero_zero, add_zero]

/-- The endpoint distance of an edge of a translated square: the distance from the two
translated endpoints.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:170, 246–248`. -/
theorem edgeMarkDist_sub (n : ℝ) (e : SquareEdge) (y o : ℝ × ℝ) :
    edgeMarkDist n e (y - o) =
      min (dist y (o + e.point n 0 0)) (dist y (o + e.point n n 0)) := by
  have h (v : ℝ × ℝ) : dist (y - o) v = dist y (o + v) := by
    rw [← dist_sub_right y (o + v) o, add_sub_cancel_left]
  simp only [edgeMarkDist, h]

/-! ### Block guides -/

/-- The index `(⌊p₁ / n⌋, ⌊p₂ / n⌋)` of the `n`-block containing `p`, with the half-open
convention on block boundaries.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:62–67, 69–80`. -/
noncomputable def blockIndex (n : ℝ) (p : ℝ × ℝ) : ℤ × ℤ := (⌊p.1 / n⌋, ⌊p.2 / n⌋)

/-- The guide that is uniform on `n`-blocks, with label `lab Q` on the block `Q`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–90`. -/
noncomputable def blockGuide {ι : Type*} (n : ℝ) (lab : ℤ × ℤ → ι) (p : ℝ × ℝ) : ι :=
  lab (blockIndex n p)

/-- The lower-left corner `(n r, n s)` of the block `(r, s)`. -/
def blockCorner (n : ℝ) (S : ℤ × ℤ) : ℝ × ℝ := (n * S.1, n * S.2)

/-- The block across an edge of the block `(r, s)`. -/
def SquareEdge.nbrBlock : SquareEdge → ℤ × ℤ → ℤ × ℤ
  | bottom, S => (S.1, S.2 - 1)
  | right, S => (S.1 + 1, S.2)
  | top, S => (S.1, S.2 + 1)
  | left, S => (S.1 - 1, S.2)

private theorem floor_add_div {n x : ℝ} (hn : 0 < n) {k r : ℤ} (h1 : k * n ≤ x)
    (h2 : x < (k + 1) * n) : ⌊(x + n * r) / n⌋ = r + k := by
  have : (x + n * r) / n = x / n + r := by field_simp
  rw [this, Int.floor_add_intCast, add_comm]
  congr 1
  rw [Int.floor_eq_iff]
  exact ⟨(le_div_iff₀ hn).2 h1, (div_lt_iff₀ hn).2 h2⟩

/-- On the open block `(r, s)` the block index is `(r, s)`. -/
theorem blockIndex_of_mem_openSquare {n : ℝ} (hn : 0 < n) {p : ℝ × ℝ} (S : ℤ × ℤ)
    (hp : p ∈ openSquare n) : blockIndex n (p + blockCorner n S) = S := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_openSquare.1 hp
  simp only [blockIndex, blockCorner, Prod.fst_add, Prod.snd_add]
  rw [floor_add_div hn (k := 0) (by simpa using h1.le) (by simpa using h2),
    floor_add_div hn (k := 0) (by simpa using h3.le) (by simpa using h4)]
  simp

/-- On the open exterior neighboring square across an edge, the block index is the neighboring
block. -/
theorem blockIndex_of_mem_edgeNeighbor {n : ℝ} (hn : 0 < n) {p : ℝ × ℝ} (S : ℤ × ℤ)
    (e : SquareEdge) (hp : p ∈ edgeNeighbor n e) :
    blockIndex n (p + blockCorner n S) = e.nbrBlock S := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  cases e <;> simp only [par, nor] at h1 h2 h3 h4 <;>
    simp only [blockIndex, blockCorner, Prod.fst_add, Prod.snd_add, SquareEdge.nbrBlock]
  · rw [floor_add_div hn (k := 0) (by simpa using h1.le) (by simpa using h2),
      floor_add_div hn (k := -1) (by simp; linarith) (by simpa using h4)]
    simp [sub_eq_add_neg]
  · rw [floor_add_div hn (k := 1) (by simp; linarith) (by norm_num; linarith),
      floor_add_div hn (k := 0) (by simpa using h1.le) (by simpa using h2)]
    simp
  · rw [floor_add_div hn (k := 0) (by simpa using h1.le) (by simpa using h2),
      floor_add_div hn (k := 1) (by simp; linarith) (by norm_num; linarith)]
    simp
  · rw [floor_add_div hn (k := -1) (by simp; linarith) (by simpa using h4),
      floor_add_div hn (k := 0) (by simpa using h1.le) (by simpa using h2)]
    simp [sub_eq_add_neg]

/-- Off the closed block `(r, s)` the block index is another block. -/
theorem blockIndex_ne_of_notMem_closedSquare {n : ℝ} (hn : 0 < n) {p : ℝ × ℝ} (S : ℤ × ℤ)
    (hp : p ∉ closedSquare n) : blockIndex n (p + blockCorner n S) ≠ S := by
  intro h
  simp only [blockIndex, blockCorner, Prod.fst_add, Prod.snd_add, Prod.ext_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [Int.floor_eq_iff, le_div_iff₀ hn, div_lt_iff₀ hn] at h1 h2
  apply hp
  rw [mem_closedSquare]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The starting guide of the repainting of the block `S` to the label `B`, moved to the origin:
the block guide with labels `lab`, which is `lab S` on the open block and `lab` of the
neighboring block across each edge.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–100, 142–143, 166–168`. -/
noncomputable def blockBaseline {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι)
    (S : ℤ × ℤ) (B : ι) : RepaintingBaseline ι where
  n := n
  n_pos := hn
  guide p := blockGuide n lab (p + blockCorner n S)
  oldLabel := lab S
  finalLabel := B
  nbrLabel e := lab (e.nbrBlock S)
  guide_openSquare p hp := by
    simp only [blockGuide, blockIndex_of_mem_openSquare hn S hp]
  guide_edgeNeighbor e p hp := by
    simp only [blockGuide, blockIndex_of_mem_edgeNeighbor hn S e hp]

theorem shiftGuide_blockBaseline_guide {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι)
    (S : ℤ × ℤ) (B : ι) :
    shiftGuide (blockCorner n S) (blockBaseline hn lab S B).guide = blockGuide n lab := by
  funext p
  simp [shiftGuide, blockBaseline]

/-! ### Lemma 7.2 -/

section Lemma72

variable {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι) (S : ℤ × ℤ) (B : ι)

local notation "R" => blockBaseline hn lab S B
local notation "o" => blockCorner n S

/-- **Lemma 7.2, central birth.** In the repainting of the block `S` of side `n`, the closure of
the changed region of the central birth has diameter at most `n`, and each of its points `y` lies
at sup distance at least `a₀ min(n, d_V(y))` from the closure of the positions of labels other
than the old label in the surrounding guide, with `a₀ = 1/5000` and `V` the four corners of `S`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 276–281`. -/
theorem blockRepainting_central :
    (∀ y ∈ closure {p | blockGuide n lab p ≠ shiftGuide o (R).centralGuide p},
      ∀ z ∈ closure {p | blockGuide n lab p ≠ shiftGuide o (R).centralGuide p},
        dist y z ≤ n) ∧
    ∀ y ∈ closure {p | blockGuide n lab p ≠ shiftGuide o (R).centralGuide p},
      ∀ z ∈ closure {p | blockGuide n lab p ≠ lab S},
        angularConstant * min n (cornerMarkDist n (y - o)) ≤ dist y z := by
  rw [← shiftGuide_blockBaseline_guide hn lab S B]
  refine ⟨fun y hy z hz => dist_le_shift o (fun _ hy _ hz => (R).dist_le_central hy hz) hy hz,
    fun y hy z hz => le_dist_of_mem_closure (fun z hz => ?_) hz⟩
  exact clearance_shift o (fun _ hy _ hz => (R).clearance_central hy hz) hy hz

/-- **Lemma 7.2, auxiliary births.** For every elementary birth on the auxiliary sheet of the
edge `e`, the closure of the changed region has diameter at most `n`, and each of its points `y`
lies at sup distance at least `a₀ min(n, d_V(y))` from the closure of the positions of labels
other than the surrounding label in the surrounding guide; `V` is the two endpoints of `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 283–286`. -/
theorem blockRepainting_auxStep (e : SquareEdge) {op : BandOperation ι}
    (hop : op ∈ auxSteps (lab S) B (lab (e.nbrBlock S))) :
    (∀ y ∈ closure {p | shiftGuide o ((R).auxGuide e op.before) p ≠
          shiftGuide o ((R).auxGuide e op.after) p},
      ∀ z ∈ closure {p | shiftGuide o ((R).auxGuide e op.before) p ≠
          shiftGuide o ((R).auxGuide e op.after) p}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | shiftGuide o ((R).auxGuide e op.before) p ≠
          shiftGuide o ((R).auxGuide e op.after) p},
      ∀ z ∈ closure {p | shiftGuide o ((R).auxGuide e op.surrounding) p ≠ op.label},
        angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z :=
  ⟨fun _ hy _ hz => dist_le_shift o (fun _ hy _ hz => op.dist_le_bandUpdate e _ hy hz) hy hz,
    fun _ hy _ hz => le_dist_of_mem_closure (fun _ hz =>
      clearance_shift o (fun _ hy _ hz => (R).clearance_auxStep e hop hy hz) hy hz) hz⟩

/-- **Lemma 7.2, main births and deaths.** For every elementary birth or death on the main sheet
along the edge `e`, after the edges of `E` have been completed, the closure of the changed region
has diameter at most `n`, and each of its points `y` lies at sup distance at least
`a₀ min(n, d_V(y))` from the closure of the positions of labels other than the surrounding label
in the surrounding guide; `V` is the two endpoints of `e`. The schedule reaches these guides for
`e ∉ E`; the estimate holds for every `E`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 286–293`. -/
theorem blockRepainting_mainStep (E : List SquareEdge) (e : SquareEdge) {op : BandOperation ι}
    (hop : op ∈ mainSteps (lab S) B (lab (e.nbrBlock S))) :
    (∀ y ∈ closure {p | shiftGuide o ((R).mainGuide E e op.before) p ≠
          shiftGuide o ((R).mainGuide E e op.after) p},
      ∀ z ∈ closure {p | shiftGuide o ((R).mainGuide E e op.before) p ≠
          shiftGuide o ((R).mainGuide E e op.after) p}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | shiftGuide o ((R).mainGuide E e op.before) p ≠
          shiftGuide o ((R).mainGuide E e op.after) p},
      ∀ z ∈ closure {p | shiftGuide o ((R).mainGuide E e op.surrounding) p ≠ op.label},
        angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z :=
  ⟨fun _ hy _ hz => dist_le_shift o (fun _ hy _ hz => op.dist_le_bandUpdate e _ hy hz) hy hz,
    fun _ hy _ hz => le_dist_of_mem_closure (fun _ hz =>
      clearance_shift o (fun _ hy _ hz => (R).clearance_mainStep E e hop hy hz) hy hz) hz⟩

/-- **Lemma 7.2, lens exchange.** Every point `y` in the closure of the positions that are not
common `C_e` on the two guides before the exchange along `e` lies at sup distance at least
`a₀ min(n, d_V(y))` from the boundary of the translated lens `Y`. The main guide is the one the
schedule specifies at the start of the construction along `e ∉ E`; at the lattice sites it equals
the guide reached (`blockRepainting_start_site`).

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-exchange-clearance`, `06-geometry.tex:265–272, 295–299`. -/
theorem blockRepainting_exchange (E : List SquareEdge) (e : SquareEdge) :
    ∀ y ∈ closure {p |
        shiftGuide o ((R).mainGuide E e (edgeStartWord (lab S) B (lab (e.nbrBlock S)))) p ≠
          lab (e.nbrBlock S) ∨
        shiftGuide o ((R).auxGuide e (auxWord (lab S) B (lab (e.nbrBlock S)))) p ≠
          lab (e.nbrBlock S)},
      ∀ z ∈ frontier ((fun p => p - o) ⁻¹' edgeLens n e),
        angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z := by
  intro y hy z hz
  have hy' := sub_mem_closure (s := {p |
      (R).mainGuide E e (edgeStartWord (lab S) B (lab (e.nbrBlock S))) p ≠ lab (e.nbrBlock S) ∨
      (R).auxGuide e (auxWord (lab S) B (lab (e.nbrBlock S))) p ≠ lab (e.nbrBlock S)}) hy
  have hz' := sub_mem_frontier hz
  have := (R).clearance_exchange E e hy' hz'
  rwa [dist_sub_right] at this

end Lemma72

/-! ### Labels of a level -/

/-- The block `Q` lies in the root square, which has `M` blocks per side. -/
def InRoot (M : ℤ) (Q : ℤ × ℤ) : Prop := 0 ≤ Q.1 ∧ Q.1 < M ∧ 0 ≤ Q.2 ∧ Q.2 < M

open Classical in
/-- The labels of the `n`-blocks during the pass to level `n`, when the blocks of `done` have been
repainted: a repainted block carries its new label, another block of the root square the label of
its parent `2n`-block, and a block outside the root square the placeholder.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–100`. -/
noncomputable def levelLabels {ι : Type*} (M : ℤ) (old new : ℤ × ℤ → ι) (ph : ι)
    (done : Set (ℤ × ℤ)) (Q : ℤ × ℤ) : ι :=
  if InRoot M Q then (if Q ∈ done then new Q else old (Q.1 / 2, Q.2 / 2)) else ph

section Level

variable {ι : Type*} (M : ℤ) (old new : ℤ × ℤ → ι) (ph : ι)

theorem levelLabels_insert_of_ne {done : Set (ℤ × ℤ)} {S Q : ℤ × ℤ} (h : Q ≠ S) :
    levelLabels M old new ph (insert S done) Q = levelLabels M old new ph done Q := by
  classical
  simp [levelLabels, h]

/-- **Active labels of a level.** Every block label is the placeholder, an old label or a new
label; before any repainting no new label occurs, and once every block of the root square is
repainted no old label occurs.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-active-labels`,
`06-geometry.tex:597–609`. -/
theorem levelLabels_mem (done : Set (ℤ × ℤ)) (Q : ℤ × ℤ) :
    levelLabels M old new ph done Q ∈ insert ph (range old ∪ range new) := by
  classical
  unfold levelLabels
  split_ifs
  · exact mem_insert_of_mem _ (Or.inr ⟨Q, rfl⟩)
  · exact mem_insert_of_mem _ (Or.inl ⟨_, rfl⟩)
  · exact mem_insert _ _

theorem levelLabels_empty_mem (Q : ℤ × ℤ) :
    levelLabels M old new ph ∅ Q ∈ insert ph (range old) := by
  classical
  unfold levelLabels
  split_ifs with h h'
  · exact absurd h' (notMem_empty _)
  · exact mem_insert_of_mem _ ⟨_, rfl⟩
  · exact mem_insert _ _

theorem levelLabels_mem_of_subset {done : Set (ℤ × ℤ)} (hd : {Q | InRoot M Q} ⊆ done)
    (Q : ℤ × ℤ) : levelLabels M old new ph done Q ∈ insert ph (range new) := by
  classical
  unfold levelLabels
  split_ifs with h h'
  · exact mem_insert_of_mem _ ⟨Q, rfl⟩
  · exact absurd (hd h) h'
  · exact mem_insert _ _

/-- **Owners of a block label.** The label of a block during the pass to level `n` is the
placeholder, the new label of that block, or the label of its parent `2n`-block. In the
repainting of `S` the labels `A = lab S`, `B = new S` and `C_e = lab (nbrBlock e S)` are therefore
owned by `S`, its parent, a neighboring block of `S` or its parent, or the placeholder, which is
attached to `S`; with `dyadicAnchor_dist_lt_of_adjacent` these are parties at the same or adjacent
scales with address coordinates within `3 · 2n` of each other.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:34–37, 585–596`. -/
theorem levelLabels_mem_owners (done : Set (ℤ × ℤ)) (Q : ℤ × ℤ) :
    levelLabels M old new ph done Q ∈ ({ph, new Q, old (Q.1 / 2, Q.2 / 2)} : Set ι) := by
  classical
  unfold levelLabels
  split_ifs <;> simp

/-- A neighboring block differs from `S` by at most one in each index. -/
theorem SquareEdge.nbrBlock_adjacent (e : SquareEdge) (S : ℤ × ℤ) :
    |(e.nbrBlock S).1 - S.1| ≤ 1 ∧ |(e.nbrBlock S).2 - S.2| ≤ 1 := by
  cases e <;> simp [SquareEdge.nbrBlock]

/-- **Active labels during a repainting.** While the block `S` is repainted to its new label,
every value of the main guide after the central birth and any completed edges, and of every main
or auxiliary guide of an edge construction, is the placeholder, an old label or a new label.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-active-labels`,
`06-geometry.tex:585–609`. -/
theorem blockRepainting_labels {n : ℝ} (hn : 0 < n) (done : Set (ℤ × ℤ)) (S : ℤ × ℤ)
    (E : List SquareEdge) (e : SquareEdge) {W : ℝ → ι}
    (hW : ∀ x, W x = levelLabels M old new ph done S ∨ W x = new S ∨
      W x = levelLabels M old new ph done (e.nbrBlock S)) (p : ℝ × ℝ) :
    (blockBaseline hn (levelLabels M old new ph done) S (new S)).completedGuide E p ∈
        insert ph (range old ∪ range new) ∧
      (blockBaseline hn (levelLabels M old new ph done) S (new S)).mainGuide E e W p ∈
        insert ph (range old ∪ range new) ∧
      (blockBaseline hn (levelLabels M old new ph done) S (new S)).auxGuide e W p ∈
        insert ph (range old ∪ range new) := by
  set R := blockBaseline hn (levelLabels M old new ph done) S (new S)
  have key : insert R.finalLabel (range R.guide) ⊆ insert ph (range old ∪ range new) := by
    rintro l (rfl | ⟨q, rfl⟩)
    · exact mem_insert_of_mem _ (Or.inr ⟨S, rfl⟩)
    · exact levelLabels_mem M old new ph done _
  exact ⟨key (R.completedGuide_mem E p), key ((R.mainGuide_mem E e hW p).1),
    key ((R.mainGuide_mem E e hW p).2)⟩

/-- **The guide left by a repainting.** Once the four edges of the block `S` of the root square
are completed, the main guide agrees, off the boundary of `S`, with the block guide in which `S`
also carries its new label: the starting guide of the next repainting.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:86–90, 238–241`. -/
theorem blockRepainting_final {n : ℝ} (hn : 0 < n) (done : Set (ℤ × ℤ)) {S : ℤ × ℤ}
    (hS : InRoot M S) {E : List SquareEdge} (hE : ∀ e, e ∈ E) {p : ℝ × ℝ}
    (hp : p - blockCorner n S ∈ openSquare n ∨ p - blockCorner n S ∉ closedSquare n) :
    shiftGuide (blockCorner n S)
        ((blockBaseline hn (levelLabels M old new ph done) S (new S)).completedGuide E) p =
      blockGuide n (levelLabels M old new ph (insert S done)) p := by
  classical
  set R := blockBaseline hn (levelLabels M old new ph done) S (new S)
  have hp' : p = p - blockCorner n S + blockCorner n S := (sub_add_cancel _ _).symm
  rcases hp with hp | hp
  · rw [shiftGuide, R.completedGuide_of_mem_openSquare hE hp, blockGuide, hp',
      blockIndex_of_mem_openSquare hn S hp]
    simp [levelLabels, hS, R, blockBaseline]
  · rw [shiftGuide, R.completedGuide_of_notMem_closedSquare E hp]
    simp only [R, blockBaseline, blockGuide, sub_add_cancel]
    rw [levelLabels_insert_of_ne]
    have := blockIndex_ne_of_notMem_closedSquare hn S hp
    rwa [sub_add_cancel] at this

/-- **From level `2n` to level `n`.** The guide at the end of the pass to level `2n`, uniform on
`2n`-blocks with their new labels and the placeholder outside the root square of `M` blocks per
side, is the guide at the start of the pass to level `n`, in which every `n`-block of the root
square of `2M` blocks per side carries the label of its parent.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–86`. -/
theorem blockGuide_levelLabels_start (n : ℝ) (old' new' : ℤ × ℤ → ι)
    {done : Set (ℤ × ℤ)} (hd : {Q | InRoot M Q} ⊆ done) :
    blockGuide (2 * n) (levelLabels M old' new ph done) =
      blockGuide n (levelLabels (2 * M) new new' ph ∅) := by
  classical
  funext p
  have hfl (x : ℝ) : ⌊x / (2 * n)⌋ = ⌊x / n⌋ / 2 := by
    have h := Int.floor_div_natCast (x / n) 2
    rw [div_div, mul_comm] at h
    exact_mod_cast h
  have hroot (Q : ℤ × ℤ) : InRoot (2 * M) Q ↔ InRoot M (Q.1 / 2, Q.2 / 2) := by
    simp only [InRoot]
    omega
  simp only [blockGuide, blockIndex, levelLabels, hfl, hroot, mem_empty_iff_false, ite_false]
  split_ifs with h1 h2
  · rfl
  · exact absurd (hd h1) h2
  · rfl

end Level

/-! ### Lattice sites lie off the interface curves

The guides of the schedule are labellings of the plane that represent the source's polygonal
guides by their values on the open chambers. At the start of each edge construction the guide
reached by the schedule is identified with the main guide carrying the starting word, and at the
end of each repainting with the next block guide; the two labellings agree only off the curves
`x = 0` and `x = 1` of the band, respectively off the boundary of the block. The source specifies
guides by their open chambers and samples them at the lattice sites (`06-geometry.tex:62–80`), and
no lattice site lies on those curves, so the labels the schedule assigns to the sites do not jump
at these identifications. -/

/-- The lattice sites are the cell centers `(i + 1/2, j + 1/2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:62–63`. -/
def IsCellCenter (p : ℝ × ℝ) : Prop := ∃ i j : ℤ, p = ((i : ℝ) + 1 / 2, (j : ℝ) + 1 / 2)

/-- A half-odd number `k + 1/2` is not an integer. -/
private theorem half_add_intCast_ne (k l : ℤ) : (k : ℝ) + 1 / 2 ≠ l := by
  intro h
  have h' : ((2 * (k - l) + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
  have : (2 * (k - l) + 1 : ℤ) = 0 := by exact_mod_cast h'
  omega

/-- The coordinates of a cell center relative to an edge of an integer square are half-odd. -/
private theorem IsCellCenter.par_nor {p : ℝ × ℝ} (hp : IsCellCenter p) (m : ℤ) (e : SquareEdge) :
    (∃ k : ℤ, e.par p = k + 1 / 2) ∧ ∃ k : ℤ, e.nor m p = k + 1 / 2 := by
  obtain ⟨i, j, rfl⟩ := hp
  cases e
  · exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
  · exact ⟨⟨j, rfl⟩, ⟨m - i - 1, by simp only [nor]; push_cast; ring⟩⟩
  · exact ⟨⟨i, rfl⟩, ⟨m - j - 1, by simp only [nor]; push_cast; ring⟩⟩
  · exact ⟨⟨j, rfl⟩, ⟨i, rfl⟩⟩

theorem IsCellCenter.sub_blockCorner {p : ℝ × ℝ} (hp : IsCellCenter p) (m : ℤ) (S : ℤ × ℤ) :
    IsCellCenter (p - blockCorner m S) := by
  obtain ⟨i, j, rfl⟩ := hp
  refine ⟨i - m * S.1, j - m * S.2, ?_⟩
  ext <;> simp only [blockCorner, Prod.fst_sub, Prod.snd_sub] <;> push_cast <;> ring

/-- A cell center lies in the open integer square or outside the closed one: never on its
boundary.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:62–63, 69–80`. -/
theorem IsCellCenter.mem_openSquare_or_notMem_closedSquare {p : ℝ × ℝ} (hp : IsCellCenter p)
    (m : ℤ) : p ∈ openSquare m ∨ p ∉ closedSquare m := by
  by_cases h : p ∈ closedSquare m
  · left
    obtain ⟨i, j, rfl⟩ := hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 h
    refine mem_openSquare.2 ⟨?_, ?_, ?_, ?_⟩
    · exact lt_of_le_of_ne h1 (half_add_intCast_ne i 0 ∘ by simpa using Eq.symm)
    · exact lt_of_le_of_ne h2 (half_add_intCast_ne i m)
    · exact lt_of_le_of_ne h3 (half_add_intCast_ne j 0 ∘ by simpa using Eq.symm)
    · exact lt_of_le_of_ne h4 (half_add_intCast_ne j m)
  · exact Or.inr h

/-- A cell center lies on neither interface curve `x = 0`, `x = 1` of the band of an edge of an
integer square: `d = k + 1/2` is not `0`, and `1000 d` is an integer while `min(s, n - s)` is not.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:62–63, 69–80, 161–165`. -/
theorem IsCellCenter.notMem_edgeInterface {ι : Type*} {R : RepaintingBaseline ι} {m : ℤ}
    (hm : R.n = m) {p : ℝ × ℝ} (hp : IsCellCenter p) (e : SquareEdge) :
    p ∉ R.edgeInterface e := by
  rintro ⟨hb, hx⟩
  obtain ⟨s1, s2, -, -⟩ := mem_edgeBand_iff_bandCoord.1 hb
  have hw := bandWidth_pos s1 s2
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := hp.par_nor m e
  rw [hm] at hx hw
  rcases hx with hx | hx
  · rw [bandCoord, div_eq_zero_iff, hl] at hx
    rcases hx with hx | hx
    · exact half_add_intCast_ne l 0 (by simpa using hx)
    · exact hw.ne' hx
  · rw [bandCoord, div_eq_one_iff_eq hw.ne', hl, bandWidth, hk] at hx
    rcases min_choice ((k : ℝ) + 1 / 2) ((m : ℝ) - (k + 1 / 2)) with hmin | hmin <;>
      rw [hmin] at hx
    · exact half_add_intCast_ne k (1000 * l + 500) (by push_cast; linarith)
    · exact half_add_intCast_ne (m - k - 1) (1000 * l + 500) (by push_cast; linarith)

section Sites

variable {ι : Type*} {m : ℤ} (hn : 0 < (m : ℝ)) (lab : ℤ × ℤ → ι) (S : ℤ × ℤ) (B : ι)

/-- **The start of an edge construction, at the sites.** At every lattice site, the guide reached
after the central birth and the edges of `E` agrees with the main guide carrying the starting word
`C_e | A | B` on the band of `e ∉ E`, on which the estimates of the edge are proved.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:62–80, 160–168, 237–238`. -/
theorem blockRepainting_start_site {E : List SquareEdge} {e : SquareEdge} (he : e ∉ E)
    {p : ℝ × ℝ} (hp : IsCellCenter p) :
    shiftGuide (blockCorner m S) ((blockBaseline hn lab S B).completedGuide E) p =
      shiftGuide (blockCorner m S) ((blockBaseline hn lab S B).mainGuide E e
        (edgeStartWord (lab S) B (lab (e.nbrBlock S)))) p :=
  (blockBaseline hn lab S B).completedGuide_eq_mainGuide_start he
    ((hp.sub_blockCorner m S).notMem_edgeInterface rfl e)

/-- **The guide left by a repainting, at the sites.** Once the four edges of the block `S` of the
root square are completed, the main guide agrees at every lattice site with the block guide in
which `S` also carries its new label.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:62–80, 86–90, 238–241`. -/
theorem blockRepainting_final_site (M : ℤ) (old new : ℤ × ℤ → ι) (ph : ι)
    (done : Set (ℤ × ℤ)) {S : ℤ × ℤ} (hS : InRoot M S) {E : List SquareEdge} (hE : ∀ e, e ∈ E)
    {p : ℝ × ℝ} (hp : IsCellCenter p) :
    shiftGuide (blockCorner m S)
        ((blockBaseline hn (levelLabels M old new ph done) S (new S)).completedGuide E) p =
      blockGuide m (levelLabels M old new ph (insert S done)) p :=
  blockRepainting_final M old new ph hn done hS hE
    ((hp.sub_blockCorner m S).mem_openSquare_or_notMem_closedSquare m)

end Sites

end TNLean.PEPS.Approximation
