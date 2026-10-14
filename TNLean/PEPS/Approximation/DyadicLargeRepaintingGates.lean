/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicPatchRewriteGates

/-!
# Gate data of the large-scale repaintings

For `n > K₀ t` the polynomial-PEPS manuscript repaints a square `S` of side `n` by the edge
construction: a central birth, then along each edge an auxiliary sheet initialized at `C_e`, its
births, a lens exchange, and the main births and deaths, each preceded by a point treatment that
homogenizes the involved sheets near the marks and followed by its removal
(`06-geometry.tex:142–241, 328–390`). The lifetime argument (`06-geometry.tex:585–596`) needs
that every party of these gates is an owner of a block next to `S`: “At a level-`n` repainting,
every active main owner is an `n`- or `2n`-block owner. On the affected footprints those blocks
lie at distance `O(n)` from the repainted square. … An auxiliary uses only the labels of the
local edge and point diagrams; its uniform initial owner `C` is the actual neighboring-block
owner.”

This file proves the locality part of that statement for the guides of the schedule and for the
patch data of their gates. With the square moved to `[0, n] ^ 2`, call a guide *local* over a base
guide `b` (the starting main guide, or the uniform auxiliary guide `C_e`) if it agrees with `b`
outside the `n / 2`-neighborhood of the closed square and takes only the *local labels* on its
`n`-neighborhood: the final label `B` and the values of the starting guide there. Then:

* the starting main guide, the guide after the central birth, the completed guides, every main
  and auxiliary guide of an edge construction with any of its normal words, the fresh auxiliary
  guide, and every guide obtained from local guides by homogenizing to a local label on a set
  inside the `n / 2`-neighborhood (the point treatments, for `t ≤ n / 2`) or by replacing one of
  them by a local guide over another base on such a set are local; in particular both sheets after
  the lens exchange, which lies in the band of its edge, are local over their own bases;
* two local guides over the same base differ only inside the `n / 2`-neighborhood;
* for the block guides of a level, every local label that is a block party is used by the
  repainting of the square, in the sense of `TNLean.PEPS.Approximation.RepaintingUses`.

A gate of a large-scale repainting is described by patch data
(`TNLean.PEPS.Approximation.GuidePatchRewrite`) whose old and new guides are local guides over one
base and whose footprint lies within distance `n` of the square
(`GuidePatchRewrite.IsLargeRepaintingStep`). For a point treatment this is the patch net of the
source's small-patch rewrite, of mesh `ν t` about a mark (`exists_pointTreatment`); conditions 1–3
of Lemma `lem:small-rewrite` are not checked here. For a bulk birth, death or exchange the gate is
given by Lemma `lem:birth` or `lem:exchange`, and the patch data here (`exists_bulkStep`) is a net
of mesh `ν n` over the `3n/4`-neighborhood of the square that covers the changed set and the
affected outer holes. Its parties contain the raw owners on the changed set, the affected outer
holes and the tag holders of those holes; it serves only to bound the parties of the gate. In both
cases every block party of the patch data is used by the repainting of `S`
(`IsLargeRepaintingStep.uses`), so the conditional lifetime bound of
`TNLean.PEPS.Approximation.card_gates_le_of_uses` applies, under the hypothesis that each gate's
block parties are parties of its patch data, to schedules that mix large-scale repaintings, direct
repaintings and junction resizes (`card_gates_le_of_repaintingRewrites`).

The conditions of Lemma `lem:small-rewrite` and of the birth and exchange lemmas are not verified
here, and the reduction of a gate's parties to those of its patch data is the hypothesis of the
count, as in `TNLean.PEPS.Approximation.card_gates_le_of_guidePatchRewrites`.

## Main results

* `TNLean.PEPS.Approximation.RepaintingBaseline.IsLocalGuide`: local guides, and the instances
  `isLocalGuide_completedGuide`, `isLocalGuide_mainGuide`, `isLocalGuide_auxGuide`,
  `isLocalGuide_treatedStartMain`, `isLocalGuide_treatedAux`, `IsLocalGuide.homogenize`,
  `IsLocalGuide.piecewise`, `isLocalGuide_exchangedMain`, `isLocalGuide_exchangedAux`.
* `TNLean.PEPS.Approximation.RepaintingBaseline.IsLocalGuide.changed_subset`: two local guides
  over one base differ only near the square.
* `TNLean.PEPS.Approximation.repaintingUses_of_mem_localLabels`: local labels of a level are
  used by the repainting.
* `TNLean.PEPS.Approximation.GuidePatchRewrite.IsLargeRepaintingStep.uses`,
  `TNLean.PEPS.Approximation.exists_pointTreatment`, `TNLean.PEPS.Approximation.exists_bulkStep`,
  `TNLean.PEPS.Approximation.card_gates_le_of_repaintingRewrites`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the edge construction (lines
  142–241), the point treatment and the bulk operations (lines 328–437), the point-treatment
  patches (lines 482–505), and the party lifetimes (lines 572–631).
-/

namespace TNLean.PEPS.Approximation

open Set Metric SquareEdge

/-! ### Points of the square and its neighborhoods -/

/-- The point at parallel coordinate `s ∈ [0, n]` on an edge lies in the closed square. -/
theorem SquareEdge.point_mem_closedSquare {n s : ℝ} (e : SquareEdge) (h0 : 0 ≤ s) (h1 : s ≤ n) :
    e.point n s 0 ∈ closedSquare n := by
  rw [mem_closedSquare]
  cases e <;> simp only [SquareEdge.point, sub_zero] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The band `-8 < x < 2` of an edge lies in the `n / 2`-neighborhood of the closed square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-band`,
`06-geometry.tex:146–150`. -/
theorem edgeBand_subset_thickening {n : ℝ} (hn : 0 < n) (e : SquareEdge) :
    edgeBand n e (-8) 2 ⊆ thickening (n / 2) (closedSquare n) := by
  intro p hp
  by_cases hd : 0 ≤ e.nor n p
  · exact self_subset_thickening (half_pos hn) _ (mem_closedSquare_of_mem_edgeBand hp hd)
  · obtain ⟨h1, h2, h3, -⟩ := hp
    have w1 := bandWidth_le_left n (e.par p)
    have w2 := bandWidth_le_right n (e.par p)
    refine mem_thickening_iff.2 ⟨_, e.point_mem_closedSquare h1.le h2.le, ?_⟩
    rw [SquareEdge.dist_eq n e, par_point, nor_point, sub_self, abs_zero, sub_zero,
      abs_of_neg (not_le.1 hd)]
    refine max_lt (half_pos hn) ?_
    linarith [min_le_left (e.par p) (n - e.par p), min_le_right (e.par p) (n - e.par p),
      show bandWidth n (e.par p) = min (e.par p) (n - e.par p) / 1000 from rfl]

/-- The treated squares of radius `t ≤ n / 2` about the endpoints of an edge lie in the
`n / 2`-neighborhood of the closed square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–333`. -/
theorem edgeTreated_subset_thickening {n t : ℝ} (hn : 0 < n) (ht : t ≤ n / 2) (e : SquareEdge) :
    edgeTreated n e t ⊆ thickening (n / 2) (closedSquare n) := by
  rintro p (hp | hp) <;> exact mem_thickening_iff.2
    ⟨_, e.point_mem_closedSquare (by linarith) (by linarith), (mem_ball.1 hp).trans_le ht⟩

/-- The lens `-7 < x < -7/2` of an edge lies in the `n / 2`-neighborhood of the closed square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-lens`,
`06-geometry.tex:199–202`. -/
theorem edgeLens_subset_thickening {n : ℝ} (hn : 0 < n) (e : SquareEdge) :
    edgeLens n e ⊆ thickening (n / 2) (closedSquare n) :=
  (edgeBand_mono (by norm_num) (by norm_num)).trans (edgeBand_subset_thickening hn e)

/-- The treated squares of radius `t ≤ n / 2` about the four corners lie in the
`n / 2`-neighborhood of the closed square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–333`. -/
theorem cornerTreated_subset_thickening {n t : ℝ} (hn : 0 < n) (ht : t ≤ n / 2) :
    cornerTreated n t ⊆ thickening (n / 2) (closedSquare n) := by
  have hc : ∀ a b : ℝ, (a = 0 ∨ a = n) → (b = 0 ∨ b = n) → (a, b) ∈ closedSquare n := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> rw [mem_closedSquare] <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  rintro p ((hp | hp) | (hp | hp)) <;>
    exact mem_thickening_iff.2 ⟨_, hc _ _ (by simp) (by simp), (mem_ball.1 hp).trans_le ht⟩

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-! ### Local labels and local guides -/

/-- The local labels of a repainting: the final label `B` and the values of the starting guide
within sup distance `n` of the closed square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “An auxiliary uses only the labels of the
local edge and point diagrams”, `06-geometry.tex:585–596`. -/
def localLabels : Set ι :=
  insert R.finalLabel (R.guide '' thickening R.n (closedSquare R.n))

/-- A guide is local over the base guide `b` if it takes only local labels within sup distance
`n` of the closed square and agrees with `b` outside the `n / 2`-neighborhood of the closed
square. The bases are the starting main guide and the uniform auxiliary guide `C_e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:227–241, 585–596`. -/
def IsLocalGuide (b g : ℝ × ℝ → ι) : Prop :=
  (∀ p ∈ thickening R.n (closedSquare R.n), g p ∈ R.localLabels) ∧
    ∀ p ∉ thickening (R.n / 2) (closedSquare R.n), g p = b p

theorem finalLabel_mem_localLabels : R.finalLabel ∈ R.localLabels :=
  mem_insert _ _

theorem guide_mem_localLabels {p : ℝ × ℝ} (hp : p ∈ thickening R.n (closedSquare R.n)) :
    R.guide p ∈ R.localLabels :=
  mem_insert_of_mem _ (mem_image_of_mem _ hp)

/-- The old label `A` is a local label. -/
theorem oldLabel_mem_localLabels : R.oldLabel ∈ R.localLabels := by
  have hn := R.n_pos
  have hp : (R.n / 2, R.n / 2) ∈ openSquare R.n :=
    mem_openSquare.2 ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [← R.guide_openSquare _ hp]
  exact R.guide_mem_localLabels
    (self_subset_thickening hn _ (openSquare_subset_closedSquare _ hp))

/-- The label `C_e` across an edge is a local label.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “its uniform initial owner `C` is the actual
neighboring-block owner”, `06-geometry.tex:590–592`. -/
theorem nbrLabel_mem_localLabels (e : SquareEdge) : R.nbrLabel e ∈ R.localLabels := by
  have hn := R.n_pos
  have hp : e.point R.n (R.n / 2) (-(R.n / 2)) ∈ edgeNeighbor R.n e := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [par_point, nor_point] <;> linarith
  rw [← R.guide_edgeNeighbor e _ hp]
  refine R.guide_mem_localLabels (mem_thickening_iff.2
    ⟨_, e.point_mem_closedSquare (s := R.n / 2) (by linarith) (by linarith), ?_⟩)
  rw [SquareEdge.dist_eq R.n e, par_point, par_point, nor_point, nor_point, sub_self, abs_zero,
    sub_zero, abs_neg, abs_of_pos (half_pos hn)]
  exact max_lt hn (half_lt_self hn)

/-- Every value of a normal word of an edge construction is a local label. -/
theorem edgeWords_mem_localLabels {e : SquareEdge} {W : ℝ → ι}
    (hW : W ∈ edgeWords R.oldLabel R.finalLabel (R.nbrLabel e)) (x : ℝ) :
    W x ∈ R.localLabels := by
  rcases edgeWords_mem _ _ _ hW x with h | h | h <;> rw [h]
  · exact R.oldLabel_mem_localLabels
  · exact R.finalLabel_mem_localLabels
  · exact R.nbrLabel_mem_localLabels e

/-- The starting main guide is local over itself. -/
theorem isLocalGuide_guide : R.IsLocalGuide R.guide R.guide :=
  ⟨fun _ hp => R.guide_mem_localLabels hp, fun _ _ => rfl⟩

/-- The fresh auxiliary guide, uniform at `C_e`, is local over itself.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:187–189`. -/
theorem isLocalGuide_const (e : SquareEdge) :
    R.IsLocalGuide (fun _ => R.nbrLabel e) (fun _ => R.nbrLabel e) :=
  ⟨fun _ _ => R.nbrLabel_mem_localLabels e, fun _ _ => rfl⟩

variable {R}

/-- Changing a local guide on a set inside the `n / 2`-neighborhood to local labels gives a local
guide over the same base. -/
theorem IsLocalGuide.update {b g g' : ℝ × ℝ → ι} (hg : R.IsLocalGuide b g) {U : Set (ℝ × ℝ)}
    (hU : U ⊆ thickening (R.n / 2) (closedSquare R.n)) (hmem : ∀ p ∈ U, g' p ∈ R.localLabels)
    (hoff : ∀ p ∉ U, g' p = g p) : R.IsLocalGuide b g' := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · by_cases hpU : p ∈ U
    · exact hmem p hpU
    · rw [hoff p hpU]
      exact hg.1 p hp
  · rw [hoff p fun h => hp (hU h)]
    exact hg.2 p hp

/-- **Homogenization.** Homogenizing a local guide to a local label on a set inside the
`n / 2`-neighborhood of the square, as the point treatment does with the surrounding label `P∘`
on the treated squares, gives a local guide over the same base.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–340`. -/
theorem IsLocalGuide.homogenize {b g : ℝ × ℝ → ι} (hg : R.IsLocalGuide b g)
    {U : Set (ℝ × ℝ)} (hU : U ⊆ thickening (R.n / 2) (closedSquare R.n)) {P : ι}
    (hP : P ∈ R.localLabels) : R.IsLocalGuide b (TNLean.PEPS.Approximation.homogenize U P g) :=
  hg.update hU (fun _ hp => by rw [homogenize_of_mem hp]; exact hP)
    fun _ hp => homogenize_of_notMem hp

open Classical in
/-- **Exchange.** Replacing a local guide over `b` by a local guide over another base `b'` on a set
`Y` inside the `n / 2`-neighborhood of the square, as the lens exchange does between the main and
the auxiliary sheet on the lens, gives a local guide over `b`. The two sheets need not share a
base: each keeps its own outside the neighborhood.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:198–212, 341–343`. -/
theorem IsLocalGuide.piecewise {b b' g g' : ℝ × ℝ → ι} (hg : R.IsLocalGuide b g)
    (hg' : R.IsLocalGuide b' g') {Y : Set (ℝ × ℝ)}
    (hY : Y ⊆ thickening (R.n / 2) (closedSquare R.n)) :
    R.IsLocalGuide b fun p => if p ∈ Y then g' p else g p :=
  hg.update hY
    (fun p hp => by
      rw [ite_eq_left hp]
      exact hg'.1 p (thickening_mono (half_le_self R.n_pos.le) _ (hY hp)))
    fun _ hp => ite_eq_right hp

/-- A band update of a local guide by a word with local labels is local over the same base. -/
theorem IsLocalGuide.bandUpdate {b g : ℝ × ℝ → ι} (hg : R.IsLocalGuide b g) (e : SquareEdge)
    {W : ℝ → ι} (hW : ∀ x, W x ∈ R.localLabels) :
    R.IsLocalGuide b (TNLean.PEPS.Approximation.bandUpdate R.n e W g) :=
  hg.update (edgeBand_subset_thickening R.n_pos e)
    (fun p hp => by rw [bandUpdate_of_mem hp]; exact hW _) fun _ hp => bandUpdate_of_notMem hp

/-- **Changed sets are local.** Two local guides over one base differ only inside the
`n / 2`-neighborhood of the closed square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “On the affected footprints those blocks lie at
distance `O(n)` from the repainted square”, `06-geometry.tex:227–241, 585–589`. -/
theorem IsLocalGuide.changed_subset {b g₁ g₂ : ℝ × ℝ → ι} (h₁ : R.IsLocalGuide b g₁)
    (h₂ : R.IsLocalGuide b g₂) :
    {p | g₁ p ≠ g₂ p} ⊆ thickening (R.n / 2) (closedSquare R.n) := by
  intro p hp
  by_contra h
  exact hp ((h₁.2 p h).trans (h₂.2 p h).symm)

variable (R)

/-! ### The guides of the schedule -/

/-- The guide after the central birth is local over the starting guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160`. -/
theorem isLocalGuide_centralGuide : R.IsLocalGuide R.guide R.centralGuide :=
  R.isLocalGuide_guide.update
    ((centralRegion_subset_openSquare R.n).trans
      ((openSquare_subset_closedSquare R.n).trans
        (self_subset_thickening (half_pos R.n_pos) _)))
    (fun p hp => by rw [R.centralGuide_of_mem hp]; exact R.finalLabel_mem_localLabels)
    fun _ hp => R.centralGuide_of_notMem hp

/-- Every completed guide is local over the starting guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:219–241`. -/
theorem isLocalGuide_completedGuide (E : List SquareEdge) :
    R.IsLocalGuide R.guide (R.completedGuide E) := by
  induction E with
  | nil => exact R.isLocalGuide_centralGuide
  | cons e E ih =>
    refine ih.bandUpdate e fun x => R.edgeWords_mem_localLabels (e := e) ?_ x
    exact Or.inr ⟨mainDeathB R.finalLabel (R.nbrLabel e), by simp [edgeOperations], Or.inr
      (Or.inl rfl)⟩

/-- **Main guides.** Every main guide of an edge construction, with any of its normal words, is
local over the starting guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:161–221, 585–596`. -/
theorem isLocalGuide_mainGuide (E : List SquareEdge) (e : SquareEdge) {W : ℝ → ι}
    (hW : W ∈ edgeWords R.oldLabel R.finalLabel (R.nbrLabel e)) :
    R.IsLocalGuide R.guide (R.mainGuide E e W) :=
  (R.isLocalGuide_completedGuide E).bandUpdate e (R.edgeWords_mem_localLabels hW)

/-- **Auxiliary guides.** Every auxiliary guide of an edge construction, with any of its normal
words, is local over the uniform guide `C_e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “An auxiliary uses only the labels of the
local edge and point diagrams; its uniform initial owner `C` is the actual neighboring-block
owner”, `06-geometry.tex:187–197, 590–592`. -/
theorem isLocalGuide_auxGuide (e : SquareEdge) {W : ℝ → ι}
    (hW : W ∈ edgeWords R.oldLabel R.finalLabel (R.nbrLabel e)) :
    R.IsLocalGuide (fun _ => R.nbrLabel e) (R.auxGuide e W) :=
  (R.isLocalGuide_const e).bandUpdate e (R.edgeWords_mem_localLabels hW)

/-- The treated main guide of an exchange, homogenized to `C_e` near the endpoints of `e`, is
local over the starting guide for `t ≤ n / 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:334–343`. -/
theorem isLocalGuide_treatedStartMain {t : ℝ} (ht : t ≤ R.n / 2) (E : List SquareEdge)
    (e : SquareEdge) : R.IsLocalGuide R.guide (R.treatedStartMain t E e) :=
  (R.isLocalGuide_mainGuide E e (mem_insert _ _)).homogenize
    (edgeTreated_subset_thickening R.n_pos ht e) (R.nbrLabel_mem_localLabels e)

/-- The treated auxiliary guide of an exchange, homogenized to `C_e` near the endpoints of `e`,
is local over the uniform guide `C_e` for `t ≤ n / 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:334–343`. -/
theorem isLocalGuide_treatedAux {t : ℝ} (ht : t ≤ R.n / 2) (e : SquareEdge) :
    R.IsLocalGuide (fun _ => R.nbrLabel e) (R.treatedAux t e) := by
  refine (R.isLocalGuide_auxGuide e ?_).homogenize (edgeTreated_subset_thickening R.n_pos ht e)
    (R.nbrLabel_mem_localLabels e)
  exact Or.inr ⟨auxBirthC R.oldLabel R.finalLabel (R.nbrLabel e), by simp [edgeOperations],
    Or.inr (Or.inl rfl)⟩

open Classical in
/-- **The exchanged main guide.** After the lens exchange along `e` the main sheet carries the
treated auxiliary guide on the lens and the treated main guide elsewhere; for `t ≤ n / 2` it is
local over the starting guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:198–212, 341–343`. -/
theorem isLocalGuide_exchangedMain {t : ℝ} (ht : t ≤ R.n / 2) (E : List SquareEdge)
    (e : SquareEdge) :
    R.IsLocalGuide R.guide fun p =>
      if p ∈ edgeLens R.n e then R.treatedAux t e p else R.treatedStartMain t E e p :=
  (R.isLocalGuide_treatedStartMain ht E e).piecewise (R.isLocalGuide_treatedAux ht e)
    (edgeLens_subset_thickening R.n_pos e)

open Classical in
/-- **The exchanged auxiliary guide.** After the lens exchange along `e` the auxiliary sheet
carries the treated main guide on the lens and the treated auxiliary guide elsewhere; for
`t ≤ n / 2` it is local over the uniform guide `C_e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:198–212, 341–343`. -/
theorem isLocalGuide_exchangedAux {t : ℝ} (ht : t ≤ R.n / 2) (E : List SquareEdge)
    (e : SquareEdge) :
    R.IsLocalGuide (fun _ => R.nbrLabel e) fun p =>
      if p ∈ edgeLens R.n e then R.treatedStartMain t E e p else R.treatedAux t e p :=
  (R.isLocalGuide_treatedAux ht e).piecewise (R.isLocalGuide_treatedStartMain ht E e)
    (edgeLens_subset_thickening R.n_pos e)

end RepaintingBaseline

/-! ### Local labels of a level -/

section Parties

variable {ι : Type*} {party : ℕ × ℕ × ℕ → ι} {ph : ι}

/-- The starting guide of the repainting of the square `(r, s)` of side `2 ^ j'` during the pass
to level `2 ^ j'`, moved to the origin, with final label the new party of the square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–100, 142–143`. -/
noncomputable def levelBaseline (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j' : ℕ)
    (done : Set (ℤ × ℤ)) (r s : ℕ) : RepaintingBaseline ι :=
  blockBaseline (pow_pos two_pos j') (levelLabels M (oldParty party j') (newParty party j') ph done)
    ((r : ℤ), (s : ℤ)) (newParty party j' ((r : ℤ), (s : ℤ)))

/-- **Local labels are used.** In the repainting of the square `(r, s)` of side `2 ^ j'`, every
local label that is a block party, among them the labels `A`, `B` and `C_e` of the edge diagrams
and every label of the starting guide within distance `2 ^ j'` of the square, is a party used by
the repainting.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “every active main owner is an `n`- or
`2n`-block owner. On the affected footprints those blocks lie at distance `O(n)` from the
repainted square. … An auxiliary uses only the labels of the local edge and point diagrams”,
`06-geometry.tex:585–596`. -/
theorem repaintingUses_of_mem_localLabels (hp : Function.Injective party)
    (hph : ∀ x, party x ≠ ph) (M : ℤ) (j' : ℕ) (done : Set (ℤ × ℤ)) (r s : ℕ)
    {x : ℕ × ℕ × ℕ} (hx : party x ∈ (levelBaseline party ph M j' done r s).localLabels) :
    RepaintingUses j' r s x := by
  rcases hx with hx | ⟨q, hq, hqx⟩
  · have := hp hx
    simp only [Int.toNat_natCast] at this
    exact ⟨r, s, by omega, by omega, by omega, by omega, Or.inl this⟩
  · obtain ⟨y, hy, hqy⟩ := mem_thickening_iff.1 hq
    set o := blockCorner ((2 : ℝ) ^ j') ((r : ℤ), (s : ℤ))
    refine repaintingUses_of_blockGuide_eq hp hph M j' done (y := y + o) (p := q + o)
      (by rwa [add_sub_cancel_right]) (by rwa [dist_add_right]) ?_
    simpa [levelBaseline, blockBaseline] using hqx

/-! ### Gates of the large-scale repaintings -/

namespace GuidePatchRewrite

/-- **A gate of a large-scale repainting.** The patch data of a gate of the repainting of the
square `(r, s)` of side `n = 2 ^ j'` during the pass to level `2 ^ j'`: its old and new guides are
local guides over one base (a main or an auxiliary sheet of the edge construction), moved to the
square, and its footprint lies within sup distance `n` of the closed square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–241, 328–437, 585–596`.
-/
def IsLargeRepaintingStep (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j' r s : ℕ)
    (G : GuidePatchRewrite ι) : Prop :=
  ∃ (done : Set (ℤ × ℤ)) (b g₁ g₂ : ℝ × ℝ → ι),
    (levelBaseline party ph M j' done r s).IsLocalGuide b g₁ ∧
    (levelBaseline party ph M j' done r s).IsLocalGuide b g₂ ∧
    G.old = shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₁ ∧
    G.new = shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₂ ∧ 0 < G.holeOuter ∧
    ∀ p ∈ G.footprint,
      p - blockCorner (2 ^ j') ((r : ℤ), (s : ℤ)) ∈ thickening (2 ^ j') (closedSquare (2 ^ j'))

/-- **Parties of a large-scale repainting.** Every block party of a gate of the large-scale
repainting of the square `(r, s)` of side `2 ^ j'` is used by that repainting.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:585–596`, with Lemma
`lem:small-rewrite`, `05-frames.tex:203–216`. -/
theorem IsLargeRepaintingStep.uses (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph)
    {M : ℤ} {j' r s : ℕ} {G : GuidePatchRewrite ι}
    (hG : G.IsLargeRepaintingStep party ph M j' r s) {x : ℕ × ℕ × ℕ}
    (hx : party x ∈ G.parties ph) : RepaintingUses j' r s x := by
  obtain ⟨done, b, g₁, g₂, h₁, h₂, hold, hnew, h0, hfp⟩ := hG
  refine repaintingUses_of_mem_localLabels hp hph M j' done r s ?_
  rcases G.parties_subset ph h0 hx with ⟨p, hpF, hpx⟩ | ⟨p, hpF, hpx⟩
  · rw [hold, shiftGuide] at hpx
    rw [← hpx]
    exact h₁.1 _ (hfp p hpF)
  · rw [hnew, shiftGuide] at hpx
    rw [← hpx]
    exact h₂.1 _ (hfp p hpF)

end GuidePatchRewrite

/-! ### Construction by square nets -/

/-- A finite square net of mesh `u` over a set `K` inside a ball gives patch data of a
large-scale repainting step between two local guides over one base, provided every point within
`3 u` of `K` is within distance `n` of the square and the affected outer holes lie in `K`. -/
theorem exists_largeRepaintingStep_of_cover (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j' : ℕ)
    (done : Set (ℤ × ℤ)) (r s : ℕ) {b g₁ g₂ : ℝ × ℝ → ι}
    (h₁ : (levelBaseline party ph M j' done r s).IsLocalGuide b g₁)
    (h₂ : (levelBaseline party ph M j' done r s).IsLocalGuide b g₂) {K : Set (ℝ × ℝ)}
    {c : ℝ × ℝ} {ρ u : ℝ} (hρ : 0 ≤ ρ) (hu : 0 < u) (hK : K ⊆ closedBall c ρ)
    (H : Finset (ℝ × ℝ)) {R : ℝ} (hR : 0 < R) (hH : ∀ h ∈ H, closedBall h R ⊆ K)
    (hnear : ∀ p y, y ∈ K → dist p y < 3 * u →
      p - blockCorner (2 ^ j') ((r : ℤ), (s : ℤ)) ∈ thickening (2 ^ j') (closedSquare (2 ^ j'))) :
    ∃ G : GuidePatchRewrite ι, G.IsLargeRepaintingStep party ph M j' r s ∧
      G.old = shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₁ ∧
      G.new = shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₂ ∧
      G.holes = H ∧ G.holeOuter = R ∧ G.mesh = u ∧
      (G.centers.card : ℝ) ≤ (2 * (ρ + u) / u + 1) ^ 2 ∧ K ⊆ ⋃ c ∈ G.centers, ball c u := by
  classical
  obtain ⟨net, hcard, hcov, hnet⟩ := exists_netCover hu hρ hK
  let G : GuidePatchRewrite ι :=
    { old := shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₁
      new := shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₂
      centers := net.image (blockCorner u)
      mesh := u
      holes := H
      holeOuter := R }
  refine ⟨G, ⟨done, b, g₁, g₂, h₁, h₂, rfl, rfl, hR, ?_⟩, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rintro z (hz | hz)
    · obtain ⟨c', hc', hz⟩ := mem_iUnion₂.1 hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc'
      obtain ⟨y, hy, hky⟩ := hnet k hk
      refine hnear z y hy ?_
      have := dist_triangle z (blockCorner u k) y
      have := mem_closedBall.1 hz
      linarith
    · obtain ⟨h, hh, hz⟩ := mem_iUnion₂.1 hz
      exact hnear z z (hH h hh hz) (by rw [dist_self]; positivity)
  · calc ((net.image (blockCorner u)).card : ℝ) ≤ net.card := by
          exact_mod_cast Finset.card_image_le
      _ ≤ _ := hcard
  · intro y hy
    obtain ⟨k, hk, hyk⟩ := hcov y hy
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)) (mem_ball.2 hyk)

/-- **The patches of a point treatment.** Let `0 < t`, `2 t ≤ n = 2 ^ j'`, `0 < ν` and
`2 ε₀ + 3 ν < 1`, and let `c` be a point of the closed square `[0, n] ^ 2`, such as a mark at a
corner of the repainted square. A homogenization or removal of a point treatment between two local
guides over one base, whose affected holes are centered within `t` of `c` with outer radius
`2 ε₀ t`, has patch data of a large-scale repainting step whose patches form a square net of mesh
`u = ν t`. The net has at most `(2 (1 + 2 ε₀ + ν) / ν + 1) ^ 2` patches, a number independent of
the scale, and their inner squares cover the treated square of radius `t` about `c` and the outer
footprints of the affected holes.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “For one mark in the large-scale case, work in
its radius-`2t` neighborhood. … Patches with inner radius `u = ν t`, centered on a square net of
mesh at most `u`, cover the treated square and all affected outer holes”, `06-geometry.tex:482–505`.
-/
theorem exists_pointTreatment (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j' : ℕ)
    (done : Set (ℤ × ℤ)) (r s : ℕ) {b g₁ g₂ : ℝ × ℝ → ι}
    (h₁ : (levelBaseline party ph M j' done r s).IsLocalGuide b g₁)
    (h₂ : (levelBaseline party ph M j' done r s).IsLocalGuide b g₂) {c : ℝ × ℝ}
    (hc : c ∈ closedSquare (2 ^ j')) {t ε₀ ν : ℝ} (ht : 0 < t) (htn : 2 * t ≤ 2 ^ j')
    (hε : 0 < ε₀) (hν : 0 < ν) (hεν : 2 * ε₀ + 3 * ν < 1) (H : Finset (ℝ × ℝ))
    (hH : ∀ h ∈ H, h ∈ closedBall (c + blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) t) :
    ∃ G : GuidePatchRewrite ι, G.IsLargeRepaintingStep party ph M j' r s ∧
      G.old = shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₁ ∧
      G.new = shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₂ ∧
      G.holes = H ∧ G.holeOuter = 2 * ε₀ * t ∧ G.mesh = ν * t ∧
      (G.centers.card : ℝ) ≤ (2 * ((1 + 2 * ε₀) + ν) / ν + 1) ^ 2 ∧
      closedBall (c + blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) t ∪
          (⋃ h ∈ H, closedBall h (2 * ε₀ * t)) ⊆ ⋃ c ∈ G.centers, ball c G.mesh := by
  set o := blockCorner ((2 : ℝ) ^ j') ((r : ℤ), (s : ℤ))
  have hK : closedBall (c + o) t ∪ (⋃ h ∈ H, closedBall h (2 * ε₀ * t)) ⊆
      closedBall (c + o) ((1 + 2 * ε₀) * t) := by
    rintro y (hy | hy)
    · exact closedBall_subset_closedBall (by nlinarith) hy
    · obtain ⟨h, hh, hy⟩ := mem_iUnion₂.1 hy
      have := dist_triangle y h (c + o)
      have := mem_closedBall.1 (hH h hh)
      have := mem_closedBall.1 hy
      exact mem_closedBall.2 (by nlinarith)
  obtain ⟨G, hG, hold, hnew, hholes, hR, hmesh, hcard, hcov⟩ :=
    exists_largeRepaintingStep_of_cover party ph M j' done r s h₁ h₂ (c := c + o)
      (ρ := (1 + 2 * ε₀) * t) (u := ν * t) (by positivity) (by positivity) hK H (by positivity)
      (fun h hh => subset_union_right.trans' (subset_biUnion_of_mem (u := fun h =>
        closedBall h (2 * ε₀ * t)) (Finset.mem_coe.2 hh)))
      (fun p y hy hpy => by
        refine mem_thickening_iff.2 ⟨_, hc, ?_⟩
        have h1 := mem_closedBall.1 (hK hy)
        have := dist_triangle p y (c + o)
        rw [← dist_add_right (p - o) c o, sub_add_cancel]
        nlinarith)
  refine ⟨G, hG, hold, hnew, hholes, hR, hmesh, ?_, by rw [hmesh]; exact hcov⟩
  calc (G.centers.card : ℝ) ≤ (2 * ((1 + 2 * ε₀) * t + ν * t) / (ν * t) + 1) ^ 2 := hcard
    _ = _ := by
      congr 2
      field_simp

/-- **The patch data of a bulk step.** Let `n = 2 ^ j'`, `0 < ν ≤ 1/12` and `0 < R ≤ n / 4`. A
bulk birth, death or exchange between two local guides over one base, whose affected outer holes
of radius `R` are centered in the `n / 2`-neighborhood of the square, has patch data of a
large-scale repainting step whose patches form a square net of mesh `ν n` over the
`3 n / 4`-neighborhood of the square. Their inner squares cover the changed set and the outer
footprints of the affected holes, and there are at most `(2 (5/4 + ν) / ν + 1) ^ 2` of them.

The bulk step itself is implemented by Lemma `lem:birth` or `lem:exchange`, not by this net; the
patch data serves to bound the parties of the step: its raw owners on the changed set and on the
affected outer holes, and their tag holders.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “The raw target `T` is therefore outside all
holes, compactly located in diameter `O(n)` … The set `T` has diameter `O(n)`”,
`06-geometry.tex:383–387, 421–430`, and the party lifetimes, lines 585–596. -/
theorem exists_bulkStep (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j' : ℕ)
    (done : Set (ℤ × ℤ)) (r s : ℕ) {b g₁ g₂ : ℝ × ℝ → ι}
    (h₁ : (levelBaseline party ph M j' done r s).IsLocalGuide b g₁)
    (h₂ : (levelBaseline party ph M j' done r s).IsLocalGuide b g₂) {ν R : ℝ} (hν : 0 < ν)
    (hν' : ν ≤ 1 / 12) (hR : 0 < R) (hRn : R ≤ 2 ^ j' / 4) (H : Finset (ℝ × ℝ))
    (hH : ∀ h ∈ H, h - blockCorner (2 ^ j') ((r : ℤ), (s : ℤ)) ∈
      thickening (2 ^ j' / 2) (closedSquare (2 ^ j'))) :
    ∃ G : GuidePatchRewrite ι, G.IsLargeRepaintingStep party ph M j' r s ∧
      G.old = shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₁ ∧
      G.new = shiftGuide (blockCorner (2 ^ j') ((r : ℤ), (s : ℤ))) g₂ ∧
      G.holes = H ∧ G.holeOuter = R ∧ G.mesh = ν * 2 ^ j' ∧
      (G.centers.card : ℝ) ≤ (2 * (5 / 4 + ν) / ν + 1) ^ 2 ∧
      {p | G.old p ≠ G.new p} ∪ (⋃ h ∈ H, closedBall h R) ⊆ ⋃ c ∈ G.centers, ball c G.mesh := by
  set n : ℝ := 2 ^ j' with hn
  have hn0 : 0 < n := pow_pos two_pos j'
  set o := blockCorner n ((r : ℤ), (s : ℤ))
  set K : Set (ℝ × ℝ) := {p | ∃ y ∈ closedSquare n, dist (p - o) y ≤ 3 * n / 4}
  set m : ℝ × ℝ := (n / 2, n / 2)
  have hm : ∀ y ∈ closedSquare n, dist y m ≤ n / 2 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 hy
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le, abs_le]
    simp only [m]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hK : K ⊆ closedBall (m + o) (5 / 4 * n) := by
    rintro p ⟨y, hy, hpy⟩
    refine mem_closedBall.2 ?_
    rw [← dist_sub_right p (m + o) o, add_sub_cancel_right]
    have := dist_triangle (p - o) y m
    have := hm y hy
    linarith
  have hHK : ∀ h ∈ H, closedBall h R ⊆ K := by
    intro h hh z hz
    obtain ⟨y, hy, hhy⟩ := mem_thickening_iff.1 (hH h hh)
    refine ⟨y, hy, ?_⟩
    have := dist_triangle (z - o) (h - o) y
    rw [dist_sub_right] at this
    have := mem_closedBall.1 hz
    linarith
  obtain ⟨G, hG, hold, hnew, hholes, hRG, hmesh, hcard, hcov⟩ :=
    exists_largeRepaintingStep_of_cover party ph M j' done r s h₁ h₂ (c := m + o)
      (ρ := 5 / 4 * n) (u := ν * n) (by positivity) (by positivity) hK H hR hHK
      (fun p y hy hpy => by
        obtain ⟨z, hz, hyz⟩ := hy
        refine mem_thickening_iff.2 ⟨_, hz, ?_⟩
        have := dist_triangle (p - o) (y - o) z
        rw [dist_sub_right] at this
        nlinarith)
  refine ⟨G, hG, hold, hnew, hholes, hRG, hmesh, ?_, ?_⟩
  · calc (G.centers.card : ℝ) ≤ (2 * (5 / 4 * n + ν * n) / (ν * n) + 1) ^ 2 := hcard
      _ = _ := by
        congr 2
        field_simp
  · rw [hmesh]
    refine (union_subset (fun p hp => ?_) fun p hp => ?_).trans hcov
    · rw [hold, hnew] at hp
      obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.1 (h₁.changed_subset h₂ hp)
      exact ⟨y, hy, by
        simp only [levelBaseline, blockBaseline] at hpy
        linarith⟩
    · obtain ⟨h, hh, hp⟩ := mem_iUnion₂.1 hp
      exact hHK h hh hp

end Parties

/-! ### Lifetime participation -/

/-- **Bounded lifetime participation with large-scale repaintings.** Let the gates `Γ` of a
schedule on the hierarchy of `[0, 2 ^ k] ^ 2` belong to repaintings and junction resizes, `ev γ`,
with at most `G` gates for each, and let each gate `γ` carry patch data `rw γ`: for a repainting,
either the direct repainting of its square or a gate of its large-scale repainting (a point
treatment, or a bulk birth, death or exchange); for a junction, the resize of its hole. If the
block party `x` participates in a gate only when it is a party of the gate's patch data, then `x`
participates in at most `64 G` gates.

The bound is conditional on that hypothesis `hP`, the conclusion of Lemma `lem:small-rewrite` and
of the birth and exchange lemmas for the parties of the patch data.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex:31–32`, and the lifetime argument, `06-geometry.tex:572–631`. -/
theorem card_gates_le_of_repaintingRewrites {ι : Type*} {party : ℕ × ℕ × ℕ → ι} {ph : ι}
    (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph) {k : ℕ} {Γ : Type*}
    [Fintype Γ] (ev : Γ → DyadicSquare k ⊕ DyadicJunction k) {G : ℕ}
    (hG : ∀ e, (Finset.univ.filter fun γ => ev γ = e).card ≤ G) (rw : Γ → GuidePatchRewrite ι)
    (hrw : ∀ γ, Sum.elim
      (fun S => (rw γ).IsDirectRepainting party ph ((2 : ℤ) ^ (k - (S.1 : ℕ))) S.1 S.2.1 S.2.2 ∨
        (rw γ).IsLargeRepaintingStep party ph ((2 : ℤ) ^ (k - (S.1 : ℕ))) S.1 S.2.1 S.2.2)
      (fun J => (rw γ).IsJunctionResize party ph ((2 : ℤ) ^ (k - (J.1 : ℕ))) J.1 J.2.1 J.2.2)
      (ev γ))
    (x : ℕ × ℕ × ℕ) (P : Γ → Prop) [DecidablePred P]
    (hP : ∀ γ, P γ → party x ∈ (rw γ).parties ph) :
    (Finset.univ.filter P).card ≤ 64 * G := by
  refine card_gates_le_of_uses ev hG x P fun γ hγ => ?_
  have h := hrw γ
  rcases hev : ev γ with S | J <;> rw [hev] at h
  · rcases h with h | h
    · exact h.uses hp hph (hP γ hγ)
    · exact h.uses hp hph (hP γ hγ)
  · exact h.uses hp hph (hP γ hγ)

end TNLean.PEPS.Approximation
