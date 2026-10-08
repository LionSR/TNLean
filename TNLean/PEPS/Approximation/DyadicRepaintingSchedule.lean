/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicRepaintingClearance

/-!
# The schedule of guides of a large-scale dyadic repainting

Let `S = [0, n] ^ 2` be an `n`-square of the padded dyadic hierarchy that is being repainted
from its old label `A` to its final label `B`. At the start of the repainting the main guide is
`A` on the open square and carries one label `C_e` on the open exterior neighboring square across
each edge `e`. The repainting first births `B` in the central region, and then processes the
four edges one at a time: along an edge `e` the guides of the main sheet and of a fresh auxiliary
sheet change only on the band `-8 < x < 2`, through the normal words of
`TNLean.PEPS.Approximation.DyadicRepaintingClearance`. This file constructs these guides and
proves:

* the guides after the central birth and after any set of completed edges, and their values on
  each band, using the disjointness of the bands along distinct edges;
* that at the start of an edge operation the main guide carries the normal word `C | A | B` on
  the band of that edge, off the two interface curves `x = 0` and `x = 1`;
* that the lens exchange produces the main word `eq:geometry-main-word`, that consecutive
  elementary operations on one sheet match, and that after the four edges `S` has label `B`
  while every point outside the closed square keeps its starting label;
* the estimates of Lemma 7.2 (`lem:geometry-angular`) for every elementary birth, death and lens
  exchange of this schedule, with `a₀ = 1/5000`, and the diameter bound on the changed regions;
* the labels of the main guides: every value is the final label or a value of the starting guide,
  and outside the closed square together with the four exterior bands the main guides keep their
  starting values.

A guide of the source is specified by its open polygonal chambers and read at the lattice sites
after one small generic displacement (`06-geometry.tex:62–80`). A guide here is a labelling of the
whole plane, and the estimates are proved for the labellings that the schedule specifies at each
operation. Within an edge construction consecutive labellings match exactly. At the start of the
construction along `e` the schedule passes from the completed guide to the main guide with the
starting word `C | A | B`; the two agree only off the curves `x = 0` and `x = 1`
(`RepaintingBaseline.completedGuide_eq_mainGuide_start`), and no lattice site lies on those curves
(`IsCellCenter.notMem_edgeInterface` in `TNLean.PEPS.Approximation.DyadicLevelSchedule`). The
estimates are not claimed for every labelling that agrees with the schedule's off these curves:
the set where two labellings differ depends on their values on a curve.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: guides (lines 69–80),
  the repainting by levels (lines 82–100), the edge construction (lines 142–241), and Lemma 7.2
  `lem:geometry-angular` (lines 243–319).
-/

namespace TNLean.PEPS.Approximation

open Set Metric SquareEdge

/-! ### The square and the bands -/

/-- The open square `(0, n) ^ 2`. -/
def openSquare (n : ℝ) : Set (ℝ × ℝ) := Ioo 0 n ×ˢ Ioo 0 n

/-- The closed square `[0, n] ^ 2`. -/
def closedSquare (n : ℝ) : Set (ℝ × ℝ) := Icc 0 n ×ˢ Icc 0 n

theorem mem_openSquare {n : ℝ} {p : ℝ × ℝ} :
    p ∈ openSquare n ↔ 0 < p.1 ∧ p.1 < n ∧ 0 < p.2 ∧ p.2 < n := by
  simp only [openSquare, Set.mem_prod, Set.mem_Ioo, and_assoc]

theorem mem_closedSquare {n : ℝ} {p : ℝ × ℝ} :
    p ∈ closedSquare n ↔ 0 ≤ p.1 ∧ p.1 ≤ n ∧ 0 ≤ p.2 ∧ p.2 ≤ n := by
  simp only [closedSquare, Set.mem_prod, Set.mem_Icc, and_assoc]

theorem openSquare_subset_closedSquare (n : ℝ) : openSquare n ⊆ closedSquare n := by
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := mem_openSquare.1 hp
  exact mem_closedSquare.2 ⟨h1.le, h2.le, h3.le, h4.le⟩

/-- On the open square every edge has parallel coordinate in `(0, n)` and positive normal
coordinate. -/
theorem par_nor_of_mem_openSquare {n : ℝ} {p : ℝ × ℝ} (hp : p ∈ openSquare n) (e : SquareEdge) :
    0 < e.par p ∧ e.par p < n ∧ 0 < e.nor n p := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_openSquare.1 hp
  cases e <;> simp only [par, nor] <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem centralRegion_subset_openSquare (n : ℝ) : centralRegion n ⊆ openSquare n :=
  fun _ ⟨h1, h2, h3, h4, _⟩ => mem_openSquare.2 ⟨h1, h2, h3, h4⟩

/-- Bands grow with their normal intervals. -/
theorem edgeBand_mono {n : ℝ} {e : SquareEdge} {α β α' β' : ℝ} (hα : α' ≤ α) (hβ : β ≤ β') :
    edgeBand n e α β ⊆ edgeBand n e α' β' := by
  intro p ⟨h1, h2, h3, h4⟩
  have hw := bandWidth_nonneg h1.le h2.le
  exact ⟨h1, h2, (mul_le_mul_of_nonneg_right hα hw).trans_lt h3,
    h4.trans_le (mul_le_mul_of_nonneg_right hβ hw)⟩

/-- The nonnegative part of a band of normal ratio below `2` lies in the closed square, and its
positive part in the open square. -/
theorem mem_closedSquare_of_mem_edgeBand {n : ℝ} {e : SquareEdge} {α : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edgeBand n e α 2) (hd : 0 ≤ e.nor n p) : p ∈ closedSquare n := by
  obtain ⟨h1, h2, -, h4⟩ := hp
  have w1 := bandWidth_le_left n (e.par p)
  have w2 := bandWidth_le_right n (e.par p)
  rw [mem_closedSquare]
  cases e <;> simp only [par, nor] at * <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem mem_openSquare_of_mem_edgeBand {n : ℝ} {e : SquareEdge} {α : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edgeBand n e α 2) (hd : 0 < e.nor n p) : p ∈ openSquare n := by
  obtain ⟨h1, h2, -, h4⟩ := hp
  have w1 := bandWidth_le_left n (e.par p)
  have w2 := bandWidth_le_right n (e.par p)
  rw [mem_openSquare]
  cases e <;> simp only [par, nor] at * <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem notMem_closedSquare_of_mem_edgeNeighbor {n : ℝ} {e : SquareEdge} {p : ℝ × ℝ}
    (hp : p ∈ edgeNeighbor n e) : p ∉ closedSquare n := by
  obtain ⟨-, -, -, h4⟩ := hp
  rw [mem_closedSquare]
  cases e <;> simp only [nor] at h4 <;> intro h <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- A point of the open square outside the central region lies in the band `0 < x ≤ 1` of some
edge.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160`. -/
theorem exists_edgeBand_of_notMem_centralRegion {n : ℝ} {p : ℝ × ℝ} (hp : p ∈ openSquare n)
    (hc : p ∉ centralRegion n) :
    ∃ e : SquareEdge, p ∈ edgeBand n e (-8) 2 ∧ e.nor n p ≤ bandWidth n (e.par p) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_openSquare.1 hp
  have : ¬ ∀ e : SquareEdge, bandWidth n (e.par p) < e.nor n p := fun h => hc ⟨h1, h2, h3, h4, h⟩
  push Not at this
  obtain ⟨e, he⟩ := this
  obtain ⟨s1, s2, d0⟩ := par_nor_of_mem_openSquare hp e
  have hw := bandWidth_pos s1 s2
  exact ⟨e, ⟨s1, s2, by linarith, by linarith⟩, he⟩

/-- A point of the open square outside the bands `-8 < x < 2` of all edges lies in the central
region.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160, 227–236`. -/
theorem mem_centralRegion_of_forall_notMem {n : ℝ} {p : ℝ × ℝ} (hp : p ∈ openSquare n)
    (hb : ∀ e : SquareEdge, p ∉ edgeBand n e (-8) 2) : p ∈ centralRegion n := by
  by_contra hc
  obtain ⟨e, he, -⟩ := exists_edgeBand_of_notMem_centralRegion hp hc
  exact hb e he

/-- A lower bound on the distance from a point to every point of a set extends to its closure. -/
theorem le_dist_of_mem_closure {X : Type*} [PseudoMetricSpace X] {s : Set X} {y : X} {c : ℝ}
    (h : ∀ z ∈ s, c ≤ dist y z) {z : X} (hz : z ∈ closure s) : c ≤ dist y z :=
  closure_minimal h (isClosed_le continuous_const (continuous_const.dist continuous_id)) hz

/-! ### Band updates -/

open Classical in
/-- The guide `g` with its band `-8 < x < 2` along the edge `e` replaced by the normal word `W`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:161–170, 227–241`. -/
noncomputable def bandUpdate {ι : Type*} (n : ℝ) (e : SquareEdge) (W : ℝ → ι) (g : ℝ × ℝ → ι) :
    ℝ × ℝ → ι := fun p => if p ∈ edgeBand n e (-8) 2 then W (bandCoord n e p) else g p

section BandUpdate

variable {ι : Type*} {n : ℝ} {e : SquareEdge} {W : ℝ → ι} {g : ℝ × ℝ → ι} {p : ℝ × ℝ}

theorem bandUpdate_of_mem (hp : p ∈ edgeBand n e (-8) 2) :
    bandUpdate n e W g p = W (bandCoord n e p) := by
  classical
  simp only [bandUpdate, hp, ↓reduceIte]

theorem bandUpdate_of_notMem (hp : p ∉ edgeBand n e (-8) 2) : bandUpdate n e W g p = g p := by
  classical
  simp only [bandUpdate, hp, ↓reduceIte]

end BandUpdate

/-- **Clearance of a band update.** An elementary birth or death performed by band updates of one
sheet guide `g` satisfies the clearance estimate of Lemma 7.2.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:254–264, 283–293`. -/
theorem BandOperation.clearance_bandUpdate {ι : Type*} (op : BandOperation ι) {n : ℝ}
    (e : SquareEdge) (g : ℝ × ℝ → ι) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | bandUpdate n e op.before g p ≠ bandUpdate n e op.after g p})
    {z : ℝ × ℝ} (hz : bandUpdate n e op.surrounding g z ≠ op.label) :
    angularConstant * min n (edgeMarkDist n e y) ≤ dist y z :=
  op.clearance e (fun _ hp => bandUpdate_of_mem hp) (fun _ hp => bandUpdate_of_mem hp)
    (fun _ hp => by rw [bandUpdate_of_notMem hp, bandUpdate_of_notMem hp])
    (fun _ hp => bandUpdate_of_mem hp) hy hz

/-- The changed region of an elementary operation performed by band updates has diameter at most
`n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:257`. -/
theorem BandOperation.dist_le_bandUpdate {ι : Type*} (op : BandOperation ι) {n : ℝ}
    (e : SquareEdge) (g : ℝ × ℝ → ι) {y z : ℝ × ℝ}
    (hy : y ∈ closure {p | bandUpdate n e op.before g p ≠ bandUpdate n e op.after g p})
    (hz : z ∈ closure {p | bandUpdate n e op.before g p ≠ bandUpdate n e op.after g p}) :
    dist y z ≤ n :=
  op.dist_le_of_mem_closure_changed e (fun _ hp => bandUpdate_of_mem hp)
    (fun _ hp => bandUpdate_of_mem hp)
    (fun _ hp => by rw [bandUpdate_of_notMem hp, bandUpdate_of_notMem hp]) hy hz

/-! ### The elementary operations of one edge -/

section Steps

variable {ι : Type*} (A B C : ι)

/-- The three births on the auxiliary sheet, in order.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:187–197`. -/
noncomputable def auxSteps : List (BandOperation ι) :=
  [auxBirthB B C, auxBirthA A B C, auxBirthC A B C]

/-- The four deaths and births on the main sheet after the lens exchange, in order.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:215–220`. -/
noncomputable def mainSteps : List (BandOperation ι) :=
  [mainDeathC A B C, mainDeathA A B C, mainBirthC B C, mainDeathB B C]

theorem edgeOperations_eq_append : edgeOperations A B C = auxSteps A B C ++ mainSteps A B C :=
  rfl

/-- The auxiliary births start from the uniform word `C`, each one starts from the word left by
the previous one, and they end at the auxiliary word `eq:geometry-aux-word`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:187–197`. -/
theorem auxSteps_chain :
    (auxBirthB B C).before = (fun _ => C) ∧
      (auxSteps A B C).IsChain (fun o o' => o.after = o'.before) ∧
      (auxBirthC A B C).after = auxWord A B C := by
  refine ⟨funext fun _ => rfl, ?_, rfl⟩
  simp only [auxSteps, List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact ⟨rfl, rfl⟩

/-- The main operations start from the main word `eq:geometry-main-word` produced by the lens
exchange, each one starts from the word left by the previous one, and they end at the word
`C | B` with interface at zero.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:207–220`. -/
theorem mainSteps_chain :
    (mainDeathC A B C).before = mainWordOne A B C ∧
      (mainSteps A B C).IsChain (fun o o' => o.after = o'.before) ∧
      (mainDeathB B C).after = mainWordFive B C := by
  refine ⟨rfl, ?_, rfl⟩
  simp only [mainSteps, List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact ⟨rfl, rfl, rfl⟩

end Steps

/-! ### The starting guide of a repainting -/

/-- The main guide at the start of the repainting of `S = [0, n] ^ 2`: it has the old label `A`
on the open square and one label `C_e` on the open exterior neighboring square across each edge
`e` (the label of that neighboring `n`-square, or the placeholder).

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:86–90, 142–143, 166–168`. -/
structure RepaintingBaseline (ι : Type*) where
  /-- The side `n` of the square. -/
  n : ℝ
  n_pos : 0 < n
  /-- The main guide at the start of the repainting. -/
  guide : ℝ × ℝ → ι
  /-- The old label `A`. -/
  oldLabel : ι
  /-- The final label `B`. -/
  finalLabel : ι
  /-- The label `C_e` across the edge `e`. -/
  nbrLabel : SquareEdge → ι
  guide_openSquare : ∀ p ∈ openSquare n, guide p = oldLabel
  guide_edgeNeighbor : ∀ e, ∀ p ∈ edgeNeighbor n e, guide p = nbrLabel e

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

open Classical in
/-- The main guide after the central birth: `B` on the central region.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160`. -/
noncomputable def centralGuide : ℝ × ℝ → ι :=
  fun p => if p ∈ centralRegion R.n then R.finalLabel else R.guide p

/-- The main guide after the central birth and the edge constructions along the edges of `E`
(the head of the list is the edge completed last): the word `C_e | B` with interface at zero on
the band of each completed edge `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:160–161, 219–220, 237–238`. -/
noncomputable def completedGuide : List SquareEdge → ℝ × ℝ → ι
  | [] => R.centralGuide
  | e :: E => bandUpdate R.n e (mainWordFive R.finalLabel (R.nbrLabel e)) (completedGuide E)

/-- The main guide during the edge construction along `e`, after the edges of `E`, with normal
word `W` on the band of `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:161–165, 207–220`. -/
noncomputable def mainGuide (E : List SquareEdge) (e : SquareEdge) (W : ℝ → ι) : ℝ × ℝ → ι :=
  bandUpdate R.n e W (R.completedGuide E)

/-- The guide of the auxiliary sheet of the edge `e`, initialized uniformly at `C_e`, with normal
word `W` on the band of `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:187–197`. -/
noncomputable def auxGuide (e : SquareEdge) (W : ℝ → ι) : ℝ × ℝ → ι :=
  bandUpdate R.n e W fun _ => R.nbrLabel e

/-- The interface curves `x = 0` and `x = 1` of the starting word along `e`. -/
def edgeInterface (e : SquareEdge) : Set (ℝ × ℝ) :=
  {p | p ∈ edgeBand R.n e (-8) 2 ∧ (bandCoord R.n e p = 0 ∨ bandCoord R.n e p = 1)}

theorem centralGuide_of_notMem {p : ℝ × ℝ} (hp : p ∉ centralRegion R.n) :
    R.centralGuide p = R.guide p := by
  classical
  simp only [centralGuide, hp, ↓reduceIte]

theorem centralGuide_of_mem {p : ℝ × ℝ} (hp : p ∈ centralRegion R.n) :
    R.centralGuide p = R.finalLabel := by
  classical
  simp only [centralGuide, hp, ↓reduceIte]

/-- Off the bands of the completed edges, the completed guide is the guide after the central
birth. -/
theorem completedGuide_of_forall_notMem {E : List SquareEdge} {p : ℝ × ℝ}
    (h : ∀ e ∈ E, p ∉ edgeBand R.n e (-8) 2) : R.completedGuide E p = R.centralGuide p := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rw [completedGuide, bandUpdate_of_notMem h.1, ih h.2]

/-- On the band of an edge `e`, the completed guide carries `C_e | B` if `e` is completed, and is
the guide after the central birth otherwise. This is where the disjointness of the bands enters:
completing one edge does not alter the band of another.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:227–238`. -/
theorem completedGuide_of_mem_edgeBand {E : List SquareEdge} {e : SquareEdge} {p : ℝ × ℝ}
    (hp : p ∈ edgeBand R.n e (-8) 2) :
    R.completedGuide E p = if e ∈ E then mainWordFive R.finalLabel (R.nbrLabel e)
      (bandCoord R.n e p) else R.centralGuide p := by
  induction E with
  | nil => simp [completedGuide]
  | cons e' E ih =>
    by_cases he : e' = e
    · subst he
      simp [completedGuide, bandUpdate_of_mem hp]
    · have hp' : p ∉ edgeBand R.n e' (-8) 2 := fun h =>
        Set.disjoint_left.1 (disjoint_edgeBand he) h hp
      rw [completedGuide, bandUpdate_of_notMem hp', ih]
      simp [List.mem_cons, Ne.symm he]

/-- **The starting word of an edge operation.** After the central birth and the completion of
any edges other than `e`, the main guide carries the normal word `C_e | A | B` with interfaces
`0, 1` on the band of `e`, off those two interfaces.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:160–168, 227–238`. -/
theorem completedGuide_eq_edgeStartWord {E : List SquareEdge} {e : SquareEdge} (he : e ∉ E)
    {p : ℝ × ℝ} (hp : p ∈ edgeBand R.n e (-8) 2) (h0 : bandCoord R.n e p ≠ 0)
    (h1 : bandCoord R.n e p ≠ 1) :
    R.completedGuide E p =
      edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e) (bandCoord R.n e p) := by
  rw [R.completedGuide_of_mem_edgeBand hp]
  simp only [he, ↓reduceIte]
  obtain ⟨s1, s2, x1, x2⟩ := mem_edgeBand_iff_bandCoord.1 hp
  have hw := bandWidth_pos s1 s2
  have hd : e.nor R.n p = bandCoord R.n e p * bandWidth R.n (e.par p) := by
    rw [bandCoord, div_mul_cancel₀ _ hw.ne']
  set x := bandCoord R.n e p
  rcases lt_or_gt_of_ne h0 with hx | hx
  · -- the exterior part: the neighboring label
    have hN : p ∈ edgeNeighbor R.n e := edgeBand_neg_subset_edgeNeighbor e
      (mem_edgeBand_iff_bandCoord.2 ⟨s1, s2, x1, hx⟩)
    have hc : p ∉ centralRegion R.n := fun h =>
      notMem_closedSquare_of_mem_edgeNeighbor hN
        (openSquare_subset_closedSquare _ (centralRegion_subset_openSquare _ h))
    rw [R.centralGuide_of_notMem hc, R.guide_edgeNeighbor e p hN]
    simp [edgeStartWord, bandWord, hx]
  · have hdpos : 0 < e.nor R.n p := by rw [hd]; positivity
    have hS := mem_openSquare_of_mem_edgeBand hp hdpos
    rcases lt_or_gt_of_ne h1 with hx1 | hx1
    · -- the inward strip `0 < x < 1`: the old label
      have hc : p ∉ centralRegion R.n := fun h => by
        have := h.2.2.2.2 e
        nlinarith
      rw [R.centralGuide_of_notMem hc, R.guide_openSquare p hS]
      simp [edgeStartWord, bandWord, hx1, not_lt.2 hx.le]
    · -- the part `1 < x < 2`: the central region
      have hc : p ∈ centralRegion R.n := by
        obtain ⟨q1, q2, q3, q4⟩ := mem_openSquare.1 hS
        refine ⟨q1, q2, q3, q4, fun e' => ?_⟩
        by_cases he' : e' = e
        · subst he'; nlinarith
        · obtain ⟨t1, t2, t3⟩ := par_nor_of_mem_openSquare hS e'
          have hw' := bandWidth_pos t1 t2
          by_contra hlt
          exact Set.disjoint_left.1 (disjoint_edgeBand he') ⟨t1, t2, by linarith, by linarith⟩ hp
      rw [R.centralGuide_of_mem hc]
      simp [edgeStartWord, bandWord, not_lt.2 hx.le, not_lt.2 hx1.le]

/-- The main guide at the start of the edge construction along `e`, with the starting word
`C_e | A | B` on the band of `e`, agrees with the completed guide off the two interface curves:
the two represent the same guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 160–168, 237–238`. -/
theorem completedGuide_eq_mainGuide_start {E : List SquareEdge} {e : SquareEdge} (he : e ∉ E)
    {p : ℝ × ℝ} (hp : p ∉ R.edgeInterface e) :
    R.completedGuide E p =
      R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e)) p := by
  by_cases hb : p ∈ edgeBand R.n e (-8) 2
  · have h01 : bandCoord R.n e p ≠ 0 ∧ bandCoord R.n e p ≠ 1 := by
      by_contra h
      rw [not_and_or, not_not, not_not] at h
      exact hp ⟨hb, h⟩
    rw [mainGuide, bandUpdate_of_mem hb, R.completedGuide_eq_edgeStartWord he hb h01.1 h01.2]
  · rw [mainGuide, bandUpdate_of_notMem hb]

open Classical in
/-- **The lens exchange.** Exchanging the starting main guide and the auxiliary guide on the lens
`Y` gives the main guide with word `eq:geometry-main-word` on the band of `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:198–212`. -/
theorem lensExchange_mainGuide (E : List SquareEdge) (e : SquareEdge) :
    (fun p => if p ∈ edgeLens R.n e then
        R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e)) p
      else R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e)) p) =
      R.mainGuide E e (mainWordOne R.oldLabel R.finalLabel (R.nbrLabel e)) := by
  funext p
  have hYB : edgeLens R.n e ⊆ edgeBand R.n e (-8) 2 := edgeBand_mono (by norm_num) (by norm_num)
  by_cases hb : p ∈ edgeBand R.n e (-8) 2
  · obtain ⟨s1, s2, -, -⟩ := mem_edgeBand_iff_bandCoord.1 hb
    have hY : p ∈ edgeLens R.n e ↔ -7 < bandCoord R.n e p ∧ bandCoord R.n e p < -7 / 2 := by
      rw [edgeLens, mem_edgeBand_iff_bandCoord]
      exact ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨s1, s2, h.1, h.2⟩⟩
    rw [mainGuide, mainGuide, bandUpdate_of_mem hb, bandUpdate_of_mem hb, ← lens_exchange_word]
    by_cases h : p ∈ edgeLens R.n e
    · simp only [h, hY.1 h, and_self, ↓reduceIte, auxGuide, bandUpdate_of_mem hb]
    · have h' : ¬(-7 < bandCoord R.n e p ∧ bandCoord R.n e p < -7 / 2) := mt hY.2 h
      simp only [h, h', ↓reduceIte]
  · have hY : p ∉ edgeLens R.n e := fun h => hb (hYB h)
    simp only [hY, ↓reduceIte, mainGuide, bandUpdate_of_notMem hb]

/-- The main guide after the last main operation along `e` is the completed guide with `e`
completed. -/
theorem mainGuide_mainWordFive (E : List SquareEdge) (e : SquareEdge) :
    R.mainGuide E e (mainWordFive R.finalLabel (R.nbrLabel e)) = R.completedGuide (e :: E) :=
  rfl

/-- The fresh auxiliary sheet is uniform at `C_e`. -/
theorem auxGuide_uniform (e : SquareEdge) :
    R.auxGuide e (fun _ => R.nbrLabel e) = fun _ => R.nbrLabel e := by
  funext p
  by_cases hb : p ∈ edgeBand R.n e (-8) 2
  · rw [auxGuide, bandUpdate_of_mem hb]
  · rw [auxGuide, bandUpdate_of_notMem hb]

/-- Outside the closed square, every completed guide keeps the starting label.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:238–241`. -/
theorem completedGuide_of_notMem_closedSquare (E : List SquareEdge) {p : ℝ × ℝ}
    (hp : p ∉ closedSquare R.n) : R.completedGuide E p = R.guide p := by
  have hc : p ∉ centralRegion R.n := fun h =>
    hp (openSquare_subset_closedSquare _ (centralRegion_subset_openSquare _ h))
  by_cases hb : ∃ e, p ∈ edgeBand R.n e (-8) 2
  · obtain ⟨e, he⟩ := hb
    rw [R.completedGuide_of_mem_edgeBand he]
    split_ifs
    · have hd : e.nor R.n p < 0 := by
        by_contra h
        exact hp (mem_closedSquare_of_mem_edgeBand he (not_lt.1 h))
      have hN : p ∈ edgeNeighbor R.n e := edgeBand_neg_subset_edgeNeighbor e
        ⟨he.1, he.2.1, he.2.2.1, by rw [zero_mul]; exact hd⟩
      obtain ⟨s1, s2, -, -⟩ := he
      have hx : bandCoord R.n e p < 0 := div_neg_of_neg_of_pos hd (bandWidth_pos s1 s2)
      rw [R.guide_edgeNeighbor e p hN]
      simp [mainWordFive, bandWord, hx]
    · exact R.centralGuide_of_notMem hc
  · push Not at hb
    rw [R.completedGuide_of_forall_notMem fun e _ => hb e, R.centralGuide_of_notMem hc]

/-- **End of the repainting.** Once all four edges are completed, the open square carries the
final label `B`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:238–239`. -/
theorem completedGuide_of_mem_openSquare {E : List SquareEdge} (hE : ∀ e, e ∈ E) {p : ℝ × ℝ}
    (hp : p ∈ openSquare R.n) : R.completedGuide E p = R.finalLabel := by
  by_cases hb : ∃ e, p ∈ edgeBand R.n e (-8) 2
  · obtain ⟨e, he⟩ := hb
    rw [R.completedGuide_of_mem_edgeBand he]
    simp only [hE e, ↓reduceIte]
    obtain ⟨s1, s2, d0⟩ := par_nor_of_mem_openSquare hp e
    have hx : 0 < bandCoord R.n e p := div_pos d0 (bandWidth_pos s1 s2)
    simp [mainWordFive, bandWord, not_lt.2 hx.le]
  · push Not at hb
    rw [R.completedGuide_of_forall_notMem fun e _ => hb e,
      R.centralGuide_of_mem (mem_centralRegion_of_forall_notMem hp hb)]

/-! ### Lemma 7.2 for the schedule -/

/-- **Lemma 7.2 for the central birth of the schedule.** Every point `y` of the closure of the
changed region of the central birth lies at ambient sup distance at least `a₀ min(n, d_V(y))`
from every position of a label other than `A` in its surrounding guide, the starting guide; here
`V` is the set of four corners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 276–281`. -/
theorem clearance_central {y : ℝ × ℝ}
    (hy : y ∈ closure {p | R.guide p ≠ R.centralGuide p}) {z : ℝ × ℝ}
    (hz : R.guide z ≠ R.oldLabel) :
    angularConstant * min R.n (cornerMarkDist R.n y) ≤ dist y z := by
  have hsub : {p | R.guide p ≠ R.centralGuide p} ⊆ centralRegion R.n := fun p hp => by
    by_contra h
    exact hp (R.centralGuide_of_notMem h).symm
  exact centralBirth_clearance (fun p h1 h2 h3 h4 => R.guide_openSquare p
    (mem_openSquare.2 ⟨h1, h2, h3, h4⟩)) (closure_mono hsub hy) hz

/-- The changed region of the central birth has diameter at most `n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:257`. -/
theorem dist_le_central {y z : ℝ × ℝ}
    (hy : y ∈ closure {p | R.guide p ≠ R.centralGuide p})
    (hz : z ∈ closure {p | R.guide p ≠ R.centralGuide p}) : dist y z ≤ R.n := by
  have hsub : {p | R.guide p ≠ R.centralGuide p} ⊆ centralRegion R.n := fun p hp => by
    by_contra h
    exact hp (R.centralGuide_of_notMem h).symm
  exact dist_le_of_mem_closure_centralRegion (closure_mono hsub hy) (closure_mono hsub hz)

/-- **Lemma 7.2 for the auxiliary births of the schedule.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 283–286`. -/
theorem clearance_auxStep (e : SquareEdge) {op : BandOperation ι}
    (_hop : op ∈ auxSteps R.oldLabel R.finalLabel (R.nbrLabel e)) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | R.auxGuide e op.before p ≠ R.auxGuide e op.after p})
    {z : ℝ × ℝ} (hz : R.auxGuide e op.surrounding z ≠ op.label) :
    angularConstant * min R.n (edgeMarkDist R.n e y) ≤ dist y z :=
  op.clearance_bandUpdate e _ hy hz

/-- **Lemma 7.2 for the main births and deaths of the schedule.** For `e ∉ E` the guides
`R.mainGuide E e W` are the main guides of the construction along `e`; the estimate holds for every
list `E`, since it uses only that these guides are band replacements of one guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 286–293`. -/
theorem clearance_mainStep (E : List SquareEdge) (e : SquareEdge) {op : BandOperation ι}
    (_hop : op ∈ mainSteps R.oldLabel R.finalLabel (R.nbrLabel e)) {y : ℝ × ℝ}
    (hy : y ∈ closure {p | R.mainGuide E e op.before p ≠ R.mainGuide E e op.after p})
    {z : ℝ × ℝ} (hz : R.mainGuide E e op.surrounding z ≠ op.label) :
    angularConstant * min R.n (edgeMarkDist R.n e y) ≤ dist y z :=
  op.clearance_bandUpdate e _ hy hz

/-- **Lemma 7.2 for the lens exchange of the schedule.** Every point `y` of the closure of the
positions that are not common `C_e` on the two guides before the exchange lies at ambient sup
distance at least `a₀ min(n, d_V(y))` from the boundary of the lens. For `e ∉ E` the main guide
here is the one the schedule specifies at the start of the construction along `e`, which agrees
with the completed guide off the curves `x = 0` and `x = 1`
(`completedGuide_eq_mainGuide_start`).

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-exchange-clearance`, `06-geometry.tex:265–272, 295–299`. -/
theorem clearance_exchange (E : List SquareEdge) (e : SquareEdge) {y : ℝ × ℝ}
    (hy : y ∈ closure {p |
      R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e)) p ≠ R.nbrLabel e ∨
        R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e)) p ≠ R.nbrLabel e})
    {z : ℝ × ℝ} (hz : z ∈ frontier (edgeLens R.n e)) :
    angularConstant * min R.n (edgeMarkDist R.n e y) ≤ dist y z := by
  refine lensExchange_clearance e (fun p hp => ?_) (fun _ hp => bandUpdate_of_mem hp)
    (fun _ hp => bandUpdate_of_notMem hp) hy hz
  have hb : p ∈ edgeBand R.n e (-8) 2 := edgeBand_mono le_rfl (by norm_num) hp
  obtain ⟨-, -, -, hx⟩ := mem_edgeBand_iff_bandCoord.1 hp
  rw [mainGuide, bandUpdate_of_mem hb]
  simp [edgeStartWord, bandWord, hx]

/-! ### The labels of the main guides -/

/-- A normal word with all labels in a set takes values in it. -/
theorem bandWord_mem {s : Set ι} {c : ι} (hc : c ∈ s) {l : List (ℝ × ι)}
    (hl : ∀ q ∈ l, q.2 ∈ s) (x : ℝ) : bandWord c l x ∈ s := by
  induction l generalizing c with
  | nil => exact hc
  | cons q l ih =>
    obtain ⟨t, d⟩ := q
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    simp only [bandWord]
    split_ifs
    · exact hc
    · exact ih hl.1 hl.2

/-- The label `C_e` across an edge is a value of the starting guide. -/
theorem nbrLabel_mem (e : SquareEdge) : R.nbrLabel e ∈ Set.range R.guide := by
  have hn := R.n_pos
  refine ⟨e.point R.n (R.n / 2) (-(R.n / 2)), R.guide_edgeNeighbor e _ ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [par_point, nor_point] <;> linarith

/-- The old label `A` is a value of the starting guide. -/
theorem oldLabel_mem : R.oldLabel ∈ Set.range R.guide := by
  have hn := R.n_pos
  exact ⟨(R.n / 2, R.n / 2), R.guide_openSquare _
    (mem_openSquare.2 ⟨by linarith, by linarith, by linarith, by linarith⟩)⟩

/-- **Active labels.** Every value of a completed guide is the final label or a value of the
starting guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:585–609`. -/
theorem completedGuide_mem (E : List SquareEdge) (p : ℝ × ℝ) :
    R.completedGuide E p ∈ insert R.finalLabel (Set.range R.guide) := by
  induction E with
  | nil =>
    classical
    simp only [completedGuide, centralGuide]
    split_ifs
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨p, rfl⟩
  | cons e E ih =>
    by_cases hb : p ∈ edgeBand R.n e (-8) 2
    · rw [completedGuide, bandUpdate_of_mem hb]
      refine bandWord_mem (mem_insert_of_mem _ (R.nbrLabel_mem e)) ?_ _
      simp
    · rw [completedGuide, bandUpdate_of_notMem hb]
      exact ih

/-- **Active labels during an edge construction.** Every value of a main guide whose word uses the
labels `A`, `B`, `C_e` is the final label or a value of the starting guide; so is every value of
the auxiliary guides.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:585–609`. -/
theorem mainGuide_mem (E : List SquareEdge) (e : SquareEdge) {W : ℝ → ι}
    (hW : ∀ x, W x = R.oldLabel ∨ W x = R.finalLabel ∨ W x = R.nbrLabel e) (p : ℝ × ℝ) :
    R.mainGuide E e W p ∈ insert R.finalLabel (Set.range R.guide) ∧
      R.auxGuide e W p ∈ insert R.finalLabel (Set.range R.guide) := by
  have hW' : W (bandCoord R.n e p) ∈ insert R.finalLabel (Set.range R.guide) := by
    rcases hW (bandCoord R.n e p) with h | h | h <;> rw [h]
    · exact mem_insert_of_mem _ R.oldLabel_mem
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (R.nbrLabel_mem e)
  by_cases hb : p ∈ edgeBand R.n e (-8) 2
  · rw [mainGuide, auxGuide, bandUpdate_of_mem hb, bandUpdate_of_mem hb]
    exact ⟨hW', hW'⟩
  · rw [mainGuide, auxGuide, bandUpdate_of_notMem hb, bandUpdate_of_notMem hb]
    exact ⟨R.completedGuide_mem E p, mem_insert_of_mem _ (R.nbrLabel_mem e)⟩

/-- **Locality of the repainting.** Outside the closed square and the exterior bands
`-8 < x < 0`, every main guide of the schedule keeps its starting value.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:227–241`. -/
theorem mainGuide_of_notMem (E : List SquareEdge) (e : SquareEdge) (W : ℝ → ι) {p : ℝ × ℝ}
    (hp : p ∉ closedSquare R.n) (hb : p ∉ edgeBand R.n e (-8) 0) :
    R.mainGuide E e W p = R.guide p := by
  have hb' : p ∉ edgeBand R.n e (-8) 2 := by
    intro h
    by_cases hd : 0 ≤ e.nor R.n p
    · exact hp (mem_closedSquare_of_mem_edgeBand h hd)
    · exact hb ⟨h.1, h.2.1, h.2.2.1, by rw [zero_mul]; exact not_le.1 hd⟩
  rw [mainGuide, bandUpdate_of_notMem hb', R.completedGuide_of_notMem_closedSquare E hp]

end RepaintingBaseline

end TNLean.PEPS.Approximation
