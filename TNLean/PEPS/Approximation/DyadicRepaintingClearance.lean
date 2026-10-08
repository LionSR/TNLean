/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicEdgeBands

/-!
# Clearance of the repainting operations of a dyadic square

Let `S = [0, n] ^ 2` be an `n`-square of the padded dyadic hierarchy that is being repainted
from its old label `A` to its final label `B`, with the edge coordinates, the bands and the lens
of `TNLean.PEPS.Approximation.DyadicEdgeBands`. The large-scale repainting first births `B` in
the central part of `S` (the points beyond `x = 1` for every edge), and then for each edge runs
a fixed sequence of births, deaths and one lens exchange with an auxiliary sheet, recorded by
the normal words of the main and auxiliary sheets. This file formalizes:

* the normal words of the edge construction and the identities between them (the changed
  interval of every elementary birth or death, the surrounding sector, and the main word
  produced by the lens exchange);
* the clearance estimates of the proof of Lemma 7.2 (`lem:geometry-angular`) for guides with
  the stated properties: one fixed constant `a₀ = 1/5000` gives the conical clearance
  `dist(y, {f ≠ P∘}) ≥ a₀ min(n, d_V(y))` for every point `y` of the closed changed region of
  the central birth and of each elementary edge birth or death, and the clearance
  `dist(y, ∂Y) ≥ a₀ min(n, d_V(y))` for every point `y` of the closed noncommon-`C` set of the
  lens exchange; the changed regions have diameter at most `n`.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

Labels are elements of an arbitrary type `ι`, and nothing assumes `A`, `B`, `C` distinct: the
source's nominal labels may coincide (`06-geometry.tex:168–169`), and identifying labels only
shrinks the obstructing sets (`06-geometry.tex:315–318`).

The clearance theorems `BandOperation.clearance`, `centralBirth_clearance` and
`lensExchange_clearance` hold for every guide with the properties that the source's proof uses
(`06-geometry.tex:276–299`): the operation's normal word on the band `-8 < x < 2` and no change
off it (edge operations), the label `A` on the open square (central birth), and the label `C` on
the exterior band `-8 < x < 0` (main sheet of the exchange). The guides of the schedule are
constructed, and shown to have these properties, in
`TNLean.PEPS.Approximation.DyadicRepaintingSchedule`; Lemma 7.2 for the repainting of every
block of the hierarchy is in `TNLean.PEPS.Approximation.DyadicLevelSchedule`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the edge construction
  (lines 155–241) and Lemma 7.2 `lem:geometry-angular` (lines 254–319).
-/

namespace TNLean.PEPS.Approximation

open Set Metric SquareEdge

/-! ### Normal words of the edge construction -/

/-- A normal word: label `c` below the first interface, then at each interface `t` the label
switches to the paired label. On an interface itself the label to its right is taken. The
source instead samples labels after one generic displacement (`06-geometry.tex:72–77`); the
two conventions differ only on the interface curves, and no clearance below depends on the
values there.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:161–170, 193–197`. -/
noncomputable def bandWord {ι : Type*} (c : ι) : List (ℝ × ι) → ℝ → ι
  | [], _ => c
  | (t, l) :: rest, x => if x < t then c else bandWord l rest x

section Words

variable {ι : Type*} (A B C : ι)

/-- The normal word `C | A | B` at interfaces `0, 1` at the start of an edge operation.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:160–165`. -/
noncomputable def edgeStartWord : ℝ → ι := bandWord C [(0, A), (1, B)]

/-- The auxiliary word after the birth of `B` in `-6 < x < -1`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:188–190`. -/
noncomputable def auxWordOne : ℝ → ι := bandWord C [(-6, B), (-1, C)]

/-- The auxiliary word after the birth of `A` in `-5 < x < -2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:188–190`. -/
noncomputable def auxWordTwo : ℝ → ι := bandWord C [(-6, B), (-5, A), (-2, B), (-1, C)]

/-- The auxiliary word `C | B | A | C | A | B | C` at interfaces `-6, …, -1`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-aux-word`,
`06-geometry.tex:190–197`. -/
noncomputable def auxWord : ℝ → ι :=
  bandWord C [(-6, B), (-5, A), (-4, C), (-3, A), (-2, B), (-1, C)]

/-- The main word `C | B | A | C | A | B` at interfaces `-6, -5, -4, 0, 1` after the exchange.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-main-word`,
`06-geometry.tex:207–212`. -/
noncomputable def mainWordOne : ℝ → ι := bandWord C [(-6, B), (-5, A), (-4, C), (0, A), (1, B)]

/-- The main word `C | B | A | B` at `-6, -5, 1`, after the `C` band `(-4, 0)` dies into `A`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:216–217`. -/
noncomputable def mainWordTwo : ℝ → ι := bandWord C [(-6, B), (-5, A), (1, B)]

/-- The main word `C | B` at `-6`, after the `A` band `(-5, 1)` dies into `B`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:217–218`. -/
noncomputable def mainWordThree : ℝ → ι := bandWord C [(-6, B)]

/-- The main word `C | B | C | B` at `-6, -3, 0`, after the birth of `C` in `(-3, 0)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:218–219`. -/
noncomputable def mainWordFour : ℝ → ι := bandWord C [(-6, B), (-3, C), (0, B)]

/-- The final main word `C | B` at `0`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:219–220`. -/
noncomputable def mainWordFive : ℝ → ι := bandWord C [(0, B)]

/-- **The exchange produces the main word.** Replacing the starting main word by the auxiliary
word on the lens `-7 < x < -7/2` gives `eq:geometry-main-word`, at every value of `x`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:199–212`. -/
theorem lens_exchange_word (x : ℝ) :
    (if -7 < x ∧ x < -7 / 2 then auxWord A B C x else edgeStartWord A B C x) =
      mainWordOne A B C x := by
  by_cases h : -7 < x ∧ x < -7 / 2
  · simp only [h, and_self, ↓reduceIte]
    obtain ⟨h1, h2⟩ := h
    simp only [auxWord, mainWordOne, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  · simp only [h, ↓reduceIte]
    have h' : x ≤ -7 ∨ -7 / 2 ≤ x := by
      rcases le_or_gt x (-7) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (le_of_not_gt fun h2 => h ⟨h1, h2⟩)
    simp only [edgeStartWord, mainWordOne, bandWord]
    rcases h' with h' | h' <;> split_ifs <;> first | rfl | (exfalso; linarith)

end Words

/-! ### Lemma 7.2 -/

/-- One elementary birth or death of the edge construction: a before word and an after word that
differ only in the closed changed interval `[lo, hi]`, a surrounding word (the before word for a
birth, the after word for a death) equal to the label `P∘` on the open sector `(lo', hi')`, with
margins at least `1/2` and the sector inside `(-8, 2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:246–252, 283–293`. -/
structure BandOperation (ι : Type*) where
  /-- The normal word before the operation. -/
  before : ℝ → ι
  /-- The normal word after the operation. -/
  after : ℝ → ι
  /-- The surrounding word: `before` for a birth, `after` for a death. -/
  surrounding : ℝ → ι
  /-- The surrounding label `P∘`. -/
  label : ι
  /-- The changed interval. -/
  lo : ℝ
  hi : ℝ
  /-- The surrounding sector. -/
  lo' : ℝ
  hi' : ℝ
  changed : ∀ x, before x ≠ after x → lo ≤ x ∧ x ≤ hi
  sector : ∀ x, lo' < x → x < hi' → surrounding x = label
  lo_le_hi : lo ≤ hi
  margin_lo : lo' + 1 / 2 ≤ lo
  margin_hi : hi + 1 / 2 ≤ hi'
  lo'_ge : -8 ≤ lo'
  hi'_le : hi' ≤ 2

/-- The changed set of an elementary edge operation lies in the closed band of its changed
interval, when the guides have the operation's words on the band `-8 < x < 2` and agree off it.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:246–252`. -/
theorem BandOperation.changed_subset_closedEdgeBand {ι : Type*} (op : BandOperation ι) {n : ℝ}
    (e : SquareEdge) {fb fa : ℝ × ℝ → ι}
    (hfb : ∀ p ∈ edgeBand n e (-8) 2, fb p = op.before (bandCoord n e p))
    (hfa : ∀ p ∈ edgeBand n e (-8) 2, fa p = op.after (bandCoord n e p))
    (hoff : ∀ p ∉ edgeBand n e (-8) 2, fb p = fa p) :
    {p | fb p ≠ fa p} ⊆ closedEdgeBand n e op.lo op.hi := by
  intro p hp
  by_cases hb : p ∈ edgeBand n e (-8) 2
  · have hx := op.changed _ (by rwa [← hfb p hb, ← hfa p hb])
    obtain ⟨h1, h2, -, -⟩ := mem_edgeBand_iff_bandCoord.1 hb
    have hw := bandWidth_pos h1 h2
    exact ⟨h1.le, h2.le, (le_div_iff₀ hw).1 hx.1, (div_le_iff₀ hw).1 hx.2⟩
  · exact absurd (hoff p hb) hp

/-- **Diameter of a changed region.** Two points of the closure of the changed set of an
elementary edge operation are at sup distance at most `n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:257`. -/
theorem BandOperation.dist_le_of_mem_closure_changed {ι : Type*} (op : BandOperation ι) {n : ℝ}
    (e : SquareEdge) {fb fa : ℝ × ℝ → ι}
    (hfb : ∀ p ∈ edgeBand n e (-8) 2, fb p = op.before (bandCoord n e p))
    (hfa : ∀ p ∈ edgeBand n e (-8) 2, fa p = op.after (bandCoord n e p))
    (hoff : ∀ p ∉ edgeBand n e (-8) 2, fb p = fa p) {y z : ℝ × ℝ}
    (hy : y ∈ closure {p | fb p ≠ fa p}) (hz : z ∈ closure {p | fb p ≠ fa p}) :
    dist y z ≤ n := by
  have hsub := closure_minimal (op.changed_subset_closedEdgeBand e hfb hfa hoff)
    (isClosed_closedEdgeBand n e op.lo op.hi)
  have := op.margin_lo
  have := op.margin_hi
  have := op.lo'_ge
  have := op.hi'_le
  exact dist_le_of_mem_closedEdgeBand (by linarith) (by linarith) (hsub hy) (hsub hz)

/-- **Clearance of the edge births and deaths in the proof of Lemma 7.2.** For an elementary birth
or death of the edge construction, every point `y` of the closure of the changed region lies at
ambient sup distance at least `a₀ min(n, d_V(y))` from every position of a label other than `P∘` in
the surrounding guide. Here the guides `fb` (before) and `fa` (after) have the operation's normal
words on the band `-8 < x < 2` and agree off it, and the surrounding guide `fs` has the surrounding
word on that band. The guides of the schedule have these properties
(`RepaintingBaseline.clearance_auxStep`, `RepaintingBaseline.clearance_mainStep`).

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 283–293`. -/
theorem BandOperation.clearance {ι : Type*} (op : BandOperation ι) {n : ℝ} (e : SquareEdge)
    {fb fa fs : ℝ × ℝ → ι}
    (hfb : ∀ p ∈ edgeBand n e (-8) 2, fb p = op.before (bandCoord n e p))
    (hfa : ∀ p ∈ edgeBand n e (-8) 2, fa p = op.after (bandCoord n e p))
    (hoff : ∀ p ∉ edgeBand n e (-8) 2, fb p = fa p)
    (hfs : ∀ p ∈ edgeBand n e (-8) 2, fs p = op.surrounding (bandCoord n e p))
    {y : ℝ × ℝ} (hy : y ∈ closure {p | fb p ≠ fa p}) {z : ℝ × ℝ} (hz : fs z ≠ op.label) :
    angularConstant * min n (edgeMarkDist n e y) ≤ dist y z := by
  have hyc := closure_minimal (op.changed_subset_closedEdgeBand e hfb hfa hoff)
    (isClosed_closedEdgeBand n e op.lo op.hi) hy
  refine le_of_not_gt fun hlt => ?_
  have hlo := op.margin_lo
  have hhi := op.margin_hi
  have hlo' := op.lo'_ge
  have hhi' := op.hi'_le
  have hzY := mem_edgeBand_of_dist_lt_markDist op.lo_le_hi hlo hhi hlo' (by linarith) hyc hlt
  have hzB : z ∈ edgeBand n e (-8) 2 := by
    obtain ⟨h1, h2, h3, h4⟩ := mem_edgeBand_iff_bandCoord.1 hzY
    exact mem_edgeBand_iff_bandCoord.2 ⟨h1, h2, by linarith, by linarith⟩
  obtain ⟨-, -, h3, h4⟩ := mem_edgeBand_iff_bandCoord.1 hzY
  exact hz ((hfs z hzB).trans (op.sector _ h3 h4))

section Operations

variable {ι : Type*} (A B C : ι)

/-- Birth of `B` in `-6 < x < -1` on the uniform auxiliary sheet `C`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:188–189, 283`. -/
noncomputable def auxBirthB : BandOperation ι where
  before := bandWord C []
  after := auxWordOne B C
  surrounding := bandWord C []
  label := C
  lo := -6
  hi := -1
  lo' := -7
  hi' := 0
  changed x h := by
    simp only [auxWordOne, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector _ _ _ := rfl
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Birth of `A` in `-5 < x < -2` inside the auxiliary `B` band `(-6, -1)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:189, 284–286`. -/
noncomputable def auxBirthA : BandOperation ι where
  before := auxWordOne B C
  after := auxWordTwo A B C
  surrounding := auxWordOne B C
  label := B
  lo := -5
  hi := -2
  lo' := -6
  hi' := -1
  changed x h := by
    simp only [auxWordOne, auxWordTwo, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [auxWordOne, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Birth of `C` in `-4 < x < -3` inside the auxiliary `A` band `(-5, -2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:189–190, 284–286`. -/
noncomputable def auxBirthC : BandOperation ι where
  before := auxWordTwo A B C
  after := auxWord A B C
  surrounding := auxWordTwo A B C
  label := A
  lo := -4
  hi := -3
  lo' := -5
  hi' := -2
  changed x h := by
    simp only [auxWordTwo, auxWord, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [auxWordTwo, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Death of the main `C` band `(-4, 0)` into `A`; the surrounding `A` interval is `(-5, 1)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:216, 286–287`. -/
noncomputable def mainDeathC : BandOperation ι where
  before := mainWordOne A B C
  after := mainWordTwo A B C
  surrounding := mainWordTwo A B C
  label := A
  lo := -4
  hi := 0
  lo' := -5
  hi' := 1
  changed x h := by
    simp only [mainWordOne, mainWordTwo, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [mainWordTwo, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Death of the main `A` band `(-5, 1)` into `B`; the surrounding `B` sector includes `(-6, 2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:216–218, 287–288`. -/
noncomputable def mainDeathA : BandOperation ι where
  before := mainWordTwo A B C
  after := mainWordThree B C
  surrounding := mainWordThree B C
  label := B
  lo := -5
  hi := 1
  lo' := -6
  hi' := 2
  changed x h := by
    simp only [mainWordTwo, mainWordThree, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [mainWordThree, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Birth of `C` in `(-3, 0)` inside the main `B` sector, which includes `(-6, 2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:218–219, 289–290`. -/
noncomputable def mainBirthC : BandOperation ι where
  before := mainWordThree B C
  after := mainWordFour B C
  surrounding := mainWordThree B C
  label := B
  lo := -3
  hi := 0
  lo' := -6
  hi' := 2
  changed x h := by
    simp only [mainWordThree, mainWordFour, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [mainWordThree, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Death of the remaining main `B` band `(-6, -3)` into `C`; the surrounding `C` sector
includes `(-8, 0)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:219–220, 290–292`. -/
noncomputable def mainDeathB : BandOperation ι where
  before := mainWordFour B C
  after := mainWordFive B C
  surrounding := mainWordFive B C
  label := C
  lo := -6
  hi := -3
  lo' := -8
  hi' := 0
  changed x h := by
    simp only [mainWordFour, mainWordFive, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [mainWordFive, bandWord, h2, ↓reduceIte]
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- The seven elementary births and deaths of one edge construction, in order.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:185–221`. -/
noncomputable def edgeOperations : List (BandOperation ι) :=
  [auxBirthB B C, auxBirthA A B C, auxBirthC A B C, mainDeathC A B C, mainDeathA A B C,
    mainBirthC B C, mainDeathB B C]

end Operations

/-! ### The central birth -/

/-- The changed region of the central birth: the points of the open square `(0, n) ^ 2` beyond
the `x = 1` boundary for every edge, i.e. with `d > w(s)` for all four edges.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160`. -/
def centralRegion (n : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < n ∧ 0 < p.2 ∧ p.2 < n ∧ ∀ e : SquareEdge, bandWidth n (e.par p) < e.nor n p}

private def closedCentralRegion (n : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ n ∧ 0 ≤ p.2 ∧ p.2 ≤ n ∧
    bandWidth n p.1 ≤ p.2 ∧ bandWidth n p.1 ≤ n - p.2 ∧
    bandWidth n p.2 ≤ p.1 ∧ bandWidth n p.2 ≤ n - p.1}

private theorem isClosed_closedCentralRegion (n : ℝ) : IsClosed (closedCentralRegion n) := by
  have h1 : Continuous (Prod.fst : ℝ × ℝ → ℝ) := continuous_fst
  have h2 : Continuous (Prod.snd : ℝ × ℝ → ℝ) := continuous_snd
  have w1 : Continuous fun p : ℝ × ℝ => bandWidth n p.1 := (continuous_bandWidth n).comp h1
  have w2 : Continuous fun p : ℝ × ℝ => bandWidth n p.2 := (continuous_bandWidth n).comp h2
  exact (isClosed_le continuous_const h1).inter ((isClosed_le h1 continuous_const).inter
    ((isClosed_le continuous_const h2).inter ((isClosed_le h2 continuous_const).inter
    ((isClosed_le w1 h2).inter ((isClosed_le w1 (continuous_const.sub h2)).inter
    ((isClosed_le w2 h1).inter (isClosed_le w2 (continuous_const.sub h1))))))))

private theorem closure_centralRegion_subset (n : ℝ) :
    closure (centralRegion n) ⊆ closedCentralRegion n := by
  refine closure_minimal ?_ (isClosed_closedCentralRegion n)
  rintro p ⟨h1, h2, h3, h4, h5⟩
  have b := h5 .bottom
  have t := h5 .top
  have l := h5 .left
  have r := h5 .right
  simp only [par, nor] at b t l r
  exact ⟨h1.le, h2.le, h3.le, h4.le, b.le, t.le, l.le, r.le⟩

/-- **Clearance of the central birth in the proof of Lemma 7.2.** Every point `y` of the closed
central region lies at ambient sup distance at least `a₀ min(n, d_V(y))` from every position of a
label other than `A` in any guide which is `A` on the open square `(0, n) ^ 2`; here `V` is the set
of four corners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 276–281`. -/
theorem centralBirth_clearance {ι : Type*} {n : ℝ} {f : ℝ × ℝ → ι} {A : ι}
    (hf : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 < n → 0 < p.2 → p.2 < n → f p = A)
    {y : ℝ × ℝ} (hy : y ∈ closure (centralRegion n)) {z : ℝ × ℝ} (hz : f z ≠ A) :
    angularConstant * min n (cornerMarkDist n y) ≤ dist y z := by
  obtain ⟨y1, y2, y3, y4, b, t, l, r⟩ := closure_centralRegion_subset n hy
  set u := min y.1 (n - y.1) with hu
  set v := min y.2 (n - y.2) with hv
  have hwu : bandWidth n y.1 = u / 1000 := rfl
  have hwv : bandWidth n y.2 = v / 1000 := rfl
  have hvu : u / 1000 ≤ v := le_min (by linarith) (by linarith)
  have huv : v / 1000 ≤ u := le_min (by linarith) (by linarith)
  have hu0 : 0 ≤ u := le_min y1 (by linarith)
  have hv0 : 0 ≤ v := le_min y3 (by linarith)
  -- the mark distance is at most the distance to the nearest corner, `max u v`
  have hmark : cornerMarkDist n y ≤ max u v := by
    unfold cornerMarkDist
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    rcases min_choice y.1 (n - y.1) with h1 | h1 <;>
      rcases min_choice y.2 (n - y.2) with h2 | h2
    · refine min_le_of_left_le (min_le_of_left_le ?_)
      rw [abs_of_nonneg y1, abs_of_nonneg y3, hu, hv, h1, h2]
    · refine min_le_of_right_le (min_le_of_left_le ?_)
      rw [abs_of_nonneg y1, abs_sub_comm, abs_of_nonneg (by linarith), hu, hv, h1, h2]
    · refine min_le_of_left_le (min_le_of_right_le ?_)
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_of_nonneg y3, hu, hv, h1, h2]
    · refine min_le_of_right_le (min_le_of_right_le ?_)
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm y.2,
        abs_of_nonneg (by linarith), hu, hv, h1, h2]
  refine le_of_not_gt fun hlt => ?_
  have hmin : min n (cornerMarkDist n y) ≤ max u v := (min_le_right _ _).trans hmark
  have hr : dist y z < max u v / 5000 := by
    unfold angularConstant at hlt; nlinarith
  have hd := Prod.dist_eq (x := y) (y := z)
  have hzd1 : |y.1 - z.1| < min u v := by
    have : |y.1 - z.1| ≤ dist y z := by rw [hd, Real.dist_eq]; exact le_max_left _ _
    rcases le_total u v with h | h
    · rw [max_eq_right h] at hr; rw [min_eq_left h]; linarith
    · rw [max_eq_left h] at hr; rw [min_eq_right h]; linarith
  have hzd2 : |y.2 - z.2| < min u v := by
    have : |y.2 - z.2| ≤ dist y z := by rw [hd, Real.dist_eq]; exact le_max_right _ _
    rcases le_total u v with h | h
    · rw [max_eq_right h] at hr; rw [min_eq_left h]; linarith
    · rw [max_eq_left h] at hr; rw [min_eq_right h]; linarith
  rw [abs_lt] at hzd1 hzd2
  have := min_le_left u v
  have := min_le_right u v
  have := min_le_left y.1 (n - y.1)
  have := min_le_right y.1 (n - y.1)
  have := min_le_left y.2 (n - y.2)
  have := min_le_right y.2 (n - y.2)
  exact hz (hf z (by linarith) (by linarith) (by linarith) (by linarith))

/-- **Diameter of the central changed region.** Two points of the closure of the central region
are at sup distance at most `n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:257`. -/
theorem dist_le_of_mem_closure_centralRegion {n : ℝ} {y z : ℝ × ℝ}
    (hy : y ∈ closure (centralRegion n)) (hz : z ∈ closure (centralRegion n)) :
    dist y z ≤ n := by
  obtain ⟨y1, y2, y3, y4, -⟩ := closure_centralRegion_subset n hy
  obtain ⟨z1, z2, z3, z4, -⟩ := closure_centralRegion_subset n hz
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)

/-! ### The lens exchange -/

private theorem frontier_edgeLens_subset {n : ℝ} {e : SquareEdge} {z : ℝ × ℝ}
    (hz : z ∈ frontier (edgeLens n e)) :
    z = e.point n 0 0 ∨ z = e.point n n 0 ∨
      (0 < e.par z ∧ e.par z < n ∧
        (e.nor n z = -7 * bandWidth n (e.par z) ∨
          e.nor n z = -7 / 2 * bandWidth n (e.par z))) := by
  rw [edgeLens, frontier, (isOpen_edgeBand n e _ _).interior_eq] at hz
  obtain ⟨hzc, hzo⟩ := hz
  obtain ⟨z1, z2, z3, z4⟩ := closure_edgeBand_subset n e _ _ hzc
  rcases z1.lt_or_eq with z1 | z1
  · rcases z2.lt_or_eq with z2 | z2
    · right; right
      refine ⟨z1, z2, ?_⟩
      by_contra h
      exact hzo ⟨z1, z2, lt_of_le_of_ne z3 fun h' => h (Or.inl h'.symm),
        lt_of_le_of_ne z4 fun h' => h (Or.inr h')⟩
    · right; left
      have hw : bandWidth n (e.par z) = 0 := by
        simp [bandWidth, z2, show (0 : ℝ) ≤ n by linarith]
      rw [hw] at z3 z4
      rw [← point_par_nor n e z, z2, show e.nor n z = 0 by linarith]
  · left
    have hw : bandWidth n (e.par z) = 0 := by
      simp [bandWidth, ← z1, show (0 : ℝ) ≤ n by linarith]
    rw [hw] at z3 z4
    rw [← point_par_nor n e z, ← z1, show e.nor n z = 0 by linarith]

/-- **Clearance of the lens exchange in the proof of Lemma 7.2.** Before the exchange the main
guide `fm` is `C` on the exterior band `-8 < x < 0`, and the auxiliary guide `fx` has the word
`eq:geometry-aux-word` on the band `-8 < x < 2` and is `C` off it. Then every point `y` of the
closure of the positions that are not common `C` on the two guides lies at ambient sup distance
at least `a₀ min(n, d_V(y))` from the boundary of the lens `Y`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-exchange-clearance`, `06-geometry.tex:265–272, 295–299`. -/
theorem lensExchange_clearance {ι : Type*} {n : ℝ} (e : SquareEdge) {A B C : ι}
    {fm fx : ℝ × ℝ → ι} (hfm : ∀ p ∈ edgeBand n e (-8) 0, fm p = C)
    (hfx : ∀ p ∈ edgeBand n e (-8) 2, fx p = auxWord A B C (bandCoord n e p))
    (hfx' : ∀ p ∉ edgeBand n e (-8) 2, fx p = C)
    {y : ℝ × ℝ} (hy : y ∈ closure {p | fm p ≠ C ∨ fx p ≠ C})
    {z : ℝ × ℝ} (hz : z ∈ frontier (edgeLens n e)) :
    angularConstant * min n (edgeMarkDist n e y) ≤ dist y z := by
  have ha0 := angularConstant_pos
  have hsub : {p | fm p ≠ C ∨ fx p ≠ C} ⊆
      (edgeBand n e (-8) 0)ᶜ ∪ (closedEdgeBand n e (-6) (-4) ∪ closedEdgeBand n e (-3) (-1)) := by
    rintro p (hp | hp)
    · exact Or.inl fun h => hp (hfm p h)
    · right
      by_cases hb : p ∈ edgeBand n e (-8) 2
      · rw [hfx p hb] at hp
        obtain ⟨h1, h2, -, -⟩ := mem_edgeBand_iff_bandCoord.1 hb
        have hw := bandWidth_pos h1 h2
        have key : (-6 ≤ bandCoord n e p ∧ bandCoord n e p ≤ -4) ∨
            (-3 ≤ bandCoord n e p ∧ bandCoord n e p ≤ -1) := by
          simp only [auxWord, bandWord] at hp
          split_ifs at hp <;> first | exact absurd rfl hp |
            (left; constructor <;> linarith) | (right; constructor <;> linarith)
        rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exact Or.inl ⟨h1.le, h2.le, (le_div_iff₀ hw).1 k1, (div_le_iff₀ hw).1 k2⟩
        · exact Or.inr ⟨h1.le, h2.le, (le_div_iff₀ hw).1 k1, (div_le_iff₀ hw).1 k2⟩
      · exact absurd (hfx' p hb) hp
  have hcl : IsClosed ((edgeBand n e (-8) 0)ᶜ ∪
      (closedEdgeBand n e (-6) (-4) ∪ closedEdgeBand n e (-3) (-1))) :=
    (isOpen_edgeBand n e _ _).isClosed_compl.union
      ((isClosed_closedEdgeBand n e _ _).union (isClosed_closedEdgeBand n e _ _))
  have hyc := closure_minimal hsub hcl hy
  have hmarkle : angularConstant * min n (edgeMarkDist n e y) ≤ edgeMarkDist n e y := by
    have : min n (edgeMarkDist n e y) ≤ edgeMarkDist n e y := min_le_right _ _
    have h0 : 0 ≤ edgeMarkDist n e y := le_min dist_nonneg dist_nonneg
    unfold angularConstant at *; nlinarith [min_le_right n (edgeMarkDist n e y)]
  rcases frontier_edgeLens_subset hz with rfl | rfl | ⟨z1, z2, hzγ⟩
  · exact hmarkle.trans (min_le_left _ _)
  · exact hmarkle.trans (min_le_right _ _)
  have wz := bandWidth_pos z1 z2
  rcases hyc with hyN | hyb
  · -- `y` lies outside the open exterior band `-8 < x < 0`
    refine le_of_not_gt fun hlt => ?_
    set mz := min (e.par z) (n - e.par z)
    have hwz : bandWidth n (e.par z) = mz / 1000 := rfl
    have hmz : 0 < mz := lt_min z1 (by linarith)
    have hmarkz : edgeMarkDist n e z ≤ mz := by
      refine edgeMarkDist_le_of_mem_closedEdgeBand (α := -7) (β := -7 / 2) (by norm_num)
        (by norm_num) ⟨z1.le, z2.le, ?_, ?_⟩ <;> rcases hzγ with h | h <;> rw [h] <;> nlinarith
    have htri := edgeMarkDist_le_add n e y z
    have hdist : dist y z < mz / 2000 := by
      have h1 : dist y z < angularConstant * edgeMarkDist n e y :=
        hlt.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) ha0.le)
      unfold angularConstant at h1; nlinarith [dist_nonneg (x := y) (y := z)]
    have hss := e.abs_par_sub_le n y z
    have hdd := e.abs_nor_sub_le n y z
    have hws := (abs_bandWidth_sub_le n (e.par y) (e.par z)).trans
      (div_le_div_of_nonneg_right hss (by norm_num))
    rw [abs_le] at hss hdd hws
    have := min_le_left (e.par z) (n - e.par z)
    have := min_le_right (e.par z) (n - e.par z)
    apply hyN
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> rcases hzγ with h | h <;> rw [hwz] at h <;>
      rw [hwz] at hws <;> nlinarith
  · -- `y` lies in one of the two closed auxiliary bands
    have hzC : z ∈ closedEdgeBand n e (-7) (-7) ∨ z ∈ closedEdgeBand n e (-7 / 2) (-7 / 2) := by
      rcases hzγ with h | h
      · exact Or.inl ⟨z1.le, z2.le, h.ge, h.le⟩
      · exact Or.inr ⟨z1.le, z2.le, h.ge, h.le⟩
    refine le_of_not_gt fun hlt => ?_
    rcases hyb with hy | hy
    · have hzY := mem_edgeBand_of_dist_lt_markDist (α' := -13 / 2) (β' := -7 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hy hlt
      rcases hzC with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> obtain ⟨-, -, h3, h4⟩ := hzY <;>
        nlinarith
    · have hzY := mem_edgeBand_of_dist_lt_markDist (α' := -7 / 2) (β' := -1 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hy hlt
      rcases hzC with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> obtain ⟨-, -, h3, h4⟩ := hzY <;>
        nlinarith

end TNLean.PEPS.Approximation
