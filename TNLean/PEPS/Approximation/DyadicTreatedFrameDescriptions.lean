/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBulkStepFloors
import TNLean.PEPS.Approximation.DyadicGuideFrames
import TNLean.PEPS.Approximation.DyadicTreatedTrueVertices

/-!
# The frames of the treated guides meet the descriptions of the bulk steps

The bulk steps of `TNLean.PEPS.Approximation.DyadicBulkStepFloors` describe their frames against
the guide of the change, homogenized on the treated squares of radius `t` and placed at the block
by a translation `d` (`06-geometry.tex`, lines 357–430):

* every hole is centered at a true vertex of that guide, with inner radius at most `ε₀ t`
  (lines 106, 109–118 and 368–373);
* the raw target lies in the remaining closed changed region (lines 357–358), and the sites of
  the lens are those placed in the translated lens (lines 421–423);
* the other owners are placed at other labels of that guide (lines 383–385 and 421–423).

This file shows that the frames of the protocol meet these descriptions. Such a frame is the
encoded frame of the sampled guide: the owner of a site is the party of the label read at the
site after a small generic displacement (lines 69–80), and the holes sit at the true vertices of
the sampled guide (lines 109–118). The point-treated guide of the protocol, homogenized on the
squares about the grid corners at the ends of an edge or at the four corners of the block, is
the guide of the step lemmas moved to the block (`homogenize_endpointBlocks`,
`homogenize_cornerBlocks`).

The first and the second description hold for the sampled guide as stated. The third holds in
closure form: a site whose owner is not the party of the label `l` lies in the closure of the
positions of labels other than `l` (`sub_mem_closure_ne_of_guideFrame_owner_ne`). Pointwise it
can fail on a boundary of the guide, where the tie convention of the sampled guide may pick a
label other than the one the guide assigns there. The source states its separation estimates for
closures so that they remain valid for the sampled labels (lines 77–79), and the plane floors
extend to closures, so the closure form suffices. The step lemmas below
(`bandBirth_step_guideFrame`, `bandDeath_step_guideFrame`, `centralBirth_step_guideFrame`,
`edgeExchange_step_guideFrame`) are the bulk steps for the frames of sampled guides, with the
three descriptions discharged. No injectivity of the owner map on labels is needed: a site whose
label is `l` is owned by the party of `l`.

## Main definitions

* `SquareEdge.endpointBlocks`, `cornerBlocks`: the grid corners treated before an edge operation
  and before the central birth.
* `lensSample`: the sites placed in the translated lens.

## Main results

* `homogenize_endpointBlocks`, `homogenize_cornerBlocks`.
* `guideFrame_holes_isTrueVertex`: description (i).
* `sub_mem_closure_ne_of_reading_ne`, `mem_lensSample`: description (ii).
* `sub_mem_closure_ne_of_guideFrame_owner_ne`: description (iii) in closure form.
* `bandBirth_step_guideFrame`, `bandDeath_step_guideFrame`, `centralBirth_step_guideFrame`,
  `edgeExchange_step_guideFrame`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`: guides and their sampling (lines 69–80), the scales (lines 102–108), the
  holes at true vertices (lines 109–125), the point treatment (lines 328–339) and the bulk
  operations (lines 357–445).

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Set Metric EncodedFrame PairEffect
open EuclideanSpace (vecKron)

/-! ### The treated squares at the block -/

/-- The grid corners at the two ends of the edge `e` of the block `S`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–333`. -/
def SquareEdge.endpointBlocks : SquareEdge → ℤ × ℤ → Finset (ℤ × ℤ)
  | .bottom, S => {S, S + (1, 0)}
  | .right, S => {S + (1, 0), S + (1, 1)}
  | .top, S => {S + (0, 1), S + (1, 1)}
  | .left, S => {S, S + (0, 1)}

/-- The four grid corners of the block `S`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–333`. -/
def cornerBlocks (S : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {S, S + (1, 0), S + (0, 1), S + (1, 1)}

/-- The open square about a point, moved by `-o`, is the open square about the moved point. -/
private theorem sub_mem_ball_iff {p o c : ℝ × ℝ} {t : ℝ} :
    p - o ∈ ball c t ↔ p ∈ ball (c + o) t := by
  rw [mem_ball, mem_ball, ← dist_sub_right p (c + o) o, add_sub_cancel_right]

private theorem blockCorner_add (n : ℝ) (S : ℤ × ℤ) (i j : ℤ) :
    blockCorner n (S + (i, j)) = (n * i, n * j) + blockCorner n S := by
  simp only [blockCorner, Prod.fst_add, Prod.snd_add, Int.cast_add, Prod.mk_add_mk]
  ring_nf

private theorem blockCorner_self (n : ℝ) (S : ℤ × ℤ) :
    blockCorner n S = ((0 : ℝ), (0 : ℝ)) + blockCorner n S := by
  rw [zero_add']

/-- **The treated squares of an edge at the block.** The open squares of radius `t` about the
grid corners at the ends of the edge `e` of the block `S` are the treated squares of `e`, moved
from the origin to the block.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–333`. -/
theorem preimage_edgeTreated (n t : ℝ) (e : SquareEdge) (S : ℤ × ℤ) :
    (· - blockCorner n S) ⁻¹' edgeTreated n e t =
      ⋃ Q ∈ e.endpointBlocks S, ball (blockCorner n Q) t := by
  ext p
  simp only [mem_preimage, edgeTreated, mem_union, sub_mem_ball_iff, mem_iUnion, exists_prop]
  cases e <;>
    simp [SquareEdge.endpointBlocks, SquareEdge.point, blockCorner_add] <;>
    simp [blockCorner, Prod.mk_add_mk]

/-- **The treated squares of the central birth at the block.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–333`. -/
theorem preimage_cornerTreated (n t : ℝ) (S : ℤ × ℤ) :
    (· - blockCorner n S) ⁻¹' cornerTreated n t =
      ⋃ Q ∈ cornerBlocks S, ball (blockCorner n Q) t := by
  ext p
  simp only [mem_preimage, cornerTreated, mem_union, sub_mem_ball_iff, mem_iUnion, exists_prop]
  simp [cornerBlocks, blockCorner_add] <;>
    simp [blockCorner, Prod.mk_add_mk, or_assoc]

/-- Homogenizing a guide moved by `o` on the preimage of `U` is moving the homogenized guide. -/
theorem homogenize_preimage_shiftGuide {κ : Type*} (o : ℝ × ℝ) (U : Set (ℝ × ℝ)) (P : κ)
    (g : ℝ × ℝ → κ) :
    homogenize ((· - o) ⁻¹' U) P (shiftGuide o g) = shiftGuide o (homogenize U P g) :=
  rfl

/-- **The point-treated guide of an edge operation.** The guide of the block `S`, homogenized to
`P` on the open squares of radius `t` about the grid corners at the ends of the edge `e`, is the
guide homogenized on the treated squares of `e`, moved to the block.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–336`. -/
theorem homogenize_endpointBlocks {κ : Type*} (n t : ℝ) (e : SquareEdge) (S : ℤ × ℤ) (P : κ)
    (g : ℝ × ℝ → κ) :
    homogenize (⋃ Q ∈ e.endpointBlocks S, ball (blockCorner n Q) t) P
        (shiftGuide (blockCorner n S) g) =
      shiftGuide (blockCorner n S) (homogenize (edgeTreated n e t) P g) := by
  rw [← preimage_edgeTreated, homogenize_preimage_shiftGuide]

/-- **The point-treated guide of the central birth.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–336`. -/
theorem homogenize_cornerBlocks {κ : Type*} (n t : ℝ) (S : ℤ × ℤ) (P : κ) (g : ℝ × ℝ → κ) :
    homogenize (⋃ Q ∈ cornerBlocks S, ball (blockCorner n Q) t) P
        (shiftGuide (blockCorner n S) g) =
      shiftGuide (blockCorner n S) (homogenize (cornerTreated n t) P g) := by
  rw [← preimage_cornerTreated, homogenize_preimage_shiftGuide]

/-! ### The three descriptions -/

section Descriptions

variable {κ : Type*} {G G₁ G₂ f f₁ f₂ : ℝ × ℝ → κ} {d v : ℝ × ℝ}

/-- A true vertex of a moved guide is a true vertex of the guide, moved back. -/
theorem isTrueVertex_shiftGuide_iff {c : ℝ × ℝ} :
    IsTrueVertex (shiftGuide d G) c ↔ IsTrueVertex G (c - d) :=
  isTrueVertex_comp_homeomorph (f := G) (Homeomorph.subRight d)

/-- A point lies in the closure of a set moved by `d` exactly when it lies there moved back. -/
private theorem mem_closure_preimage_sub_iff {S : Set (ℝ × ℝ)} {p : ℝ × ℝ} :
    p ∈ closure ((· - d) ⁻¹' S) ↔ p - d ∈ closure S := by
  rw [← (Homeomorph.subRight d).preimage_closure]
  rfl

/-- **A true vertex of the sampled guide.** Every true vertex of a reading of a guide moved by
`d` is a true vertex of the guide, moved back.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 109–111`. -/
theorem IsDisplacedReading.sub_isTrueVertex (hf : IsDisplacedReading f (shiftGuide d G) v)
    {c : ℝ × ℝ} (hc : IsTrueVertex f c) : IsTrueVertex G (c - d) :=
  isTrueVertex_shiftGuide_iff.1 (hf.isTrueVertex hc)

/-- **Description (ii): the changed region of the sampled guides.** Where the readings along one
displacement of two guides moved by `d` differ, the point moved back lies in the closure of the
region where the guides differ.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:76–80, 357–358`. -/
theorem sub_mem_closure_ne_of_reading_ne (h₁ : IsDisplacedReading f₁ (shiftGuide d G₁) v)
    (h₂ : IsDisplacedReading f₂ (shiftGuide d G₂) v) {p : ℝ × ℝ} (hp : f₁ p ≠ f₂ p) :
    p - d ∈ closure {x | G₁ x ≠ G₂ x} :=
  mem_closure_preimage_sub_iff.1 (h₁.ne_subset_closure h₂ hp)

/-- Where the reading of a guide moved by `d` is not `l`, the point moved back lies in the
closure of the positions of labels other than `l`. -/
theorem sub_mem_closure_ne_of_reading_ne_const (hf : IsDisplacedReading f (shiftGuide d G) v)
    {l : κ} {p : ℝ × ℝ} (hp : f p ≠ l) : p - d ∈ closure {x | G x ≠ l} :=
  sub_mem_closure_ne_of_reading_ne (G₂ := fun _ => l) hf (isDisplacedReading_const l v) hp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type*}
  {own : κ → Party} {ph : κ} {rank : κ → ℕ} {V : Finset (ℝ × ℝ)}
  {hole : ℝ × ℝ → SquarePatch pos q}
  {hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer}

/-- **Description (i): the holes of the frame of a sampled guide.** If the holes of the frame of
a reading of a guide moved by `d` sit at true vertices of the reading, with patches centered
there and of radius at most `r`, every hole is centered, moved back, at a true vertex of the
guide, with inner radius at most `r`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:106, 109–118, 368–373`. -/
theorem guideFrame_holes_isTrueVertex (hf : IsDisplacedReading f (shiftGuide d G) v)
    (hVf : ∀ c ∈ V, IsTrueVertex f c) {r : ℝ}
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale ≤ r) :
    ∀ hl ∈ (guideFrame pos q f own ph rank V hole hV).holes,
      IsTrueVertex G (hl.patch.center - d) ∧ hl.patch.scale ≤ r := by
  intro hl hhl
  obtain ⟨z, hz, rfl⟩ := mem_holes_guideFrame.1 hhl
  refine ⟨?_, (hhole z).2⟩
  rw [(hhole z).1]
  exact hf.sub_isTrueVertex (hVf z hz)

/-- The centers of the true-vertex set of a temporary guide are true vertices of it. -/
theorem isTrueVertex_of_mem_treatedTrueVertices {κ : Type} {n t : ℝ} {M : ℤ}
    {marks : Finset (ℤ × ℤ)} {f : ℝ × ℝ → κ} {c : ℝ × ℝ}
    (hc : c ∈ treatedTrueVertices n t M marks f) : IsTrueVertex f c := by
  classical
  exact (Finset.mem_filter.1 hc).2

/-- **Description (iii), in closure form: the other owners.** In the frame of a reading of a
guide moved by `d`, a site not owned by the party of the label `l` is placed, moved back, in the
closure of the positions of labels other than `l`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:76–80, 383–385, 421–423`. -/
theorem sub_mem_closure_ne_of_guideFrame_owner_ne
    (hf : IsDisplacedReading f (shiftGuide d G) v) {l : κ} {x : ι}
    (hx : (guideFrame pos q f own ph rank V hole hV).owner x ≠ own l) :
    pos x - d ∈ closure {p | G p ≠ l} :=
  sub_mem_closure_ne_of_reading_ne_const hf fun h => hx (by rw [guideFrame_owner, h])

end Descriptions

/-- The sites placed in the lens of the edge `e`, moved by `d`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:421–423`. -/
def lensSample {ι : Type*} [Fintype ι] (pos : ι → ℝ × ℝ) (n : ℝ) (e : SquareEdge)
    (d : ℝ × ℝ) : Finset ι :=
  open Classical in Finset.univ.filter fun x => pos x - d ∈ edgeLens n e

/-- **Description (ii) for the exchange.** The sites of the lens sample are those placed in the
translated lens. -/
theorem mem_lensSample {ι : Type*} [Fintype ι] {pos : ι → ℝ × ℝ} {n : ℝ} {e : SquareEdge}
    {d : ℝ × ℝ} (x : ι) : x ∈ lensSample pos n e d ↔ pos x - d ∈ edgeLens n e := by
  classical
  simp [lensSample]

/-! ### Separation in closure form -/

/-- The tapering separation passes to the closure of the exterior. -/
theorem AngularSeparation.closure_right {X E : Set (ℝ × ℝ)} {n t a : ℝ} {V : Finset (ℝ × ℝ)}
    (h : AngularSeparation X E n t a V) : AngularSeparation X (closure E) n t a V := by
  intro x hx y hy
  exact closure_minimal (fun z hz => h x hx z hz)
    (isClosed_le continuous_const (continuous_const.dist continuous_id)) hy

variable {q : ℕ} [NeZero q] {J Δ a A₀ D L₀ : ℝ} {m₀ : ℕ} {L : ℕ}
  {h : SquareHamiltonian L q J} {E₀ : ℝ} {Ω : StateSpace L q}
  {pos : SquareLatticeVertex L L → ℝ × ℝ} {c : ℝ × ℝ} {Party : Type} {κ : Type*}
  {own : κ → Party} {ph : κ} {rank : κ → ℕ} {V : Finset (ℝ × ℝ)}
  {hole : ℝ × ℝ → SquarePatch pos q}
  {hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer}

omit [NeZero q] in
/-- **The separation premise of a birth or death for the frame of a sampled guide.** Let `f` read
the guide `G` moved by `d`, and let the holes of its frame sit at true vertices of `f` with radius
at most `r`. If the plane separation of the remaining changed region `X` from the other labels of
`G` and the zone `Z` of radius `2 r` about its true vertices holds, then the moved target `T`,
placed in `X`, is separated from the exterior of the birth of the party of `l`. -/
theorem angularSeparation_birthEnv_guideFrame {G f : ℝ × ℝ → κ} {d v : ℝ × ℝ}
    (hf : IsDisplacedReading f (shiftGuide d G) v) (hVf : ∀ z ∈ V, IsTrueVertex f z) {r : ℝ}
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale ≤ r) {X : Set (ℝ × ℝ)} {l : κ}
    {n t a' : ℝ} {W : Finset (ℝ × ℝ)}
    (hsep : AngularSeparation ((· + d) '' X) ((· + d) '' ({z | G z ≠ l} ∪ vertexZone G (2 * r)))
      n t a' W)
    (ht : 0 ≤ t) (ha : a ≤ a') {T : Finset (SquareLatticeVertex L L)}
    (hT : ∀ x ∈ T, pos x - d ∈ X) :
    AngularSeparation (pos '' T)
      (pos '' (guideFrame pos q f own ph rank V hole hV).birthEnv (own l)) n t a W := by
  refine ((hsep.closure_right.mono_left ?_).mono_right ?_).mono_const ht ha
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_image_add_right_iff.2 (hT x hx)
  · rintro _ ⟨x, hx, rfl⟩
    have himg : ∀ y, y - d ∈ {z | G z ≠ l} ∪ vertexZone G (2 * r) →
        y ∈ (· + d) '' ({z | G z ≠ l} ∪ vertexZone G (2 * r)) :=
      fun y hy => mem_image_add_right_iff.2 hy
    rcases (Frame.mem_birthEnv _).1 hx with hx | hx
    · have hcl := sub_mem_closure_ne_of_guideFrame_owner_ne hf hx
      have hsub : (· + d) '' closure {p | G p ≠ l} ⊆
          closure ((· + d) '' ({z | G z ≠ l} ∪ vertexZone G (2 * r))) :=
        (image_closure_subset_closure_image (continuous_add_right d)).trans
          (closure_mono (image_mono subset_union_left))
      exact hsub (mem_image_add_right_iff.2 hcl)
    · exact subset_closure (himg _ (Or.inr (mem_image_add_right_iff.1
        (mem_image_vertexZone_of_mem_outerHoles _
          (guideFrame_holes_isTrueVertex hf hVf hhole) hx))))

/-- The marked points of an edge operation, translated, number at most two. -/
private theorem card_edgeMarks_le' (n : ℝ) (e : SquareEdge) (d : ℝ × ℝ) :
    (({e.point n 0 0, e.point n n 0} : Finset (ℝ × ℝ)).image (· + d)).card ≤ 2 :=
  Finset.card_image_le.trans (Finset.card_le_two)

/-- The four corners, translated, number at most four. -/
private theorem card_cornerMarks_le' (n : ℝ) (d : ℝ × ℝ) :
    (({(0, 0), (n, 0), (0, n), (n, n)} : Finset (ℝ × ℝ)).image (· + d)).card ≤ 4 :=
  Finset.card_image_le.trans (Finset.card_le_four)

/-- **An edge birth for the frame of the sampled guide, conditional on Proposition 3.4.** In the
setting of `bandBirth_step`, let the frame be the encoded frame of a reading `f`, along a
displacement `v`, of the surrounding guide homogenized on the treated squares and moved to the
block by `d`, with holes at true vertices of `f` of inner radius at most `ε₀ t`. Let `T` be a set
of sites, owned by the party of the surrounding label, outside every outer hole and of diameter
at most `A₀ n`, at which the readings along `v` of the moved homogenized guides before and after
the operation differ. Then the birth of `T` at `Q∘` is an allowed word using only `P∘` and `Q∘`,
with at most one pair source and error `L^{-30}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80`, `102–125`,
`357–387` and `440–445`. -/
theorem bandBirth_step_guideFrame (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hm₀ : 2 ≤ m₀) (ha : a ≤ angularConstant / 2) (op : BandOperation κ) (e : SquareEdge)
    (g : ℝ × ℝ → κ) (d v : ℝ × ℝ) {n ε₀ : ℝ} (ht : 0 ≤ D * Real.log L)
    (htn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L) (hε : 2 * ε₀ ≤ angularConstant / 2)
    {f fb fa : ℝ × ℝ → κ}
    (hf : IsDisplacedReading f (shiftGuide d (homogenize (edgeTreated n e (D * Real.log L))
      op.label (bandUpdate n e op.surrounding g))) v)
    (hfb : IsDisplacedReading fb (shiftGuide d (homogenize (edgeTreated n e (D * Real.log L))
      op.label (bandUpdate n e op.before g))) v)
    (hfa : IsDisplacedReading fa (shiftGuide d (homogenize (edgeTreated n e (D * Real.log L))
      op.label (bandUpdate n e op.after g))) v)
    (hVf : ∀ z ∈ V, IsTrueVertex f z)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale ≤ ε₀ * (D * Real.log L))
    {T : Finset (SquareLatticeVertex L L)} {Q : Party}
    (hTP : ∀ x ∈ T, own (f (pos x)) = own op.label)
    (hTH : Disjoint (T : Set _) (guideFrame pos q f own ph rank V hole hV).outerHoles)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * n)
    (hT : ∀ x ∈ T, fb (pos x) ≠ fa (pos x)) :
    ∃ w : Word (guideFrame pos q f own ph rank V hole hV).regs
        ((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).regs,
      w.IsAllowed ∧ w.UsesOnly {own op.label, Q} ∧ w.sourceCount ≤ 1 ∧
      ‖w.eval ((guideFrame pos q f own ph rank V hole hV).regIso.symm
          ((guideFrame pos q f own ph rank V hole hV).refVec Ω)) -
        ((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).regIso.symm
          (((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).refVec Ω)‖ ≤
          (L : ℝ) ^ (-30 : ℤ) :=
  bulkBirth_step hD hL hΩ hpos _ hTP hTH ((card_edgeMarks_le' n e d).trans hm₀) htn hnL hdiam
    (angularSeparation_birthEnv_guideFrame hf hVf hhole
      (op.angularSeparation_bandUpdate ht htn hε e g d) ht ha
      fun x hx => sub_mem_closure_ne_of_reading_ne hfb hfa (hT x hx))

/-- **An edge death for the frame of the sampled guide, conditional on Proposition 3.4.** In the
setting of `bandBirth_step_guideFrame`, with the frame that of the sampled surrounding guide after
the death, the death of `T` from the frame in which `T` is owned by `Q∘` is an allowed monomial
using only `P∘` and `Q∘`, without pair sources, with at most one pair effect and error
`L^{-30}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80`, `102–125`,
`357–387` and `440–445`. -/
theorem bandDeath_step_guideFrame (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hm₀ : 2 ≤ m₀) (ha : a ≤ angularConstant / 2) (op : BandOperation κ) (e : SquareEdge)
    (g : ℝ × ℝ → κ) (d v : ℝ × ℝ) {n ε₀ : ℝ} (ht : 0 ≤ D * Real.log L)
    (htn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L) (hε : 2 * ε₀ ≤ angularConstant / 2)
    {f fb fa : ℝ × ℝ → κ}
    (hf : IsDisplacedReading f (shiftGuide d (homogenize (edgeTreated n e (D * Real.log L))
      op.label (bandUpdate n e op.surrounding g))) v)
    (hfb : IsDisplacedReading fb (shiftGuide d (homogenize (edgeTreated n e (D * Real.log L))
      op.label (bandUpdate n e op.before g))) v)
    (hfa : IsDisplacedReading fa (shiftGuide d (homogenize (edgeTreated n e (D * Real.log L))
      op.label (bandUpdate n e op.after g))) v)
    (hVf : ∀ z ∈ V, IsTrueVertex f z)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale ≤ ε₀ * (D * Real.log L))
    {T : Finset (SquareLatticeVertex L L)} {Q : Party}
    (hTP : ∀ x ∈ T, own (f (pos x)) = own op.label)
    (hTH : Disjoint (T : Set _) (guideFrame pos q f own ph rank V hole hV).outerHoles)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * n)
    (hT : ∀ x ∈ T, fb (pos x) ≠ fa (pos x)) :
    ∃ M : PartyChain ((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).regs
        (guideFrame pos q f own ph rank V hole hV).regs,
      M.IsAllowed ∧ M.UsesOnly {own op.label, Q} ∧ M.sourceCount = 0 ∧
      M.toEffectChain.effectCount ≤ 1 ∧
      ‖M.toEffectChain.eval
          (((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).regIso.symm
            (((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).refVec Ω)) -
        (guideFrame pos q f own ph rank V hole hV).regIso.symm
          ((guideFrame pos q f own ph rank V hole hV).refVec Ω)‖ ≤ (L : ℝ) ^ (-30 : ℤ) :=
  bulkDeath_step hD hL hΩ hpos _ hTP hTH ((card_edgeMarks_le' n e d).trans hm₀) htn hnL hdiam
    (angularSeparation_birthEnv_guideFrame hf hVf hhole
      (op.angularSeparation_bandUpdate ht htn hε e g d) ht ha
      fun x hx => sub_mem_closure_ne_of_reading_ne hfb hfa (hT x hx))

/-- **The central birth for the frame of the sampled guide, conditional on Proposition 3.4.** In
the setting of `centralBirth_step`, let the frame be the encoded frame of a reading `f`, along
`v`, of the starting guide homogenized to the old label on the treated squares about the four
corners and moved to the block by `d`, with holes at true vertices of `f` of inner radius at most
`ε₀ t`. If the target `T` is owned by the party of the old label, lies outside every outer hole,
has diameter at most `A₀ n`, and consists of sites at which the readings along `v` of the moved
homogenized starting and central guides differ, then the birth of `T` at `Q∘` is an allowed word
using only `P∘` and `Q∘`, with at most one pair source and error `L^{-30}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80`, `102–125`,
`155–160`, `357–387` and `440–445`. -/
theorem centralBirth_step_guideFrame (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hm₀ : 4 ≤ m₀) (ha : a ≤ angularConstant / 2) (R : RepaintingBaseline κ) (d v : ℝ × ℝ)
    {ε₀ : ℝ} (ht : 0 ≤ D * Real.log L) (htn : D * Real.log L ≤ R.n) (hnL : R.n ≤ A₀ * L)
    (hε : 2 * ε₀ ≤ angularConstant / 2) {f fb fa : ℝ × ℝ → κ}
    (hf : IsDisplacedReading f (shiftGuide d
      (homogenize (cornerTreated R.n (D * Real.log L)) R.oldLabel R.guide)) v)
    (hfa : IsDisplacedReading fa (shiftGuide d
      (homogenize (cornerTreated R.n (D * Real.log L)) R.oldLabel R.centralGuide)) v)
    (hVf : ∀ z ∈ V, IsTrueVertex f z)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale ≤ ε₀ * (D * Real.log L))
    {T : Finset (SquareLatticeVertex L L)} {Q : Party}
    (hTP : ∀ x ∈ T, own (f (pos x)) = own R.oldLabel)
    (hTH : Disjoint (T : Set _) (guideFrame pos q f own ph rank V hole hV).outerHoles)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * R.n)
    (hT : ∀ x ∈ T, f (pos x) ≠ fa (pos x)) :
    ∃ w : Word (guideFrame pos q f own ph rank V hole hV).regs
        ((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).regs,
      w.IsAllowed ∧ w.UsesOnly {own R.oldLabel, Q} ∧ w.sourceCount ≤ 1 ∧
      ‖w.eval ((guideFrame pos q f own ph rank V hole hV).regIso.symm
          ((guideFrame pos q f own ph rank V hole hV).refVec Ω)) -
        ((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).regIso.symm
          (((guideFrame pos q f own ph rank V hole hV).changeOwner T Q).refVec Ω)‖ ≤
          (L : ℝ) ^ (-30 : ℤ) :=
  bulkBirth_step hD hL hΩ hpos _ hTP hTH ((card_cornerMarks_le' R.n d).trans hm₀) htn hnL hdiam
    (angularSeparation_birthEnv_guideFrame hf hVf hhole
      (R.angularSeparation_central ht htn hε d) ht ha
      fun x hx => sub_mem_closure_ne_of_reading_ne hf hfa (hT x hx))

/-- **The lens exchange of an edge for the frames of the sampled guides, conditional on
Proposition 3.4.** In the setting of `edgeExchange_step`, let the frames of the two sheets be the
encoded frames of readings `f₁`, `f₂`, along one displacement `v`, of the main and auxiliary
guides homogenized to `C_e` on the treated squares and moved to the block by `d`, with holes at
true vertices of the readings of inner radius at most `ε₀ t`, and let `Y` be the sites placed in
the translated lens. Then the exchange, by the party of `C_e`, is an allowed word using only that
party, without pair resources, with error at most `4 L^{-30}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80`, `102–125`,
`389–430` and `440–445`. -/
theorem edgeExchange_step_guideFrame (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hm₀ : 2 ≤ m₀) (ha : a ≤ angularConstant / 2) (R : RepaintingBaseline κ)
    (E : List SquareEdge) (e : SquareEdge) (d v : ℝ × ℝ) {ε₀ : ℝ} (ht : 0 < D * Real.log L)
    (htn : D * Real.log L ≤ R.n) (hnL : R.n ≤ A₀ * L)
    (hε : 2 * ε₀ * (angularConstant + 1) ≤ angularConstant / 2) {f₁ f₂ : ℝ × ℝ → κ}
    (hf₁ : IsDisplacedReading f₁ (shiftGuide d
      (homogenize (edgeTreated R.n e (D * Real.log L)) (R.nbrLabel e)
        (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e))))) v)
    (hf₂ : IsDisplacedReading f₂ (shiftGuide d
      (homogenize (edgeTreated R.n e (D * Real.log L)) (R.nbrLabel e)
        (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e))))) v)
    {V₁ V₂ : Finset (ℝ × ℝ)}
    {hV₁ : (V₁ : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer}
    {hV₂ : (V₂ : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer}
    (hVf₁ : ∀ z ∈ V₁, IsTrueVertex f₁ z) (hVf₂ : ∀ z ∈ V₂, IsTrueVertex f₂ z)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale ≤ ε₀ * (D * Real.log L))
    (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ (guideFrame pos q f₁ own ph rank V₁ hole hV₁).holes ++
        (guideFrame pos q f₂ own ph rank V₂ hole hV₂).holes, out h = true →
      Disjoint (h.patch.outer : Set (SquareLatticeVertex L L)) (lensSample pos R.n e d))
    (hin : ∀ h ∈ (guideFrame pos q f₁ own ph rank V₁ hole hV₁).holes ++
        (guideFrame pos q f₂ own ph rank V₂ hole hV₂).holes, out h = false →
      (h.patch.outer : Set (SquareLatticeVertex L L)) ⊆ lensSample pos R.n e d)
    (hdiam : ∀ x ∈ (TwoSheetExchange.ofFrames (guideFrame pos q f₁ own ph rank V₁ hole hV₁)
        (guideFrame pos q f₂ own ph rank V₂ hole hV₂) (lensSample pos R.n e d) out hout
          hin).tSet (own (R.nbrLabel e)),
      ∀ y ∈ (TwoSheetExchange.ofFrames (guideFrame pos q f₁ own ph rank V₁ hole hV₁)
        (guideFrame pos q f₂ own ph rank V₂ hole hV₂) (lensSample pos R.n e d) out hout
          hin).tSet (own (R.nbrLabel e)),
        dist (pos x) (pos y) ≤ A₀ * R.n) :
    ∃ w : Word ((guideFrame pos q f₁ own ph rank V₁ hole hV₁).regs ++
          (guideFrame pos q f₂ own ph rank V₂ hole hV₂).regs)
        ((TwoSheetExchange.ofFrames (guideFrame pos q f₁ own ph rank V₁ hole hV₁)
            (guideFrame pos q f₂ own ph rank V₂ hole hV₂) (lensSample pos R.n e d) out hout
              hin).newFrame₁.regs ++
          (TwoSheetExchange.ofFrames (guideFrame pos q f₁ own ph rank V₁ hole hV₁)
            (guideFrame pos q f₂ own ph rank V₂ hole hV₂) (lensSample pos R.n e d) out hout
              hin).newFrame₂.regs),
      w.IsAllowed ∧ w.UsesOnly {own (R.nbrLabel e)} ∧ w.sourceCount = 0 ∧
      ‖w.eval ((twoLayoutIso _ _ (guideFrame pos q f₁ own ph rank V₁ hole hV₁).owner
            (guideFrame pos q f₂ own ph rank V₂ hole hV₂).owner).symm
          (vecKron ((guideFrame pos q f₁ own ph rank V₁ hole hV₁).refVec Ω)
            ((guideFrame pos q f₂ own ph rank V₂ hole hV₂).refVec Ω))) -
        (twoLayoutIso _ _
            (TwoSheetExchange.ofFrames (guideFrame pos q f₁ own ph rank V₁ hole hV₁)
              (guideFrame pos q f₂ own ph rank V₂ hole hV₂) (lensSample pos R.n e d) out hout
                hin).newFrame₁.owner
            (TwoSheetExchange.ofFrames (guideFrame pos q f₁ own ph rank V₁ hole hV₁)
              (guideFrame pos q f₂ own ph rank V₂ hole hV₂) (lensSample pos R.n e d) out hout
                hin).newFrame₂.owner).symm
          (vecKron
            ((TwoSheetExchange.ofFrames (guideFrame pos q f₁ own ph rank V₁ hole hV₁)
              (guideFrame pos q f₂ own ph rank V₂ hole hV₂) (lensSample pos R.n e d) out hout
                hin).newFrame₁.refVec Ω)
            ((TwoSheetExchange.ofFrames (guideFrame pos q f₁ own ph rank V₁ hole hV₁)
              (guideFrame pos q f₂ own ph rank V₂ hole hV₂) (lensSample pos R.n e d) out hout
                hin).newFrame₂.refVec Ω))‖ ≤
        4 * (L : ℝ) ^ (-30 : ℤ) := by
  have hfl := R.floor_exchange_frontier ht htn hε E e d
  refine lensExchange_step_of_frontier hD hL hΩ hpos _ _ _ out hout hin _
    (K := (· + d) '' edgeLens R.n e)
    (fun x => (mem_lensSample x).trans mem_image_add_right_iff.symm)
    ((card_edgeMarks_le' R.n e d).trans hm₀) htn hnL hdiam fun x hx z hz => ?_
  refine (mul_le_mul_of_nonneg_right ha (ht.le.trans (le_max_left _ _))).trans
    (hfl (pos x) ?_ z hz)
  have hZ := (Finset.mem_inter.1 hx).1
  rw [TwoSheetExchange.mem_ofFrames_exchangeEnv] at hZ
  have h2 : (2 : ℝ) * ε₀ * (D * Real.log L) = 2 * (ε₀ * (D * Real.log L)) := mul_assoc _ _ _
  rcases hZ with hZ | hZ | hZ
  · refine mem_image_add_right_iff.2 (Or.inl (Or.inl ?_))
    by_cases h₁ : (guideFrame pos q f₁ own ph rank V₁ hole hV₁).owner x = own (R.nbrLabel e)
    · exact closure_mono (fun p hp => Or.inr hp)
        (sub_mem_closure_ne_of_guideFrame_owner_ne hf₂ fun h₂ => hZ ⟨h₁, h₂⟩)
    · exact closure_mono (fun p hp => Or.inl hp) (sub_mem_closure_ne_of_guideFrame_owner_ne hf₁ h₁)
  · obtain ⟨y, hy, he⟩ := mem_image_vertexZone_of_mem_outerHoles _
      (guideFrame_holes_isTrueVertex hf₁ hVf₁ hhole) hZ
    exact ⟨y, Or.inl (Or.inr (h2 ▸ hy)), he⟩
  · obtain ⟨y, hy, he⟩ := mem_image_vertexZone_of_mem_outerHoles _
      (guideFrame_holes_isTrueVertex hf₂ hVf₂ hhole) hZ
    exact ⟨y, Or.inr (h2 ▸ hy), he⟩

end TNLean.PEPS.Approximation
