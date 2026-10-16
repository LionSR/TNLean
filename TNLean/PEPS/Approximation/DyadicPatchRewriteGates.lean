/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicActiveLabelParties
import TNLean.PEPS.Approximation.DyadicSmallPatchCovers

/-!
# Patch data of the junction resizes and the direct repaintings

Proposition 7.1 of the polynomial-PEPS manuscript (`prop:protocol`, item 2) bounds the number of
gates with other parties in which a party participates over its lifetime. The count is
`TNLean.PEPS.Approximation.card_gates_le_of_uses`, under the hypothesis that each gate involves
only the parties its event uses. This file constructs the patch data of candidate small-patch
rewrites for two kinds of events, and proves that every party of such patch data is used by its
event:

* the resize of the hole at a grid corner of the guide uniform on `2 ^ j`-blocks, before the
  level `2 ^ j / 2` (`06-geometry.tex:127–131, 529–541`);
* the direct repainting of a square of side `n = 2 ^ j'` by one small-patch rewrite, as the
  source does for `n ≤ K₀ t` (`06-geometry.tex:500–524`).

The patch data of a candidate small-patch rewrite (Lemma `lem:small-rewrite`,
`05-frames.tex:188–218`) is its old and new guide, the centres of its patches with a common inner
radius `u`, and the centres of its affected holes with one outer radius covering every affected
old and new hole. Its parties are those named in item 4 of the lemma: the raw owners, under the
old and the new guide, on the outer patch squares (radius `2 u`) and on the outer footprints of
the affected holes, and the tag holders of the affected holes. Conditions 1–3 of the lemma (the
two-owner tests outside the old and new inner holes, and the avoidance of the untouched hole
footprints by the outer patch squares) are not part of the patch data and are not verified here
for the constructed nets. The patch data is not connected to the frame form of the lemma,
`TNLean.PEPS.EncodedFrame.SmallPatchRewrite`; here the raw owners are the labels of the guides,
read in the plane.

For both kinds of events the patches are a square net of mesh `u = ν 2 ^ j` over the region the
source covers: the two outer footprints of the resized hole, or the repainted square together with
the outer holes at its four corners. With `2 ε₀ + 3 ν < 1` the whole footprint of the rewrite
lies within sup distance `2 ^ j` of the junction, or of the repainted square. A block guide takes
there only the labels of the four blocks at the junction, or of the blocks that differ from the
repainted square by at most one in each index. Hence every block party of the patch data is used
by its event. The lifetime bound follows for every schedule of such events, under the hypothesis
that each gate involves only the parties of its patch data. That hypothesis is the conclusion of
Lemma `lem:small-rewrite`; it is not yet derived here from the frame-level lemma.

Geometric facts behind the two-owner condition, the avoidance of the untouched holes, and the
choice of `ν` are in `TNLean.PEPS.Approximation.DyadicSmallPatchCovers` and
`TNLean.PEPS.Approximation.DyadicFootprintScaling`; they do not enter the party count. The gates
of the large-scale repaintings (`n > K₀ t`), with their births, deaths, exchanges and point
treatments, are not treated here.

## Main results

* `TNLean.PEPS.Approximation.GuidePatchRewrite`: the patch data of a candidate small-patch
  rewrite, with its footprint and its parties.
* `TNLean.PEPS.Approximation.GuidePatchRewrite.IsJunctionResize.uses`,
  `TNLean.PEPS.Approximation.GuidePatchRewrite.IsDirectRepainting.uses`: every block party of the
  patch data is used by its event.
* `TNLean.PEPS.Approximation.exists_junctionResize`,
  `TNLean.PEPS.Approximation.exists_directRepainting`: patch data for the rewrites of the source,
  with a net of at most a fixed number of patches covering the region the source covers.
* `TNLean.PEPS.Approximation.card_gates_le_of_guidePatchRewrites`: the lifetime bound, conditional
  on each gate involving only the parties of its patch data.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §6, `05-frames.tex:182–218` (Lemma
  `lem:small-rewrite`), and §7, `06-geometry.tex`: the holes and their resizing (lines 102–133),
  the direct repainting and the hole resizing by small-patch rewrites (lines 500–541), and the
  party lifetimes (lines 572–631).
-/

namespace TNLean.PEPS.Approximation

open Set Metric

/-! ### Small-patch rewrites -/

/-- The patch data of a candidate small-patch rewrite of one sheet: its old and new guide, the
centres of its patches with a common inner radius `mesh`, and the centres of its affected old and
new holes with an outer radius `holeOuter` covering each of them. Conditions 1–3 of Lemma
`lem:small-rewrite` (`05-frames.tex:194–202`) are not part of this structure.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma `lem:small-rewrite`,
`05-frames.tex:188–218`. -/
structure GuidePatchRewrite (ι : Type*) where
  /-- The guide before the rewrite. -/
  old : ℝ × ℝ → ι
  /-- The guide after the rewrite. -/
  new : ℝ × ℝ → ι
  /-- The centres of the patches. -/
  centers : Finset (ℝ × ℝ)
  /-- The inner radius of every patch; its outer square has radius `2 * mesh`. -/
  mesh : ℝ
  /-- The centres of the affected old and new holes. -/
  holes : Finset (ℝ × ℝ)
  /-- An outer radius covering every affected old and new hole. -/
  holeOuter : ℝ

namespace GuidePatchRewrite

variable {ι : Type*} (G : GuidePatchRewrite ι)

/-- The footprint of the patch data: its outer patch squares and the outer footprints of
its affected holes.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “the involved patch and affected-hole
footprints”, `05-frames.tex:203`. -/
def footprint : Set (ℝ × ℝ) :=
  (⋃ c ∈ G.centers, closedBall c (2 * G.mesh)) ∪ ⋃ h ∈ G.holes, closedBall h G.holeOuter

/-- The parties of the patch data: the raw owners, under the old and the new guide, on its
footprint, and the tag holders of its affected holes. These are the parties named in item 4 of
Lemma `lem:small-rewrite`; that a rewrite meeting conditions 1–3 uses only them is the lemma's
conclusion, not proved here.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma `lem:small-rewrite`, item 4 and its
conclusion, `05-frames.tex:203–216`. -/
def parties (ph : ι) : Set ι :=
  G.old '' G.footprint ∪ G.new '' G.footprint ∪
    {l | ∃ h ∈ G.holes, IsTagHolder G.old ph h l ∨ IsTagHolder G.new ph h l}

/-- The tag holder of an affected hole is a raw owner on its outer footprint, so the parties of a
patch data are the raw owners on its footprint. -/
theorem parties_subset (ph : ι) (h0 : 0 < G.holeOuter) :
    G.parties ph ⊆ G.old '' G.footprint ∪ G.new '' G.footprint := by
  have key : ∀ (f : ℝ × ℝ → ι), ∀ h ∈ G.holes, incidentLabels f h ⊆ f '' G.footprint :=
    fun f h hh => incidentLabels_subset (closedBall_mem_nhds h h0) fun p hp =>
      mem_image_of_mem f (Or.inr (mem_biUnion hh hp))
  rintro l ((hl | hl) | ⟨h, hh, hl | hl⟩)
  · exact Or.inl hl
  · exact Or.inr hl
  · exact Or.inl (key _ h hh hl.1)
  · exact Or.inr (key _ h hh hl.1)

end GuidePatchRewrite

/-! ### Block indices near a block or a grid corner -/

/-- The floor of `y / n` for `n a - n < y < n b + n` lies in `[a - 1, b]`. -/
theorem floor_div_mem_Icc {n y : ℝ} (hn : 0 < n) {a b : ℤ} (h1 : n * a - n < y)
    (h2 : y < n * b + n) : a - 1 ≤ ⌊y / n⌋ ∧ ⌊y / n⌋ ≤ b := by
  constructor
  · rw [Int.le_floor, le_div_iff₀ hn]
    push_cast
    linarith
  · rw [← Int.lt_add_one_iff, Int.floor_lt, div_lt_iff₀ hn]
    push_cast
    linarith

/-- Within sup distance `n` of the grid corner `(n u, n v)`, the block index is that of one of
the four blocks at the corner. -/
theorem blockIndex_of_dist_blockCorner_lt {n : ℝ} (hn : 0 < n) {Q : ℤ × ℤ} {p : ℝ × ℝ}
    (hp : dist p (blockCorner n Q) < n) :
    Q.1 - 1 ≤ (blockIndex n p).1 ∧ (blockIndex n p).1 ≤ Q.1 ∧
      Q.2 - 1 ≤ (blockIndex n p).2 ∧ (blockIndex n p).2 ≤ Q.2 := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hp
  simp only [blockCorner] at hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  obtain ⟨a1, a2⟩ := floor_div_mem_Icc hn (y := p.1) (a := Q.1) (b := Q.1) (by linarith)
    (by linarith)
  obtain ⟨a3, a4⟩ := floor_div_mem_Icc hn (y := p.2) (a := Q.2) (b := Q.2) (by linarith)
    (by linarith)
  exact ⟨a1, a2, a3, a4⟩

/-- Within sup distance `n` of the closed block `S`, the block index differs from `S` by at most
one in each index. -/
theorem abs_blockIndex_sub_le {n : ℝ} (hn : 0 < n) {S : ℤ × ℤ} {p y : ℝ × ℝ}
    (hy : y - blockCorner n S ∈ closedSquare n) (hp : dist p y < n) :
    |(blockIndex n p).1 - S.1| ≤ 1 ∧ |(blockIndex n p).2 - S.2| ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 hy
  simp only [blockCorner, Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hp
  obtain ⟨⟨k1, k2⟩, k3, k4⟩ := hp
  obtain ⟨a1, a2⟩ := floor_div_mem_Icc hn (y := p.1) (a := S.1) (b := S.1 + 1) (by linarith)
    (by push_cast; linarith)
  obtain ⟨a3, a4⟩ := floor_div_mem_Icc hn (y := p.2) (a := S.2) (b := S.2 + 1) (by linarith)
    (by push_cast; linarith)
  simp only [blockIndex]
  exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩

/-! ### Parties of block guides near an event -/

section Parties

variable {ι : Type*} {party : ℕ × ℕ × ℕ → ι} {ph : ι}

/-- **Raw owners near a junction.** At the end of the pass to level `2 ^ j`, a block party that
owns a point within sup distance `2 ^ j` of the grid corner `(2 ^ j u, 2 ^ j v)` is the party of
one of the four blocks at the corner, and so is used by the resize of the hole there.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “Resizing uses the current block labels near
its junction”, `06-geometry.tex:127–131, 529–541, 594`. -/
theorem junctionUses_of_blockGuide_eq (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph)
    (M : ℤ) (j : ℕ) {done : Set (ℤ × ℤ)} (hd : {Q | InRoot M Q} ⊆ done) {u v : ℕ}
    {p : ℝ × ℝ} (hpc : dist p (blockCorner (2 ^ j) ((u : ℤ), (v : ℤ))) < 2 ^ j) {x : ℕ × ℕ × ℕ}
    (h : blockGuide (2 ^ j) (levelLabels M (oldParty party j) (newParty party j) ph done) p =
      party x) :
    JunctionUses j u v x := by
  obtain ⟨a1, a2, a3, a4⟩ := blockIndex_of_dist_blockCorner_lt (pow_pos two_pos j) hpc
  have hs := levelLabels_eq_party_of_subset hp hph M j hd h
  obtain ⟨⟨h1, -, h2, -⟩, hx | hx⟩ := levelLabels_eq_party hp hph M j done h
  · subst hx
    refine ⟨rfl, ?_⟩
    dsimp only at a1 a2 a3 a4 ⊢
    omega
  · rw [hx] at hs
    simp at hs

/-- **Raw owners near a repainted square.** During the level `2 ^ j'`, a block party that owns a
point within sup distance `2 ^ j'` of the closed square `(r, s)` of side `2 ^ j'`, at a transition
time between repaintings, is used by the repainting of that square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “every active main owner is an `n`- or
`2n`-block owner. On the affected footprints those blocks lie at distance `O(n)` from the
repainted square”, `06-geometry.tex:500–524, 585–592`. -/
theorem repaintingUses_of_blockGuide_eq (hp : Function.Injective party)
    (hph : ∀ x, party x ≠ ph) (M : ℤ) (j' : ℕ) (done : Set (ℤ × ℤ)) {r s : ℕ}
    {p y : ℝ × ℝ} (hy : y - blockCorner (2 ^ j') ((r : ℤ), (s : ℤ)) ∈ closedSquare (2 ^ j'))
    (hpy : dist p y < 2 ^ j') {x : ℕ × ℕ × ℕ}
    (h : blockGuide (2 ^ j') (levelLabels M (oldParty party j') (newParty party j') ph done) p =
      party x) :
    RepaintingUses j' r s x := by
  have := repaintingUses_of_levelLabels hp hph M j' done
    (S := ((r : ℤ), (s : ℤ))) (abs_blockIndex_sub_le (pow_pos two_pos j') hy hpy) h
  simpa using this

/-! ### The rewrites of the junction resizes and the direct repaintings -/

namespace GuidePatchRewrite

/-- **The resize of a hole at a junction.** The rewrite resizes the hole at the grid corner
`(2 ^ j u, 2 ^ j v)` of the guide uniform on `2 ^ j`-blocks at the end of the pass to level
`2 ^ j`, without changing the guide; its footprint lies within sup distance `2 ^ j` of the corner.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:127–131, 529–541`. -/
def IsJunctionResize (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j u v : ℕ)
    (G : GuidePatchRewrite ι) : Prop :=
  ∃ done : Set (ℤ × ℤ), {Q | InRoot M Q} ⊆ done ∧
    G.old = blockGuide (2 ^ j) (levelLabels M (oldParty party j) (newParty party j) ph done) ∧
    G.new = G.old ∧ G.holes = {blockCorner (2 ^ j) ((u : ℤ), (v : ℤ))} ∧ 0 < G.holeOuter ∧
    G.footprint ⊆ ball (blockCorner (2 ^ j) ((u : ℤ), (v : ℤ))) (2 ^ j)

/-- **The direct repainting of a square.** The rewrite repaints the square `(r, s)` of side
`2 ^ j'` from the block guide of level `2 ^ j'` at a transition time to the block guide in which
the square carries its new label; its affected holes are at the corners of the square, and its
footprint lies within sup distance `2 ^ j'` of the closed square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:82–90, 500–524`. -/
def IsDirectRepainting (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j' r s : ℕ)
    (G : GuidePatchRewrite ι) : Prop :=
  ∃ done : Set (ℤ × ℤ),
    G.old = blockGuide (2 ^ j') (levelLabels M (oldParty party j') (newParty party j') ph done) ∧
    G.new = blockGuide (2 ^ j')
      (levelLabels M (oldParty party j') (newParty party j') ph (insert ((r : ℤ), (s : ℤ)) done)) ∧
    (∀ h ∈ G.holes, ∃ Q : ℤ × ℤ, IsBlockCornerOf ((r : ℤ), (s : ℤ)) Q ∧
      h = blockCorner (2 ^ j') Q) ∧ 0 < G.holeOuter ∧
    ∀ p ∈ G.footprint, ∃ y, y - blockCorner (2 ^ j') ((r : ℤ), (s : ℤ)) ∈ closedSquare (2 ^ j') ∧
      dist p y < 2 ^ j'

/-- **Parties of a junction resize.** Every block party of the resize of the hole at the grid
corner `(2 ^ j u, 2 ^ j v)` is the party of one of the four blocks at the corner, and so is used
by the resize.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “Resizing uses the current block labels near
its junction”, `06-geometry.tex:594`, with Lemma `lem:small-rewrite`, `05-frames.tex:203–216`. -/
theorem IsJunctionResize.uses (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph) {M : ℤ}
    {j u v : ℕ} {G : GuidePatchRewrite ι} (hG : G.IsJunctionResize party ph M j u v)
    {x : ℕ × ℕ × ℕ} (hx : party x ∈ G.parties ph) : JunctionUses j u v x := by
  obtain ⟨done, hd, hold, hnew, -, h0, hfp⟩ := hG
  rcases G.parties_subset ph h0 hx with ⟨p, hpF, hpx⟩ | ⟨p, hpF, hpx⟩
  · rw [hold] at hpx
    exact junctionUses_of_blockGuide_eq hp hph M j hd (hfp hpF) hpx
  · rw [hnew, hold] at hpx
    exact junctionUses_of_blockGuide_eq hp hph M j hd (hfp hpF) hpx

/-- **Parties of a direct repainting.** Every block party of the direct repainting of the square
`(r, s)` of side `2 ^ j'` is used by that repainting.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:500–524, 585–592`, with Lemma
`lem:small-rewrite`, `05-frames.tex:203–216`. -/
theorem IsDirectRepainting.uses (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph)
    {M : ℤ} {j' r s : ℕ} {G : GuidePatchRewrite ι} (hG : G.IsDirectRepainting party ph M j' r s)
    {x : ℕ × ℕ × ℕ} (hx : party x ∈ G.parties ph) : RepaintingUses j' r s x := by
  obtain ⟨done, hold, hnew, -, h0, hfp⟩ := hG
  rcases G.parties_subset ph h0 hx with ⟨p, hpF, hpx⟩ | ⟨p, hpF, hpx⟩
  · obtain ⟨y, hy, hpy⟩ := hfp p hpF
    rw [hold] at hpx
    exact repaintingUses_of_blockGuide_eq hp hph M j' done hy hpy hpx
  · obtain ⟨y, hy, hpy⟩ := hfp p hpF
    rw [hnew] at hpx
    exact repaintingUses_of_blockGuide_eq hp hph M j' _ hy hpy hpx

end GuidePatchRewrite

/-! ### Construction by square nets -/

/-- The patch count of a square net of mesh `ν n` over a set of radius `c n`. -/
private theorem net_count_eq {n c ν : ℝ} (hn : 0 < n) (hν : 0 < ν) :
    (2 * (c * n + ν * n) / (ν * n) + 1) ^ 2 = (2 * (c + ν) / ν + 1) ^ 2 := by
  congr 2
  field_simp

/-- A hole radius at scale `n` is at most `ε₀ n`. -/
private theorem holeRadius_le {ε₀ n t : ℝ} (hε : 0 ≤ ε₀) : holeRadius ε₀ n t ≤ ε₀ * n :=
  mul_le_mul_of_nonneg_left (min_le_left _ _) hε

/-- A hole radius is positive for positive `ε₀`, `n` and `t`. -/
private theorem holeRadius_pos {ε₀ n t : ℝ} (hε : 0 < ε₀) (hn : 0 < n) (ht : 0 < t) :
    0 < holeRadius ε₀ n t :=
  mul_pos hε (lt_min hn ht)

/-- **The rewrite of a junction resize.** For `0 < ν` and `2 ε₀ + 3 ν < 1`, the resize of the hole
at the grid corner `c = (2 ^ j u, 2 ^ j v)` of the guide uniform on `2 ^ j`-blocks, from the outer
radius `2 ε₀ min(2 ^ j, t)` to `2 ε₀ min(2 ^ j / 2, t)`, has patch data whose patches form a
square net of mesh `u = ν 2 ^ j`. The net has at most `(2 (2 ε₀ + ν) / ν + 1) ^ 2`
patches, a number independent of the scale, and their inner squares cover both outer footprints
of the hole.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “Resize one true-vertex hole at a time. The
union of its two outer footprints has diameter `O(n)` … The same compactness and fine-net argument
covers both footprints”, `06-geometry.tex:529–541`. -/
theorem exists_junctionResize (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j : ℕ)
    {done : Set (ℤ × ℤ)} (hd : {Q | InRoot M Q} ⊆ done) (u v : ℕ) {ε₀ ν t : ℝ} (hε : 0 < ε₀)
    (hν : 0 < ν) (ht : 0 < t) (hc : 2 * ε₀ + 3 * ν < 1) :
    ∃ G : GuidePatchRewrite ι, G.IsJunctionResize party ph M j u v ∧
      G.old = blockGuide (2 ^ j) (levelLabels M (oldParty party j) (newParty party j) ph done) ∧
      G.mesh = ν * 2 ^ j ∧ G.holeOuter = 2 * holeRadius ε₀ (2 ^ j) t ∧
      (G.centers.card : ℝ) ≤ (2 * (2 * ε₀ + ν) / ν + 1) ^ 2 ∧
      closedBall (blockCorner (2 ^ j) ((u : ℤ), (v : ℤ))) (2 * holeRadius ε₀ (2 ^ j / 2) t) ⊆
        ⋃ c ∈ G.centers, ball c G.mesh ∧
      closedBall (blockCorner (2 ^ j) ((u : ℤ), (v : ℤ))) (2 * holeRadius ε₀ (2 ^ j) t) ⊆
        ⋃ c ∈ G.centers, ball c G.mesh := by
  classical
  set m : ℝ := 2 ^ j with hm
  have hm0 : 0 < m := pow_pos two_pos j
  set o := blockCorner m ((u : ℤ), (v : ℤ))
  set r := holeRadius ε₀ m t
  have hr0 : 0 < r := holeRadius_pos hε hm0 ht
  have hrm : r ≤ ε₀ * m := holeRadius_le hε.le
  have hum : 0 < ν * m := mul_pos hν hm0
  have hK : closedBall o (2 * r) ⊆ closedBall o ((2 * ε₀) * m) :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨s, hcard, hcov, hnear⟩ := exists_netCover hum (by positivity) hK
  let G : GuidePatchRewrite ι :=
    { old := blockGuide m (levelLabels M (oldParty party j) (newParty party j) ph done)
      new := blockGuide m (levelLabels M (oldParty party j) (newParty party j) ph done)
      centers := s.image (blockCorner (ν * m))
      mesh := ν * m
      holes := {o}
      holeOuter := 2 * r }
  have hcov' : closedBall o (2 * r) ⊆ ⋃ c ∈ G.centers, ball c G.mesh := fun y hy => by
    obtain ⟨k, hk, hyk⟩ := hcov y hy
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)) (mem_ball.2 hyk)
  have hnew : holeRadius ε₀ (m / 2) t ≤ r := by
    have := (holeRadius_resize hε.le (by positivity : (0 : ℝ) ≤ m / 2) ht.le).1
    rwa [show 2 * (m / 2) = m by ring] at this
  refine ⟨G, ⟨done, hd, rfl, rfl, rfl, by positivity, ?_⟩, rfl, rfl, rfl, ?_,
    (closedBall_subset_closedBall (by linarith)).trans hcov', hcov'⟩
  · rintro z (hz | hz)
    · obtain ⟨c, hc', hz⟩ := mem_iUnion₂.1 hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc'
      obtain ⟨y, hy, hky⟩ := hnear k hk
      have h1 := mem_closedBall.1 hz
      have h2 := mem_closedBall.1 hy
      refine mem_ball.2 ?_
      have := dist_triangle4 z (blockCorner (ν * m) k) y o
      nlinarith
    · obtain ⟨c, hc', hz⟩ := mem_iUnion₂.1 hz
      rw [Finset.mem_singleton] at hc'
      subst hc'
      exact mem_ball.2 ((mem_closedBall.1 hz).trans_lt (by nlinarith))
  · calc ((s.image (blockCorner (ν * m))).card : ℝ) ≤ s.card := by
          exact_mod_cast Finset.card_image_le
      _ ≤ _ := hcard
      _ = _ := net_count_eq hm0 hν

/-- **The rewrite of a direct repainting.** For `0 < ν` and `2 ε₀ + 3 ν < 1`, the direct
repainting of the square `S = (r, s)` of side `n = 2 ^ j'` at a transition time of the level
`2 ^ j'`, with affected holes at the four corners of `S` and outer radius `2 ε₀ min(n, t)`, has
patch data whose patches form a square net of mesh `u = ν n`. The net has at most
`(2 (1/2 + 2 ε₀ + ν) / ν + 1) ^ 2` patches, a number independent of the scale, and their inner
squares cover the closed square `S` and the outer footprints of the affected holes.

Conditions 1–3 of Lemma `lem:small-rewrite` are not verified for this net. The source repaints
directly only for `n ≤ K₀ t`; that restriction enters the two-owner condition on the patches, not
the construction or its parties.

Source: Polynomial-PEPS manuscript (Sept 24 2026), “A fine net covers `S` and the entire affected
outer holes with a fixed number of such patches”, `06-geometry.tex:500–524`. -/
theorem exists_directRepainting (party : ℕ × ℕ × ℕ → ι) (ph : ι) (M : ℤ) (j' : ℕ)
    (done : Set (ℤ × ℤ)) (r s : ℕ) {ε₀ ν t : ℝ} (hε : 0 < ε₀) (hν : 0 < ν) (ht : 0 < t)
    (hc : 2 * ε₀ + 3 * ν < 1) :
    ∃ G : GuidePatchRewrite ι, G.IsDirectRepainting party ph M j' r s ∧
      G.old = blockGuide (2 ^ j')
        (levelLabels M (oldParty party j') (newParty party j') ph done) ∧
      (∀ Q, IsBlockCornerOf ((r : ℤ), (s : ℤ)) Q → blockCorner (2 ^ j') Q ∈ G.holes) ∧
      G.mesh = ν * 2 ^ j' ∧ G.holeOuter = 2 * holeRadius ε₀ (2 ^ j') t ∧
      (G.centers.card : ℝ) ≤ (2 * ((1 / 2 + 2 * ε₀) + ν) / ν + 1) ^ 2 ∧
      {p | p - blockCorner (2 ^ j') ((r : ℤ), (s : ℤ)) ∈ closedSquare (2 ^ j')} ∪
          (⋃ h ∈ G.holes, closedBall h G.holeOuter) ⊆ ⋃ c ∈ G.centers, ball c G.mesh := by
  classical
  set n : ℝ := 2 ^ j' with hn
  have hn0 : 0 < n := pow_pos two_pos j'
  set S : ℤ × ℤ := ((r : ℤ), (s : ℤ))
  set R := holeRadius ε₀ n t
  have hR0 : 0 < R := holeRadius_pos hε hn0 ht
  have hRn : R ≤ ε₀ * n := holeRadius_le hε.le
  have hun : 0 < ν * n := mul_pos hν hn0
  set B : Set (ℝ × ℝ) := {p | p - blockCorner n S ∈ closedSquare n}
  set corners : Finset (ℝ × ℝ) :=
    (({0, 1} : Finset ℤ) ×ˢ ({0, 1} : Finset ℤ)).image fun d =>
      blockCorner n (S.1 + d.1, S.2 + d.2)
  have hcornersB : ∀ h ∈ corners,
      h ∈ B ∧ ∃ Q : ℤ × ℤ, IsBlockCornerOf S Q ∧ h = blockCorner n Q := by
    intro h hh
    obtain ⟨⟨d1, d2⟩, hd, rfl⟩ := Finset.mem_image.1 hh
    rw [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.mem_singleton] at hd
    refine ⟨?_, ⟨(S.1 + d1, S.2 + d2), ⟨by omega, by omega⟩, rfl⟩⟩
    refine mem_closedSquare.2 ?_
    simp only [blockCorner, Prod.fst_sub, Prod.snd_sub]
    push_cast
    obtain ⟨h1 | h1, h2 | h2⟩ := hd <;> subst h1 h2 <;>
      simp only [Int.cast_zero, Int.cast_one, mul_add, mul_one, add_zero] <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  set o : ℝ × ℝ := blockCorner n S + (n / 2, n / 2)
  have hBo : ∀ y ∈ B, dist y o ≤ n / 2 := by
    intro y hy
    obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 hy
    simp only [blockCorner, Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le, abs_le]
    simp only [o, blockCorner, Prod.fst_add, Prod.snd_add]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  set K : Set (ℝ × ℝ) := B ∪ ⋃ h ∈ corners, closedBall h (2 * R)
  have hK : K ⊆ closedBall o ((1 / 2 + 2 * ε₀) * n) := by
    rintro y (hy | hy)
    · exact mem_closedBall.2 ((hBo y hy).trans (by nlinarith))
    · obtain ⟨h, hh, hy⟩ := mem_iUnion₂.1 hy
      refine mem_closedBall.2 ?_
      have := dist_triangle y h o
      have := hBo h (hcornersB h hh).1
      have := mem_closedBall.1 hy
      nlinarith
  obtain ⟨net, hcard, hcov, hnear⟩ := exists_netCover hun (by positivity) hK
  let G : GuidePatchRewrite ι :=
    { old := blockGuide n (levelLabels M (oldParty party j') (newParty party j') ph done)
      new := blockGuide n (levelLabels M (oldParty party j') (newParty party j') ph (insert S done))
      centers := net.image (blockCorner (ν * n))
      mesh := ν * n
      holes := corners
      holeOuter := 2 * R }
  -- every point of `K` is within `2 R` of a point of the closed square
  have hKB : ∀ y ∈ K, ∃ b ∈ B, dist y b ≤ 2 * R := by
    rintro y (hy | hy)
    · exact ⟨y, hy, by rw [dist_self]; positivity⟩
    · obtain ⟨h, hh, hy⟩ := mem_iUnion₂.1 hy
      exact ⟨h, (hcornersB h hh).1, mem_closedBall.1 hy⟩
  refine ⟨G, ⟨done, rfl, rfl, fun h hh => (hcornersB h hh).2, by positivity, ?_⟩, rfl, ?_, rfl,
    rfl, ?_, ?_⟩
  · rintro z (hz | hz)
    · obtain ⟨c, hc', hz⟩ := mem_iUnion₂.1 hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc'
      obtain ⟨y, hy, hky⟩ := hnear k hk
      obtain ⟨b, hb, hyb⟩ := hKB y hy
      refine ⟨b, hb, ?_⟩
      have h1 := mem_closedBall.1 hz
      have := dist_triangle4 z (blockCorner (ν * n) k) y b
      nlinarith
    · obtain ⟨h, hh, hz⟩ := mem_iUnion₂.1 hz
      refine ⟨h, (hcornersB h hh).1, (mem_closedBall.1 hz).trans_lt (by nlinarith)⟩
  · intro Q hQ
    refine Finset.mem_image.2 ⟨(Q.1 - S.1, Q.2 - S.2), ?_, by simp⟩
    obtain ⟨h1, h2⟩ := hQ
    rw [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  · calc ((net.image (blockCorner (ν * n))).card : ℝ) ≤ net.card := by
          exact_mod_cast Finset.card_image_le
      _ ≤ _ := hcard
      _ = _ := net_count_eq hn0 hν
  · intro y hy
    obtain ⟨k, hk, hyk⟩ := hcov y hy
    exact mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)) (mem_ball.2 hyk)

end Parties

/-! ### Lifetime participation -/

/-- **Bounded lifetime participation for patch rewrites.** Let the gates `Γ` of a schedule on the
hierarchy of `[0, 2 ^ k] ^ 2` belong to repaintings and junction resizes, `ev γ`, with at most `G`
gates for each, and let each gate `γ` carry the patch data `rw γ` of its event: a direct
repainting of its square or the resize of the hole at its junction, at level `j` with the root
`[0, 2 ^ k] ^ 2` of `2 ^ (k - j)` blocks per side. If the block party `x` participates in a gate
only when it is a party of the gate's patch data, then `x` participates in at most `64 G` gates.

The bound is conditional on that hypothesis `hP`. It is the conclusion of Lemma
`lem:small-rewrite`, and is not yet derived from the frame-level lemma. The large-scale
repaintings, implemented by births, deaths, exchanges
and point treatments, are not covered.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex:31–32`, the direct repaintings and the hole resizing (lines 500–541), and the
lifetime argument (lines 572–631). -/
theorem card_gates_le_of_guidePatchRewrites {ι : Type*} {party : ℕ × ℕ × ℕ → ι} {ph : ι}
    (hp : Function.Injective party) (hph : ∀ x, party x ≠ ph) {k : ℕ} {Γ : Type*}
    [Fintype Γ] (ev : Γ → DyadicSquare k ⊕ DyadicJunction k) {G : ℕ}
    (hG : ∀ e, (Finset.univ.filter fun γ => ev γ = e).card ≤ G) (rw : Γ → GuidePatchRewrite ι)
    (hrw : ∀ γ, Sum.elim
      (fun S => (rw γ).IsDirectRepainting party ph ((2 : ℤ) ^ (k - (S.1 : ℕ))) S.1 S.2.1 S.2.2)
      (fun J => (rw γ).IsJunctionResize party ph ((2 : ℤ) ^ (k - (J.1 : ℕ))) J.1 J.2.1 J.2.2)
      (ev γ))
    (x : ℕ × ℕ × ℕ) (P : Γ → Prop) [DecidablePred P]
    (hP : ∀ γ, P γ → party x ∈ (rw γ).parties ph) :
    (Finset.univ.filter P).card ≤ 64 * G := by
  refine card_gates_le_of_uses ev hG x P fun γ hγ => ?_
  have h := hrw γ
  rcases hev : ev γ with S | J <;> rw [hev] at h
  · exact h.uses hp hph (hP γ hγ)
  · exact h.uses hp hph (hP γ hγ)

end TNLean.PEPS.Approximation
