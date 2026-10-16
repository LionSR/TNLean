/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicExchangeChange

/-!
# The treated frames at the ends of a large-scale repainting

The edge construction of a square `S` of side `n > K₀ t` in the protocol of Proposition 7.1 of
the polynomial-PEPS manuscript starts from the main frame of its level, with `S` not yet
repainted, and ends with the main frame of its level with `S` repainted (`06-geometry.tex`,
lines 82–100 and 142–221). Each auxiliary sheet starts as a raw copy held by the party of the
label `C_e` across its edge (lines 183–187). This file identifies these frames with treated
frames without marks:

* `treatedFrame_congr` : a treated frame depends on its guide only through the treated guide, so
  without marks it does not depend on the homogenizing label;
* `levelFrame_eq_treatedFrame_guide` : the main frame before the repainting;
* `treatedFrame_completedGuide_eq_levelFrame` : the main frame after it;
* `treatedFrame_auxStart_eq_raw` : the fresh auxiliary sheet.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the repainting by
  levels (lines 82–100), the scales and the holes (lines 102–125), the edge construction
  (lines 142–221) and the point treatment (lines 328–339).
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-! ### Readings off the boundary of a square -/

/-- Moving a real number by a small positive amount avoids any given value. -/
theorem eventually_add_ne (x c : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), x + ε ≠ c := by
  rcases le_or_gt (c - x) 0 with h | h
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    intro he
    linarith
  · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds h)] with ε hε
    have : ε < c - x := hε
    intro he
    linarith

/-- **The diagonal displacement leaves the boundary of a square.** Every point moved by a small
positive multiple of `(1, 1)` lies in the open square `(0, n) ^ 2` or outside the closed square.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 69–80. -/
theorem eventually_mem_openSquare_or_notMem_closedSquare (n : ℝ) (p : ℝ × ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε • ((1 : ℝ), (1 : ℝ)) ∈ openSquare n ∨
      p + ε • ((1 : ℝ), (1 : ℝ)) ∉ closedSquare n := by
  filter_upwards [eventually_add_ne p.1 0, eventually_add_ne p.1 n, eventually_add_ne p.2 0,
    eventually_add_ne p.2 n] with ε h1 h2 h3 h4
  by_cases hc : p + ε • ((1 : ℝ), (1 : ℝ)) ∈ closedSquare n
  · left
    simp only [closedSquare, Set.mem_prod, Set.mem_Icc, Prod.fst_add, Prod.snd_add,
      Prod.smul_mk, smul_eq_mul, mul_one] at hc
    simp only [openSquare, Set.mem_prod, Set.mem_Ioo, Prod.fst_add, Prod.snd_add,
      Prod.smul_mk, smul_eq_mul, mul_one]
    exact ⟨⟨lt_of_le_of_ne hc.1.1 (Ne.symm h1), lt_of_le_of_ne hc.1.2 h2⟩,
      lt_of_le_of_ne hc.2.1 (Ne.symm h3), lt_of_le_of_ne hc.2.2 h4⟩
  · exact Or.inr hc

/-- An affine function of nonzero slope avoids any given value for small positive arguments. -/
theorem eventually_affine_ne (a m c : ℝ) (hm : m ≠ 0) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a + m * ε ≠ c := by
  rcases le_or_gt ((c - a) / m) 0 with h | h
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    intro he
    have : ε = (c - a) / m := by field_simp; linarith
    linarith
  · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds h)] with ε hε
    have : ε < (c - a) / m := hε
    intro he
    have : ε = (c - a) / m := by field_simp; linarith
    linarith

/-- Along the diagonal the normal coordinate of an edge avoids zero and the band width. -/
private theorem eventually_nor_ne (n a b σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), a + σ * ε ≠ 0 ∧ a + σ * ε ≠ bandWidth n (b + ε) := by
  have h0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have h1 : σ - 1 / 1000 ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have h2 : σ + 1 / 1000 ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  filter_upwards [eventually_affine_ne a σ 0 h0, eventually_affine_ne (a - b / 1000) _ 0 h1,
    eventually_affine_ne (a - (n - b) / 1000) _ 0 h2] with ε e0 e1 e2
  refine ⟨e0, fun he => ?_⟩
  rcases min_choice (b + ε) (n - (b + ε)) with hm | hm <;> rw [bandWidth, hm] at he
  · exact e1 (by linarith)
  · exact e2 (by linarith)

/-- **The diagonal displacement leaves the interface curves.** Every point moved by a small
positive multiple of `(1, 1)` lies off the curves `x = 0` and `x = 1` of the band of an edge.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 69–80 and 161–168. -/
theorem RepaintingBaseline.eventually_notMem_edgeInterface {ι : Type*}
    (R : RepaintingBaseline ι) (e : SquareEdge) (p : ℝ × ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε • ((1 : ℝ), (1 : ℝ)) ∉ R.edgeInterface e := by
  have key : ∀ᶠ ε in 𝓝[>] (0 : ℝ), e.nor R.n (p + ε • ((1 : ℝ), (1 : ℝ))) ≠ 0 ∧
      e.nor R.n (p + ε • ((1 : ℝ), (1 : ℝ))) ≠
        bandWidth R.n (e.par (p + ε • ((1 : ℝ), (1 : ℝ)))) := by
    cases e
    · simpa [SquareEdge.nor, SquareEdge.par] using eventually_nor_ne R.n p.2 p.1 1 (Or.inl rfl)
    · simpa [SquareEdge.nor, SquareEdge.par, sub_add_eq_sub_sub, ← sub_eq_add_neg] using
        eventually_nor_ne R.n (R.n - p.1) p.2 (-1) (Or.inr rfl)
    · simpa [SquareEdge.nor, SquareEdge.par, sub_add_eq_sub_sub, ← sub_eq_add_neg] using
        eventually_nor_ne R.n (R.n - p.2) p.1 (-1) (Or.inr rfl)
    · simpa [SquareEdge.nor, SquareEdge.par] using eventually_nor_ne R.n p.1 p.2 1 (Or.inl rfl)
  filter_upwards [key] with ε ⟨h0, h1⟩
  rintro ⟨hb, hx⟩
  obtain ⟨s1, s2, -, -⟩ := mem_edgeBand_iff_bandCoord.1 hb
  have hw := bandWidth_pos s1 s2
  rcases hx with hx | hx
  · rw [bandCoord, div_eq_zero_iff] at hx
    exact hx.elim h0 hw.ne'
  · rw [bandCoord, div_eq_one_iff_eq hw.ne'] at hx
    exact h1 hx

/-- A reading of a labelling reads every labelling that agrees with it eventually along the
displacement. -/
theorem IsDisplacedReading.congr_eventually {X κ : Type*} [AddCommGroup X] [Module ℝ X]
    {g G G' : X → κ} {v : X} (hg : IsDisplacedReading g G v)
    (h : ∀ p, ∀ᶠ ε in 𝓝[>] (0 : ℝ), G (p + ε • v) = G' (p + ε • v)) :
    IsDisplacedReading g G' v := fun p =>
  ((hg p).and (h p)).mono fun _ hε => hε.1.trans hε.2

/-- A block index fixes the point in the closed block. -/
theorem sub_blockCorner_mem_closedSquare {n : ℝ} (hn : 0 < n) {x : ℝ × ℝ} {S : ℤ × ℤ}
    (h : blockIndex n x = S) : x - blockCorner n S ∈ closedSquare n := by
  have h1 : ⌊x.1 / n⌋ = S.1 := congrArg Prod.fst h
  have h2 : ⌊x.2 / n⌋ = S.2 := congrArg Prod.snd h
  rw [Int.floor_eq_iff] at h1 h2
  rw [le_div_iff₀ hn, div_lt_iff₀ hn] at h1 h2
  simp only [closedSquare, Set.mem_prod, Set.mem_Icc, Prod.fst_sub, Prod.snd_sub, blockCorner]
  refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

variable {k : ℕ}

/-! ### Treated frames of equal treated guides -/

variable {L q : ℕ} {Ω : StateSpace L q} {B₀ C c : ℝ}
  (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
  (R : RepaintedSquare k)

/-- **A treated frame depends only on its treated guide and marks.** -/
theorem treatedFrame_congr {ε₀ t : ℝ}
    {hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L} {M : Finset (ℤ × ℤ)}
    {L₀ L₀' : GuideLabel} {g g' : ℝ × ℝ → GuideLabel}
    (h : treatedGuide R.1.1 R.1.index t M L₀ g = treatedGuide R.1.1 R.1.index t M L₀' g') :
    treatedFrame (q := q) P rank R hr M L₀ g = treatedFrame P rank R hr M L₀' g' := by
  change (fun f : ℝ × ℝ → GuideLabel =>
      if h : ((treatedVertices k R.1.1 t M f : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise
          fun z z' => Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer then
        guideFrame (cellCenterPos L) q f (labelParty R) guidePlaceholder rank
          (treatedVertices k R.1.1 t M f) (suppliedPatch P _ hr) h
      else Frame.raw fun _ => .inl R.1) (treatedGuide R.1.1 R.1.index t M L₀ g) =
    (fun f : ℝ × ℝ → GuideLabel =>
      if h : ((treatedVertices k R.1.1 t M f : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise
          fun z z' => Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer then
        guideFrame (cellCenterPos L) q f (labelParty R) guidePlaceholder rank
          (treatedVertices k R.1.1 t M f) (suppliedPatch P _ hr) h
      else Frame.raw fun _ => .inl R.1) (treatedGuide R.1.1 R.1.index t M L₀' g')
  rw [h]

/-- Without marks, the treated guide is the sampled guide placed on the square. -/
theorem treatedGuide_empty (j : ℕ) (S : ℤ × ℤ) (t : ℝ) (L₀ : GuideLabel)
    (g : ℝ × ℝ → GuideLabel) :
    treatedGuide j S t ∅ L₀ g = sampleGuide (shiftGuide (blockCorner ((2 : ℝ) ^ j) S) g) := by
  unfold treatedGuide homogenize
  congr 1
  funext p
  simp

/-- **Without marks the homogenizing label does not matter.** -/
theorem treatedFrame_empty_congr {ε₀ t : ℝ}
    {hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L} (L₀ L₀' : GuideLabel)
    (g : ℝ × ℝ → GuideLabel) :
    treatedFrame (q := q) P rank R hr ∅ L₀ g = treatedFrame P rank R hr ∅ L₀' g :=
  treatedFrame_congr P rank R (by rw [treatedGuide_empty, treatedGuide_empty])

/-! ### The main frame at the ends of the repainting -/

/-- The repainting baseline of the square `R` at a stage `done` of its level. -/
abbrev repaintBaseline (R : RepaintedSquare k) (done : Set (ℤ × ℤ)) :
    RepaintingBaseline GuideLabel :=
  blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
    (protocolLevelLabels k R.1.1 done) R.1.index (newParty Sum.inl R.1.1 R.1.index)

/-- **The main frame before the repainting.** At the constants of the protocol, for a square `R`
of side `n = 2 ^ j > K₀ t`, the main frame of level `j` at the stage `done`, with holes of radius
`h_n = ε₀ t`, is the frame of the starting guide of the repainting of `R`, treated at no mark.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–125 and 142–160. -/
theorem levelFrame_eq_treatedFrame_guide {K₀ ε₀ ν a D : ℝ}
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hkL : L ≤ 2 ^ k)
    (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ)) (R₀ : RepaintedSquare k)
    (done : Set (ℤ × ℤ)) (L₀ : GuideLabel) :
    levelFrame (q := q) P rank R₀ R.1.1 done
        (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) (D * Real.log L))
        (hc.holeRadius_bounds hL (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)) =
      treatedFrame P rank R (hc.treatedRadius_bounds hL) ∅ L₀ (repaintBaseline R done).guide := by
  have hr := hc.treatedRadius_bounds hL
  have hρ := hc.holeRadius_bounds hL (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
  set t := D * Real.log L with ht_def
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < t := mul_pos hc.D_pos hℓ
  have htn : t ≤ (2 : ℝ) ^ (R.1.1 : ℕ) := by nlinarith [hc.twenty_le_K₀]
  have hg : treatedGuide R.1.1 R.1.index t ∅ L₀ (repaintBaseline R done).guide =
      levelGuide k R.1.1 done := by
    rw [treatedGuide_empty]
    congr 1
    funext p
    have hguide : ∀ x, (repaintBaseline R done).guide x = blockGuide ((2 : ℝ) ^ (R.1.1 : ℕ))
        (protocolLevelLabels k R.1.1 done) (x + blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) R.1.index) :=
      fun _ => rfl
    rw [shiftGuide, hguide, sub_add_cancel]
  obtain ⟨-, hmem, hd, hF⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done (Or.inl rfl)
    ∅ L₀
  have hV : treatedVertices k R.1.1 t ∅ (treatedGuide R.1.1 R.1.index t ∅ L₀
      (repaintBaseline R done).guide) = levelVertices k R.1.1 done :=
    Finset.ext fun z => by rw [hmem, mem_levelVertices, hg]
  have hpatch : ∀ z, suppliedPatch P (fun _ => ε₀ * t) hr z =
      suppliedPatch P (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) t) hρ z := fun z =>
    suppliedPatch_congr P hr hρ (holeRadius_of_le htn).symm
  have hd' : ((levelVertices k R.1.1 done : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise
      fun z z' => Disjoint
        (suppliedPatch P (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) t) hρ z).outer
        (suppliedPatch P (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) t) hρ z').outer := by
    intro z hz z' hz' hne
    rw [← hpatch, ← hpatch]
    exact hd (by rw [Finset.mem_coe, hV]; exact hz) (by rw [Finset.mem_coe, hV]; exact hz') hne
  rw [hF, levelFrame_eq P rank R₀ hd']
  symm
  calc _ = guideFrame (cellCenterPos L) q (levelGuide k R.1.1 done) (labelParty R)
        guidePlaceholder rank (levelVertices k R.1.1 done)
        (suppliedPatch P (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) t) hρ) hd' :=
        guideFrame_congr_guide hg hV fun z _ => hpatch z
    _ = _ := guideFrame_levelLabels_labelParty_eq hkL R.2 (isDisplacedReading_levelGuide _ _) R
        R₀ rank (fun z hz => mem_levelVertices.1 hz) _ hd'

/-- **The completed guide is read as the level guide with the square repainted.** Once all four
edges of `R` are completed, the guide of the main sheet, placed on `R`, has the same reading as
the block guide of the level with `R` repainted: the two agree off the boundary of `R`, which the
displacement leaves at once.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 69–100 and 215–221. -/
theorem treatedGuide_completedGuide (done : Set (ℤ × ℤ)) {E : List SquareEdge}
    (hE : ∀ e, e ∈ E) (t : ℝ) (L₀ : GuideLabel) :
    treatedGuide R.1.1 R.1.index t ∅ L₀ ((repaintBaseline R done).completedGuide E) =
      levelGuide k R.1.1 (insert R.1.index done) := by
  classical
  set n : ℝ := (2 : ℝ) ^ (R.1.1 : ℕ) with hn_def
  set d := blockCorner n R.1.index with hd_def
  have hn : 0 < n := by positivity
  rw [treatedGuide_empty]
  symm
  refine IsDisplacedReading.eq_sampleGuide ((isDisplacedReading_levelGuide (k := k) R.1.1
    (insert R.1.index done)).congr_eventually fun p => ?_)
  filter_upwards [eventually_mem_openSquare_or_notMem_closedSquare n (p - d)] with ε hε
  have hx : p + ε • ((1 : ℝ), (1 : ℝ)) - d = p - d + ε • ((1 : ℝ), (1 : ℝ)) := by abel
  have hx' : p + ε • ((1 : ℝ), (1 : ℝ)) = (p - d + ε • ((1 : ℝ), (1 : ℝ))) + d := by abel
  change blockGuide n _ _ = (repaintBaseline R done).completedGuide E (p + ε • _ - d)
  rw [hx]
  rcases hε with hε | hε
  · rw [(repaintBaseline R done).completedGuide_of_mem_openSquare hE hε, blockGuide, hx',
      blockIndex_of_mem_openSquare hn _ hε]
    simp [protocolLevelLabels, levelLabels, R.1.inRoot_index, repaintBaseline, blockBaseline]
  · rw [(repaintBaseline R done).completedGuide_of_notMem_closedSquare E hε]
    have hguide : ∀ x, (repaintBaseline R done).guide x =
        blockGuide n (protocolLevelLabels k R.1.1 done) (x + d) := fun _ => rfl
    rw [hguide, ← hx']
    have hne : blockIndex n (p + ε • ((1 : ℝ), (1 : ℝ))) ≠ R.1.index := fun h => hε (by
      rw [← hx]; exact sub_blockCorner_mem_closedSquare hn h)
    simp only [blockGuide, protocolLevelLabels]
    exact levelLabels_insert_of_ne _ _ _ _ hne

/-- **The main frame after the repainting.** At the constants of the protocol, for a square `R`
of side `n = 2 ^ j > K₀ t`, the frame of the guide with all four edges completed, treated at no
mark, is the main frame of level `j` with `R` repainted as well, with holes of radius
`h_n = ε₀ t`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–125 and 215–221. -/
theorem treatedFrame_completedGuide_eq_levelFrame {K₀ ε₀ ν a D : ℝ}
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hkL : L ≤ 2 ^ k)
    (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ)) (R₀ : RepaintedSquare k)
    (done : Set (ℤ × ℤ)) {E : List SquareEdge} (hE : ∀ e, e ∈ E)
    (L₀ : GuideLabel) :
    treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL) ∅ L₀
        ((repaintBaseline R done).completedGuide E) =
      levelFrame P rank R₀ R.1.1 (insert R.1.index done)
        (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) (D * Real.log L))
        (hc.holeRadius_bounds hL (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)) := by
  have hr := hc.treatedRadius_bounds hL
  have hρ := hc.holeRadius_bounds hL (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
  set t := D * Real.log L with ht_def
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < t := mul_pos hc.D_pos hℓ
  have htn : t ≤ (2 : ℝ) ^ (R.1.1 : ℕ) := by nlinarith [hc.twenty_le_K₀]
  have hg := treatedGuide_completedGuide R done hE t L₀
  obtain ⟨-, hmem, hd, hF⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done
    (Or.inr (Or.inr (Or.inl ⟨E, rfl⟩))) ∅ L₀
  have hV : treatedVertices k R.1.1 t ∅ (treatedGuide R.1.1 R.1.index t ∅ L₀
      ((repaintBaseline R done).completedGuide E)) =
        levelVertices k R.1.1 (insert R.1.index done) :=
    Finset.ext fun z => by rw [hmem, mem_levelVertices, hg]
  have hpatch : ∀ z, suppliedPatch P (fun _ => ε₀ * t) hr z =
      suppliedPatch P (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) t) hρ z := fun z =>
    suppliedPatch_congr P hr hρ (holeRadius_of_le htn).symm
  have hd' : ((levelVertices k R.1.1 (insert R.1.index done) : Finset (ℝ × ℝ)) :
      Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint
        (suppliedPatch P (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) t) hρ z).outer
        (suppliedPatch P (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) t) hρ z').outer := by
    intro z hz z' hz' hne
    rw [← hpatch, ← hpatch]
    exact hd (by rw [Finset.mem_coe, hV]; exact hz) (by rw [Finset.mem_coe, hV]; exact hz') hne
  rw [hF, levelFrame_eq P rank R₀ hd']
  calc _ = guideFrame (cellCenterPos L) q (levelGuide k R.1.1 (insert R.1.index done))
        (labelParty R) guidePlaceholder rank (levelVertices k R.1.1 (insert R.1.index done))
        (suppliedPatch P (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) t) hρ) hd' :=
        guideFrame_congr_guide hg hV fun z _ => hpatch z
    _ = _ := guideFrame_levelLabels_labelParty_eq hkL R.2 (isDisplacedReading_levelGuide _ _) R
        R₀ rank (fun z hz => mem_levelVertices.1 hz) _ hd'

/-- **The start of an edge construction.** At the constants of the protocol, the frame of the
guide left by the central birth and the edges of `E`, treated at no mark, is the frame of the main
guide with the starting word `C_e | A | B` on the band of `e ∉ E`: the two guides agree off the
interface curves of the band, which the displacement leaves at once, so their readings agree.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 62–80 and 160–168. -/
theorem treatedFrame_edgeStart {K₀ ε₀ ν a D : ℝ} (hc : IsProtocolConstants K₀ ε₀ ν a D B₀)
    (hL : 2 ≤ L) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) {E : List SquareEdge} {e : SquareEdge} (he : e ∉ E)
    (L₀ L₀' : GuideLabel) :
    treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL) ∅ L₀
        ((repaintBaseline R done).completedGuide E) =
      treatedFrame P rank R (hc.treatedRadius_bounds hL) ∅ L₀'
        ((repaintBaseline R done).mainGuide E e (edgeStartWord (repaintBaseline R done).oldLabel (repaintBaseline R done).finalLabel
          ((repaintBaseline R done).nbrLabel e))) := by
  have hr := hc.treatedRadius_bounds hL
  classical
  set d := blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) R.1.index
  obtain ⟨hf, -⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done
    (Or.inr (Or.inr (Or.inl ⟨E, rfl⟩))) ∅ L₀
  refine treatedFrame_congr P rank R ((hf.congr_eventually fun p => ?_).eq_sampleGuide)
  filter_upwards [(repaintBaseline R done).eventually_notMem_edgeInterface e (p - d)] with ε hε
  have hx : p - d + ε • ((1 : ℝ), (1 : ℝ)) = p + ε • ((1 : ℝ), (1 : ℝ)) - d := by abel
  rw [hx] at hε
  simp only [homogenize, Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty,
    Set.mem_empty_iff_false, ite_false, shiftGuide]
  exact (repaintBaseline R done).completedGuide_eq_mainGuide_start he hε

/-! ### The fresh auxiliary sheet -/

/-- **The fresh auxiliary sheet.** The auxiliary sheet of an edge `e` starts with the guide
uniform at the label `C_e` across `e`; its frame, treated at no mark, has no hole and every site
owned by the party of `C_e`, so it is the raw copy held by that party.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–187. -/
theorem treatedFrame_auxStart_eq_raw {ε₀ t : ℝ}
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L) (done : Set (ℤ × ℤ))
    (e : SquareEdge) (L₀ : GuideLabel) :
    treatedFrame (q := q) P rank R hr ∅ L₀
        ((repaintBaseline R done).auxGuide e (bandWord ((repaintBaseline R done).nbrLabel e) [])) =
      Frame.raw fun _ => labelParty R ((repaintBaseline R done).nbrLabel e) := by
  classical
  set C₀ := (repaintBaseline R done).nbrLabel e
  have haux : (repaintBaseline R done).auxGuide e (bandWord C₀ []) = fun _ => C₀ := by
    funext p
    by_cases hb : p ∈ edgeBand (repaintBaseline R done).n e (-8) 2 <;>
      simp [RepaintingBaseline.auxGuide, bandUpdate, bandWord, hb, C₀]
  have hg : treatedGuide R.1.1 R.1.index t ∅ L₀
      ((repaintBaseline R done).auxGuide e (bandWord C₀ [])) = fun _ => C₀ := by
    rw [haux, treatedGuide_empty]
    exact ((isDisplacedReading_const C₀ ((1 : ℝ), (1 : ℝ))).eq_sampleGuide).symm
  have hV : treatedVertices k R.1.1 t ∅ (treatedGuide R.1.1 R.1.index t ∅ L₀
      ((repaintBaseline R done).auxGuide e (bandWord C₀ []))) = ∅ := by
    rw [hg]
    refine Finset.filter_false_of_mem fun z _ => not_isTrueVertex_of_subset_pair (P := C₀)
      (Q := C₀) ?_
    exact incidentLabels_subset univ_mem fun _ _ => by simp
  have hd : (((treatedVertices k R.1.1 t ∅ (treatedGuide R.1.1 R.1.index t ∅ L₀
      ((repaintBaseline R done).auxGuide e (bandWord C₀ [])))) : Finset (ℝ × ℝ)) :
      Set (ℝ × ℝ)).Pairwise fun z z' =>
        Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer := by
    rw [hV, Finset.coe_empty]
    exact Set.pairwise_empty _
  rw [treatedFrame_eq P rank R hd,
    guideFrame_congr_guide (g' := fun _ => C₀) (V' := ∅) (patch' := suppliedPatch P _ hr)
      (hV' := by rw [Finset.coe_empty]; exact Set.pairwise_empty _) hg hV fun _ _ => rfl]
  unfold guideFrame Frame.raw
  congr 1
  simp

end TNLean.PEPS.Approximation
