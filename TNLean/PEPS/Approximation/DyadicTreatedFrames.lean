/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLevelEvents

/-!
# The frames of a large-scale repainting and its point treatments

During the large-scale repainting of a square `S` of side `n > K₀ t` in the protocol of
Proposition 7.1 of the polynomial-PEPS manuscript, every sheet carries the encoded frame of an
unmodified guide of the repainting, placed on `S` and homogenized to a label `L₀` on the open
squares of radius `t` about a finite set of marked grid corners (`06-geometry.tex`, lines
328–339). Its labels are read at the sites after one generic displacement, its holes sit at its
true vertices with the radius `h_n = ε₀ t` and the patches supplied by Proposition 4.1, and its
raw owners and tags are read through the party map of the repainting.

* `treatedGuide`, `treatedFrame` : this guide and its frame;
* `exists_pointTreatment_hasSourceBoundedChange` : adding or removing one marked corner of `S` is
  a bounded change of the frame whose participants the repainting uses, with the bounds of the
  small-patch rewrites, for every mesh ratio below a threshold depending only on `ε₀`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the scales and the holes
  (lines 102–125), the point treatment (lines 328–355), the point homogenization and removal
  (lines 481–505), and the parties of a repainting (lines 585–596).
-/

noncomputable section

open Set Metric

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k : ℕ}

/-- **The guide of a treated sheet.** The unmodified guide `g` of the repainting of the block `S`
of side `2 ^ j`, placed on `S`, homogenized to `L₀` on the open squares of radius `t` about the
grid corners of `M`, and read after the displacement `(1, 1)`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 69–80 and 328–339. -/
abbrev treatedGuide (j : ℕ) (S : ℤ × ℤ) (t : ℝ) (M : Finset (ℤ × ℤ)) (L₀ : GuideLabel)
    (g : ℝ × ℝ → GuideLabel) : ℝ × ℝ → GuideLabel :=
  sampleGuide (homogenize (⋃ Q ∈ M, ball (blockCorner ((2 : ℝ) ^ j) Q) t) L₀
    (shiftGuide (blockCorner ((2 : ℝ) ^ j) S) g))

/-- The true vertices of a treated guide: grid corners of the closed root square and points of
the rims of the treated squares. -/
abbrev treatedVertices (k j : ℕ) (t : ℝ) (M : Finset (ℤ × ℤ)) (f : ℝ × ℝ → GuideLabel) :
    Finset (ℝ × ℝ) :=
  treatedTrueVertices ((2 : ℝ) ^ j) t ((2 : ℤ) ^ (k - j)) M f

/-- **A bounded change of one frame with bounded pair sources.** An original circuit from the
registers of `F` to those of `F'` that is a bounded change from the reference vector of `F` to that
of `F'`, with at most `rs` pair sources in each monomial.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 572–583. -/
def HasFrameChange {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q]
    {pos : ι → ℝ × ℝ} {Party : Type} (Ω : EuclideanSpace ℂ (ι → Fin q))
    (F F' : Frame pos q Party) (S : Set Party) (r K rs : ℕ) (ε : ℝ) : Prop :=
  ∃ w : OriginalCircuit F.regs F'.regs,
    w.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω) ∧ w.IsSourceBounded rs

variable {L q : ℕ} {Ω : StateSpace L q} {B₀ C c : ℝ}

open Classical in
/-- **The frame of a treated sheet.** The encoded frame of the treated guide, read through the
party map of the repainting `R`, with a hole of radius `ε₀ t` and the supplied patch at every true
vertex. When the outer squares of these holes are not disjoint the frame is not defined by the
source, and a raw frame stands in for it.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 102–125 and 328–355. -/
def treatedFrame (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L)
    (rank : GuideLabel → ℕ) (R : RepaintedSquare k) {ε₀ t : ℝ}
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L) (M : Finset (ℤ × ℤ))
    (L₀ : GuideLabel) (g : ℝ × ℝ → GuideLabel) : Frame (cellCenterPos L) q (ProtocolParty k) :=
  if h : ((treatedVertices k R.1.1 t M (treatedGuide R.1.1 R.1.index t M L₀ g) :
      Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer then
    guideFrame (cellCenterPos L) q (treatedGuide R.1.1 R.1.index t M L₀ g) (labelParty R)
      guidePlaceholder rank (treatedVertices k R.1.1 t M (treatedGuide R.1.1 R.1.index t M L₀ g))
      (suppliedPatch P _ hr) h
  else Frame.raw fun _ => .inl R.1

variable (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
  (R : RepaintedSquare k)

theorem treatedFrame_eq {ε₀ t : ℝ} {hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L}
    {M : Finset (ℤ × ℤ)} {L₀ : GuideLabel} {g : ℝ × ℝ → GuideLabel}
    (h : ((treatedVertices k R.1.1 t M (treatedGuide R.1.1 R.1.index t M L₀ g) :
      Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer) :
    treatedFrame (q := q) P rank R hr M L₀ g =
      guideFrame (cellCenterPos L) q (treatedGuide R.1.1 R.1.index t M L₀ g) (labelParty R)
        guidePlaceholder rank (treatedVertices k R.1.1 t M (treatedGuide R.1.1 R.1.index t M L₀ g))
        (suppliedPatch P _ hr) h :=
  dite_eq_left h

/-- The block of a square of the hierarchy lies in the root square of its level. -/
theorem DyadicSquare.inRoot_index (S : DyadicSquare k) :
    InRoot ((2 : ℤ) ^ (k - (S.1 : ℕ))) S.index := by
  have h1 := S.2.1.isLt
  have h2 := S.2.2.isLt
  have e : ((2 ^ (k - (S.1 : ℕ)) : ℕ) : ℤ) = (2 : ℤ) ^ (k - (S.1 : ℕ)) := by push_cast; rfl
  simp only [InRoot, DyadicSquare.index]
  omega

/-- A large-scale patch bound exceeds `53` when `ν < 1/3`. -/
theorem fiftyThree_le_protocolPatchBound {ε₀ ν : ℝ} (hε : 0 ≤ ε₀) (hν : 0 < ν)
    (hν3 : ν < 1 / 3) : 53 ≤ protocolPatchBound ε₀ ν := by
  have h4 : (12 : ℝ) < (4 + 8 * ε₀ + 2 * ν) / ν := by
    rw [lt_div_iff₀ hν]; nlinarith
  have hsq : (53 : ℝ) ≤ ((4 + 8 * ε₀ + 2 * ν) / ν + 1) ^ 2 := by nlinarith
  have := (Nat.le_ceil (((4 + 8 * ε₀ + 2 * ν) / ν + 1) ^ 2))
  have h : (53 : ℝ) ≤ (⌈((4 + 8 * ε₀ + 2 * ν) / ν + 1) ^ 2⌉₊ : ℝ) := hsq.trans this
  have h' : 53 ≤ ⌈((4 + 8 * ε₀ + 2 * ν) / ν + 1) ^ 2⌉₊ := by exact_mod_cast h
  exact h'.trans (le_max_right _ _)

/-- **A point treatment as a change of a sheet.** Fix `0 < ε₀ ≤ 1/16`. There is a threshold
`ν' > 0` such that for every mesh ratio `0 < ν ≤ ν'` and constants of the protocol the following
holds. In the repainting of the square `R` of side `n = 2 ^ j > K₀ t`, `t = D log L`, let `g` be
an unmodified guide of the repainting, `L₀` the final label or a label of a block next to `R`,
and `M`, `M'` sets of grid corners that differ at most at one corner `Q₀` of `R`. Then passing
from the frame of the treated sheet with the marks `M` to that with the marks `M'` is a bounded
change whose participants the repainting uses, with the bounds of the small-patch rewrites with
`b = protocolPatchBound ε₀ ν` patches.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339, 481–505, 559–570 and 572–596. -/
theorem exists_pointTreatment_hasSourceBoundedChange {ε₀ : ℝ} (hε : 0 < ε₀)
    (hε₀ : ε₀ ≤ 1 / 16) :
    ∃ ν' > 0, ∀ ν : ℝ, 0 < ν → ν ≤ ν' → ∀ {k : ℕ} {K₀ a D B₀ : ℝ},
      IsProtocolConstants K₀ ε₀ ν a D B₀ → ∀ {L q : ℕ} [NeZero q] {Ω : StateSpace L q} {C c : ℝ},
      2 ≤ L → ‖Ω‖ = 1 →
      ∀ (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
        (R : RepaintedSquare k), K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ) →
      ∀ (done : Set (ℤ × ℤ)) {g : ℝ × ℝ → GuideLabel},
        (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
          (protocolLevelLabels k R.1.1 done) R.1.index
          (newParty Sum.inl R.1.1 R.1.index)).IsUnmodifiedGuide g →
      ∀ {M M' : Finset (ℤ × ℤ)} (Q₀ : ℤ × ℤ), IsBlockCornerOf R.1.index Q₀ →
        (∀ Q, Q ≠ Q₀ → (Q ∈ M ↔ Q ∈ M')) → ∀ L₀ : GuideLabel,
        (L₀ = newParty Sum.inl R.1.1 R.1.index ∨
          ∃ R' ∈ blockWindow 1, L₀ = protocolLevelLabels k R.1.1 done (R' + R.1.index)) →
      ∀ (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧
          ε₀ * (D * Real.log L) ≤ B₀ * Real.log L) {C' c' : ℕ}, C ≤ C' → 1 ≤ C' → c ≤ c' →
      HasFrameChange Ω (treatedFrame (q := q) P rank R hr M L₀ g)
        (treatedFrame (q := q) P rank R hr M' L₀ g) {p | EventUses (.inl R.1) p}
        (2 * protocolPatchBound ε₀ ν) (rewriteGateBound C' c' (protocolPatchBound ε₀ ν) L)
        (2 * protocolPatchBound ε₀ ν) ((2 * protocolPatchBound ε₀ ν + 1) * ((L : ℝ) ^ 20)⁻¹) := by
  obtain ⟨ν', hν', H⟩ := exists_pointTreatment_step_supplied hε hε₀
  refine ⟨ν', hν', fun ν hν hνν' {k K₀ a D B₀} hc {L q} _ {Ω C c} hL hΩ P rank R hlarge done g hg
    {M M'} Q₀ hQ₀ hM L₀ hL₀ hr {C' c'} hC hC' hcc => ?_⟩
  classical
  set n : ℝ := (2 : ℝ) ^ (R.1.1 : ℕ) with hn_def
  set t := D * Real.log L with ht_def
  have hn : 0 < n := by positivity
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < t := mul_pos hc.D_pos hℓ
  have htn : 20 * t < n := by nlinarith [hc.twenty_le_K₀]
  have hε4 := hc.lt_one_div_four_thousand
  have hgr : IsRayConstant (shiftGuide (blockCorner n R.1.index) g) :=
    (hg.isRayConstant _ (by
      change IsRayConstant fun p => blockGuide n (protocolLevelLabels k R.1.1 done)
        (p + blockCorner n R.1.index)
      exact (isRayConstant_blockGuide _ _).comp_add _)).shiftGuide _
  have hf : ∀ M₀ : Finset (ℤ × ℤ), IsDisplacedReading (treatedGuide R.1.1 R.1.index t M₀ L₀ g)
      (homogenize (⋃ Q ∈ M₀, ball (blockCorner n Q) t) L₀ (shiftGuide (blockCorner n R.1.index) g))
      ((1 : ℝ), (1 : ℝ)) := fun M₀ => (hgr.homogenize M₀ n t L₀).isDisplacedReading_sampleGuide
  have hout : ∀ Q, ¬InRoot ((2 : ℤ) ^ (k - (R.1.1 : ℕ))) Q →
      protocolLevelLabels k R.1.1 done Q = guidePlaceholder := fun Q hQ => by
    simp only [protocolLevelLabels, levelLabels, hQ, ite_false]
  have hmem : ∀ M₀ : Finset (ℤ × ℤ), ∀ z, z ∈ treatedVertices k R.1.1 t M₀
      (treatedGuide R.1.1 R.1.index t M₀ L₀ g) ↔
      IsTrueVertex (treatedGuide R.1.1 R.1.index t M₀ L₀ g) z := fun M₀ z =>
    mem_treatedTrueVertices hn (by linarith) hout R.1.inRoot_index hg M₀ L₀ (hf M₀)
  have hdisj : ∀ M₀ : Finset (ℤ × ℤ), ((treatedVertices k R.1.1 t M₀
      (treatedGuide R.1.1 R.1.index t M₀ L₀ g) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise
      fun z z' => Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer := by
    intro M₀ z hz z' hz' hne
    have h := (homogenize_reading_outerHoles_disjoint hn ht htn hε4 hg M₀ L₀
      ((1 : ℝ), (1 : ℝ))).2 _ (hf M₀) z z' ((hmem M₀ z).1 hz) ((hmem M₀ z').1 hz') hne
    refine disjoint_outer_of_disjoint_closedBall ?_
    simp only [suppliedPatch_center, suppliedPatch_scale]
    rwa [← mul_assoc]
  rw [treatedFrame_eq P rank R (hdisj M), treatedFrame_eq P rank R (hdisj M')]
  have hu : ∀ _ : ℝ × ℝ, 0 < ν * t / 2 ∧ ν * t / 2 ≤ B₀ * Real.log L := by
    have hD : D ≤ B₀ := by nlinarith [hc.B₀_ge, hc.twenty_le_K₀, hc.D_pos]
    have hν1 := hc.ν_lt_one
    refine fun _ => ⟨by positivity, ?_⟩
    have : t ≤ B₀ * Real.log L := mul_le_mul_of_nonneg_right hD hℓ.le
    nlinarith
  have hb : (2 * (2 + 4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (protocolPatchBound ε₀ ν : ℝ) :=
    sq_le_protocolPatchBound (by positivity) (le_of_eq (by ring_nf))
  have hb53 := fiftyThree_le_protocolPatchBound hε.le hν (by linarith [hc.ν_small, hc.ε₀_pos])
  obtain ⟨w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H ν hν hνν' isGenericDisplacement_one_one hn ht
    (by linarith) hg Q₀ hQ₀ hM L₀ hL₀ (hf M) (hf M') (labelParty R) guidePlaceholder rank
    (fun z hz => (hmem M z).1 hz) (fun z hz => (hmem M' z).1 hz)
    (fun z _ hz => (hmem M z).2 hz) (fun z _ hz => (hmem M' z).2 hz)
    (fun z hz => by
      rw [hmem M, hmem M']
      exact isTrueVertex_reading_homogenize_iff hM L₀ _ (hf M) (hf M') (by linarith))
    P hΩ hL hr hu (hdisj M) (hdisj M') hC hC' hcc hb hb53
  exact ⟨w, ⟨h₁, fun γ => (h₂ γ).trans (coe_blockParties_subset_eventUses R done), h₃, h₄, h₅⟩,
    h₆⟩

/-- **The treated frame is the frame of its sampled guide.** At the constants of the protocol, for
a square `R` of side `n = 2 ^ j > K₀ t` and an unmodified guide `g` of its repainting, the treated
guide is a reading of the homogenized guide, its true vertices are the points of
`treatedVertices`, the outer squares of their holes are disjoint, and the treated frame is the
encoded frame of the treated guide.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 69–80, 102–125 and 328–355. -/
theorem treatedFrame_spec {K₀ ε₀ ν a D : ℝ} (hc : IsProtocolConstants K₀ ε₀ ν a D B₀)
    (hL : 2 ≤ L) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) {g : ℝ × ℝ → GuideLabel}
    (hg : (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
      (protocolLevelLabels k R.1.1 done) R.1.index
      (newParty Sum.inl R.1.1 R.1.index)).IsUnmodifiedGuide g)
    (M : Finset (ℤ × ℤ)) (L₀ : GuideLabel)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L) :
    IsDisplacedReading (treatedGuide R.1.1 R.1.index (D * Real.log L) M L₀ g)
      (homogenize (⋃ Q ∈ M, ball (blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) Q) (D * Real.log L)) L₀
        (shiftGuide (blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) R.1.index) g)) ((1 : ℝ), (1 : ℝ)) ∧
    (∀ z, z ∈ treatedVertices k R.1.1 (D * Real.log L) M
        (treatedGuide R.1.1 R.1.index (D * Real.log L) M L₀ g) ↔
      IsTrueVertex (treatedGuide R.1.1 R.1.index (D * Real.log L) M L₀ g) z) ∧
    ∃ h, treatedFrame (q := q) P rank R hr M L₀ g =
      guideFrame (cellCenterPos L) q (treatedGuide R.1.1 R.1.index (D * Real.log L) M L₀ g)
        (labelParty R) guidePlaceholder rank
        (treatedVertices k R.1.1 (D * Real.log L) M
          (treatedGuide R.1.1 R.1.index (D * Real.log L) M L₀ g)) (suppliedPatch P _ hr) h := by
  classical
  set n : ℝ := (2 : ℝ) ^ (R.1.1 : ℕ) with hn_def
  set t := D * Real.log L with ht_def
  have hn : 0 < n := by positivity
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < t := mul_pos hc.D_pos hℓ
  have htn : 20 * t < n := by nlinarith [hc.twenty_le_K₀]
  have hε4 := hc.lt_one_div_four_thousand
  have hgr : IsRayConstant (shiftGuide (blockCorner n R.1.index) g) :=
    (hg.isRayConstant _ (by
      change IsRayConstant fun p => blockGuide n (protocolLevelLabels k R.1.1 done)
        (p + blockCorner n R.1.index)
      exact (isRayConstant_blockGuide _ _).comp_add _)).shiftGuide _
  have hf := (hgr.homogenize M n t L₀).isDisplacedReading_sampleGuide
  have hout : ∀ Q, ¬InRoot ((2 : ℤ) ^ (k - (R.1.1 : ℕ))) Q →
      protocolLevelLabels k R.1.1 done Q = guidePlaceholder := fun Q hQ => by
    simp only [protocolLevelLabels, levelLabels, hQ, ite_false]
  have hmem : ∀ z, z ∈ treatedVertices k R.1.1 t M (treatedGuide R.1.1 R.1.index t M L₀ g) ↔
      IsTrueVertex (treatedGuide R.1.1 R.1.index t M L₀ g) z := fun z =>
    mem_treatedTrueVertices hn (by linarith) hout R.1.inRoot_index hg M L₀ hf
  refine ⟨hf, hmem, ?_, treatedFrame_eq P rank R _⟩
  intro z hz z' hz' hne
  have h := (homogenize_reading_outerHoles_disjoint hn ht htn hε4 hg M L₀
    ((1 : ℝ), (1 : ℝ))).2 _ hf z z' ((hmem z).1 hz) ((hmem z').1 hz') hne
  refine disjoint_outer_of_disjoint_closedBall ?_
  simp only [suppliedPatch_center, suppliedPatch_scale]
  rwa [← mul_assoc]

end TNLean.PEPS.Approximation
