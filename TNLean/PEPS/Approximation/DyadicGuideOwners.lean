/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicGuideFrames
import TNLean.PEPS.Approximation.DyadicGuideReadings
import TNLean.PEPS.Approximation.DyadicProtocolOwners

/-!
# Owners of the treated and directly repainted guides

During the repainting of a square the labels of the guides are read as parties by `labelParty`,
which is injective on the placeholder and the labels of the squares of the hierarchy
(`labelParty_injOn`). `blockRepainting_mem_validLabels` shows that the main and auxiliary guides of
an edge construction take only such labels. This file extends this to every guide that occurs in
a repainting:

* the block guides of a level, which are the old and new guides of a direct repainting
  (`blockGuide_mem_validLabels`);
* the guides placed on a block (`shiftGuide`) and homogenized on treated squares to a valid label,
  as in the point treatments (`homogenize_mem`);
* the readings of such guides after a small displacement (`IsDisplacedReading.mem`), which are the
  guides read at the sites.

For a guide with valid labels, two sites of its encoded frame have the same raw owner exactly when
they carry the same label (`guideFrame_owner_eq_iff`), so the owners of the frames are read
faithfully from the labels (`06-geometry.tex`, lines 82–100, 328–339 and 507–527).

## Main results

* `TNLean.PEPS.Approximation.blockGuide_mem_validLabels`,
  `TNLean.PEPS.Approximation.homogenize_mem`, `TNLean.PEPS.Approximation.shiftGuide_mem`,
  `TNLean.PEPS.Approximation.IsDisplacedReading.mem`.
* `TNLean.PEPS.Approximation.blockRepainting_treated_mem_validLabels`.
* `TNLean.PEPS.Approximation.guideFrame_owner_eq_iff`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`: the level schedule and the placeholder (lines 82–100), point treatment
  (lines 328–339), direct repainting (lines 507–527) and the active labels (lines 585–609).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Set Filter Topology EncodedFrame

/-! ### Closure of a set of labels under the guide operations -/

/-- A guide homogenized to a label of `A` on any set takes values in `A` if the guide does. -/
theorem homogenize_mem {X κ : Type*} {A : Set κ} {U : Set X} {P : κ} {f : X → κ}
    (hf : ∀ p, f p ∈ A) (hP : P ∈ A) (p : X) : homogenize U P f p ∈ A := by
  classical
  by_cases hp : p ∈ U
  · rw [homogenize_of_mem hp]; exact hP
  · rw [homogenize_of_notMem hp]; exact hf p

/-- A guide placed on a block takes the values of the guide. -/
theorem shiftGuide_mem {κ : Type*} {A : Set κ} {o : ℝ × ℝ} {g : ℝ × ℝ → κ}
    (hg : ∀ p, g p ∈ A) (p : ℝ × ℝ) : shiftGuide o g p ∈ A :=
  hg _

/-- A reading of a guide after a small displacement takes only values of the guide. -/
theorem IsDisplacedReading.mem {X κ : Type*} [AddCommGroup X] [Module ℝ X] {A : Set κ}
    {f' f : X → κ} {v : X} (h : IsDisplacedReading f' f v) (hf : ∀ p, f p ∈ A) (p : X) :
    f' p ∈ A := by
  obtain ⟨ε, hε⟩ := (h p).exists
  exact hε ▸ hf _

/-- **Valid labels of a block guide.** At level `2 ^ j'` with `j' < k`, the block guide of the
level labels takes only valid labels. These are the guides before and after a direct repainting.

Polynomial-PEPS manuscript (September 24, 2026), `06-geometry.tex`, lines 82–100 and 507–527. -/
theorem blockGuide_mem_validLabels {k j' : ℕ} (hj : j' < k) (n : ℝ) (done : Set (ℤ × ℤ))
    (p : ℝ × ℝ) : blockGuide n (protocolLevelLabels k j' done) p ∈ validLabels k :=
  levelLabels_mem_validLabels hj done _

/-- **Valid labels of the treated guides of a repainting.** In the repainting of a genuine block
`S` of level `2 ^ j'`, every guide of `blockRepainting_mem_validLabels`, placed on the block and
homogenized on any set to a valid label, takes only valid labels. These are the guides of the
point treatments, before and after the bulk steps.

Polynomial-PEPS manuscript (September 24, 2026), `06-geometry.tex`, lines 328–339 and 585–609. -/
theorem blockRepainting_treated_mem_validLabels {k j' : ℕ} (hj : j' < k) {n : ℝ} (hn : 0 < n)
    (done : Set (ℤ × ℤ)) {S : ℤ × ℤ} (hS : InRoot ((2 : ℤ) ^ (k - j')) S)
    (E : List SquareEdge) (e : SquareEdge) {W : ℝ → GuideLabel}
    (hW : W ∈ edgeWords (protocolLevelLabels k j' done S) (newParty Sum.inl j' S)
      (protocolLevelLabels k j' done (e.nbrBlock S))) (o : ℝ × ℝ) (U : Set (ℝ × ℝ))
    {P : GuideLabel} (hP : P ∈ validLabels k) (p : ℝ × ℝ) :
    homogenize U P (shiftGuide o ((blockBaseline hn (protocolLevelLabels k j' done) S
        (newParty Sum.inl j' S)).completedGuide E)) p ∈ validLabels k ∧
      homogenize U P (shiftGuide o ((blockBaseline hn (protocolLevelLabels k j' done) S
        (newParty Sum.inl j' S)).mainGuide E e W)) p ∈ validLabels k ∧
      homogenize U P (shiftGuide o ((blockBaseline hn (protocolLevelLabels k j' done) S
        (newParty Sum.inl j' S)).auxGuide e W)) p ∈ validLabels k :=
  ⟨homogenize_mem (shiftGuide_mem fun x =>
      (blockRepainting_mem_validLabels hj hn done hS E e hW x).1) hP p,
    homogenize_mem (shiftGuide_mem fun x =>
      (blockRepainting_mem_validLabels hj hn done hS E e hW x).2.1) hP p,
    homogenize_mem (shiftGuide_mem fun x =>
      (blockRepainting_mem_validLabels hj hn done hS E e hW x).2.2) hP p⟩

/-! ### Owners of the encoded frames -/

/-- **Owners of the frame of a guide with valid labels.** If a guide takes only valid labels,
two sites of its encoded frame, with labels read as parties of the repainting of `R`, have the
same raw owner exactly when they carry the same label.

Polynomial-PEPS manuscript (September 24, 2026), `06-geometry.tex`, lines 82–100 and 585–609. -/
theorem guideFrame_owner_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {pos : ι → ℝ × ℝ} {k : ℕ} (R : RepaintedSquare k) {g : ℝ × ℝ → GuideLabel}
    (hg : ∀ p, g p ∈ validLabels k) (ph : GuideLabel) (rank : GuideLabel → ℕ)
    (V : Finset (ℝ × ℝ)) (patch : ℝ × ℝ → SquarePatch pos q)
    (hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer)
    (x y : ι) :
    (guideFrame pos q g (labelParty R) ph rank V patch hV).owner x =
        (guideFrame pos q g (labelParty R) ph rank V patch hV).owner y ↔
      g (pos x) = g (pos y) := by
  simp only [guideFrame_owner]
  exact ⟨fun h => labelParty_injOn R (hg _) (hg _) h, fun h => h ▸ rfl⟩

end TNLean.PEPS.Approximation
