/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicPointTreatmentRewrite
import TNLean.PEPS.Approximation.DyadicProtocolConstants
import TNLean.PEPS.Approximation.DyadicReadingFootprints
import TNLean.PEPS.Approximation.DyadicResizeRewrite

/-!
# The two-owner footprints of the protocol steps

The plane conditions of the direct repainting, the resize and the point treatment
(`exists_directRepainting_planeConditions`, `exists_resize_planeConditions` and
`exists_pointTreatment_planeConditions`) take the two-owner condition for footprints of radius
`2 u` as a hypothesis. In the source this condition comes from the compactness observation, with
the mesh parameter `ν` chosen after `K₀` and `ε₀` and before the displacement
(`06-geometry.tex`, lines 447–541 and 559–563). This file derives it at the protocol's radii: the
hole radius `h_n = ε₀ min(n, t)` and the patch radius `u = ν s / 2`, so that `2 u = ν s`, with
`s = n` for a direct repainting at level `n ≤ K₀ t` (lines 507–527), `s = 2 n` for the resize of
a hole of a guide uniform on the `2 n`-blocks when `n < t` (lines 529–541), and `s = t` for a
point treatment at a level `n > K₀ t` (lines 481–505).

* `IsFootprintRatio K₀ ε₀ ν` states the conclusions of the footprint-ratio theorems for the
  readings, `exists_template_footprintRatio_reading`,
  `exists_directRepainting_footprintRatio_reading` and
  `exists_resizing_footprintRatio_mixed_reading`, with the ratio `ν`. It holds for every
  sufficiently small `ν > 0` (`exists_isFootprintRatio`), a smallness condition on `ν` given
  `K₀` and `ε₀` of the kind met by `exists_isProtocolConstants`; hence constants in the source's
  order exist for which it holds (`exists_isProtocolConstants_isFootprintRatio`).
* From it follow the two-owner hypotheses of the three rewrites, for readings after a generic
  displacement (`IsFootprintRatio.hasTwoOwnerFootprints_directRepainting`,
  `IsFootprintRatio.twoOwner_resize`, `IsFootprintRatio.hasTwoOwnerFootprints_pointTreatment`).
* Hence the three plane-condition theorems hold at the protocol's radii without the two-owner
  hypotheses (`exists_directRepainting_planeConditions_of_isFootprintRatio`,
  `exists_resize_planeConditions_of_isFootprintRatio`,
  `exists_pointTreatment_planeConditions_of_isFootprintRatio`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the scales
  `eq:geometry-scales` (lines 102–117), the point treatment (lines 328–343), the compactness
  observation (lines 447–479), the point covers (lines 481–505), the direct repainting
  (lines 507–527), the resizing (lines 529–541) and the order of the constants (lines 559–570).
-/

open Set Metric Filter Topology

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

/-! ### The footprint ratio of the protocol -/

/-- **An admissible footprint ratio.** The ratio `ν` serves the readings after every generic
displacement in the three footprint-ratio theorems of the source's compactness observation:

* near a mark, for a guide that agrees on the open square of radius `4 t` about `c` with an
  injective relabelling of a scaled template of the point treatment, with working set the closed
  square of radius `2 t`, holes at the true vertices within `3 t`, inner radius `ε₀ t` and
  footprint radius `ν t`;
* for a direct repainting at level `n ≤ K₀ t`, with working set the closed square of radius `2 n`
  about a grid corner, holes at the true vertices within `3 n`, inner radius `h_n` and footprint
  radius `ν n`;
* for a resize at level `n < t` of a guide uniform on the `2 n`-blocks, with working set the
  closed square of radius `2 n` about a grid corner, holes at the true vertices within `4 n`, each
  of radius `h_n` or `h_{2n}`, and footprint radius `ν (2 n)`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 447–541 and 559–563. -/
structure IsFootprintRatio (K₀ ε₀ ν : ℝ) : Prop where
  template : ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
    ∀ {κ : Type} {t : ℝ}, 0 < t → ∀ (i : TemplateIndex) (σ : BlockSlot 1 → κ),
    InjOn σ (range (footprintTemplate i)) → ∀ (c : ℝ × ℝ) (f g' : ℝ × ℝ → κ),
    (∀ q ∈ ball c (4 * t), f q = σ (footprintTemplate i (t⁻¹ • (q - c)))) →
    IsDisplacedReading g' f v →
    HasTwoOwnerFootprints g' (closedBall c (2 * t))
      {x | x ∈ closedBall c (3 * t) ∧ IsTrueVertex g' x} (ε₀ * t) (ν * t)
  directRepainting : ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
    ∀ {κ : Type} {n t : ℝ}, 0 < n → 0 < t → n ≤ K₀ * t →
    ∀ (lab : ℤ × ℤ → κ) (Q : ℤ × ℤ) (g' : ℝ × ℝ → κ),
    IsDisplacedReading g' (blockGuide n lab) v →
    HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (2 * n))
      {c | c ∈ closedBall (blockCorner n Q) (3 * n) ∧ IsTrueVertex g' c}
      (holeRadius ε₀ n t) (ν * n)
  resizing : ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
    ∀ {κ : Type} {n t : ℝ}, 0 < n → n < t → ∀ (lab : ℤ × ℤ → κ) (Q : ℤ × ℤ)
    (g' : ℝ × ℝ → κ), IsDisplacedReading g' (blockGuide (2 * n) lab) v →
    ∀ ρ : ℝ × ℝ → ℝ, (∀ c, ρ c = holeRadius ε₀ n t ∨ ρ c = holeRadius ε₀ (2 * n) t) →
    ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
      p ∈ (closedBall x (ν * (2 * n)) ∩ closedBall (blockCorner (2 * n) Q) (2 * n)) \
        ⋃ c ∈ {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)) ∧
          IsTrueVertex g' c}, ball c (ρ c)) →
    g' p₁ = g' p₂ ∨ g' p₁ = g' p₃ ∨ g' p₂ = g' p₃

/-- **Every sufficiently small ratio is admissible.** For `ε₀ > 0` and any `K₀` there is
`ν' > 0` such that every `ν ∈ (0, ν']` is an admissible footprint ratio: the minimum of the three
ratios of the footprint-ratio theorems, since the two-owner condition survives shrinking the
footprint.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 464–479, 491–499, 520–525 and 559–563. -/
theorem exists_isFootprintRatio (K₀ : ℝ) {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν' > 0, ∀ ν, 0 < ν → ν ≤ ν' → IsFootprintRatio K₀ ε₀ ν := by
  obtain ⟨ν₁, hν₁, H₁⟩ := exists_template_footprintRatio_reading.{0} hε
  obtain ⟨ν₂, hν₂, H₂⟩ := exists_directRepainting_footprintRatio_reading.{0} (K₀ := K₀) hε
  obtain ⟨ν₃, hν₃, H₃⟩ := exists_resizing_footprintRatio_mixed_reading.{0} hε
  refine ⟨min ν₁ (min ν₂ ν₃), lt_min hν₁ (lt_min hν₂ hν₃), fun ν _ hle => ⟨?_, ?_, ?_⟩⟩
  · intro v hv κ t ht i σ hσ c f g' hf hg'
    exact (H₁ hv ht i σ hσ c f g' hf hg').mono
      (mul_le_mul_of_nonneg_right (hle.trans (min_le_left _ _)) ht.le)
  · intro v hv κ n t hn ht hK lab Q g' hg'
    have h := (H₂ hv hn ht hK lab Q g' hg').mono
      (mul_le_mul_of_nonneg_right
        (hle.trans ((min_le_right _ _).trans (min_le_left _ _))) hn.le)
    rwa [mul_comm n 2, show n * (2 + 1) = 3 * n by ring] at h
  · intro v hv κ n t hn hnt lab Q g' hg' ρ hρ x p₁ p₂ p₃ hp
    have hν : ν * (2 * n) ≤ ν₃ * (2 * n) :=
      mul_le_mul_of_nonneg_right (hle.trans ((min_le_right _ _).trans (min_le_right _ _)))
        (by positivity)
    refine H₃ hv hn hnt lab Q g' hg' ρ hρ x p₁ p₂ p₃ fun p hp' => ?_
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hp p hp'
    refine ⟨⟨closedBall_subset_closedBall hν h₁, by rwa [mul_one]⟩, ?_⟩
    rwa [show 2 * n * (1 + 1) = 2 * (2 * n) by ring]

/-- **Constants in the source's order with an admissible footprint ratio.** The constants of the
protocol can be chosen in the source's order so that the mesh parameter `ν` is also an admissible
footprint ratio for `K₀` and `ε₀`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 559–570. -/
theorem exists_isProtocolConstants_isFootprintRatio :
    ∃ K₀ ε₀ ν a D B₀, IsProtocolConstants K₀ ε₀ ν a D B₀ ∧ IsFootprintRatio K₀ ε₀ ν := by
  obtain ⟨K₀, ε₀, ν, a, D, B₀, hc, -, -, hν, -⟩ :=
    exists_isProtocolConstants (fun _ => True) (fun _ _ => True)
      (fun K₀ ε₀ ν => IsFootprintRatio K₀ ε₀ ν) (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True) ⟨0, fun _ _ => trivial⟩
      (fun _ => ⟨1, one_pos, fun _ _ _ => trivial⟩)
      (fun K₀ _ hε => exists_isFootprintRatio K₀ hε)
      (fun _ _ _ _ _ => ⟨1, one_pos, fun _ _ _ => trivial⟩)
      (fun _ _ _ _ _ => ⟨1, one_pos, trivial⟩) (fun _ _ _ _ _ => ⟨0, fun _ _ => trivial⟩)
  exact ⟨K₀, ε₀, ν, a, D, B₀, hc, hν⟩

/-! ### The two-owner hypotheses of the three rewrites -/

namespace IsFootprintRatio

variable {K₀ ε₀ ν : ℝ}

/-- **The two-owner condition of a direct repainting.** For an admissible ratio `ν`, a level
`n ≤ K₀ t` and a reading `g` after a generic displacement of a guide uniform on the `n`-blocks,
`g` has the two-owner condition about the corner of every block `S` with working set the closed
square of radius `2 n`, holes of radius `h_n` at its true vertices within `3 n`, and footprints
of radius `2 u = ν n`. This is the hypothesis of `exists_directRepainting_planeConditions`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527. -/
theorem hasTwoOwnerFootprints_directRepainting (hm : IsFootprintRatio K₀ ε₀ ν) {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) {κ : Type} {n t : ℝ} (hn : 0 < n) (ht : 0 < t)
    (hK : n ≤ K₀ * t) (lab : ℤ × ℤ → κ) (S : ℤ × ℤ) {g : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v) :
    HasTwoOwnerFootprints g (closedBall (blockCorner n S) (2 * n))
      {c | c ∈ closedBall (blockCorner n S) (3 * n) ∧ IsTrueVertex g c}
      (holeRadius ε₀ n t) (2 * patchRadius ν n) := by
  rw [two_mul_patchRadius]
  exact hm.directRepainting hv hn ht hK lab S g hg

/-- **The two-owner condition of a resize.** For an admissible ratio `ν`, a level `n < t` and a
reading `g` after a generic displacement of a guide uniform on the `2 n`-blocks, every closed
footprint of radius `2 u = ν (2 n)` meets at most two labels of `g` at its points in the closed
square of radius `2 n` about a grid corner, outside the open holes at the true vertices within
`4 n` of it, each hole of its own radius `h_n` or `h_{2n}`. These are the hypotheses of
`exists_resize_planeConditions`, for the old and for the new radii, and they cover the
intermediate configurations in which only some holes have been resized.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 529–541. -/
theorem twoOwner_resize (hm : IsFootprintRatio K₀ ε₀ ν) {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) {κ : Type} {n t : ℝ} (hn : 0 < n) (hnt : n < t)
    (lab : ℤ × ℤ → κ) (Q : ℤ × ℤ) {g : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide (2 * n) lab) v) {ρ : ℝ × ℝ → ℝ}
    (hρ : ∀ c, ρ c = holeRadius ε₀ n t ∨ ρ c = holeRadius ε₀ (2 * n) t) :
    ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
      p ∈ (closedBall x (2 * patchRadius ν (2 * n)) ∩
          closedBall (blockCorner (2 * n) Q) (2 * n)) \
        ⋃ c ∈ {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)) ∧ IsTrueVertex g c},
          ball c (ρ c)) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃ := by
  rw [two_mul_patchRadius]
  exact hm.resizing hv hn hnt lab Q g hg ρ hρ

/-- Away from the treated squares of the other marks: if `Q₀ ∉ M` and `8 t < n`, homogenizing on
the open squares of radius `t` about the grid corners of `M` changes nothing on the open square of
radius `4 t` about `Q₀`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 330–343. -/
theorem _root_.TNLean.PEPS.Approximation.homogenize_iUnion_eq_of_notMem {ι : Type*} {n t : ℝ}
    (hn : 0 < n) (htn : 8 * t < n) (M : Finset (ℤ × ℤ)) {Q₀ : ℤ × ℤ} (hQ₀ : Q₀ ∉ M) (P : ι)
    (f : ℝ × ℝ → ι) {q : ℝ × ℝ} (hq : q ∈ ball (blockCorner n Q₀) (4 * t)) :
    homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P f q = f q := by
  refine homogenize_of_notMem fun h => ?_
  simp only [mem_iUnion, exists_prop] at h
  obtain ⟨Q, hQ, hQ'⟩ := h
  have h₁ := le_dist_blockCorner_of_ne hn (fun e : Q = Q₀ => hQ₀ (e ▸ hQ))
  have h₂ := dist_triangle (blockCorner n Q) q (blockCorner n Q₀)
  rw [mem_ball] at hq hQ'
  rw [dist_comm] at hQ'
  linarith

/-- **The two-owner condition near a mark.** For an admissible ratio `ν` and `8 t < n`, let `g`
be an unmodified guide of the repainting of the block `S`, `Q₀` a corner of `S`, and `g₁` the
reading after a generic displacement of `g` homogenized to a label `L₀` of the nine blocks around
`S` on the open squares of radius `t` about the grid corners of a finite set `M`, whether or not
`Q₀ ∈ M`. Then `g₁` has the two-owner condition with working set the closed square of radius
`2 t` about `Q₀`, holes of radius `ε₀ t` at its true vertices within `3 t`, and footprints of
radius `2 u = ν t`. This is the hypothesis of `exists_pointTreatment_planeConditions`, for the
treatment (`Q₀ ∈ M`) and for the guide before it or after its removal (`Q₀ ∉ M`).

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339 and 481–505. -/
theorem hasTwoOwnerFootprints_pointTreatment (hm : IsFootprintRatio K₀ ε₀ ν) {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) {κ : Type} {n t : ℝ} (hn : 0 < n) (ht : 0 < t)
    (htn : 8 * t < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ} {g : ℝ × ℝ → κ}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (M : Finset (ℤ × ℤ)) {Q₀ : ℤ × ℤ}
    (hQ₀ : IsBlockCornerOf S Q₀) (L₀ : κ) (hL₀ : L₀ = B ∨ ∃ R ∈ blockWindow 1, L₀ = lab (R + S))
    {g₁ : ℝ × ℝ → κ} (hg₁ : IsDisplacedReading g₁
      (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) L₀ (shiftGuide (blockCorner n S) g)) v) :
    HasTwoOwnerFootprints g₁ (closedBall (blockCorner n Q₀) (2 * t))
      {c | c ∈ closedBall (blockCorner n Q₀) (3 * t) ∧ IsTrueVertex g₁ c} (ε₀ * t)
      (2 * patchRadius ν t) := by
  classical
  set P : Option κ := if Q₀ ∈ M then some L₀ else none with hPdef
  have hP : ∀ x ∈ P, x = B ∨ ∃ R ∈ blockWindow 1, x = lab (R + S) := by
    intro x hx
    by_cases h : Q₀ ∈ M
    · rw [hPdef, if_pos h, Option.mem_some_iff] at hx
      exact hx ▸ hL₀
    · rw [hPdef, if_neg h] at hx
      exact absurd hx (Option.notMem_none x)
  obtain ⟨i, hinj, heq⟩ := exists_template_injOn hn hg hQ₀ ht htn P hP
  rw [two_mul_patchRadius]
  refine hm.template hv ht i _ hinj _ _ g₁ (fun q hq => ?_) hg₁
  rw [← heq q hq]
  by_cases h : Q₀ ∈ M
  · rw [homogenize_iUnion_eq_of_mem_ball hn htn M h L₀ _ hq, hPdef, if_pos h]
    rfl
  · rw [homogenize_iUnion_eq_of_notMem hn htn M h L₀ _ hq, hPdef, if_neg h]
    rfl

end IsFootprintRatio

/-! ### The plane conditions at the protocol's radii -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}
  {K₀ ε₀ ν B₀ t ℓ : ℝ}

/-- **The direct repainting at the protocol's radii.** Let `ν` be an admissible footprint ratio,
let the separations of the protocol hold at `t`, and let `0 < n ≤ K₀ t`. Then the conclusion of
`exists_directRepainting_planeConditions` holds for the readings after a generic displacement,
with holes of radius `h_n` and patches of radius `u = ν n / 2`, without the two-owner hypotheses.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527 and 559–570; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–207. -/
theorem exists_directRepainting_planeConditions_of_isFootprintRatio
    (hm : IsFootprintRatio K₀ ε₀ ν) (hs : ProtocolSeparations K₀ ε₀ ν B₀ t ℓ) {n : ℝ}
    (hn : 0 < n) (hK : n ≤ K₀ * t) {v : ℝ × ℝ} (hv : IsGenericDisplacement v)
    {lab lab' : ℤ × ℤ → κ} {S : ℤ × ℤ} (hlab : ∀ Q, Q ≠ S → lab' Q = lab Q) {g g' : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v)
    (hg' : IsDisplacedReading g' (blockGuide n lab') v) (own : κ → Party) (ph : κ)
    (rank : κ → ℕ) {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g c)
    (hV' : ∀ c ∈ V', IsTrueVertex g' c)
    (hVc : ∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g c → c ∈ V)
    (hVc' : ∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g' c → c ∈ V')
    (hVV' : ∀ c ∉ squareCorners n S, (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = holeRadius ε₀ n t)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = patchRadius ν n) :
    ∃ G : GuideFrameRewrite pos q κ Party, G.PlaneConditions ∧ G.old = g ∧ G.new = g' ∧
      G.own = own ∧ G.ph = ph ∧ G.rank = rank ∧ G.holeOld = hole ∧ G.holeNew = hole ∧
      G.patch = patch ∧ G.untouched ∪ G.oldAffected = V ∧ G.untouched ∪ G.newAffected = V' ∧
      G.oldAffected.card ≤ 4 ∧ G.newAffected.card ≤ 4 ∧
      (G.centers.card : ℝ) ≤
        (2 * (n / 2 + 2 * holeRadius ε₀ n t + patchRadius ν n) / patchRadius ν n + 1) ^ 2 ∧
      G.parties.card ≤ 18 ∧ G.parties.Nonempty ∧
      ∀ x ∈ G.parties, ∃ R ∈ blockWindow 1, x = own (lab (R + S)) ∨ x = own (lab' (R + S)) := by
  obtain ⟨hr, hu, -, hsep, -⟩ := hs.direct n hn
  exact exists_directRepainting_planeConditions hn hr hu hsep hlab hg hg' own ph rank hV hV' hVc
    hVc' hVV' hole patch hhole hpatch
    (hm.hasTwoOwnerFootprints_directRepainting hv hn hs.t_pos hK lab S hg)
    (hm.hasTwoOwnerFootprints_directRepainting hv hn hs.t_pos hK lab' S hg')

/-- **The resize at the protocol's radii.** Let `ν` be an admissible footprint ratio, let the
separations of the protocol hold at `t`, and let `0 < n < t`. For the reading `g` after a generic
displacement of a guide uniform on the `2 n`-blocks, and hole patches whose radii are `h_n` or
`h_{2n}`, the conclusion of `exists_resize_planeConditions` holds with `N = 2 n`, `R = h_{2n}` and
patches of radius `u = ν (2 n) / 2`, without the two-owner hypotheses.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 529–541 and 559–570; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–207. -/
theorem exists_resize_planeConditions_of_isFootprintRatio
    (hm : IsFootprintRatio K₀ ε₀ ν) (hs : ProtocolSeparations K₀ ε₀ ν B₀ t ℓ) {n : ℝ}
    (hn : 0 < n) (hnt : n < t) {v : ℝ × ℝ} (hv : IsGenericDisplacement v) {lab : ℤ × ℤ → κ}
    {Q : ℤ × ℤ} {g : ℝ × ℝ → κ} (hg : IsDisplacedReading g (blockGuide (2 * n) lab) v)
    (own : κ → Party) (ph : κ) (rank : κ → ℕ) {V : Finset (ℝ × ℝ)}
    (hV : ∀ c ∈ V, IsTrueVertex g c) (hc₀ : blockCorner (2 * n) Q ∈ V)
    (hVc : ∀ c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)), IsTrueVertex g c → c ∈ V)
    (holeOld holeNew patch : ℝ × ℝ → SquarePatch pos q)
    (hcenter : ∀ z, (holeOld z).center = z ∧ (holeNew z).center = z)
    (hold : ∀ z, (holeOld z).scale = holeRadius ε₀ n t ∨
      (holeOld z).scale = holeRadius ε₀ (2 * n) t)
    (hnew : ∀ z, (holeNew z).scale = holeRadius ε₀ n t ∨
      (holeNew z).scale = holeRadius ε₀ (2 * n) t)
    (hsame : ∀ z, z ≠ blockCorner (2 * n) Q → holeOld z = holeNew z)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = patchRadius ν (2 * n)) :
    ∃ G : GuideFrameRewrite pos q κ Party, G.PlaneConditions ∧ G.old = g ∧ G.new = g ∧
      G.own = own ∧ G.ph = ph ∧ G.rank = rank ∧ G.holeOld = holeOld ∧ G.holeNew = holeNew ∧
      G.patch = patch ∧ G.untouched ∪ G.oldAffected = V ∧ G.untouched ∪ G.newAffected = V ∧
      G.oldAffected.card ≤ 1 ∧ G.newAffected.card ≤ 1 ∧
      (G.centers.card : ℝ) ≤ (2 * (2 * holeRadius ε₀ (2 * n) t + patchRadius ν (2 * n)) /
        patchRadius ν (2 * n) + 1) ^ 2 ∧ G.parties.card ≤ 9 ∧
      G.parties.Nonempty ∧ ∀ x ∈ G.parties, ∃ R ∈ blockWindow 1,
        x = own (lab (R + (Q.1 - 1, Q.2 - 1))) := by
  have hN : 0 < 2 * n := by positivity
  obtain ⟨hR, hu, -, hsep, -⟩ := hs.resize (2 * n) hN
  have hε : 0 < ε₀ :=
    (mul_pos_iff_of_pos_right (lt_min hn hs.t_pos)).1 (hs.direct n hn).1
  have hle : holeRadius ε₀ n t ≤ holeRadius ε₀ (2 * n) t :=
    mul_le_mul_of_nonneg_left (min_le_min (by linarith) le_rfl) hε.le
  have hscale (z : ℝ × ℝ) : (holeOld z).scale ≤ holeRadius ε₀ (2 * n) t ∧
      (holeNew z).scale ≤ holeRadius ε₀ (2 * n) t :=
    ⟨(hold z).elim (fun h => h ▸ hle) fun h => h.le, (hnew z).elim (fun h => h ▸ hle) fun h => h.le⟩
  exact exists_resize_planeConditions hN hR hu hsep hg own ph rank hV hc₀ hVc holeOld holeNew
    patch hcenter hscale hsame hpatch (hm.twoOwner_resize hv hn hnt lab Q hg hold)
    (hm.twoOwner_resize hv hn hnt lab Q hg hnew)

/-- **The point treatment at the protocol's radii.** Let the constants be chosen as in the
source, `ν` an admissible footprint ratio, the separations of the protocol hold at `t`, and
`K₀ t < n`. Let `g` be an unmodified guide of the repainting of the block `S`, `Q₀` a corner of
`S`, and `g₁`, `g₂` the readings after a generic displacement of `g` homogenized to a label `L₀`
of the nine blocks around `S` on the open squares of radius `t` about the grid corners of `M₁`
and of `M₂`, two sets that differ at most at `Q₀`. Let `V` and `V'` contain the true vertices of
`g₁` and `g₂` within `3 t` of `Q₀`. Then the conclusion of `exists_pointTreatment_planeConditions`
holds with holes of radius `h_n = ε₀ t` and patches of radius `u = ν t / 2`, without the
two-owner hypotheses.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–343, 481–505 and 559–570; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–207. -/
theorem exists_pointTreatment_planeConditions_of_isFootprintRatio {a D : ℝ}
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hm : IsFootprintRatio K₀ ε₀ ν)
    (hs : ProtocolSeparations K₀ ε₀ ν B₀ t ℓ) {n : ℝ} (hn : 0 < n) (hnK : K₀ * t < n)
    {v : ℝ × ℝ} (hv : IsGenericDisplacement v) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ}
    {g : ℝ × ℝ → κ} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g)
    {M₁ M₂ : Finset (ℤ × ℤ)} (Q₀ : ℤ × ℤ) (hQ₀ : IsBlockCornerOf S Q₀)
    (hM : ∀ Q, Q ≠ Q₀ → (Q ∈ M₁ ↔ Q ∈ M₂)) (L₀ : κ)
    (hL₀ : L₀ = B ∨ ∃ R ∈ blockWindow 1, L₀ = lab (R + S)) {g₁ g₂ : ℝ × ℝ → κ}
    (hg₁ : IsDisplacedReading g₁ (homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v)
    (hg₂ : IsDisplacedReading g₂ (homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v) (own : κ → Party) (ph : κ) (rank : κ → ℕ)
    {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g₁ c) (hV' : ∀ c ∈ V', IsTrueVertex g₂ c)
    (hVc : ∀ c ∈ closedBall (blockCorner n Q₀) (3 * t), IsTrueVertex g₁ c → c ∈ V)
    (hVc' : ∀ c ∈ closedBall (blockCorner n Q₀) (3 * t), IsTrueVertex g₂ c → c ∈ V')
    (hVV' : ∀ c, n - t ≤ dist c (blockCorner n Q₀) → (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = holeRadius ε₀ n t)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = patchRadius ν t)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (P : Finset Party)
    (hP : ∀ p, dist p (blockCorner n Q₀) ≤ t + 2 * holeRadius ε₀ n t + 3 * patchRadius ν t →
      own (g₁ p) ∈ P ∧ own (g₂ p) ∈ P)
    (hPt : ∀ a ∈ V, dist a (blockCorner n Q₀) ≤ t → own (tagHolder rank g₁ ph a) ∈ P)
    (hPt' : ∀ a ∈ V', dist a (blockCorner n Q₀) ≤ t → own (tagHolder rank g₂ ph a) ∈ P) :
    ∃ G : GuideFrameRewrite pos q κ Party, G.PlaneConditions ∧ G.old = g₁ ∧ G.new = g₂ ∧
      G.own = own ∧ G.ph = ph ∧ G.rank = rank ∧ G.holeOld = hole ∧ G.holeNew = hole ∧
      G.patch = patch ∧ G.parties = P ∧ G.untouched ∪ G.oldAffected = V ∧
      G.untouched ∪ G.newAffected = V' ∧
      (∀ a ∈ G.oldAffected, dist a (blockCorner n Q₀) ≤ t) ∧
      (∀ a ∈ G.newAffected, dist a (blockCorner n Q₀) ≤ t) ∧
      (G.centers.card : ℝ) ≤
        (2 * (t + 2 * holeRadius ε₀ n t + patchRadius ν t) / patchRadius ν t + 1) ^ 2 := by
  obtain ⟨hr, hu, -, hsep, -, -⟩ := hs.point n hnK
  have ht := hs.t_pos
  have htn : 8 * t < n := by nlinarith [mul_le_mul_of_nonneg_right hc.twenty_le_K₀ ht.le]
  have hrt : holeRadius ε₀ n t = ε₀ * t := holeRadius_of_le (by linarith)
  have hW : closedBall (blockCorner n Q₀) (t + 2 * holeRadius ε₀ n t + 3 * patchRadius ν t) ⊆
      closedBall (blockCorner n Q₀) (2 * t) := by
    refine closedBall_subset_closedBall ?_
    rw [hrt, patchRadius]
    nlinarith [mul_lt_mul_of_pos_right hc.ν_small ht, mul_pos hc.ν_pos ht]
  have htwo := hm.hasTwoOwnerFootprints_pointTreatment hv hn ht htn hg M₁ hQ₀ L₀ hL₀ hg₁
  have htwo' := hm.hasTwoOwnerFootprints_pointTreatment hv hn ht htn hg M₂ hQ₀ L₀ hL₀ hg₂
  rw [← hrt] at htwo htwo'
  exact exists_pointTreatment_planeConditions hn ht hr hu hsep hg Q₀ hM L₀ hg₁ hg₂ own ph rank
    hV hV' hVV' hole patch hhole hpatch hpV hpV' hW (fun c hc => hVc c hc.1 hc.2)
    (fun c hc => hVc' c hc.1 hc.2) htwo htwo' P hP hPt hPt'

end TNLean.PEPS.Approximation
