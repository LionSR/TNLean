/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicDirectRepaintingStep
import TNLean.PEPS.Approximation.DyadicProtocolConstants
import TNLean.PEPS.Approximation.DyadicReadingFootprints

/-!
# The direct repainting at the constants of the protocol

The direct repainting of a block at a level `n ≤ K₀ t` (`directRepainting_step`) takes the
two-owner condition of the two readings for footprints of radius `2 u` as a hypothesis, together
with the separation `3 u + 4 r < n` and the patch count `b`. In the source the two-owner
condition comes from the compactness observation, with the mesh parameter `ν` chosen after `K₀`
and `ε₀` and before the displacement (`06-geometry.tex`, lines 447–479, 507–527 and 559–563).
This file derives it at the protocol's radii, the hole radius `h_n = ε₀ min(n, t)` and the patch
radius `u = ν n / 2`, so that `2 u = ν n`, and combines it with the separations of the protocol
(`ProtocolSeparations`):

* `IsDirectRepaintingRatio K₀ ε₀ ν` states the conclusion of
  `exists_directRepainting_footprintRatio_reading` with the ratio `ν`; every
  `ν ≤ directRepaintingRatio K₀ ε₀ = min(ε₀ / max(K₀, 1), 1) / 4` satisfies it
  (`isDirectRepaintingRatio_of_le`), since three labels of a block guide near a footprint meet at
  a grid corner within twice the footprint radius, which is less than the hole radius
  (`IsDisplacedReading.hasTwoOwnerFootprints_blockGuide`); this explicit value replaces the
  compactness minimum of the source;
* hence every sufficiently small `ν > 0` satisfies it (`exists_isDirectRepaintingRatio`), a
  smallness condition on `ν` given `K₀` and `ε₀` of the kind met by `exists_isProtocolConstants`,
  so constants in the source's order exist with this property
  (`exists_isProtocolConstants_isDirectRepaintingRatio`);
* it gives the two-owner hypotheses of the direct repainting
  (`IsDirectRepaintingRatio.hasTwoOwnerFootprints`);
* hence the direct repainting is one gate with the patch bound `b = protocolPatchBound ε₀ ν`,
  with no geometric premise left over, under the separations at `t`
  (`directRepainting_step_of_protocolSeparations`), and so at `t = D log L` for every `L ≥ 2`
  (`IsProtocolConstants.directRepainting_step`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the scales
  `eq:geometry-scales` (lines 102–117), the compactness observation (lines 447–479), the direct
  repainting (lines 507–527), the order of the constants (lines 559–570) and the gate count
  (lines 574–583); Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

open Set Metric

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame TNLean.Lattice.Sheet TNLean.Lattice.PartyCircuit

/-- **An admissible ratio for the direct repaintings.** For every generic displacement `v`, every
level `0 < n ≤ K₀ t` and every reading `g'` after `v` of a guide uniform on the `n`-blocks, `g'`
has the two-owner condition about every grid corner with working set the closed square of radius
`2 n`, holes of radius `h_n` at its true vertices within `3 n`, and footprints of radius `ν n`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 447–479 and 507–527. -/
def IsDirectRepaintingRatio (K₀ ε₀ ν : ℝ) : Prop :=
  ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
    ∀ {κ : Type} {n t : ℝ}, 0 < n → 0 < t → n ≤ K₀ * t →
    ∀ (lab : ℤ × ℤ → κ) (Q : ℤ × ℤ) (g' : ℝ × ℝ → κ),
    IsDisplacedReading g' (blockGuide n lab) v →
    HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (2 * n))
      {c | c ∈ closedBall (blockCorner n Q) (3 * n) ∧ IsTrueVertex g' c}
      (holeRadius ε₀ n t) (ν * n)

/-- **The mesh ratio of the direct repaintings.** The explicit ratio
`ν₃ = min(ε₀ / max(K₀, 1), 1) / 4`, in place of the compactness minimum of the source. Twice the
footprint radius `ν₃ n` is at most half the smallest hole radius `ε₀ n / max(K₀, 1)` of
`eq:geometry-small-radius`, and at most half the side `n`. The bound is crude: it uses only that
three labels of a block guide meet at grid corners.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 447–479, 507–527 and 559–563. -/
noncomputable def directRepaintingRatio (K₀ ε₀ : ℝ) : ℝ := min (ε₀ / max K₀ 1) 1 / 4

/-- The mesh ratio of the direct repaintings is positive.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 559–563. -/
theorem directRepaintingRatio_pos (K₀ : ℝ) {ε₀ : ℝ} (hε : 0 < ε₀) :
    0 < directRepaintingRatio K₀ ε₀ := by
  have : 0 < ε₀ / max K₀ 1 := div_pos hε (lt_of_lt_of_le one_pos (le_max_right _ _))
  unfold directRepaintingRatio
  positivity

/-- **Every ratio up to `directRepaintingRatio K₀ ε₀` is admissible for the direct
repaintings.** Three distinct labels of a reading of a block guide within a footprint come from
three blocks about one grid corner, which is then a true vertex within twice the footprint radius
of a footprint point; that is less than the hole radius `h_n ≥ ε₀ n / max(K₀, 1)`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 447–479 and 507–527. -/
theorem isDirectRepaintingRatio_of_le (K₀ : ℝ) {ε₀ ν : ℝ} (hε : 0 < ε₀)
    (hν : ν ≤ directRepaintingRatio K₀ ε₀) : IsDirectRepaintingRatio K₀ ε₀ ν := by
  intro v _ κ n t hn ht hK lab Q g' hg'
  have hm : 0 < ε₀ / max K₀ 1 := div_pos hε (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hν₁ : ν ≤ ε₀ / max K₀ 1 / 4 :=
    hν.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hν₂ : ν ≤ 1 / 4 := hν.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hr := (le_div_iff₀ hn).1 (holeRadius_div_mem_Icc hε.le hn ht hK).1
  refine hg'.hasTwoOwnerFootprints_blockGuide hn ?_ ?_ ?_
  · intro c w hw hcw htv
    refine ⟨?_, htv⟩
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle c w (blockCorner n Q)]
  · nlinarith
  · nlinarith

/-- **The direct repaintings at the explicit mesh ratio.** The ratio `directRepaintingRatio K₀ ε₀`
is admissible for the direct repaintings.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 447–479, 507–527 and 559–563. -/
theorem isDirectRepaintingRatio_directRepaintingRatio (K₀ : ℝ) {ε₀ : ℝ} (hε : 0 < ε₀) :
    IsDirectRepaintingRatio K₀ ε₀ (directRepaintingRatio K₀ ε₀) :=
  isDirectRepaintingRatio_of_le K₀ hε le_rfl

/-- **Every sufficiently small ratio is admissible.** For `ε₀ > 0` and any `K₀` there is `ν' > 0`
such that every `ν ∈ (0, ν']` is an admissible ratio for the direct repaintings: the ratio of the
compactness observation, since the two-owner condition survives shrinking the footprint. The
threshold `ν' = directRepaintingRatio K₀ ε₀` serves (`isDirectRepaintingRatio_of_le`).

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 464–479, 520–525 and 559–563. -/
theorem exists_isDirectRepaintingRatio (K₀ : ℝ) {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν' > 0, ∀ ν, 0 < ν → ν ≤ ν' → IsDirectRepaintingRatio K₀ ε₀ ν :=
  ⟨directRepaintingRatio K₀ ε₀, directRepaintingRatio_pos K₀ hε,
    fun _ _ hle => isDirectRepaintingRatio_of_le K₀ hε hle⟩

/-- **Constants in the source's order with an admissible ratio.** The constants of the protocol
can be chosen in the source's order so that the mesh parameter `ν` is also an admissible ratio
for the direct repaintings.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 559–570. -/
theorem exists_isProtocolConstants_isDirectRepaintingRatio :
    ∃ K₀ ε₀ ν a D B₀, IsProtocolConstants K₀ ε₀ ν a D B₀ ∧ IsDirectRepaintingRatio K₀ ε₀ ν := by
  obtain ⟨K₀, ε₀, ν, a, D, B₀, hc, -, -, hν, -⟩ :=
    exists_isProtocolConstants (fun _ => True) (fun _ _ => True)
      (fun K₀ ε₀ ν => IsDirectRepaintingRatio K₀ ε₀ ν) (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True) ⟨0, fun _ _ => trivial⟩
      (fun _ => ⟨1, one_pos, fun _ _ _ => trivial⟩)
      (fun K₀ _ hε => exists_isDirectRepaintingRatio K₀ hε)
      (fun _ _ _ _ _ => ⟨1, one_pos, fun _ _ _ => trivial⟩)
      (fun _ _ _ _ _ => ⟨1, one_pos, trivial⟩) (fun _ _ _ _ _ => ⟨0, fun _ _ => trivial⟩)
  exact ⟨K₀, ε₀, ν, a, D, B₀, hc, hν⟩

/-- **The two-owner condition of a direct repainting.** For an admissible ratio `ν`, a level
`0 < n ≤ K₀ t` and a reading `g` after a generic displacement of a guide uniform on the
`n`-blocks, `g` has the two-owner condition about the corner of every block `S` with working set
the closed square of radius `2 n`, holes of radius `h_n` at its true vertices within `3 n`, and
footprints of radius `2 u = ν n` for the patch radius `u = ν n / 2`. This is the hypothesis of
`exists_directRepainting_planeConditions` and of `directRepainting_step`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527. -/
theorem IsDirectRepaintingRatio.hasTwoOwnerFootprints {K₀ ε₀ ν : ℝ}
    (hm : IsDirectRepaintingRatio K₀ ε₀ ν) {v : ℝ × ℝ} (hv : IsGenericDisplacement v) {κ : Type}
    {n t : ℝ} (hn : 0 < n) (ht : 0 < t) (hK : n ≤ K₀ * t) (lab : ℤ × ℤ → κ) (S : ℤ × ℤ)
    {g : ℝ × ℝ → κ} (hg : IsDisplacedReading g (blockGuide n lab) v) :
    HasTwoOwnerFootprints g (closedBall (blockCorner n S) (2 * n))
      {c | c ∈ closedBall (blockCorner n S) (3 * n) ∧ IsTrueVertex g c}
      (holeRadius ε₀ n t) (2 * patchRadius ν n) := by
  rw [two_mul_patchRadius]
  exact hm hv hn ht hK lab S g hg

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

/-- **The direct repainting as one gate at the protocol's radii.** Let `ν` be an admissible ratio
for the direct repaintings and let the separations of the protocol hold at `t`. For a level
`0 < n ≤ K₀ t`, readings `g`, `g'` after a generic displacement of two guides uniform on the
`n`-blocks that differ only on the block `S`, holes of radius `h_n` and patches of radius
`u = ν n / 2`, the conclusion of `directRepainting_step_isSourceBounded` holds with
`b = protocolPatchBound ε₀ ν`,
without the separation, patch-count and two-owner hypotheses.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527, 559–570 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218. -/
theorem directRepainting_step_of_protocolSeparations [NeZero q] {K₀ ε₀ ν B₀ t ℓ : ℝ}
    (hm : IsDirectRepaintingRatio K₀ ε₀ ν) (hs : ProtocolSeparations K₀ ε₀ ν B₀ t ℓ) {n : ℝ}
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
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = patchRadius ν n)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {C c L : ℕ} (hL : 1 ≤ L) (hcardHole : ∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (hole z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (hole z).Tag) :
    ∃ P : Finset Party, P.card ≤ 18 ∧
      (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + S)) ∨ x = own (lab' (R + S))) ∧
      ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V hole hpV).regs
        (guideFrame pos q g' own ph rank V' hole hpV').regs,
      w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
      w.IsExpansionBounded (2 * protocolPatchBound ε₀ ν)
        ((C + 1) ^ (3 * protocolPatchBound ε₀ ν) *
          (16 * protocolPatchBound ε₀ ν ^ 2 * (C + 1) ^ (6 * protocolPatchBound ε₀ ν) + 1) ^
            (2 * protocolPatchBound ε₀ ν) *
          L ^ (3 * protocolPatchBound ε₀ ν * c +
            4 * protocolPatchBound ε₀ ν * (3 * protocolPatchBound ε₀ ν * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * protocolPatchBound ε₀ ν) *
          (16 * protocolPatchBound ε₀ ν ^ 2 * (C + 1) ^ (6 * protocolPatchBound ε₀ ν) + 1) ^
            (2 * protocolPatchBound ε₀ ν) *
          L ^ (3 * protocolPatchBound ε₀ ν * c +
            4 * protocolPatchBound ε₀ ν * (3 * protocolPatchBound ε₀ ν * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g own ph rank V hole hpV).regIso.symm
          ((guideFrame pos q g own ph rank V hole hpV).refVec Ω)) -
        (guideFrame pos q g' own ph rank V' hole hpV').regIso.symm
          ((guideFrame pos q g' own ph rank V' hole hpV').refVec Ω)‖ ≤
        (2 * protocolPatchBound ε₀ ν + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * protocolPatchBound ε₀ ν) := by
  obtain ⟨hr, hu, -, hsep, hb⟩ := hs.direct n hn
  exact directRepainting_step_isSourceBounded hn hr hu hsep hlab hg hg' own ph rank hV hV' hVc
    hVc' hVV' hole
    patch hhole hpatch (hm.hasTwoOwnerFootprints hv hn hs.t_pos hK lab S hg)
    (hm.hasTwoOwnerFootprints hv hn hs.t_pos hK lab' S hg') hpV hpV' hL hcardHole hcardPatch hb
    (by exact_mod_cast hs.eighteen_le) hΩ hεpatch hεhole htag

/-- **The direct repainting as one gate at the constants of the protocol.** For constants chosen
in the source's order with an admissible ratio `ν`, every `L ≥ 2` and `t = D log L`, every direct
repainting at a level `0 < n ≤ K₀ t`, with holes of radius `h_n` and patches of radius
`u = ν n / 2`, is one gate as in `directRepainting_step` with `b = protocolPatchBound ε₀ ν`, with
at most `2 b` pair sources in each monomial.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527, 559–570 and 574–583. -/
theorem IsProtocolConstants.directRepainting_step [NeZero q] {K₀ ε₀ ν a D B₀ : ℝ}
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hm : IsDirectRepaintingRatio K₀ ε₀ ν) {L : ℕ}
    (hL : 2 ≤ L) {n : ℝ} (hn : 0 < n) (hK : n ≤ K₀ * (D * Real.log L)) {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v)
    {lab lab' : ℤ × ℤ → κ} {S : ℤ × ℤ} (hlab : ∀ Q, Q ≠ S → lab' Q = lab Q) {g g' : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v)
    (hg' : IsDisplacedReading g' (blockGuide n lab') v) (own : κ → Party) (ph : κ)
    (rank : κ → ℕ) {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g c)
    (hV' : ∀ c ∈ V', IsTrueVertex g' c)
    (hVc : ∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g c → c ∈ V)
    (hVc' : ∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g' c → c ∈ V')
    (hVV' : ∀ c ∉ squareCorners n S, (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧
      (hole z).scale = holeRadius ε₀ n (D * Real.log L))
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = patchRadius ν n)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {C c : ℕ} (hcardHole : ∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (hole z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (hole z).Tag) :
    ∃ P : Finset Party, P.card ≤ 18 ∧
      (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + S)) ∨ x = own (lab' (R + S))) ∧
      ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V hole hpV).regs
        (guideFrame pos q g' own ph rank V' hole hpV').regs,
      w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
      w.IsExpansionBounded (2 * protocolPatchBound ε₀ ν)
        ((C + 1) ^ (3 * protocolPatchBound ε₀ ν) *
          (16 * protocolPatchBound ε₀ ν ^ 2 * (C + 1) ^ (6 * protocolPatchBound ε₀ ν) + 1) ^
            (2 * protocolPatchBound ε₀ ν) *
          L ^ (3 * protocolPatchBound ε₀ ν * c +
            4 * protocolPatchBound ε₀ ν * (3 * protocolPatchBound ε₀ ν * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * protocolPatchBound ε₀ ν) *
          (16 * protocolPatchBound ε₀ ν ^ 2 * (C + 1) ^ (6 * protocolPatchBound ε₀ ν) + 1) ^
            (2 * protocolPatchBound ε₀ ν) *
          L ^ (3 * protocolPatchBound ε₀ ν * c +
            4 * protocolPatchBound ε₀ ν * (3 * protocolPatchBound ε₀ ν * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g own ph rank V hole hpV).regIso.symm
          ((guideFrame pos q g own ph rank V hole hpV).refVec Ω)) -
        (guideFrame pos q g' own ph rank V' hole hpV').regIso.symm
          ((guideFrame pos q g' own ph rank V' hole hpV').refVec Ω)‖ ≤
        (2 * protocolPatchBound ε₀ ν + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * protocolPatchBound ε₀ ν) := by
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  exact directRepainting_step_of_protocolSeparations hm (hc.protocolSeparations hℓ) hn hK hv
    hlab hg hg' own ph rank hV hV' hVc hVc' hVV' hole patch hhole hpatch hpV hpV'
    (by omega) hcardHole hcardPatch hΩ hεpatch hεhole htag

end TNLean.PEPS.Approximation
