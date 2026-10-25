/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBulkSeparation
import TNLean.PEPS.Approximation.DyadicBulkSteps

/-!
# The bulk changes of the repainting schedule from the plane floors

The step lemmas of `TNLean.PEPS.Approximation.DyadicBulkSteps` ask for the tapering separation
of the raw target `T` from the exterior `E` of a bulk birth, death or lens exchange, as a
separation of site sets. The plane lemmas of `TNLean.PEPS.Approximation.DyadicBulkSeparation`
prove it in the plane, in the coordinates of the repainted block moved to the origin: the floor
`eq:geometry-floor` against the positions of other labels and the outer-hole enlargement at the
true vertices (`06-geometry.tex`, lines 357–373), and the floor against the lens boundary
`∂Y` for the exchange (lines 389–426). This file passes from the plane sets to the site sets
of the encoded frames, with the floor `t = D log L` of `eq:geometry-scales` (line 105) and one
constant `a` below the surviving constant `a₀ / 2` (lines 440–443).

The frames enter only through the description of their sites in the source:

* the raw target lies in the remaining closed changed region (lines 357–358), or, for the
  exchange, the sites of the lens are those placed in the lens (lines 421–423);
* the sites of owners other than `P∘` (other than `C` on either sheet, for the exchange) are
  placed at positions of other labels of the guide (lines 383–385 and 421–423);
* every hole is centered at a true vertex of the guide, with inner radius `h_n ≤ ε₀ t`
  (lines 106 and 368–373), so that its outer square has radius at most `2 ε₀ t`.

Here the guide is the one the plane floors are proved for: the surrounding guide of the change,
homogenized on the treated squares of radius `t` (lines 357–360 and 389–390). Under these, no
separation premise is left: the step lemmas below are conditional only on Proposition 3.4,
through `IsAngularScale`. Identifying the frames of the dyadic protocol with these descriptions
is left to the assembly of Proposition 7.1.

## Main results

* `mem_image_vertexZone_of_mem_outerHoles`: the outer hole sites of a frame whose holes are
  centered at true vertices lie in the vertex zone.
* `bandBirth_step`, `bandDeath_step`: an edge birth or death of the repainting schedule.
* `centralBirth_step`: the central birth.
* `edgeExchange_step`: the lens exchange of an edge.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 102–108 (`eq:geometry-scales`) and 357–445; Lemma 6.5 `lem:birth` and
  Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 396–479; Proposition 3.4 `prop:angular`,
  `02-information.tex`, lines 635–658.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Set EncodedFrame TNLean.Lattice.PartyCircuit
open EuclideanSpace (vecKron)

/-- A point lies in the translate `S + d` exactly when `x - d` lies in `S`. -/
theorem mem_image_add_right_iff {S : Set (ℝ × ℝ)} {d x : ℝ × ℝ} :
    x ∈ (· + d) '' S ↔ x - d ∈ S :=
  ⟨fun ⟨y, hy, he⟩ => by rwa [← he, add_sub_cancel_right],
    fun h => ⟨x - d, h, sub_add_cancel x d⟩⟩

section VertexZone

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type*}

/-- **Outer hole sites lie in the vertex zone.** If every hole of a frame is centered, after
the translation by `-d`, at a true vertex of a guide `g`, with inner radius at most `r`, every
outer hole site is placed within `2 r` of a true vertex of `g`, translated by `d`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:368–373` and `400–405`. -/
theorem mem_image_vertexZone_of_mem_outerHoles {κ : Type*} (F : Frame pos q Party)
    {g : ℝ × ℝ → κ} {r : ℝ} {d : ℝ × ℝ}
    (hholes : ∀ h ∈ F.holes, IsTrueVertex g (h.patch.center - d) ∧ h.patch.scale ≤ r)
    {x : ι} (hx : x ∈ F.outerHoles) : pos x ∈ (· + d) '' vertexZone g (2 * r) := by
  obtain ⟨p, hp, hxp⟩ := hx
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hp
  refine mem_image_add_right_iff.2 ⟨_, (hholes h hh).1, ?_⟩
  rw [dist_sub_right]
  have hxp' := hxp
  simp only [SquarePatch.outer, squareSample, Finset.mem_filter, Finset.mem_univ,
    true_and] at hxp'
  linarith [(hholes h hh).2]

end VertexZone

variable {q : ℕ} [NeZero q] {a A₀ D L₀ : ℝ} {m₀ : ℕ} {L : ℕ}
  {G : ∀ L : ℕ, StateSpace L q → Prop} {Ω : StateSpace L q}
  {pos : SquareLatticeVertex L L → ℝ × ℝ} {c : ℝ × ℝ} {Party : Type} {κ : Type*}

/-- The marked points of an edge operation, translated, number at most two. -/
private theorem card_edgeMarks_le (n : ℝ) (e : SquareEdge) (d : ℝ × ℝ) :
    (({e.point n 0 0, e.point n n 0} : Finset (ℝ × ℝ)).image (· + d)).card ≤ 2 :=
  Finset.card_image_le.trans (Finset.card_le_two)

/-- The four corners, translated, number at most four. -/
private theorem card_cornerMarks_le (n : ℝ) (d : ℝ × ℝ) :
    (({(0, 0), (n, 0), (0, n), (n, n)} : Finset (ℝ × ℝ)).image (· + d)).card ≤ 4 :=
  Finset.card_image_le.trans (Finset.card_le_four)

omit [NeZero q] in
/-- The separation premise of a birth or death from the plane separation of the remaining
changed region `X` from the other labels and the vertex zone `Z`. -/
private theorem angularSeparation_birthEnv {F : Frame pos q Party} {T : Finset _} {P : Party}
    {X Z : Set (ℝ × ℝ)} {G : ℝ × ℝ → κ} {l : κ} {n t a' : ℝ} {d : ℝ × ℝ}
    {V : Finset (ℝ × ℝ)}
    (hsep : AngularSeparation ((· + d) '' X) ((· + d) '' ({z | G z ≠ l} ∪ Z)) n t a' V)
    (ht : 0 ≤ t) (ha : a ≤ a') (hT : ∀ x ∈ T, pos x - d ∈ X)
    (hown : ∀ x, F.owner x ≠ P → G (pos x - d) ≠ l)
    (hhole : ∀ x ∈ F.outerHoles, pos x ∈ (· + d) '' Z) :
    AngularSeparation (pos '' T) (pos '' F.birthEnv P) n t a V := by
  refine ((hsep.mono_left ?_).mono_right ?_).mono_const ht ha
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_image_add_right_iff.2 (hT x hx)
  · rintro _ ⟨x, hx, rfl⟩
    rcases (F.mem_birthEnv).1 hx with hx | hx
    · exact mem_image_add_right_iff.2 (Or.inl (hown x hx))
    · obtain ⟨y, hy, he⟩ := hhole x hx
      exact ⟨y, Or.inr hy, he⟩

/-- **An edge birth from the plane floors, conditional on Proposition 3.4.** Let `D`, `L₀` be a
slope and a threshold for Proposition 3.4 at accuracy `L^{-60}` with constants `a`, `A₀`,
`m₀ ≥ 2`, with `a ≤ a₀ / 2`, and let `L ≥ L₀` and `t = D log L` with `0 ≤ t ≤ n ≤ A₀ L`. Let
`G` be the surrounding guide of an elementary edge operation, homogenized on the treated squares
of radius `t`, and let the block be placed at translation `d`. In an encoded frame `F` over the
sites of the open square, let `T` be a set of raw sites owned by `P∘`, outside every outer hole,
of diameter at most `A₀ n`, placed in the remaining closed changed region. If the other owners
are placed at the other labels of `G` and every hole is centered at a true vertex of `G` with
inner radius at most `ε₀ t`, where `2 ε₀ ≤ a₀ / 2`, then the birth of `T` at `Q∘` is an
allowed word using only `P∘` and `Q∘`, with at most one pair source and error `L^{-30}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:102–108`, `357–387` and
`440–445`. -/
theorem bandBirth_step (hD : IsAngularScale q G a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hm₀ : 2 ≤ m₀) (ha : a ≤ angularConstant / 2) (op : BandOperation κ) (e : SquareEdge)
    (g : ℝ × ℝ → κ) (d : ℝ × ℝ) {n ε₀ : ℝ} (ht : 0 ≤ D * Real.log L)
    (htn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L) (hε : 2 * ε₀ ≤ angularConstant / 2)
    (F : Frame pos q Party) {T : Finset (SquareLatticeVertex L L)} {P Q : Party}
    (hTP : ∀ x ∈ T, F.owner x = P) (hTH : Disjoint (T : Set _) F.outerHoles)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * n)
    (hT : ∀ x ∈ T, pos x - d ∈ closure {p |
      homogenize (edgeTreated n e (D * Real.log L)) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e (D * Real.log L)) op.label (bandUpdate n e op.after g) p})
    (hown : ∀ x, F.owner x ≠ P → homogenize (edgeTreated n e (D * Real.log L)) op.label
      (bandUpdate n e op.surrounding g) (pos x - d) ≠ op.label)
    (hholes : ∀ hl ∈ F.holes, IsTrueVertex (homogenize (edgeTreated n e (D * Real.log L))
      op.label (bandUpdate n e op.surrounding g)) (hl.patch.center - d) ∧
        hl.patch.scale ≤ ε₀ * (D * Real.log L)) :
    ∃ w : Word F.regs (F.changeOwner T Q).regs,
      w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
      ‖w.eval (F.regIso.symm (F.refVec Ω)) -
        (F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)‖ ≤
          (L : ℝ) ^ (-30 : ℤ) :=
  bulkBirth_step hD hL hΩ hΩ₁ hpos F hTP hTH ((card_edgeMarks_le n e d).trans hm₀) htn hnL hdiam
    (angularSeparation_birthEnv (op.angularSeparation_bandUpdate ht htn hε e g d) ht ha hT hown
      fun _ hx => mem_image_vertexZone_of_mem_outerHoles F hholes hx)

/-- **An edge death from the plane floors, conditional on Proposition 3.4.** In the setting of
`bandBirth_step`, with `F` the frame after the death, in which `T` is owned by `P∘`, the death
from the frame in which `T` is owned by `Q∘` is an allowed monomial using only `P∘` and `Q∘`,
without pair sources, with at most one pair effect and error `L^{-30}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:102–108`, `357–387` and
`440–445`. -/
theorem bandDeath_step (hD : IsAngularScale q G a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hm₀ : 2 ≤ m₀) (ha : a ≤ angularConstant / 2) (op : BandOperation κ) (e : SquareEdge)
    (g : ℝ × ℝ → κ) (d : ℝ × ℝ) {n ε₀ : ℝ} (ht : 0 ≤ D * Real.log L)
    (htn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L) (hε : 2 * ε₀ ≤ angularConstant / 2)
    (F : Frame pos q Party) {T : Finset (SquareLatticeVertex L L)} {P Q : Party}
    (hTP : ∀ x ∈ T, F.owner x = P) (hTH : Disjoint (T : Set _) F.outerHoles)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * n)
    (hT : ∀ x ∈ T, pos x - d ∈ closure {p |
      homogenize (edgeTreated n e (D * Real.log L)) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e (D * Real.log L)) op.label (bandUpdate n e op.after g) p})
    (hown : ∀ x, F.owner x ≠ P → homogenize (edgeTreated n e (D * Real.log L)) op.label
      (bandUpdate n e op.surrounding g) (pos x - d) ≠ op.label)
    (hholes : ∀ hl ∈ F.holes, IsTrueVertex (homogenize (edgeTreated n e (D * Real.log L))
      op.label (bandUpdate n e op.surrounding g)) (hl.patch.center - d) ∧
        hl.patch.scale ≤ ε₀ * (D * Real.log L)) :
    ∃ M : PartyChain (F.changeOwner T Q).regs F.regs,
      M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧ M.toEffectChain.effectCount ≤ 1 ∧
      ‖M.toEffectChain.eval ((F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)) -
        F.regIso.symm (F.refVec Ω)‖ ≤ (L : ℝ) ^ (-30 : ℤ) :=
  bulkDeath_step hD hL hΩ hΩ₁ hpos F hTP hTH ((card_edgeMarks_le n e d).trans hm₀) htn hnL hdiam
    (angularSeparation_birthEnv (op.angularSeparation_bandUpdate ht htn hε e g d) ht ha hT hown
      fun _ hx => mem_image_vertexZone_of_mem_outerHoles F hholes hx)

/-- **The central birth from the plane floors, conditional on Proposition 3.4.** In the setting
of `bandBirth_step`, with `m₀ ≥ 4`, let `G` be the starting guide of the repainting of an
`n`-square, homogenized to the old label on the treated squares of radius `t` about the four
corners. If the raw target `T` is placed in the remaining closed changed region of the central
birth, the other owners at the labels of `G` other than the old label, and every hole is
centered at a true vertex of `G` with inner radius at most `ε₀ t`, then the birth of `T` at
`Q∘` is an allowed word using only `P∘` and `Q∘`, with at most one pair source and error
`L^{-30}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160`, `102–108`,
`357–387` and `440–445`. -/
theorem centralBirth_step (hD : IsAngularScale q G a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hm₀ : 4 ≤ m₀) (ha : a ≤ angularConstant / 2) (R : RepaintingBaseline κ) (d : ℝ × ℝ)
    {ε₀ : ℝ} (ht : 0 ≤ D * Real.log L) (htn : D * Real.log L ≤ R.n) (hnL : R.n ≤ A₀ * L)
    (hε : 2 * ε₀ ≤ angularConstant / 2)
    (F : Frame pos q Party) {T : Finset (SquareLatticeVertex L L)} {P Q : Party}
    (hTP : ∀ x ∈ T, F.owner x = P) (hTH : Disjoint (T : Set _) F.outerHoles)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * R.n)
    (hT : ∀ x ∈ T, pos x - d ∈ closure {p |
      homogenize (cornerTreated R.n (D * Real.log L)) R.oldLabel R.guide p ≠
        homogenize (cornerTreated R.n (D * Real.log L)) R.oldLabel R.centralGuide p})
    (hown : ∀ x, F.owner x ≠ P →
      homogenize (cornerTreated R.n (D * Real.log L)) R.oldLabel R.guide (pos x - d) ≠
        R.oldLabel)
    (hholes : ∀ hl ∈ F.holes,
      IsTrueVertex (homogenize (cornerTreated R.n (D * Real.log L)) R.oldLabel R.guide)
        (hl.patch.center - d) ∧ hl.patch.scale ≤ ε₀ * (D * Real.log L)) :
    ∃ w : Word F.regs (F.changeOwner T Q).regs,
      w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
      ‖w.eval (F.regIso.symm (F.refVec Ω)) -
        (F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)‖ ≤
          (L : ℝ) ^ (-30 : ℤ) :=
  bulkBirth_step hD hL hΩ hΩ₁ hpos F hTP hTH ((card_cornerMarks_le R.n d).trans hm₀) htn hnL hdiam
    (angularSeparation_birthEnv (R.angularSeparation_central ht htn hε d) ht ha hT hown
      fun _ hx => mem_image_vertexZone_of_mem_outerHoles F hholes hx)

/-- **The lens exchange of an edge from the plane floors, conditional on Proposition 3.4.** In
the setting of `bandBirth_step`, with `0 < t`, let `G₁` and `G₂` be the main guide at the start
of the edge operation and the auxiliary guide, both homogenized to `C_e` on the treated squares
of radius `t`, where `2 ε₀ (a₀ + 1) ≤ a₀ / 2`. Let `F₁`, `F₂` be the frames of the two sheets
and `Y` the sites placed in the lens, translated by `d`, with every hole classified as outside
or inside `Y`. If the sites not held by `C` on the first (second) sheet are placed at labels of
`G₁` (`G₂`) other than `C_e`, every hole of `F₁` (`F₂`) is centered at a true vertex of `G₁`
(`G₂`) with inner radius at most `ε₀ t`, and the target `T` of `eq:exchange-partition` has
diameter at most `A₀ n`, the exchange is an allowed word using only `C`, without pair resources,
with error at most `4 L^{-30}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:102–108`, `389–430` and
`440–445`. -/
theorem edgeExchange_step (hD : IsAngularScale q G a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hm₀ : 2 ≤ m₀) (ha : a ≤ angularConstant / 2) (R : RepaintingBaseline κ)
    (E : List SquareEdge) (e : SquareEdge) (d : ℝ × ℝ) {ε₀ : ℝ} (ht : 0 < D * Real.log L)
    (htn : D * Real.log L ≤ R.n) (hnL : R.n ≤ A₀ * L)
    (hε : 2 * ε₀ * (angularConstant + 1) ≤ angularConstant / 2)
    (F₁ F₂ : Frame pos q Party) (Y : Finset (SquareLatticeVertex L L))
    (hY : ∀ x, x ∈ Y ↔ pos x - d ∈ edgeLens R.n e)
    (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ F₁.holes ++ F₂.holes, out h = true →
      Disjoint (h.patch.outer : Set (SquareLatticeVertex L L)) Y)
    (hin : ∀ h ∈ F₁.holes ++ F₂.holes, out h = false →
      (h.patch.outer : Set (SquareLatticeVertex L L)) ⊆ Y)
    (C : Party)
    (hdiam : ∀ x ∈ (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).tSet C,
      ∀ y ∈ (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).tSet C,
        dist (pos x) (pos y) ≤ A₀ * R.n)
    (hown₁ : ∀ x, F₁.owner x ≠ C →
      homogenize (edgeTreated R.n e (D * Real.log L)) (R.nbrLabel e)
        (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e))) (pos x - d) ≠
        R.nbrLabel e)
    (hown₂ : ∀ x, F₂.owner x ≠ C →
      homogenize (edgeTreated R.n e (D * Real.log L)) (R.nbrLabel e)
        (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e))) (pos x - d) ≠
        R.nbrLabel e)
    (hholes₁ : ∀ hl ∈ F₁.holes,
      IsTrueVertex (homogenize (edgeTreated R.n e (D * Real.log L)) (R.nbrLabel e)
        (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e))))
        (hl.patch.center - d) ∧ hl.patch.scale ≤ ε₀ * (D * Real.log L))
    (hholes₂ : ∀ hl ∈ F₂.holes,
      IsTrueVertex (homogenize (edgeTreated R.n e (D * Real.log L)) (R.nbrLabel e)
        (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e))))
        (hl.patch.center - d) ∧ hl.patch.scale ≤ ε₀ * (D * Real.log L)) :
    ∃ w : Word (F₁.regs ++ F₂.regs)
        ((TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).newFrame₁.regs ++
          (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).newFrame₂.regs),
      w.IsAllowed ∧ w.UsesOnly {C} ∧ w.sourceCount = 0 ∧
      ‖w.eval ((twoLayoutIso _ _ F₁.owner F₂.owner).symm
          (vecKron (F₁.refVec Ω) (F₂.refVec Ω))) -
        (twoLayoutIso _ _ (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).newFrame₁.owner
            (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).newFrame₂.owner).symm
          (vecKron ((TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).newFrame₁.refVec Ω)
            ((TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).newFrame₂.refVec Ω))‖ ≤
        4 * (L : ℝ) ^ (-30 : ℤ) := by
  have hfl := R.floor_exchange_frontier ht htn hε E e d
  refine lensExchange_step_of_frontier hD hL hΩ hΩ₁ hpos F₁ F₂ Y out hout hin C
    (K := (· + d) '' edgeLens R.n e) (fun x => (hY x).trans mem_image_add_right_iff.symm)
    ((card_edgeMarks_le R.n e d).trans hm₀) htn hnL hdiam fun x hx z hz => ?_
  refine (mul_le_mul_of_nonneg_right ha (ht.le.trans (le_max_left _ _))).trans
    (hfl (pos x) ?_ z hz)
  have hZ := (Finset.mem_inter.1 hx).1
  rw [TwoSheetExchange.mem_ofFrames_exchangeEnv] at hZ
  have h2 : (2 : ℝ) * ε₀ * (D * Real.log L) = 2 * (ε₀ * (D * Real.log L)) := mul_assoc _ _ _
  rcases hZ with hZ | hZ | hZ
  · refine mem_image_add_right_iff.2 (Or.inl (Or.inl (subset_closure ?_)))
    by_cases h₁ : F₁.owner x = C
    · exact Or.inr (hown₂ x fun h₂ => hZ ⟨h₁, h₂⟩)
    · exact Or.inl (hown₁ x h₁)
  · obtain ⟨y, hy, he⟩ := mem_image_vertexZone_of_mem_outerHoles F₁ hholes₁ hZ
    exact ⟨y, Or.inl (Or.inr (h2 ▸ hy)), he⟩
  · obtain ⟨y, hy, he⟩ := mem_image_vertexZone_of_mem_outerHoles F₂ hholes₂ hZ
    exact ⟨y, Or.inr (h2 ▸ hy), he⟩

end TNLean.PEPS.Approximation
