/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularInformationBound
import TNLean.PEPS.Approximation.FrameBoundedChanges

/-!
# Bulk births, deaths and the lens exchange, conditional on Proposition 3.4

In the proof of Proposition 7.1 (`prop:protocol`), every bulk birth, death and lens exchange of
the dyadic repainting schedule is implemented by Lemma 6.5 (`lem:birth`) or Lemma 6.6
(`lem:exchange`). Both lemmas ask for `I_Ω(T : E) ≤ L^{-60}`, where `T` is the raw target and
`E` the exterior of the change, and Proposition 3.4 (`prop:angular`) supplies this bound from
the tapering separation of `T` from `E` (`06-geometry.tex`, lines 357–445). This file combines
the two: given a slope `D` and a threshold `L₀` for Proposition 3.4 at accuracy `L^{-60}`, each
bulk change whose target satisfies the tapering separation is a bounded change with
reference-vector error `L^{-30}` (birth and death) or `4 L^{-30}` (exchange).

The sites are the sites of the open square, placed at a common translation of `Λ_L`, such as the
cell centers of Section 7. Proposition 3.4 enters only through `IsAngularScale`, which
`AngularInformationBound.exists_isAngularScale` derives from it; the step lemmas are therefore
conditional on Proposition 3.4 and do not prove it. The state is any unit vector of a family
of states `G` for which the angular scale holds; the ground vectors of the model are the family
`IsSquareGroundState q J Δ`.

## Main results

* `bulkBirth_step`: a bulk birth is an allowed word using only `P∘` and `Q∘`, with at most one
  pair source and error `L^{-30}`.
* `bulkDeath_step`: a bulk death is an allowed monomial using only `P∘` and `Q∘`, without pair
  sources, with at most one pair effect and error `L^{-30}`.
* `lensExchange_step`: a lens exchange is an allowed word using only `C`, without pair resources,
  with error `4 L^{-30}`.
* `lensExchange_step_of_frontier`: the same, with the tapering separation checked against the
  boundary of the lens, as in `06-geometry.tex`, lines 418–426.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 357–445; Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–447;
  Lemma 6.6 `lem:exchange`, lines 460–561; Proposition 3.4 `prop:angular`, `02-information.tex`,
  lines 635–658.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Set EncodedFrame TNLean.Lattice.PartyCircuit
open EuclideanSpace (vecKron)

variable {q : ℕ} [NeZero q] {a A₀ D L₀ : ℝ} {m₀ : ℕ} {L : ℕ}
  {G : ∀ L : ℕ, StateSpace L q → Prop} {Ω : StateSpace L q}
  {pos : SquareLatticeVertex L L → ℝ × ℝ} {c : ℝ × ℝ} {Party : Type}
  {V : Finset (ℝ × ℝ)} {n : ℝ}

omit [NeZero q] in
/-- The information premise of Lemmas 6.5 and 6.6 from Proposition 3.4. -/
private theorem mutualInformation_le_of_isAngularScale
    (hD : IsAngularScale q G a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : G L Ω) (hpos : ∀ v, pos v = sitePosition L v + c)
    (hV : V.card ≤ m₀) {T E : Finset (SquareLatticeVertex L L)} (hTE : Disjoint T E)
    (hn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * n)
    (hsep : AngularSeparation (pos '' T) (pos '' E) n (D * Real.log L) a V) :
    FiniteProduct.mutualInformation (fun _ : SquareLatticeVertex L L ↦ Fin q) Ω T E ≤
      (L : ℝ) ^ (-60 : ℤ) := by
  simpa using hD L hL Ω hΩ pos c hpos V hV T E hTE n hn hnL hdiam hsep

/-- **Bulk birth, conditional on Proposition 3.4.** Let `D`, `L₀` be a slope and a threshold for
Proposition 3.4 at accuracy `L^{-60}` with constants `a`, `A₀`, `m₀`, and let `L ≥ L₀`. In an
encoded frame `F` over the sites of the open square, placed at a common translation of `Λ_L`,
let `T` be a set of raw sites owned by `P∘` and outside every outer hole. If `T` has diameter at
most `A₀ n` for a scale `D log L ≤ n ≤ A₀ L`, and every point of `T` is separated from the
exterior `E` of `eq:birth-partition` (the sites of other owners and all outer hole sites) by
`a max{D log L, min(n, d_V)}` for at most `m₀` marked points `V`, then the birth of `T` at `Q∘`
is an allowed word using only `P∘` and `Q∘`, with at most one pair source and reference-vector
error at most `L^{-30}`.

Source: `06-geometry.tex`, lines 357–387 and 440–445, applying Lemma 6.5 `lem:birth`
(`05-frames.tex`, lines 396–407) with Proposition 3.4 at accuracy `L^{-60}`. -/
theorem bulkBirth_step (hD : IsAngularScale q G a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hpos : ∀ v, pos v = sitePosition L v + c)
    (F : Frame pos q Party) {T : Finset (SquareLatticeVertex L L)} {P Q : Party}
    (hTP : ∀ x ∈ T, F.owner x = P) (hTH : Disjoint (T : Set _) F.outerHoles)
    (hV : V.card ≤ m₀) (hn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * n)
    (hsep : AngularSeparation (pos '' T) (pos '' F.birthEnv P) n (D * Real.log L) a V) :
    ∃ w : Word F.regs (F.changeOwner T Q).regs,
      w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
      ‖w.eval (F.regIso.symm (F.refVec Ω)) -
        (F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)‖ ≤
          (L : ℝ) ^ (-30 : ℤ) := by
  obtain ⟨-, -, -, w, hA, hU, hS, -, herr⟩ := F.birth_bounded (Q := Q) hTP hTH hΩ₁
    (mutualInformation_le_of_isAngularScale hD hL hΩ hpos hV (F.disjoint_birthEnv hTP hTH) hn
      hnL hdiam hsep)
  exact ⟨w, hA, hU, hS, herr⟩

/-- **Bulk death, conditional on Proposition 3.4.** In the setting of `bulkBirth_step`, with `F`
the frame after the death, in which `T` is owned by `P∘`, the death from the frame in which `T`
is owned by `Q∘` is an allowed monomial using only `P∘` and `Q∘`, without pair sources, with at
most one pair effect and reference-vector error at most `L^{-30}`.

Source: `06-geometry.tex`, lines 357–387 and 440–445, applying the reverse form of Lemma 6.5
`lem:birth` (`05-frames.tex`, lines 407–410) with Proposition 3.4 at accuracy `L^{-60}`. -/
theorem bulkDeath_step (hD : IsAngularScale q G a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hpos : ∀ v, pos v = sitePosition L v + c)
    (F : Frame pos q Party) {T : Finset (SquareLatticeVertex L L)} {P Q : Party}
    (hTP : ∀ x ∈ T, F.owner x = P) (hTH : Disjoint (T : Set _) F.outerHoles)
    (hV : V.card ≤ m₀) (hn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L)
    (hdiam : ∀ x ∈ T, ∀ y ∈ T, dist (pos x) (pos y) ≤ A₀ * n)
    (hsep : AngularSeparation (pos '' T) (pos '' F.birthEnv P) n (D * Real.log L) a V) :
    ∃ M : PartyChain (F.changeOwner T Q).regs F.regs,
      M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧ M.toEffectChain.effectCount ≤ 1 ∧
      ‖M.toEffectChain.eval ((F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)) -
        F.regIso.symm (F.refVec Ω)‖ ≤ (L : ℝ) ^ (-30 : ℤ) := by
  obtain ⟨-, -, -, M, hA, hU, hS, hE, -, herr⟩ := F.death_bounded (Q := Q) hTP hTH hΩ₁
    (mutualInformation_le_of_isAngularScale hD hL hΩ hpos hV (F.disjoint_birthEnv hTP hTH) hn
      hnL hdiam hsep)
  exact ⟨M, hA, hU, hS, hE, herr⟩

/-- **Lens exchange, conditional on Proposition 3.4.** In the setting of `bulkBirth_step`, let
`F₁`, `F₂` be two encoded frames and `Y` the physical sample of the lens, with every hole of
either frame classified as outside `Y` or inside it. Let `T` and `E` be the sites inside and
outside `Y` that are not common to `C` on both sheets or lie in an outer hole of either frame
(`eq:exchange-partition`). If `T` has diameter at most `A₀ n` and is separated from `E` by
`a max{D log L, min(n, d_V)}`, the exchange is an allowed word using only `C`, without pair
resources, with reference-vector error at most `4 L^{-30}`.

Source: `06-geometry.tex`, lines 389–430 and 440–445, applying Lemma 6.6 `lem:exchange`
(`05-frames.tex`, lines 460–479) with Proposition 3.4 at accuracy `L^{-60}`. -/
theorem lensExchange_step (hD : IsAngularScale q G a A₀ m₀ 60 D L₀) (hL : L₀ ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hpos : ∀ v, pos v = sitePosition L v + c)
    (F₁ F₂ : Frame pos q Party) (Y : Finset (SquareLatticeVertex L L))
    (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ F₁.holes ++ F₂.holes, out h = true →
      Disjoint (h.patch.outer : Set (SquareLatticeVertex L L)) Y)
    (hin : ∀ h ∈ F₁.holes ++ F₂.holes, out h = false →
      (h.patch.outer : Set (SquareLatticeVertex L L)) ⊆ Y)
    (C : Party) (hV : V.card ≤ m₀) (hn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L)
    (hdiam : ∀ x ∈ (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).tSet C,
      ∀ y ∈ (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).tSet C,
        dist (pos x) (pos y) ≤ A₀ * n)
    (hsep : AngularSeparation (pos '' (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).tSet C)
      (pos '' (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).eSet C) n (D * Real.log L) a V) :
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
  obtain ⟨-, -, -, -, -, -, -, w, hA, hU, hS, -, herr⟩ :=
    TwoSheetExchange.exchange_ofFrames_bounded F₁ F₂ Y out hout hin C hΩ₁
      (mutualInformation_le_of_isAngularScale hD hL hΩ hpos hV
        ((TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).disjoint_tSet_eSet C) hn hnL hdiam
        hsep)
  exact ⟨w, hA, hU, hS, herr⟩

/-- **Lens exchange from a floor against the lens boundary, conditional on Proposition 3.4.** In
the setting of `lensExchange_step`, let the sites of `Y` be exactly those placed in a plane set
`K`. If every point of the target `T` satisfies the floor `a max{D log L, min(n, d_V)}` against
every point of the boundary of `K`, then the target is separated from the exterior: any segment
from a point of `T` to a point of `E` crosses the boundary. The exchange is then an allowed word
using only `C`, without pair resources, with reference-vector error at most `4 L^{-30}`.

Source: `06-geometry.tex`, lines 389–430 and 440–445. -/
theorem lensExchange_step_of_frontier (hD : IsAngularScale q G a A₀ m₀ 60 D L₀)
    (hL : L₀ ≤ L) (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hpos : ∀ v, pos v = sitePosition L v + c)
    (F₁ F₂ : Frame pos q Party) (Y : Finset (SquareLatticeVertex L L))
    (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ F₁.holes ++ F₂.holes, out h = true →
      Disjoint (h.patch.outer : Set (SquareLatticeVertex L L)) Y)
    (hin : ∀ h ∈ F₁.holes ++ F₂.holes, out h = false →
      (h.patch.outer : Set (SquareLatticeVertex L L)) ⊆ Y)
    (C : Party) {K : Set (ℝ × ℝ)} (hY : ∀ x, x ∈ Y ↔ pos x ∈ K)
    (hV : V.card ≤ m₀) (hn : D * Real.log L ≤ n) (hnL : n ≤ A₀ * L)
    (hdiam : ∀ x ∈ (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).tSet C,
      ∀ y ∈ (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).tSet C,
        dist (pos x) (pos y) ≤ A₀ * n)
    (hfloor : ∀ x ∈ (TwoSheetExchange.ofFrames F₁ F₂ Y out hout hin).tSet C,
      ∀ z ∈ frontier K, a * max (D * Real.log L) (cappedMarkDistance n V (pos x)) ≤
        dist (pos x) z) :
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
  refine lensExchange_step hD hL hΩ hΩ₁ hpos F₁ F₂ Y out hout hin C hV hn hnL hdiam
    (angularSeparation_of_frontier (K := K) (Or.inl ⟨?_, ?_⟩) ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact (hY x).1 (Finset.mem_inter.1 hx).2
  · rintro _ ⟨x, hx, rfl⟩ hxK
    exact (Finset.mem_sdiff.1 hx).2 ((hY x).2 hxK)
  · rintro _ ⟨x, hx, rfl⟩ z hz
    exact hfloor x hx z hz

end TNLean.PEPS.Approximation
