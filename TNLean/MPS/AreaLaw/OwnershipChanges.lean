/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.FrameBoundedChanges

/-!
# Ownership changes in plain sheets

A mutual-information bound `I(T:E) ≤ L^(-2p)` gives a birth or death with
reference-vector error at most `L^(-p)`. The same hypothesis for the two-sheet
exchange gives error at most `4 * L^(-p)`. The statements retain the constructed
maps, their exact coordinate actions and their shared-resource counts.

The environment for a death is computed after the death. For an exchange, the
ownership assignments are interchanged inside the chosen set and retained outside it.
No interval-shape or geometric separation assumption is needed for these local results.

Source: the one-dimensional note, `part2b_mps_protocol.tex`, Lemmas `lem:birth`
and `lem:exchange`, lines 69–96 and 110–154. The proofs specialize the ownership
constructions at size parameter `L^(p/30)`; the site set is unchanged.
-/

open Matrix EuclideanSpace
open TNLean.PEPS.EncodedFrame TNLean.PEPS.PairEffect
open scoped InnerProductSpace Kronecker

namespace TNLean.MPS.AreaLaw

private lemma ownership_information_power (L : ℕ) (p : ℝ) :
    ((L : ℝ) ^ (p / 30)) ^ (-60 : ℤ) = (L : ℝ) ^ (-(2 * p)) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg L)]
  congr 1
  ring

private lemma ownership_error_power (L : ℕ) (p : ℝ) :
    ((L : ℝ) ^ (p / 30)) ^ (-30 : ℤ) = (L : ℝ) ^ (-p) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg L)]
  congr 1
  ring

variable {L q : ℕ} [NeZero q] {Party : Type} {pos : Fin L → ℝ × ℝ}

/-- Birth changing the owner of `T` from `P` to `Q`, with error at most `L^(-p)`.
TNLean note, part2b_mps_protocol.tex, Lemma lem:birth, lines 69–96. -/
theorem birth_bounded_rpow
    (own : Fin L → Party) (T : Finset (Fin L)) (P Q : Party)
    (hTP : ∀ x ∈ T, own x = P)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) (p : ℝ) :
    let F : Frame pos q Party := Frame.raw own
    let G : Frame pos q Party := Frame.raw (fun x ↦ if x ∈ T then Q else own x)
    let hTH : Disjoint (T : Set (Fin L)) F.outerHoles := by
      simp [F, Frame.raw, Frame.outerHoles, Frame.patches, footprint]
    let hTE : Disjoint T (F.birthEnv P) := F.disjoint_birthEnv hTP hTH
    FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω T (F.birthEnv P) ≤
        (L : ℝ) ^ (-(2 * p)) →
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error hTE Ω ≤ (L : ℝ) ^ (-p) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp hTE σ) * F.encoder = G.encoder * sheetBirthOp hTE σ ∧
      ∃ w : Word F.regs G.regs,
        w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
        (∀ z, G.regIso (w.eval z) =
          act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            sheetBirthOp hTE σ) (F.regIso z)) ∧
        ‖w.eval (F.regIso.symm (F.refVec Ω)) -
          G.regIso.symm (G.refVec Ω)‖ ≤ (L : ℝ) ^ (-p) := by
  intro F G hTH hTE hI
  convert F.birth_bounded (Q := Q) hTP hTH hΩ
    (L := (L : ℝ) ^ (p / 30)) (by simpa only [ownership_information_power] using hI) using 1
  rw [ownership_error_power]
  rfl

/-- Death returning `T` from `Q` to `P`, with its information condition after the death.
The input frame is obtained from the after-death assignment by changing `T` to `Q`.
TNLean note, part2b_mps_protocol.tex, Lemma lem:birth, lines 69–96. -/
theorem death_bounded_rpow
    (own : Fin L → Party) (T : Finset (Fin L)) (P Q : Party)
    (hTP : ∀ x ∈ T, own x = P)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) (p : ℝ) :
    let F : Frame pos q Party := Frame.raw own
    let G : Frame pos q Party := F.changeOwner T Q
    let hTH : Disjoint (T : Set (Fin L)) F.outerHoles := by
      simp [F, Frame.raw, Frame.outerHoles, Frame.patches, footprint]
    let hTE : Disjoint T (F.birthEnv P) := F.disjoint_birthEnv hTP hTH
    FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω T (F.birthEnv P) ≤
        (L : ℝ) ^ (-(2 * p)) →
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error hTE Ω ≤ (L : ℝ) ^ (-p) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp hTE σ) * G.encoder = F.encoder * sheetBirthOp hTE σ ∧
      ∃ M : PartyChain G.regs F.regs,
        M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧
        M.toEffectChain.effectCount ≤ 1 ∧
        (∀ z, F.regIso (M.toEffectChain.eval z) =
          act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            sheetBirthOp hTE σ) (G.regIso z)) ∧
        ‖M.toEffectChain.eval (G.regIso.symm (G.refVec Ω)) -
          F.regIso.symm (F.refVec Ω)‖ ≤ (L : ℝ) ^ (-p) := by
  intro F G hTH hTE hI
  simpa only [ownership_error_power] using F.death_bounded (Q := Q) hTP hTH hΩ
    (L := (L : ℝ) ^ (p / 30)) (by simpa only [ownership_information_power] using hI)

/-- Exchange of two plain ownership assignments inside `Y`, with error at most `4 * L^(-p)`.
The constructed map uses only private contractions at `P` and register relabelling.
TNLean note, part2b_mps_protocol.tex, Lemma lem:exchange, lines 110–154. -/
theorem exchange_bounded_rpow
    (own₁ own₂ : Fin L → Party) (Y : Finset (Fin L)) (P : Party)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) (p : ℝ) :
    let F₁ : Frame pos q Party := Frame.raw own₁
    let F₂ : Frame pos q Party := Frame.raw own₂
    let G₁ : Frame pos q Party :=
      Frame.raw (fun x ↦ if x ∈ Y then own₂ x else own₁ x)
    let G₂ : Frame pos q Party :=
      Frame.raw (fun x ↦ if x ∈ Y then own₁ x else own₂ x)
    let X : TwoSheetExchange pos q Party :=
      TwoSheetExchange.ofFrames F₁ F₂ Y (fun _ ↦ true)
        (by intro h hh; simp [F₁, F₂, Frame.raw] at hh)
        (by intro h hh; simp [F₁, F₂, Frame.raw] at hh)
    FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω (X.tSet P) (X.eSet P) ≤
        (L : ℝ) ^ (-(2 * p)) →
    ∃ σ : SplittingData q (X.tSet P) (X.eSet P),
      σ.error (X.disjoint_tSet_eSet P) Ω ≤ (L : ℝ) ^ (-p) ∧
      X.exchangeOp P σ *
          (F₁.encoder ⊗ₖ F₂.encoder : Matrix (X.frame₁.Layout × X.frame₂.Layout) _ ℂ) =
        (G₁.encoder ⊗ₖ G₂.encoder) *
          (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.tSet P)) ∧
      ∃ w : Word (F₁.regs ++ F₂.regs) (G₁.regs ++ G₂.regs),
        w.IsAllowed ∧ w.UsesOnly {P} ∧ w.sourceCount = 0 ∧
        (∀ z, twoLayoutIso _ _ G₁.owner G₂.owner (w.eval z) =
          act (X.exchangeOp P σ) (twoLayoutIso _ _ own₁ own₂ z)) ∧
        ‖w.eval ((twoLayoutIso _ _ own₁ own₂).symm
            (vecKron (F₁.refVec Ω) (F₂.refVec Ω))) -
          (twoLayoutIso _ _ G₁.owner G₂.owner).symm
            (vecKron (G₁.refVec Ω) (G₂.refVec Ω))‖ ≤ 4 * (L : ℝ) ^ (-p) := by
  intro F₁ F₂ G₁ G₂ X hI
  convert X.exchange_bounded P hΩ
    (L := (L : ℝ) ^ (p / 30)) (by simpa only [ownership_information_power] using hI) using 1
  rw [ownership_error_power]
  rfl

end TNLean.MPS.AreaLaw
