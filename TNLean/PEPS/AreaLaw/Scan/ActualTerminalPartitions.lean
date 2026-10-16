/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FillTransport
import TNLean.PEPS.AreaLaw.Scan.ActualChargeData

/-!
# The actual completed and pre-charge terminal family

The common finite family retains the literal physical partitions of the
actual fill and charge trees through a fixed horizon. Both terminal maps
preserve the actual histories, conditional choices, and band order.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 83–154 and
416–451, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan.ActualTerminals

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- Completed times range through the horizon, whereas pre-charge times are
strictly smaller. Source: `08-scanner.tex`, lines 83–154, adc7f124. -/
abbrev terminalFamily (K m M H : ℕ) :=
  (Σ s : Fin (H + 1), History K m M s.val) ⊕
    (Σ s : Fin H, History K m M s.val)

/-- The family keeps the literal completed or pre-charge physical status.
Source: `08-scanner.tex`, lines 83–154, adc7f124. -/
def terminalPartition (S : CollarScan V I) (H : ℕ) :
    terminalFamily S.K S.m S.M H → Fin S.K → PhysicalPartition V :=
  fun j g ↦ match j with
    | Sum.inl ⟨_, h⟩ => S.state h g
    | Sum.inr ⟨_, h⟩ => S.oldChargeState h g

/-- A charge appends its actual choice to the completed history.
Source: `08-scanner.tex`, lines 145–154 and 416–451, adc7f124. -/
def chargeTerminalIndex (K m M H : ℕ) (s : Fin H) :
    (Σ _h : History K m M s.val, Option (ChargeChoices K M)) →
      terminalFamily K m M H :=
  fun j ↦ match j with
    | ⟨h, none⟩ => Sum.inr ⟨s, h⟩
    | ⟨h, some c⟩ => Sum.inl ⟨s.succ, extendHistory h c⟩

/-- Charge terminals retain their actual physical partitions under the
finite-family indexing. Source: `08-scanner.tex`, lines 145–154 and 416–451,
adc7f124. -/
theorem actualChargeData_leafPart_terminalPartition
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
    (H : ℕ) (s : Fin H)
    (j : Σ _h : History S.K S.m S.M s.val, Option (ChargeChoices S.K S.M))
    (g : Fin S.K) :
    (S.actualChargeData hm hM s.val).leafPart j g =
      augmentedPartition
        (terminalPartition S H (chargeTerminalIndex S.K S.m S.M H s j) g) := by
  rcases j with ⟨h, c⟩
  cases c
  case some c => exact S.chargeTransportData_new _ _ h c g
  rfl


/-- A fill retains its completed history or its following pre-charge status.
Source: `08-scanner.tex`, lines 83–154 and 416–451, adc7f124. -/
def fillTerminalIndex (K m M H : ℕ) (s : Fin H) :
    (Σ _h : History K m M s.val, Option Unit) → terminalFamily K m M H :=
  fun j ↦ match j with
    | ⟨h, none⟩ => Sum.inl ⟨s.castSucc, h⟩
    | ⟨h, some _⟩ => Sum.inr ⟨s, h⟩

/-- Fill terminals retain their actual physical partitions under the
finite-family indexing. Source: `08-scanner.tex`, lines 83–154 and 416–451,
adc7f124. -/
theorem actualFillData_leafPart_terminalPartition
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
    (H : ℕ) (s : Fin H)
    (j : Σ _h : History S.K S.m S.M s.val, Option Unit)
    (g : Fin S.K) :
    (S.actualFillData hm hM s.val).leafPart j g =
      augmentedPartition
        (terminalPartition S H (fillTerminalIndex S.K S.m S.M H s j) g) := by
  rcases j with ⟨h, _ | c⟩
  case some h c => exact S.fillTransportData_new _ h c g
  rfl


end TNLean.PEPS.AreaLaw.Scan.CollarScan.ActualTerminals
