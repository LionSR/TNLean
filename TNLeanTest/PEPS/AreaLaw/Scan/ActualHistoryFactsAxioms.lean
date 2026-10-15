/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualHistoryFacts

/-! # Expected logical axioms of Lemma 9.1 for the actual scan rounds -/

set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.historyFacts_actualScanRound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms historyFacts_actualScanRound

open TNLean.PEPS.AreaLaw.Scan.CollarScan in
/-- info:
'TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_historyFacts_actualScanRound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_historyFacts_actualScanRound
