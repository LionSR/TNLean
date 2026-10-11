/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLeanTest.ActualBandGeometryData
import TNLean.PEPS.AreaLaw.Scan.SupportClassification

/-! Actual support classification on the shared nonempty two-band physical scan. -/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open TNLeanTest.ActualBandGeometryData

namespace TNLeanTest.ActualSupportClassification
noncomputable section

-- Classification derives the alternative for every label and either band;
-- no middle-incidence premise is supplied at these call sites.
example (g : Fin 2) (i : Fin 3) :
    (∃ part : Option Bool, ∀ x ∈ designatedSupport scan.graph (scan.truncationSet 192)
      scan.r₀ (scan.anchor i), scan.state history g x = part) ∨
      ∃ side, IsTerminalSplit (scan.state history)
        (designatedSupport scan.graph (scan.truncationSet 192) scan.r₀ (scan.anchor i)) g side :=
  CollarScan.state_designatedSupport_classification_domainGraph
    target_nonempty scan rfl rfl history (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows clearance g i

example (g : Fin 2) (i : Fin 3) :
    (∃ part : Option Bool, ∀ x ∈ designatedSupport scan.graph (scan.truncationSet 192)
      scan.r₀ (scan.anchor i), scan.oldChargeState history g x = part) ∨
      ∃ side, IsTerminalSplit (scan.oldChargeState history)
        (designatedSupport scan.graph (scan.truncationSet 192) scan.r₀ (scan.anchor i)) g side :=
  CollarScan.old_designatedSupport_classification_domainGraph
    target_nonempty scan rfl rfl history (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows clearance g i

-- The exclusion remains valid for every charge sequence throughout the horizon,
-- including bad histories. It needs no row bound.
example {k : ℕ} (h : History scan.K scan.m scan.M k) (hk : k ≤ scan.n * scan.m)
    (g : Fin 2) (i : Fin 3) :
    ¬ ((designatedSupport scan.graph (scan.truncationSet 192) scan.r₀ (scan.anchor i) ∩
        receiving (scan.state h g) false).Nonempty ∧
      (designatedSupport scan.graph (scan.truncationSet 192) scan.r₀ (scan.anchor i) ∩
        receiving (scan.state h g) true).Nonempty) :=
  CollarScan.state_designatedSupport_not_near_far_domainGraph target_nonempty scan rfl rfl h
    (by norm_num) hk (by norm_num) (by norm_num) (by norm_num) (by norm_num) clearance g i


end
end TNLeanTest.ActualSupportClassification
