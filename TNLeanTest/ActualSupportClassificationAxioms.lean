/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SupportClassification

/-! Executable assertions about foundational dependencies of actual support classification. -/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw.Scan.CollarScan

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_near_subset_truncationSet'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms state_near_subset_truncationSet

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_near_subset_truncationSet'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms oldChargeState_near_subset_truncationSet

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_designatedSupport_not_near_far_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms state_designatedSupport_not_near_far_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.old_designatedSupport_not_near_far_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms old_designatedSupport_not_near_far_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_designatedSupport_classification_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms state_designatedSupport_classification_domainGraph

set_option linter.hashCommand false in
/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.old_designatedSupport_classification_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms old_designatedSupport_classification_domainGraph

-- Without geometric separation, two physical sites can meet P and F with no Y.
-- Thus the new exclusion is necessary for the generic three-part argument.
example :
    ((Finset.univ : Finset Bool) ∩ TNLean.PEPS.AreaLaw.Scan.receiving some false).Nonempty ∧
    ((Finset.univ : Finset Bool) ∩ TNLean.PEPS.AreaLaw.Scan.receiving some true).Nonempty ∧
    ¬ ((Finset.univ : Finset Bool) ∩ TNLean.PEPS.AreaLaw.Scan.middle some).Nonempty := by
  decide

example : ¬ ∃ part : Option Bool, ∀ x ∈ (Finset.univ : Finset Bool), some x = part := by
  decide
