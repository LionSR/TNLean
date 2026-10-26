/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSProduct

/-!
# Axiom checks for site products and bond-one representations
-/

/-- info:
'TNLean.MPS.AreaLaw.isOpenMPS_prod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.isOpenMPS_prod

/-- info:
'TNLean.MPS.AreaLaw.IsOpenMPS.smul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.IsOpenMPS.smul

/-- info:
'TNLean.MPS.AreaLaw.IsOpenMPS.exists_eq_mul_prod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.IsOpenMPS.exists_eq_mul_prod

/-- info:
'TNLean.MPS.AreaLaw.isOpenMPS_one_iff_exists_eq_mul_prod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.isOpenMPS_one_iff_exists_eq_mul_prod

/-- info:
'TNLean.MPS.AreaLaw.isOpenMPS_operator_entries_prod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.isOpenMPS_operator_entries_prod

/-- info:
'TNLean.MPS.AreaLaw.isOpenMPS_operator_entries_rectKronecker' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.isOpenMPS_operator_entries_rectKronecker

/-- info:
'TNLean.MPS.AreaLaw.isOpenMPS_operator_entries_embed_one_site' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.isOpenMPS_operator_entries_embed_one_site

/-- info:
'TNLean.MPS.AreaLaw.isOpenMPS_operator_entries_of_supported_singleton' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.isOpenMPS_operator_entries_of_supported_singleton

/-- info:
'TNLean.MPS.AreaLaw.IsOpenMPS.exists_operator_entries_eq_mul_prod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms TNLean.MPS.AreaLaw.IsOpenMPS.exists_operator_entries_eq_mul_prod
