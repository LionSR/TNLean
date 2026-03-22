/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Aesop.Rules

/-!
# Aesop tactic registrations for TNLean

This file registers finishing tactics (`ring_nf`, `abel`, `noncomm_ring`) as
safe Aesop rules in the `TNLean` rule set.

Import this file (rather than `TNLean.Aesop.Rules` alone) when you want
`aesop` to automatically try these finishing tactics.
-/

add_aesop_rules safe tactic (rule_sets := [TNLean]) (by ring_nf)
add_aesop_rules safe tactic (rule_sets := [TNLean]) (by abel)
add_aesop_rules safe tactic (rule_sets := [TNLean]) (by noncomm_ring)
