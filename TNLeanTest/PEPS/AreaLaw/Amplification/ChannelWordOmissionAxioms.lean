/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordOmission

/-!
Standard-axiom regression guards for the seven physical omission declarations.
The payloads were copied from the raw six-flag audit at source revision
`d53502c3def2a0b8abd0d1685868ffcc9eef0d13`, including hash-command diagnostics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannelWord_sub'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.spectatorRootChannelWord_sub

/--
info: 'TNLean.PEPS.AreaLaw.norm_spectatorRootChannelWord_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_spectatorRootChannelWord_sub_le

/--
info: 'TNLean.PEPS.AreaLaw.channelWordOmissionDefect'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.channelWordOmissionDefect

/--
info: 'TNLean.PEPS.AreaLaw.channelWordOmissionDefect_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.channelWordOmissionDefect_bounds

/--
info: 'TNLean.PEPS.AreaLaw.channelWordOmissionDefect_append_sub_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.channelWordOmissionDefect_append_sub_le

/--
info: 'TNLean.PEPS.AreaLaw.channelWordOmissionDefect_le_sum_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.channelWordOmissionDefect_le_sum_prefix

/--
info: 'TNLean.PEPS.AreaLaw.integrable_and_integral_channelWordOmissionDefect_le'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.integrable_and_integral_channelWordOmissionDefect_le
