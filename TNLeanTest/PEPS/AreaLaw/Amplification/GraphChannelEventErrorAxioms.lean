/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelEventError

/-!
Standard-axiom guards for the two actual-channel event-error declarations.
The payloads were copied from the raw six-flag audit at source revision
`790fecf554318e192bab19a2d06b35039bc762fc`, including hash-command diagnostics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

/--
info: 'TNLean.PEPS.AreaLaw.norm_localRootChannel_sub_self_le_exp_sum_siteOscillation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_localRootChannel_sub_self_le_exp_sum_siteOscillation

/--
info: 'TNLean.PEPS.AreaLaw.norm_spectatorRootChannel_sub_self_le_exp_of_component_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.norm_spectatorRootChannel_sub_self_le_exp_of_component_support
