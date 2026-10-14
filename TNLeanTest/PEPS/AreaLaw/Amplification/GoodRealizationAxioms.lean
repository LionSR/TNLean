/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GoodRealization

/-! Standard-axiom audit for the choice of scales and of a good clock realization. -/

set_option linter.mathlibStandardSet true

/--
info: 'TNLean.PEPS.AreaLaw.exists_good_realization'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.exists_good_realization
