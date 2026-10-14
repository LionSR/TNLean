/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ConstraintWordTruncation

/-! Standard-axiom audit for the truncation of the retained constraint product. -/

set_option linter.mathlibStandardSet true

/--
info: 'TNLean.PEPS.AreaLaw.exists_latticeConstraintWord_truncation'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.exists_latticeConstraintWord_truncation
