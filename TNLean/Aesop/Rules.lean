/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aesop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Aesop rule set for TNLean

This file declares a custom Aesop rule set `TNLean` for use with domain-specific
automation throughout the library.

Downstream files that `import TNLean.Aesop.Rules` can register lemmas or tactics
into the `TNLean` rule set via:

```
@[aesop safe apply (rule_sets := [TNLean])] theorem myLemma ...
add_aesop_rules safe tactic (rule_sets := [TNLean]) (by ring_nf)
```

The rule set becomes visible only after importing this file.
-/

-- Declare the project-wide rule set.
declare_aesop_rule_sets [TNLean]
