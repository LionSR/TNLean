/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Aesop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Aesop rule set for TNLean

This file declares a custom Aesop rule set `TNLean` and registers
domain-specific norm tactics that allow `aesop` to close routine algebraic
goals arising throughout the library: linearity witnesses (`map_add'`/`map_smul'`),
constructor-style structural proofs, and trace identities.

## Registered tactics

* `ring_nf` — commutative ring normalisation
* `abel` — abelian group identities
* `noncomm_ring` — non-commutative ring/matrix algebra

## Usage

```lean
import TNLean.Aesop.Rules

-- replaces multi-line simp/ext/ring proofs:
map_add' X Y := by aesop
```
-/

-- Declare the project-wide rule set.
declare_aesop_rule_sets [TNLean]

-- Register finishing tactics as Aesop norm rules.
-- These let `aesop` close goals that remain after `simp`/`ext` steps
-- by appealing to ring, abelian-group, or non-commutative-ring identity.

add_aesop_rules norm tactic (by ring_nf) (rule_sets := [TNLean])
add_aesop_rules norm tactic (by abel) (rule_sets := [TNLean])
add_aesop_rules norm tactic (by noncomm_ring) (rule_sets := [TNLean])
