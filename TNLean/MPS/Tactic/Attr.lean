/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.Attr.Register

/-!
# Simp attribute sets for tensor-network proofs

This leaf module registers the custom `simp` attribute sets used by tensor-network
definitions and their consumers.  Defining modules import it in order to tag stable
evaluation equations without adding them to the global `simp` set.

## Custom simp attributes

* `mps_eval` : explicit evaluation equations for tensor-network definitions
-/

/-- Simp set for explicit tensor-network evaluation equations. -/
register_simp_attr mps_eval
