/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw

/-!
# The one-dimensional chain proof imports nothing from the two-dimensional layer

Every module of `TNLean.MPS.AreaLaw`, including the physical chain-sweep protocol, is built
from `TNLean.Lattice` and QICLean alone. The check inspects every module of the compiled
environment, so it covers transitive imports as well as direct ones.
-/

-- Inspect the compiled environment, rather than just direct source imports.
run_cmd do
  for name in (← Lean.getEnv).header.moduleNames do
    if (`TNLean.PEPS).isPrefixOf name then
      throwError "Unexpected two-dimensional dependency of the chain proof: {name}"
