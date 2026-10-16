/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceComparators
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the norm comparisons

The theorem stating Proposition 8.1 must exist and have precisely the three standard logical
axioms.
-/

run_cmd do
  let decl := Lean.Name.str `TNLean.PEPS.AreaLaw.Scan.Comparators "comparatorsStatement"
  unless (← Lean.getEnv).contains decl do
    throwError "The intended norm-comparison theorem is absent."
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
    throwError "Unexpected logical dependencies for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
