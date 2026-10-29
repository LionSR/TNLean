/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationFiniteOrbit
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom check for the finite-dimensional translation-orbit bound. -/

open TNLean.Lattice

run_cmd do
  let decl := ``norm_commutator_le_of_finite_translation_orbit_bounds
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
