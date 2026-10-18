/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.RectangleBootstrapGeometry
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of the weak-rectangle scanner -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.rectangleBootstrapScanner,
    ``TNLean.PEPS.AreaLaw.Scan.exists_rectangleBootstrapScanner_geometry]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

example {Λ : Finset (ℤ × ℤ)} (Q : IntRect) (A : Finset (Site Λ))
    (R : ℕ) (F : ScannerExponents) (Cr C₁ : ℝ) :
    let S := rectangleBootstrapScanner Q A R F Cr C₁
    S.graph = domainGraph Λ ∧ S.A = A ∧
      S.n = Nat.ceil ((24 : ℝ) * (Q.size : ℝ)) ∧
      S.m = F.m S.n ∧ S.K = F.K S.n ∧ S.D = F.D S.n ∧
      S.r₀ = roundedLogRadius Cr S.n ∧ S.C₁ = C₁ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
