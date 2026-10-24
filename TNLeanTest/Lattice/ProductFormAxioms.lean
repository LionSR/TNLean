/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the matrix product form of Trotter products in
Hastings' treatment of nonzero temperature. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``QuantumCircuit.apply_eq_apply_of_mem_supportedOperators,
    ``QuantumCircuit.exp_mem_supportedOperators,
    ``TNLean.Lattice.hasProductForm_one,
    ``TNLean.Lattice.HasProductForm.mul,
    ``TNLean.Lattice.hasProductForm_list_prod,
    ``TNLean.Lattice.HasProductForm.pow,
    ``TNLean.Lattice.hasProductForm_of_mem_supportedOperators_radius,
    ``TNLean.Lattice.hasProductForm_trotterProduct_of_radius,
    ``TNLean.Lattice.hasProductForm_of_mem_supportedOperators,
    ``TNLean.Lattice.LocalHamiltonian.hasProductForm_trotterProduct] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

namespace TNLean.Lattice

/-- Three collinear sites used to test a centre outside the support. -/
private def radiusDomain : Finset (ℤ × ℤ) := {(-1, 0), (0, 0), (1, 0)}
/-- The middle site of the test domain. -/
private def centre : Site radiusDomain := ⟨(0, 0), by decide⟩
/-- The left endpoint of the test domain. -/
private def leftSite : Site radiusDomain := ⟨(-1, 0), by decide⟩
/-- The right endpoint of the test domain. -/
private def rightSite : Site radiusDomain := ⟨(1, 0), by decide⟩

-- Both ends are within radius one of the centre, which is outside the support.
example : centre ∉ ({leftSite, rightSite} : Finset (Site radiusDomain)) := by decide

example {q : ℕ} {ρ : Matrix (Configuration radiusDomain q) (Configuration radiusDomain q) ℂ}
    (hρ : ρ ∈ QuantumCircuit.supportedOperators q
      (({leftSite, rightSite} : Finset (Site radiusDomain)) : Set (Site radiusDomain))) :
    HasProductForm radiusDomain q 1 ρ := by
  apply hasProductForm_of_mem_supportedOperators_radius centre _ hρ
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  all_goals exact ⟨.cons (by decide) .nil, by decide⟩

-- Empty supports require no invented support site.
example {Λ : Finset (ℤ × ℤ)} {q R : ℕ} (i : Site Λ)
    {ρ : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hρ : ρ ∈ QuantumCircuit.supportedOperators q (∅ : Set (Site Λ))) :
    HasProductForm Λ q R ρ := by
  exact hasProductForm_of_mem_supportedOperators_radius (X := ∅) i (by simp) (by simpa using hρ)

-- The empty domain and zero steps are admitted by the centre-indexed theorem.
example (q R : ℕ) (β : ℝ) : HasProductForm ∅ q R 1 := by
  simpa using hasProductForm_trotterProduct_of_radius (Λ := ∅) (q := q) (R := R)
    (fun _ ↦ 0) (fun _ ↦ ∅) (by simp) (fun _ ↦ Submodule.zero_mem _) [] β 0

end TNLean.Lattice
