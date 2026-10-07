/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
import TNLean.PEPS.Approximation.Basic

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

namespace ModelChecks

abbrev EmptyConfiguration := TNLean.PEPS.AreaLaw.Configuration ∅ 1

noncomputable def emptyUnit : TNLean.PEPS.AreaLaw.StateSpace ∅ 1 :=
  PiLp.single 2 (fun _ ↦ 0) 1

example : ‖emptyUnit‖ = 1 := by
  simp [emptyUnit]

example : Fintype.card EmptyConfiguration = 1 := by
  simp [EmptyConfiguration]

example :
    Matrix.vecMulVec (fun x ↦ emptyUnit x) (star (fun x ↦ emptyUnit x)) =
      (1 : Matrix EmptyConfiguration EmptyConfiguration ℂ) := by
  ext x y
  have hx := Subsingleton.elim x ((fun _ ↦ 0) : EmptyConfiguration)
  have hy := Subsingleton.elim y ((fun _ ↦ 0) : EmptyConfiguration)
  subst x
  subst y
  simp [emptyUnit, Matrix.vecMulVec_apply]

noncomputable def cancellationScalar (v : TNLean.PEPS.SquareLatticeVertex 2 2) : ℂ :=
  if v = (0, 0) then Complex.I else if v = (1, 0) then -Complex.I else 0

noncomputable def cancellationHamiltonian : TNLean.PEPS.Approximation.SquareHamiltonian 2 2 1 where
  siteTerm v := cancellationScalar v • 1
  edgeTerm _ := 0
  site_supported v := (QuantumCircuit.supportedOperators 2 {v}).smul_mem _
    (QuantumCircuit.one_mem_supportedOperators {v})
  edge_supported _ := Submodule.zero_mem _
  site_norm_le v := by
    simp only [cancellationScalar]
    split_ifs <;> simp [norm_smul]
  edge_norm_le _ := by simp
  hermitian := by
    simp [cancellationScalar, Fintype.sum_prod_type, Fin.sum_univ_two]

example : ¬(cancellationHamiltonian.siteTerm (0, 0)).IsHermitian := by
  intro h
  have hh := h.apply (fun _ ↦ 0) (fun _ ↦ 0)
  have hi := congrArg Complex.im hh
  norm_num [cancellationHamiltonian, cancellationScalar] at hi

example (h : TNLean.PEPS.AreaLaw.UniformAreaLaw) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : Finset (ℤ × ℤ), ∀ H : TNLean.PEPS.AreaLaw.LocalHamiltonian Λ 1 0 1,
        ∀ E₀ : ℝ, ∀ Ω : TNLean.PEPS.AreaLaw.StateSpace Λ 1,
          TNLean.PEPS.AreaLaw.IsGappedGroundState Λ 1 H.operator E₀ Ω 1 →
            ∀ A : Finset (TNLean.PEPS.AreaLaw.Site Λ),
              TNLean.PEPS.AreaLaw.regionalEntropy Λ 1 Ω A ≤
                C * (TNLean.PEPS.AreaLaw.edgeBoundary Λ A).card :=
  h 1 (by decide) 0 1 1 (by norm_num) (by norm_num)

example (Λ : Finset (ℤ × ℤ)) :
    Fintype.card (TNLean.PEPS.AreaLaw.Configuration Λ 1) = 1 := by
  simp

example {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
    (H : TNLean.PEPS.AreaLaw.LocalHamiltonian Λ q R J)
    (X : TNLean.PEPS.AreaLaw.AdmissibleSupport Λ R) :
    ‖H.term X‖ =
      ‖Matrix.toEuclideanCLM (n := TNLean.PEPS.AreaLaw.Configuration Λ q) (𝕜 := ℂ)
        (H.term X)‖ := rfl

end ModelChecks
