/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# GHZ parent-Hamiltonian local ground space

This file records the two-site ground-space calculation for the GHZ tensor.

## References

* Fernández-González--Wolf--Sanz--Pérez-García 2012, arXiv:1210.6613,
  Section 3, lines 432--455.
* Cirac--Pérez-García--Schuch--Verstraete 2021, arXiv:2011.12127,
  lines 1194--1196 and line 2205.
-/

namespace MPSTensor

/-- The computational two-site vector \(\ket{ab}\) for the physical space
\((\mathbb C^2)^{\otimes 2}\). -/
def twoSiteKet (a b : Fin 2) : NSiteSpace 2 2 :=
  Pi.single (fun k : Fin 2 => if k = 0 then a else b) 1

private theorem ghz_groundSpaceMap_two
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    groundSpaceMap ghzTensor 2 X =
      X 0 0 • twoSiteKet 0 0 + X 1 1 • twoSiteKet 1 1 := by
  ext σ
  let a₀ : Fin 2 := σ 0
  let a₁ : Fin 2 := σ 1
  have hσ : σ = fun k : Fin 2 => if k = 0 then a₀ else a₁ := by
    ext k
    fin_cases k <;> simp [a₀, a₁]
  suffices hcalc : ∀ a b : Fin 2,
      groundSpaceMap ghzTensor 2 X (fun k : Fin 2 => if k = 0 then a else b) =
        (X 0 0 • twoSiteKet 0 0 + X 1 1 • twoSiteKet 1 1)
          (fun k : Fin 2 => if k = 0 then a else b) by
    rw [hσ]
    exact hcalc a₀ a₁
  intro a b
  fin_cases a <;> fin_cases b
  · have hne :
        (fun _ : Fin 2 => (0 : Fin 2)) ≠ (fun _ : Fin 2 => (1 : Fin 2)) := by
      decide
    simp [groundSpaceMap_apply, twoSiteKet, ghzTensor, evalWord, Matrix.trace,
      Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hne]
  · have hne0 :
        (fun k : Fin 2 => if k = 0 then (0 : Fin 2) else (1 : Fin 2)) ≠
          (fun _ : Fin 2 => (0 : Fin 2)) := by
      decide
    have hne1 :
        (fun k : Fin 2 => if k = 0 then (0 : Fin 2) else (1 : Fin 2)) ≠
          (fun _ : Fin 2 => (1 : Fin 2)) := by
      decide
    simp [groundSpaceMap_apply, twoSiteKet, ghzTensor, evalWord, Matrix.trace,
      Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hne0, hne1]
  · have hne0 :
        (fun k : Fin 2 => if k = 0 then (1 : Fin 2) else (0 : Fin 2)) ≠
          (fun _ : Fin 2 => (0 : Fin 2)) := by
      decide
    have hne1 :
        (fun k : Fin 2 => if k = 0 then (1 : Fin 2) else (0 : Fin 2)) ≠
          (fun _ : Fin 2 => (1 : Fin 2)) := by
      decide
    simp [groundSpaceMap_apply, twoSiteKet, ghzTensor, evalWord, Matrix.trace,
      Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hne0, hne1]
  · have hne :
        (fun _ : Fin 2 => (1 : Fin 2)) ≠ (fun _ : Fin 2 => (0 : Fin 2)) := by
      decide
    simp [groundSpaceMap_apply, twoSiteKet, ghzTensor, evalWord, Matrix.trace,
      Matrix.mul_apply, Matrix.diagonal_apply, Pi.single_apply, hne]

/-- The local parent-space equation for the GHZ tensor is
\[
  \mathcal G_2(A_{\mathrm{GHZ}})
  =
  \operatorname{span}_{\mathbb C}\{\ket{00},\ket{11}\}.
\]
This is arXiv:1210.6613, lines 449--455. -/
theorem ghz_groundSpace_two_eq_span :
    groundSpace ghzTensor 2 =
      Submodule.span ℂ
        ({twoSiteKet 0 0, twoSiteKet 1 1} : Set (NSiteSpace 2 2)) := by
  apply le_antisymm
  · rintro ψ ⟨X, rfl⟩
    rw [ghz_groundSpaceMap_two]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro ψ hψ
    rw [groundSpace]
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
    rcases hψ with rfl | rfl
    · refine ⟨Matrix.diagonal (Pi.single (0 : Fin 2) 1), ?_⟩
      rw [ghz_groundSpaceMap_two]
      simp [twoSiteKet]
    · refine ⟨Matrix.diagonal (Pi.single (1 : Fin 2) 1), ?_⟩
      rw [ghz_groundSpaceMap_two]
      simp [twoSiteKet]

end MPSTensor
