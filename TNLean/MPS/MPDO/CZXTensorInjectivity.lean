/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Basis
import QICLean.Kraus.Injectivity
import TNLean.MPS.MPDO.CZXTensor

/-!
# Injectivity of the exact FBC25 CZX tensor

The once-blocked tensor in arXiv:2502.20257, `eq:MPU_CZX`
(lines 4505–4547), is injective. We use the shared tensor, including its
output Z gates and unnormalized Hadamard weights, not the normalized
2017 tensor (see `docs/paper-gaps/mpu_czx_tensor_normalization.tex`).

Writing $B_{ij}$ for its physical letters and $E_{ij}$ for the bond matrix
units, the four identities are
$E_{00}=(B_{03}-B_{12})/2$, $E_{01}=(B_{03}+B_{12})/2$,
$E_{10}=-(B_{21}+B_{30})/2$, and $E_{11}=(B_{30}-B_{21})/2$.
They show that the physical letters span the full bond matrix algebra.
-/

noncomputable section

open scoped BigOperators

namespace MPOTensor.CZX

private theorem single_eq_tensor_combination (i j : Fin 2) :
    Matrix.single i j (1 : ℂ) =
      (if i = 0 then (1 / 2 : ℂ) else -1 / 2) •
        tensor (if i = 0 then 0 else 2) (if i = 0 then 3 else 1) +
      (if j = 0 then (-1 / 2 : ℂ) else 1 / 2) •
        tensor (if i = 0 then 1 else 3) (if i = 0 then 2 else 0) := by
  have hc : ∀ (u d : Fin 4) (l : Fin 2),
      (u = complementSite d ∧ l = (show Fin 2 from (siteBits u).1)) ↔
        u = d.rev ∧ l = u.divNat (n := 2) := by decide
  have he : ∀ (u : Fin 4) (r : Fin 2), edgeExponent u r =
      u.val / 2 + u.val % 2 + (u.val / 2) * (u.val % 2) + (u.val % 2) * r.val := by
    decide
  ext l r
  simp only [Matrix.add_apply, Matrix.smul_apply, tensor_apply, hc, he]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    norm_num [Matrix.single_apply, Fin.divNat, Fin.rev, Fin.ext_iff]

/-- The once-blocked CZX tensor is injective, as asserted immediately before
arXiv:2502.20257, `eq:MPU_CZX` (lines 4505–4547). Its four nonzero physical
letters span all bond matrix units by half-sums and half-differences. -/
theorem tensor_isInjective : Kraus.IsInjective tensor.toMPSTensor := by
  rw [Kraus.IsInjective]
  let S := Submodule.span ℂ (Set.range tensor.toMPSTensor)
  have hletter (i j : Fin 4) : tensor i j ∈ S := by
    apply Submodule.subset_span
    exact ⟨finProdFinEquiv (i, j), by
      simp only [toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
        MPSTensor.finProdFinEquiv_modNat]⟩
  have hunit (i j : Fin 2) : Matrix.single i j (1 : ℂ) ∈ S := by
    rw [single_eq_tensor_combination]
    exact S.add_mem (S.smul_mem _ (hletter _ _)) (S.smul_mem _ (hletter _ _))
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    S.smul_mem (M i j) (hunit i j)

end MPOTensor.CZX
