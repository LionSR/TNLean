/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentation
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Minimal open-boundary representations of finite unitaries

Pairing the output and input letter at every site regards a finite operator
as a coefficient tensor of local dimension `d * d`. Its physical cut ranks
are the consecutive operator Schmidt ranks. A unitary has a nonzero
coefficient tensor, so the minimal finite-chain representation theorem
applies without a normalization or phase convention.

Source: the finite nonuniform MPU definition in arXiv:2508.08160v2,
`references/2508.08160/main.tex`, lines 1337--1402, and the minimal
representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix

namespace MPUCircuit

/-- The coefficients of a finite operator with its output and input letters
paired site by site. The cut ranks of this tensor are its operator Schmidt
ranks. Source: arXiv:2508.08160v2, lines 1337--1402 of the local source. -/
def operatorCoefficientTensor {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    (Fin N → Fin (d * d)) → ℂ :=
  fun σ ↦ U (fun s ↦ (finProdFinEquiv.symm (σ s)).1)
    (fun s ↦ (finProdFinEquiv.symm (σ s)).2)

/-- Pairing the two physical letters recovers the original operator entry.
Source: arXiv:2508.08160v2, lines 1337--1402 of the local source. -/
theorem operatorCoefficientTensor_apply {d N : ℕ}
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (x y : Fin N → Fin d) :
    operatorCoefficientTensor U (fun s ↦ finProdFinEquiv (x s, y s)) = U x y := by
  simp only [operatorCoefficientTensor, Equiv.symm_apply_apply]

/-- A unitary on a nonempty physical alphabet has a nonzero coefficient
tensor. Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem operatorCoefficientTensor_ne_zero {d N : ℕ} (hd : 0 < d)
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ) :
    operatorCoefficientTensor U ≠ 0 := by
  intro hzero
  have hUzero : U = 0 := by
    ext x y
    have h := congrFun hzero (fun s ↦ finProdFinEquiv (x s, y s))
    simpa only [operatorCoefficientTensor_apply, Pi.zero_apply, Matrix.zero_apply] using h
  have hu := mem_unitaryGroup_iff'.mp hU
  rw [hUzero, star_zero, Matrix.zero_mul] at hu
  let z : Fin N → Fin d := fun _ ↦ ⟨0, hd⟩
  have h := congrFun (congrFun hu z) z
  simp at h

/-- A finite unitary with bounded consecutive operator Schmidt ranks has an
exact open-boundary representation with those minimal bond dimensions.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_minimal_obcChainTensor_of_unitary {d N D : ℕ}
    (hd : 0 < d) (hN : 0 < N)
    (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin N → Fin d) ℂ)
    (hbound : ∀ k : Fin (N + 1),
      MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k.val ≤ D) :
    ∃ A : OBCChainTensor (d * d) D N,
      (∀ k, A.bondDim k = MPSPreparation.cutCoefficientRank (operatorCoefficientTensor U) k.val) ∧
      ∀ x y : Fin N → Fin d,
        A.coeff (fun s ↦ finProdFinEquiv (x s, y s)) = U x y := by
  obtain ⟨A, hA, hcoeff⟩ :=
    MPSPreparation.exists_obcChainTensor_coeff_eq_bondDim_eq_cutCoefficientRank hN
      (operatorCoefficientTensor U) (operatorCoefficientTensor_ne_zero hd U hU) hbound
  refine ⟨A, hA, fun x y ↦ ?_⟩
  rw [hcoeff, operatorCoefficientTensor_apply]

end MPUCircuit
