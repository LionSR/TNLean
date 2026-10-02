/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ReductionExistence
import TNLean.MPS.MPU.ReducedCanonicalRepresentative
import TNLean.MPS.MPU.TransferStabilizationConverse

/-!
# Canonical representatives of one-site injective matrix product unitaries

An MPU whose one-site matrices span the full bond algebra has a canonical-form-II
representative at the same bond dimension. The reduced representative cannot have
smaller bond dimension: equality of positive-length periodic operators gives a
rectangular reduction back to the injective tensor. The two dimension inequalities
therefore agree, and the reduction matrices form an invertible bond similarity.

References: CPSV17, arXiv:1703.09188, canonical-form discussion, lines 319–356;
MGSC18, arXiv:1706.07329v2, Proposition 20, lines 3815–3938 of `cornerproblem.tex`.
-/

namespace MPOTensor

variable {d D : ℕ}

/-- A one-site injective MPU admits a canonical-form-II representative at its original
bond dimension, related by a pure invertible bond similarity and preserving every
positive-length periodic operator. No canonical-form hypothesis is imposed on the
original tensor.

Sources: CPSV17, arXiv:1703.09188, lines 319–356; MGSC18, arXiv:1706.07329v2,
Proposition 20, lines 3815–3938 of `cornerproblem.tex`. -/
theorem IsMPU.exists_cfii_representative_of_isInjective [NeZero d]
    {U : MPOTensor d D} (hU : IsMPU U) (hInj : Kraus.IsInjective U.toMPSTensor) :
    ∃ (V : MPOTensor d D) (_hV : IsMPUCanonicalFormII V)
      (X : GL (Fin D) ℂ),
      (∀ i j, V i j = (X : Matrix (Fin D) (Fin D) ℂ) * U i j *
        (↑X⁻¹ : Matrix (Fin D) (Fin D) ℂ)) ∧
      (∀ N : ℕ, 0 < N → mpo V N = mpo U N) := by
  let : NeZero D := hU.neZero_bond
  obtain ⟨E, _hE, V, hV, hED, hMpo⟩ := hU.exists_reduced_cfii_representative
  have hSame : MPSTensor.SameMPV₂Pos V.toMPSTensor U.toMPSTensor := by
    intro N hN σ
    have hσ : σ = (fun n => finProdFinEquiv ((σ n).divNat, (σ n).modNat)) := by
      funext n
      exact (finProdFinEquiv.apply_symm_apply (σ n)).symm
    rw [hσ, MPSTensor.mpv_toMPSTensor_pairConfig,
      MPSTensor.mpv_toMPSTensor_pairConfig, hMpo N hN]
  obtain ⟨P, Q, hRed⟩ :=
    MPSTensor.exists_isReduction_of_isInjective_of_sameMPV₂Pos
      U.toMPSTensor V.toMPSTensor hInj hSame
  have hE : E = D := Nat.le_antisymm hED hRed.bondDim_le
  subst E
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hRed.mul_eq_one
  let X : GL (Fin D) ℂ := ⟨Q, P, hQP, hRed.mul_eq_one⟩
  refine ⟨V, hV, X, fun i j => ?_, hMpo⟩
  change V i j = Q * U i j * P
  have hij : P * V i j * Q = U i j := by
    simpa [Kraus.evalWord, toMPSTensor] using hRed.evalWord [finProdFinEquiv (i, j)]
  calc
    V i j = (Q * P) * V i j * (Q * P) := by
      rw [hQP, Matrix.one_mul, Matrix.mul_one]
    _ = Q * (P * V i j * Q) * P := by simp only [Matrix.mul_assoc]
    _ = Q * U i j * P := by rw [hij]

end MPOTensor
