/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.QuasiLocalAction
import TNLean.MPS.MPU.TwoSiteSurjectivity

/-!
# The induced QCA depends only on the periodic physical operators

Two MPU tensors, possibly on different bond spaces, which have the same
periodic matrices at every length greater than one induce the same actual
quasi-local automorphism. Both are evaluated on one common sufficiently
buffered chain; only the physical matrices are identified. Completion
density then gives equality everywhere.

Source: CPSV17, arXiv:1703.09188, Appendix eq:appendix-1,
lines 2292--2306, and the canonical replacement in lines 319--356.
-/

namespace SpinChain

/-- Equality of the actual positive-length periodic MPO family implies
equality of the actual induced quasi-local automorphisms. No source
factor, rank, gauge or bond-space identification is required.
Source: CPSV17, Appendix eq:appendix-1, lines 2292--2306. -/
theorem mpuQuasiLocalEquiv_eq_of_mpo_eq
    {d D E : ℕ} [NeZero d] {U : MPOTensor d D} {V : MPOTensor d E}
    (hU : U.IsMPU) (hV : V.IsMPU)
    (hMpo : ∀ N : ℕ, 1 < N → MPOTensor.mpo U N = MPOTensor.mpo V N) :
    mpuQuasiLocalEquiv hU = mpuQuasiLocalEquiv hV := by
  classical
  have hlocal (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
      mpuQuasiLocalEquiv hU (quasiLocalObservable d Λ A) =
        mpuQuasiLocalEquiv hV (quasiLocalObservable d Λ A) := by
    let ΓU := regionSumset Λ (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4))
    let ΓV := regionSumset Λ (Finset.Icc (-(4 * (E : ℤ) ^ 4)) (4 * (E : ℤ) ^ 4))
    obtain ⟨b, N, hN, hΓ, _, _⟩ :=
      exists_finiteChainLocalObservable_bufferedMPULocalAction hU 1 ((Λ ∪ ΓU) ∪ ΓV)
    have hΛ : Λ ⊆ finiteChainRegion b N := by
      intro x hx
      exact hΓ (Finset.mem_union_left ΓV (Finset.mem_union_left ΓU hx))
    have hΓU : ΓU ⊆ finiteChainRegion b N := by
      intro x hx
      exact hΓ (Finset.mem_union_left ΓV (Finset.mem_union_right Λ hx))
    have hΓV : ΓV ⊆ finiteChainRegion b N := by
      intro x hx
      exact hΓ (Finset.mem_union_right _ hx)
    have hmatrix : finiteChainMPOMatrix U N b = finiteChainMPOMatrix V N b := by
      unfold finiteChainMPOMatrix
      rw [hMpo N hN]
    rw [mpuQuasiLocalEquiv_finiteChainConjugation hU Λ b N hN hΛ hΓU A,
      mpuQuasiLocalEquiv_finiteChainConjugation hV Λ b N hN hΛ hΓV A]
    simp only [finiteChainConjugation_apply, hmatrix]
  apply DFunLike.ext
  intro X
  induction X using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (mpuQuasiLocalEquiv hU).isometry.continuous
      (mpuQuasiLocalEquiv hV).isometry.continuous
  | ih A =>
      induction A using DirectLimit.induction with
      | _ Λ A => exact hlocal Λ A

/-- Any supplied standard form of a positive block gives the actual named
MPU automorphism, as an equality of star-algebra equivalences.
Source: CPSV17, Appendix eq:appendix-1, lines 2300--2306. -/
theorem mpuQuasiLocalEquiv_eq_bufferedMPUQuasiLocalAut
    {d D ℓ r : ℕ} [NeZero d] {U : MPOTensor d D}
    (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v) :
    mpuQuasiLocalEquiv hU = bufferedMPUQuasiLocalAut hU k hk S := by
  apply DFunLike.ext
  intro X
  rw [bufferedMPUQuasiLocalAut_apply]
  exact mpuQuasiLocalEquiv_apply_eq_bufferedMPUQuasiLocalAction hU k hk S X

end SpinChain
