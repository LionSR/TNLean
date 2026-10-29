/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalQuasiLocalAction
import TNLean.MPS.MPU.ReducedCanonicalRepresentative
import TNLean.MPS.MPU.TransferStabilizationConverse

/-!
# The actual quasi-local QCA of a matrix product unitary

A positive physical dimension and the bare MPU property suffice. The
existing reduced canonical representative has no larger bond dimension
and exactly the same positive-length periodic operators. Its constructed
QCA therefore has the original finite-chain conjugation formula, and its
propagation radius is bounded by the source radius of the original bond.
Only periodic physical matrices are transported between representatives;
no selected source spaces, source factors or virtual gauge are identified.

Source: arXiv:1703.09188, canonical replacement lines 257--294, 319--356,
and Appendix eq:appendix-1, lines 2292--2306.
-/

namespace SpinChain

/-- Every MPU with positive physical dimension induces an actual QCA
with the source radius and original-site finite-chain formula. Bond
positivity is derived from the MPU property. The reduced representative
is used only through equality of its positive-length periodic matrices.
Source: arXiv:1703.09188, canonical replacement lines 257--294 and
319--356; eq:appendix-1, lines 2292--2306. -/
theorem exists_isQCA_of_isMPU {d D : ℕ} [NeZero d] {U : MPOTensor d D}
    (hU : U.IsMPU) :
    ∃ ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d,
      IsQCA ω ∧
      PropagatesWithin ω (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) ∧
      ∀ (Λ : Finset ℤ) (b : ℤ) (N : ℕ) (hN : 1 < N)
        (hΛ : Λ ⊆ finiteChainRegion b N)
        (hbuffer : regionSumset Λ
          (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) ⊆ finiteChainRegion b N)
        (A : LocalAlgebra d Λ),
        ω (quasiLocalObservable d Λ A) =
          quasiLocalObservable d (finiteChainRegion b N)
            (finiteChainConjugation hU hN b (localInclusion hΛ A)) := by
  classical
  let : NeZero D := hU.neZero_bond
  obtain ⟨Dred, _, Ured, hred, hDim, hMpo⟩ := hU.exists_reduced_cfii_representative
  obtain ⟨ω, hQCA, hprop, heval⟩ := exists_isQCA_of_isMPUCanonicalFormII hred
  have hradius : 4 * (Dred : ℤ) ^ 4 ≤ 4 * (D : ℤ) ^ 4 := by
    exact_mod_cast Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hDim 4)
  have hneighbourhood : Finset.Icc (-(4 * (Dred : ℤ) ^ 4)) (4 * (Dred : ℤ) ^ 4) ⊆
      Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4) := by
    intro z hz
    simp only [Finset.mem_Icc] at *
    omega
  refine ⟨ω, hQCA, hprop.mono hneighbourhood, ?_⟩
  intro Λ b N hN hΛ hbuffer A
  have hbufferRed := (regionSumset_mono_right Λ hneighbourhood).trans hbuffer
  have h := heval Λ b N hN hΛ hbufferRed A
  have hmatrix : finiteChainMPOMatrix Ured N b = finiteChainMPOMatrix U N b := by
    unfold finiteChainMPOMatrix
    rw [hMpo N (Nat.zero_lt_of_lt hN)]
  simpa only [finiteChainConjugation_apply, hmatrix] using h

/-- The actual quasi-local star-automorphism induced by a bare MPU.
Its existence is proved from the actual periodic family, rather than
supplied as compatible-action data.
Source: arXiv:1703.09188, eq:appendix-1, lines 2292--2306. -/
noncomputable def mpuQuasiLocalEquiv {d D : ℕ} [NeZero d] {U : MPOTensor d D}
    (hU : U.IsMPU) : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  Classical.choose (exists_isQCA_of_isMPU hU)

/-- The constructed quasi-local MPU action is a QCA, with covariance
and finite propagation derived from the actual tensor.
Source: arXiv:1703.09188, Appendix line 2298 and eq:appendix-1. -/
theorem isQCA_mpuQuasiLocalEquiv {d D : ℕ} [NeZero d] {U : MPOTensor d D}
    (hU : U.IsMPU) : IsQCA (mpuQuasiLocalEquiv hU) :=
  (Classical.choose_spec (exists_isQCA_of_isMPU hU)).1

/-- The actual induced MPU QCA has the original source bond-dimension
neighbourhood, even if the representative has a smaller bond space.
Source: arXiv:1703.09188, Appendix eq:appendix-1, lines 2300--2306. -/
theorem mpuQuasiLocalEquiv_propagatesWithin {d D : ℕ} [NeZero d] {U : MPOTensor d D}
    (hU : U.IsMPU) :
    PropagatesWithin (mpuQuasiLocalEquiv hU)
      (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) :=
  (Classical.choose_spec (exists_isQCA_of_isMPU hU)).2.1

/-- The actual induced QCA agrees with the original finite MPU
conjugation on every sufficiently buffered original-site interval.
No chain-length divisibility, compatible-action or inverse premise is
added. Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem mpuQuasiLocalEquiv_finiteChainConjugation {d D : ℕ} [NeZero d]
    {U : MPOTensor d D} (hU : U.IsMPU)
    (Λ : Finset ℤ) (b : ℤ) (N : ℕ) (hN : 1 < N)
    (hΛ : Λ ⊆ finiteChainRegion b N)
    (hbuffer : regionSumset Λ
      (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) ⊆ finiteChainRegion b N)
    (A : LocalAlgebra d Λ) :
    mpuQuasiLocalEquiv hU (quasiLocalObservable d Λ A) =
      quasiLocalObservable d (finiteChainRegion b N)
        (finiteChainConjugation hU hN b (localInclusion hΛ A)) :=
  (Classical.choose_spec (exists_isQCA_of_isMPU hU)).2.2 Λ b N hN hΛ hbuffer A

end SpinChain
