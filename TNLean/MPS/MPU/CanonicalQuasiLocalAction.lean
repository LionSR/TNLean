/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AdjointSimpleContraction
import TNLean.MPS.MPU.FiniteChainAdjoint
import TNLean.MPS.MPU.TwoSitePropagation
import TNLean.MPS.MPU.TwoSiteTranslationCovariance
import TNLean.QCA.IsQCA

/-!
# Actual quasi-local automorphism of a canonical-form-II MPU

Canonical form II supplies concrete standard forms for the tensor and its
physical adjoint. Their actual completed forward maps are mutual inverses:
finite support permits one common buffered chain, where actual finite
unitary conjugations cancel. Translation covariance and finite propagation
are then the derived properties of the actual automorphism.

Source: arXiv:1703.09188, Proposition III.3(ii), StandardForm/SF, and
Appendix eq:appendix-1, lines 378--427, 563--622 and 2292--2306.

**Scope restriction (canonical form II):** The public result consumes the
actual canonical-form-II datum. Both standard forms and the inverse are
derived internally. The companion `QuasiLocalAction` module supplies the
bare-MPU statement through the existing reduced representative; see
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

namespace SpinChain

private theorem leftInverse_of_finiteChainConjugation
    {d D₁ D₂ ℓ₁ r₁ ℓ₂ r₂ : ℕ} [NeZero d]
    {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : U.IsMPU) (hV : V.IsMPU) (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    {u₁ : Matrix (Fin ℓ₁ × Fin r₁)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v₁ : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r₁ × Fin ℓ₁) ℂ}
    {u₂ : Matrix (Fin ℓ₂ × Fin r₂)
      (Fin (MPSTensor.blockPhysDim d l) × Fin (MPSTensor.blockPhysDim d l)) ℂ}
    {v₂ : Matrix (Fin (MPSTensor.blockPhysDim d l) × Fin (MPSTensor.blockPhysDim d l))
      (Fin r₂ × Fin ℓ₂) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u₁ v₁)
    (T : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor V l)) u₂ v₂)
    (hfinite : ∀ (N : ℕ) (hN : 1 < N) (b : ℤ)
      (A : LocalAlgebra d (finiteChainRegion b N)),
      finiteChainConjugation hV hN b (finiteChainConjugation hU hN b A) = A) :
    Function.LeftInverse (bufferedMPUQuasiLocalAction hV l hl T)
      (bufferedMPUQuasiLocalAction hU k hk S) := by
  classical
  have hlocal : ∀ (Λ : Finset ℤ) (A : LocalAlgebra d Λ),
      bufferedMPUQuasiLocalAction hV l hl T
        (bufferedMPUQuasiLocalAction hU k hk S (quasiLocalObservable d Λ A)) =
          quasiLocalObservable d Λ A := by
    intro Λ A
    let K := regionSumset Λ (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ)))
    obtain ⟨B, hB⟩ := bufferedMPUQuasiLocalAction_supportedIn hU k hk S
      (show QuasiLocalSupportedIn (quasiLocalObservable d Λ A) Λ from ⟨A, rfl⟩)
    obtain ⟨b, N, hN, hΓ, hbuffer, _⟩ :=
      exists_finiteChainLocalObservable_bufferedMPULocalAction hU (k + l) (Λ ∪ K)
    let hΛ := Finset.subset_union_left.trans hΓ
    let hK := Finset.subset_union_right.trans hΓ
    have hΛbuffer : ∀ x ∈ Λ,
        b ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ b + N := by
      intro x hx
      have h := hbuffer x (Finset.mem_union_left K hx)
      omega
    have hKbuffer : ∀ x ∈ K,
        b ≤ x - (2 * l : ℕ) ∧ x + (4 * l : ℕ) ≤ b + N := by
      intro x hx
      have h := hbuffer x (Finset.mem_union_right Λ hx)
      omega
    have hUeval := bufferedMPUQuasiLocalAction_finiteChainConjugation
      hU k hk S Λ b N hN hΛ hΛbuffer A
    have hVeval := bufferedMPUQuasiLocalAction_finiteChainConjugation
      hV l hl T K b N hN hK hKbuffer B
    have hmatrix : localInclusion hK B =
        finiteChainConjugation hU hN b (localInclusion hΛ A) := by
      apply quasiLocalObservable_injective d (finiteChainRegion b N)
      rw [quasiLocalObservable_localInclusion, hB]
      exact hUeval
    rw [← hB, hVeval, hmatrix, hfinite, quasiLocalObservable_localInclusion]
  intro X
  induction X using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((bufferedMPUQuasiLocalAction_isometry hV l hl T).continuous.comp
          (bufferedMPUQuasiLocalAction_isometry hU k hk S).continuous) continuous_id
  | ih A =>
      induction A using DirectLimit.induction with
      | _ Λ A => exact hlocal Λ A


/-- A canonical-form-II MPU determines an actual quasi-local QCA with
the source bond-dimension neighbourhood and the actual buffered
finite-chain formula. Both its concrete standard form and the adjoint
standard form are supplied internally by the established construction.
No inverse, covariance, propagation or compatibility premise is added.
Source: arXiv:1703.09188, Proposition III.3(ii), StandardForm/SF, and
Appendix eq:appendix-1, lines 378--427, 563--622 and 2292--2306. -/
theorem exists_isQCA_of_isMPUCanonicalFormII {d D : ℕ} {U : MPOTensor d D}
    (hU : MPOTensor.IsMPUCanonicalFormII U) :
    let : NeZero d := hU.neZero_phys
    ∃ ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d,
      IsQCA ω ∧
      PropagatesWithin ω (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) ∧
      ∀ (Λ : Finset ℤ) (b : ℤ) (N : ℕ) (hN : 1 < N)
        (hΛ : Λ ⊆ finiteChainRegion b N)
        (_hbuffer : regionSumset Λ
          (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) ⊆ finiteChainRegion b N)
        (A : LocalAlgebra d Λ),
        ω (quasiLocalObservable d Λ A) =
          quasiLocalObservable d (finiteChainRegion b N)
            (finiteChainConjugation hU.isMPU hN b (localInclusion hΛ A)) := by
  classical
  let : NeZero d := hU.neZero_phys
  let : NeZero D := hU.neZero_bond
  obtain ⟨k, hk, hkbound, _, ⟨S⟩, _⟩ := hU.exists_twoSiteStandardFormData_blockTensor
  let hAdj := hU.physicalAdjointTensor
  obtain ⟨l, hl, _, _, ⟨T⟩, _⟩ := hAdj.exists_twoSiteStandardFormData_blockTensor
  let F := bufferedMPUQuasiLocalAction hU.isMPU k hk S
  let G := bufferedMPUQuasiLocalAction hAdj.isMPU l hl T
  have hGF : G.comp F = StarAlgHom.id ℂ (QuasiLocalAlgebra d) := by
    apply StarAlgHom.ext
    exact leftInverse_of_finiteChainConjugation hU.isMPU hAdj.isMPU k l hk hl S T
      (fun N hN b A ↦ finiteChainConjugation_physicalAdjointTensor_apply_apply hU.isMPU hN b A)
  have hFG : F.comp G = StarAlgHom.id ℂ (QuasiLocalAlgebra d) := by
    apply StarAlgHom.ext
    exact leftInverse_of_finiteChainConjugation hAdj.isMPU hU.isMPU l k hl hk T S
      (fun N hN b A ↦ finiteChainConjugation_apply_physicalAdjointTensor_apply hU.isMPU hN b A)
  let ω := StarAlgEquiv.ofStarAlgHom F G hGF hFG
  have hcov : TranslationCovariant ω := by
    apply (translationCovariant_iff ω).mpr
    intro t X
    exact bufferedMPUQuasiLocalAction_translation hU.isMPU k hk S t X
  have hsmall : PropagatesWithin ω (Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ))) := by
    intro Λ X hX
    exact bufferedMPUQuasiLocalAction_supportedIn hU.isMPU k hk S hX
  have hDD : D * D ≤ D ^ 4 := by
    simpa only [pow_two] using
      (Nat.pow_le_pow_right (NeZero.pos D) (show 2 ≤ 4 by omega))
  have hradius : 4 * (k : ℤ) ≤ 4 * (D : ℤ) ^ 4 := by
    exact_mod_cast Nat.mul_le_mul_left 4 (hkbound.trans hDD)
  have hneighbourhood : Finset.Icc (-(4 * (k : ℤ))) (4 * (k : ℤ)) ⊆
      Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4) := by
    intro z hz
    simp only [Finset.mem_Icc] at *
    omega
  have hprop := hsmall.mono hneighbourhood
  refine ⟨ω, IsQCA.mk hcov ⟨_, hprop⟩, hprop, ?_⟩
  intro Λ b N hN hΛ hbuffer A
  have hRnonneg : 0 ≤ 4 * (D : ℤ) ^ 4 :=
    mul_nonneg (by omega) (pow_nonneg (Nat.cast_nonneg D) 4)
  have hb : ∀ x ∈ Λ, b ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ b + N := by
    intro x hx
    have hleft : x - 4 * (D : ℤ) ^ 4 ∈ regionSumset Λ
        (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) := by
      apply (mem_regionSumset _ Λ _).mpr
      refine ⟨x, hx, -(4 * (D : ℤ) ^ 4), ?_, by omega⟩
      simp only [Finset.mem_Icc]
      omega
    have hright : x + 4 * (D : ℤ) ^ 4 ∈ regionSumset Λ
        (Finset.Icc (-(4 * (D : ℤ) ^ 4)) (4 * (D : ℤ) ^ 4)) := by
      apply (mem_regionSumset _ Λ _).mpr
      refine ⟨x, hx, 4 * (D : ℤ) ^ 4, ?_, rfl⟩
      simp only [Finset.mem_Icc]
      omega
    have hl := Finset.mem_Ico.mp (hbuffer hleft)
    have hr := Finset.mem_Ico.mp (hbuffer hright)
    omega
  exact bufferedMPUQuasiLocalAction_finiteChainConjugation hU.isMPU k hk S Λ b N hN hΛ hb A

end SpinChain
