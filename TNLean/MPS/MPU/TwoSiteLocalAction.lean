/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteBufferedAction
import TNLean.QCA.LocalNorm

/-!
# Actual compatible forward local action of an MPU

Choose one sufficiently buffered finite chain for each finite support.
The actual MPU conjugations define a finite-local family. Supplied
standard-form data prove that changing the chosen buffered chain does
not change its value, hence give a compatible algebraic-local action.
The actual finite conjugations also prove norm preservation.

Source: arXiv:1703.09188, Appendix lines 2292--2306.

**Scope restriction (supplied standard form):** Forward compatibility
uses a positive supplied block length and its actual two-site standard
form. The inverse family, derivation of that data from a bare MPU, source
bond-dimension radius and completed automorphism remain separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.
-/

open scoped ComplexOrder

namespace SpinChain

attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

private def actionBufferRadius (k : ℕ) (Λ : Finset ℤ) : ℕ :=
  Λ.sup Int.natAbs + 4 * k + 1

private def actionBufferAnchor (k : ℕ) (Λ : Finset ℤ) : ℤ :=
  -(actionBufferRadius k Λ : ℤ)

private def actionBufferLength (k : ℕ) (Λ : Finset ℤ) : ℕ :=
  2 * actionBufferRadius k Λ + 1

private theorem actionBuffer_spec (k : ℕ) (Λ : Finset ℤ) :
    1 < actionBufferLength k Λ ∧
      Λ ⊆ finiteChainRegion (actionBufferAnchor k Λ) (actionBufferLength k Λ) ∧
      ∀ x ∈ Λ, actionBufferAnchor k Λ ≤ x - (2 * k : ℕ) ∧
        x + (4 * k : ℕ) ≤ actionBufferAnchor k Λ + actionBufferLength k Λ := by
  have hbounds : ∀ x ∈ Λ, -((Λ.sup Int.natAbs : ℕ) : ℤ) ≤ x ∧ x ≤ ((Λ.sup Int.natAbs : ℕ) : ℤ) := by
    intro x hx
    apply abs_le.mp
    rw [Int.abs_eq_natAbs]
    exact_mod_cast (Finset.le_sup (f := Int.natAbs) hx)
  refine ⟨?_, ?_, ?_⟩
  · dsimp [actionBufferLength, actionBufferRadius]
    omega
  · intro x hx
    have h := hbounds x hx
    simp only [finiteChainRegion, Finset.mem_Ico]
    dsimp [actionBufferAnchor, actionBufferLength, actionBufferRadius]
    omega
  · intro x hx
    have h := hbounds x hx
    dsimp [actionBufferAnchor, actionBufferLength, actionBufferRadius]
    omega

/-- The actual finite-chain MPU action on a canonical buffered chain
chosen for a finite region. Compatibility is proved separately from the
supplied standard form; it is not part of this definition.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
noncomputable def bufferedMPULocalAction {d D : ℕ} {U : MPOTensor d D}
    (hU : U.IsMPU) (k : ℕ) (Λ : Finset ℤ) :
    LocalAlgebra d Λ →⋆ₐ[ℂ] AlgebraicLocalAlgebra d :=
  finiteChainLocalObservable hU (actionBuffer_spec k Λ).1 (actionBufferAnchor k Λ)
    (actionBuffer_spec k Λ).2.1

/-- The finite-local action is represented by an actual chain with
all required original-site buffers. The chain and its geometric bounds
are constructed explicitly, including empty supported regions.
Source: arXiv:1703.09188, finite-chain limit, lines 2300--2306. -/
theorem exists_finiteChainLocalObservable_bufferedMPULocalAction
    {d D : ℕ} {U : MPOTensor d D} (hU : U.IsMPU) (k : ℕ) (Λ : Finset ℤ) :
    ∃ (b : ℤ) (N : ℕ) (hN : 1 < N) (hΛ : Λ ⊆ finiteChainRegion b N),
      (∀ x ∈ Λ, b ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ b + N) ∧
      bufferedMPULocalAction hU k Λ = finiteChainLocalObservable hU hN b hΛ :=
  ⟨actionBufferAnchor k Λ, actionBufferLength k Λ, (actionBuffer_spec k Λ).1,
    (actionBuffer_spec k Λ).2.1, (actionBuffer_spec k Λ).2.2, rfl⟩

/-- The actual finite-local forward family is compatible with every
canonical inclusion, as a consequence of the derived buffered-chain
identity. Source: arXiv:1703.09188, Appendix lines 2292--2306. -/
theorem bufferedMPULocalAction_compatible {d D ℓ r : ℕ} {U : MPOTensor d D}
    (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    (Λ Γ : Finset ℤ) (hΛΓ : Λ ⊆ Γ) (A : LocalAlgebra d Λ) :
    bufferedMPULocalAction hU k Γ (localInclusion hΛΓ A) =
      bufferedMPULocalAction hU k Λ A := by
  have h := finiteChainLocalObservable_eq_of_twoSiteStandardForm_buffers hU k hk S Λ
    (actionBufferAnchor k Γ) (actionBufferAnchor k Λ)
    (actionBufferLength k Γ) (actionBufferLength k Λ)
    (actionBuffer_spec k Γ).1 (actionBuffer_spec k Λ).1
    (hΛΓ.trans (actionBuffer_spec k Γ).2.1) (actionBuffer_spec k Λ).2.1
    (fun x hx ↦ (actionBuffer_spec k Γ).2.2 x (hΛΓ hx)) (actionBuffer_spec k Λ).2.2
  unfold bufferedMPULocalAction
  rw [finiteChainLocalObservable_localInclusion]
  exact DFunLike.congr_fun h A

/-- The actual finite-local forward family agrees with every sufficiently
buffered original-site finite chain, not just the canonical chain chosen
in its definition. Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem bufferedMPULocalAction_eq_finiteChainLocalObservable
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    (Λ : Finset ℤ) (b : ℤ) (N : ℕ) (hN : 1 < N) (hΛ : Λ ⊆ finiteChainRegion b N)
    (hb : ∀ x ∈ Λ, b ≤ x - (2 * k : ℕ) ∧ x + (4 * k : ℕ) ≤ b + N) :
    bufferedMPULocalAction hU k Λ = finiteChainLocalObservable hU hN b hΛ :=
  finiteChainLocalObservable_eq_of_twoSiteStandardForm_buffers hU k hk S Λ
    (actionBufferAnchor k Λ) b (actionBufferLength k Λ) N (actionBuffer_spec k Λ).1 hN
    (actionBuffer_spec k Λ).2.1 hΛ (actionBuffer_spec k Λ).2.2 hb

/-- The actual compatible forward action on the existing algebraic local
algebra. No inverse or completed automorphism is asserted here.
Source: arXiv:1703.09188, Appendix lines 2292--2306. -/
noncomputable def bufferedMPUAlgebraicAction {d D ℓ r : ℕ} {U : MPOTensor d D}
    (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v) :
    AlgebraicLocalAlgebra d →⋆ₐ[ℂ] AlgebraicLocalAlgebra d :=
  algebraicLocalAlgebraLift (bufferedMPULocalAction hU k)
    (bufferedMPULocalAction_compatible hU k hk S)

/-- The actual finite-local action preserves the physical operator norm.
Source: arXiv:1703.09188, finite unitary conjugation in lines 2300--2306. -/
theorem norm_bufferedMPULocalAction {d D : ℕ} [NeZero d] {U : MPOTensor d D}
    (hU : U.IsMPU) (k : ℕ) (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    ‖bufferedMPULocalAction hU k Λ A‖ = ‖A‖ := by
  change ‖localObservable d _ (finiteChainConjugation hU (actionBuffer_spec k Λ).1
    (actionBufferAnchor k Λ) (localInclusion (actionBuffer_spec k Λ).2.1 A))‖ = _
  rw [norm_localObservable, NonUnitalStarAlgHom.norm_map
    (finiteChainConjugation hU (actionBuffer_spec k Λ).1 (actionBufferAnchor k Λ))
    (finiteChainConjugation hU (actionBuffer_spec k Λ).1 (actionBufferAnchor k Λ)).injective,
    localInclusion_norm]

/-- The derived algebraic-local forward action preserves the physical
operator norm on every representative. Source: arXiv:1703.09188,
Appendix norm completion in lines 2292--2306. -/
theorem norm_bufferedMPUAlgebraicAction {d D ℓ r : ℕ} [NeZero d] {U : MPOTensor d D}
    (hU : U.IsMPU) (k : ℕ) (hk : 0 < k)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : MPOTensor.TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v)
    (X : AlgebraicLocalAlgebra d) : ‖bufferedMPUAlgebraicAction hU k hk S X‖ = ‖X‖ := by
  induction X using DirectLimit.induction with
  | _ Λ A => exact norm_bufferedMPULocalAction hU k Λ A

end SpinChain
