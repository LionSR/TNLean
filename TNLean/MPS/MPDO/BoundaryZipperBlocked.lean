/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryZipper
import TNLean.MPS.MPDO.BoundarySourceDecomposition

/-!
# Complete zipper families from arbitrary-boundary closedness

The exact fusion maps obtained from arbitrary-boundary closedness remain
unchanged under positive physical blocking. A common positive blocking length
derived from individual injectivity and scalar-gauge separation supplies the
simultaneous block inverse. The resulting complete zipper family therefore
requires no extra star, support-completeness, or remainder hypothesis.

**Scope restriction (simultaneous block inverse):** the complete zipper family
has the blocked physical alphabet. Individual injectivity need not give the
simultaneous inverse at the original one-site alphabet. The rectangular fusion
maps and their multiplicities are those of the original unblocked exact
decomposition. See `docs/paper-gaps/bmwshv17_joint_block_left_inverse.tex`.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `algcond`,
  `fusiontensors`, `eq:orthoW`, and Appendix A.
* arXiv:1511.08090, `AnyonsPEPS.tex`, lines 181--200, 269--277,
  and the common blocking at lines 427--431.
-/

open scoped Matrix BigOperators

namespace MPSTensor.IsBiorthogonalDecomposition

/-- Blocking both incoming MPOs and all targets preserves their exact
biorthogonal decomposition with the same analysis and synthesis maps.
Source: GLM23 Appendix A, `decompopen`, and physical blocking. -/
theorem blockMPO {p g : ℕ} {D : Fin g → ℕ}
    {T : ∀ c, MPOTensor p (D c)} {N : Fin g → ℕ} {a b : Fin g}
    {V : ∀ c, Fin (N c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ}
    {W : ∀ c, Fin (N c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ}
    (h : IsBiorthogonalDecomposition (MPOTensor.mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin g) × Fin (N c) ↦ (T q.1).toMPSTensor)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2))
    {L : ℕ} (hL : 0 < L) :
    IsBiorthogonalDecomposition
      (MPOTensor.mulTensor (MPOTensor.blockTensor (T a) L)
        (MPOTensor.blockTensor (T b) L)).toMPSTensor
      (fun q : (c : Fin g) × Fin (N c) ↦ (MPOTensor.blockTensor (T q.1) L).toMPSTensor)
      (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) :=
  h.ofWords (MPOTensor.blockedPairWord p L) (MPOTensor.blockedPairWord_ne_nil hL)
    (fun I ↦ by
      rw [← MPOTensor.blockTensor_mulTensor]
      exact MPOTensor.toMPSTensor_blockTensor_apply _ L I)
    (fun q I ↦ MPOTensor.toMPSTensor_blockTensor_apply (T q.1) L I)

end MPSTensor.IsBiorthogonalDecomposition

namespace MPOTensor.CompleteZipperFusionFamily

variable {p g : ℕ} {D : Fin g → ℕ} {T : ∀ c, MPOTensor p (D c)}
  {N : Fin g → Fin g → Fin g → ℕ}

variable (hT : ∀ c, Kraus.IsNormal (T c).toMPSTensor) (hD : ∀ c, 0 < D c)
  (hne : MPSTensor.BlocksNotGaugePhaseEquiv (fun c ↦ (T c).toMPSTensor))
  (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ)
  (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ)
  (hVW : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin g) × Fin (N a b c) ↦ (T q.1).toMPSTensor)
      (fun q ↦ V a b q.1 q.2) (fun q ↦ W a b q.1 q.2))

/-- Common blocking supplies the simultaneous inverse for an exact
biorthogonal family. The multiplicities and both rectangular maps are
unchanged. Source: GLM23 Appendix A and arXiv:1511.08090, lines 427--431. -/
@[reducible] noncomputable def ofBiorthogonalBlocked :
    CompleteZipperFusionFamily (Fin g)
      (MPSTensor.blockPhysDim p (jointBlockLength T hT hD hne)) :=
  let hspec := (exists_blockTensor_isMPOBlockLeftInverse T hT hD hne).choose_spec
  ofBiorthogonal hD hspec.2.1 V W (fun a b ↦ (hVW a b).blockMPO hspec.1)
    hspec.2.2.choose hspec.2.2.choose_spec

/-- The complete family has precisely the commonly blocked source tensors. -/
theorem ofBiorthogonalBlocked_tensor (c : Fin g) :
    (ofBiorthogonalBlocked hT hD hne V W hVW).tensor c =
      blockTensor (T c) (jointBlockLength T hT hD hne) := rfl

/-- Physical blocking preserves every synthesis entry, including its
unblocked incoming bond coordinates. -/
theorem ofBiorthogonalBlocked_fusionTensor (a b c : Fin g)
    (μ : Fin (N a b c)) (x : Fin (D a) × Fin (D b)) (z : Fin (D c)) :
    (ofBiorthogonalBlocked hT hD hne V W hVW).fusionTensor a b c μ x z =
      W a b c μ (finProdFinEquiv x) z := rfl

/-- Physical blocking preserves every analysis entry. No adjoint relation
between these maps and the synthesis maps is asserted. -/
theorem ofBiorthogonalBlocked_fusionTensorLeftInverse (a b c : Fin g)
    (μ : Fin (N a b c)) (z : Fin (D c)) (x : Fin (D a) × Fin (D b)) :
    (ofBiorthogonalBlocked hT hD hne V W hVW).fusionTensorLeftInverse a b c μ z x =
      V a b c μ z (finProdFinEquiv x) := rfl

end MPOTensor.CompleteZipperFusionFamily

namespace MPOTensor

/-- The source's arbitrary-boundary closedness and separated injective blocks
give exact unblocked fusion maps and a complete zipper family after one
derived positive physical blocking, with those same maps and multiplicities.
Source: GLM23 `algcond`, `fusiontensors`, `eq:orthoW`, and Appendix A. -/
theorem IsBoundaryClosed.exists_completeZipperFusionFamily
    {p g : ℕ} {D : Fin g → ℕ}
    {T : MPOTensor p (∑ c : Fin g, D c)} (h : IsBoundaryClosed T)
    (A : (c : Fin g) → MPOTensor p (D c))
    (hBlocks : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun c ↦ (A c).toMPSTensor))
    (hInj : ∀ c, Kraus.IsInjective (A c).toMPSTensor) (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv (fun c ↦ (A c).toMPSTensor)) :
    ∃ (N : Fin g → Fin g → Fin g → ℕ)
      (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ)
      (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ),
      (∀ a b, MPSTensor.IsBiorthogonalDecomposition (mulTensor (A a) (A b)).toMPSTensor
        (fun q : (c : Fin g) × Fin (N a b c) ↦ (A q.1).toMPSTensor)
        (fun q ↦ V a b q.1 q.2) (fun q ↦ W a b q.1 q.2)) ∧
      ∃ L : ℕ, 0 < L ∧ ∃ F : CompleteZipperFusionFamily (Fin g) (MPSTensor.blockPhysDim p L),
        F.bondDim = D ∧ F.fusionMultiplicity = N ∧
        HEq F.tensor (fun c ↦ blockTensor (A c) L) ∧
        HEq F.fusionSynthesis
          (fun a b ↦ CompleteZipperFusionFamily.biorthogonalSynthesis (W a b)) ∧
        HEq F.fusionAnalysis
          (fun a b ↦ CompleteZipperFusionFamily.biorthogonalAnalysis (V a b)) := by
  classical
  choose N V W hVW using
    fun a b ↦ h.exists_blockFusionDecomposition_of_isInjective
      A hBlocks hInj hD hne a b
  let hNormal := fun c ↦ (hInj c).isNormal
  let L := CompleteZipperFusionFamily.jointBlockLength A hNormal hD hne
  let F := CompleteZipperFusionFamily.ofBiorthogonalBlocked hNormal hD hne V W hVW
  exact ⟨N, V, W, hVW, L,
    CompleteZipperFusionFamily.jointBlockLength_pos A hNormal hD hne,
    F, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end MPOTensor
