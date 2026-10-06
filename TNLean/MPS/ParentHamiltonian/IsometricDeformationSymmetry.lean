/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.InjectiveIsometricDeformationSymmetry
import TNLean.MPS.ParentHamiltonian.BlockSumIntervalSpaces
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction
import TNLean.MPS.Symmetry.ParentHamiltonianSymmetry

/-!
# Parent-Hamiltonian symmetry along the constructed polar deformation

Let \(P=QW\) be the joint left polar decomposition of a block family,
with the positive factor extended by the identity outside its physical
support. Suppose that a physical unitary \(U\) commutes with \(Q\) and
preserves the original two-site MPS space. Then the canonical parent
projections and the inverse-conjugated positive interactions along
\(P_\gamma=(\gamma Q+(1-\gamma)I)W\) commute with \(U^{\otimes2}\).
Their open and periodic sums commute with \(U^{\otimes N}\) for every
\(N\geq2\).

**Scope restriction (supplied local-space invariance):** The general block-family
parent-symmetry conclusions assume invariance of the original two-site
space and commutation of the positive polar factor with the physical action.
The derivation of these hypotheses from arbitrary multi-block state symmetry
is recorded separately in
`docs/paper-gaps/spc11_isometric_symmetry_unitary_virtual.tex`
(https://sirui-lu.com/TNLean/paper-gaps/spc11_isometric_symmetry_unitary_virtual.pdf).

These are conditional consequences of Schuch--Pérez-García--Cirac,
arXiv:1010.3732, lines 672--676. The invariance of the original local space
and commutation of the positive factor are explicit hypotheses. The
single-block consequences derive both hypotheses from exact state symmetry
for a one-site injective tensor in either canonical orientation:
\(\sum_i A_i A_i^\dagger=I\) or \(\sum_i A_i^\dagger A_i=I\).
The latter is the partial-trace normalization printed in the source. The virtual
permutation and compatible unitary gauges for arbitrary multiblock state
symmetries, invoked at source lines 649--659, remain separate.
-/

open scoped Matrix Kronecker BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Commuting physical matrices give commuting operators on every finite chain.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem onSiteTensorPow_commute {U Q : Matrix (Fin d) (Fin d) ℂ}
    (h : Commute U Q) (L : ℕ) :
    Commute (Matrix.toEuclideanLin (onSiteTensorPow L U))
      (Matrix.toEuclideanLin (onSiteTensorPow L Q)) := by
  apply (commute_iff_eq _ _).2
  simpa only [onSiteTensorPow_mul, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    Module.End.mul_eq_comp] using
      congrArg (fun M => Matrix.toEuclideanLin (onSiteTensorPow L M)) h.eq

/-- A unitary on-site action preserving the supplied local ground space commutes with its
canonical parent projection.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem parentInteractionES_commute_onSiteTensorPow_of_invariant {d D : ℕ}
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (L : ℕ)
    (hInv : (groundSpaceES A L).map (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
      groundSpaceES A L) :
    Commute (parentInteractionES A L)
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) := by
  let T := Matrix.toEuclideanLin (onSiteTensorPow L U)
  let G := groundSpaceES A L
  have hadj : T.adjoint ∘ₗ T = 1 := by
    apply LinearMap.ext
    intro v
    change T.adjoint (T v) = v
    dsimp only [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [onSiteTensorPow_conjTranspose,
      toEuclideanLin_onSiteTensorPow_mul_apply]
    have hU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
    rw [hU', onSiteTensorPow_one]
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hinner (x y : EuclideanSpace ℂ (Cfg d L)) :
      inner ℂ (T x) (T y) = inner ℂ x y := by
    have hy : T.adjoint (T y) = y := by
      simpa only [LinearMap.comp_apply, Module.End.one_apply] using
        congrArg (fun f ↦ f y) hadj
    calc
      inner ℂ (T x) (T y) = inner ℂ x (T.adjoint (T y)) :=
        (LinearMap.adjoint_inner_right T x (T y)).symm
      _ = inner ℂ x y := by rw [hy]
  let I := T.isometryOfInner hinner
  have hG : G.map I.toLinearMap = G := by
    simpa only [I, LinearMap.isometryOfInner_toLinearMap] using
      hInv
  let : G.HasOrthogonalProjection := groundSpaceES_hasOrthogonalProjection A L
  let : (G.map I.toLinearMap).HasOrthogonalProjection := by rw [hG]; infer_instance
  have hproj (v : EuclideanSpace ℂ (Cfg d L)) :
      T (G.starProjection v) = G.starProjection (T v) := by
    have h := I.map_starProjection G v
    have h' : I (G.starProjection v) = G.starProjection (I v) := by
      simpa only [hG] using h
    exact h'
  apply LinearMap.ext
  intro v
  change (Gᗮ).starProjection (T v) = T ((Gᗮ).starProjection v)
  rw [Submodule.starProjection_orthogonal]
  simp only [sub_apply, ContinuousLinearMap.id_apply]
  rw [map_sub, hproj]

/-- A commuting physical rotation transports invariance of the local MPS space.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem groundSpaceES_invariant_rotatePhysical_of_commute
    (A : MPSTensor d D) (U Q : Matrix (Fin d) (Fin d) ℂ) (hComm : Commute U Q)
    (L : ℕ) (hInv : (groundSpaceES A L).map (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
      groundSpaceES A L) :
    (groundSpaceES (rotatePhysical Q A) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        groundSpaceES (rotatePhysical Q A) L := by
  rw [groundSpaceES_rotatePhysical, ← Submodule.map_comp]
  rw [← Module.End.mul_eq_comp, (onSiteTensorPow_commute hComm L).eq,
    Module.End.mul_eq_comp, Submodule.map_comp, hInv]

private theorem commute_matrix_inv_of_isUnit {U Q : Matrix (Fin d) (Fin d) ℂ}
    (hQ : IsUnit Q) (hComm : Commute U Q) : Commute U Q⁻¹ := by
  rcases hQ with ⟨q, rfl⟩
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit] using
    Commute.units_inv_right hComm

/-- An invertible commuting physical rotation preserves and reflects invariance of the local MPS
space.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem groundSpaceES_invariant_rotatePhysical_iff_of_commute
    (A : MPSTensor d D) (U Q : Matrix (Fin d) (Fin d) ℂ) (hQ : IsUnit Q)
    (hComm : Commute U Q) (L : ℕ) :
    ((groundSpaceES (rotatePhysical Q A) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        groundSpaceES (rotatePhysical Q A) L) ↔
      ((groundSpaceES A L).map (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        groundSpaceES A L) := by
  constructor
  · intro hInv
    simpa only [rotatePhysical_rotatePhysical,
      Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).1 hQ),
      rotatePhysical_one] using
        groundSpaceES_invariant_rotatePhysical_of_commute (rotatePhysical Q A) U Q⁻¹
          (commute_matrix_inv_of_isUnit hQ hComm) L hInv
  · exact groundSpaceES_invariant_rotatePhysical_of_commute A U Q hComm L

/-- The cyclic extension of a local operator agrees with its matrix embedding in the
configuration basis.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator
    {R N : ℕ} (hRN : R ≤ N) (i : Fin N)
    (K : Matrix (Cfg d R) (Cfg d R) ℂ) :
    periodicLocalInteractionES (Matrix.toEuclideanLin K) i = Matrix.toEuclideanLin
      (MPOTensor.embedLocalOperator R N hRN i K) := by
  apply LinearMap.ext
  intro v
  ext σ
  simp only [periodicLocalInteractionES, dite_eq_left hRN, LinearEquiv.conj_apply,
    LinearMap.comp_apply]
  dsimp only [LinearIsometryEquiv.symm, LinearIsometryEquiv.toLinearEquiv]
  simp only [LinearEquiv.symm_symm, LinearEquiv.coe_coe]
  change ((cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i).symm
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
      (Matrix.toEuclideanLin K).toContinuousLinearMap
      (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v))) σ =
        (Matrix.toEuclideanLin (MPOTensor.embedLocalOperator R N hRN i K) v) σ
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply]
  change (Matrix.toEuclideanLin K (ContinuousLinearMap.rightFiber
    (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v)
      (cyclicActiveBlockConfigEquiv d R hRN i σ).2))
        (cyclicActiveBlockConfigEquiv d R hRN i σ).1 = _
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  rw [MPOTensor.embedLocalOperator_mulVec_apply]
  have he : cyclicActiveBlockConfigEquiv d R hRN i =
      MPOTensor.windowComplementEquiv R N hRN i := by
    ext ω r
    · rfl
    · simp [cyclicActiveBlockConfigEquiv, MPOTensor.windowComplementEquiv,
        cyclicWindowIndexEquiv, cyclicShiftEquiv, Nat.add_assoc]
  simp only [Matrix.mulVec, dotProduct]
  have hcfg (τ : Cfg d R) :
      (cyclicActiveBlockConfigEquiv d R hRN i).symm
        (τ, (cyclicActiveBlockConfigEquiv d R hRN i σ).2) =
          replaceWindow R hRN i σ τ := by
    apply (cyclicActiveBlockConfigEquiv d R hRN i).injective
    simp [he]
  simp only [ContinuousLinearMap.rightFiber, WithLp.ofLp_toLp,
    cyclicActiveBlockConfigLinearIsometryEquiv_apply_apply, hcfg]
  rfl

/-- A local interaction commuting with the on-site action retains this symmetry after cyclic
extension.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem periodicLocalInteractionES_commute_onSiteTensorPow
    {R N : ℕ} (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (U : Matrix (Fin d) (Fin d) ℂ) (hRN : R ≤ N) (i : Fin N)
    (hComm : Commute h (Matrix.toEuclideanLin (onSiteTensorPow R U))) :
    Commute (periodicLocalInteractionES h i)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  obtain ⟨K, rfl⟩ := Matrix.toEuclideanLin.surjective h
  have hK : Commute K (onSiteTensorPow R U) :=
    Commute.of_map (Matrix.toLpLinAlgEquiv 2).injective hComm
  rw [periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator hRN i K]
  exact (embedLocalOperator_commute_onSiteTensorPow U R hRN i K hK).map
    (Matrix.toLpLinAlgEquiv 2)

/-- A periodic sum of symmetric local interactions commutes with the global on-site action.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem periodicInteractionHamiltonianES_commute_onSiteTensorPow
    {R N : ℕ} (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (U : Matrix (Fin d) (Fin d) ℂ) (hRN : R ≤ N)
    (hComm : Commute h (Matrix.toEuclideanLin (onSiteTensorPow R U))) :
    Commute (periodicInteractionHamiltonianES h N)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  exact Commute.sum_left _ _ _ fun i _ =>
    periodicLocalInteractionES_commute_onSiteTensorPow h U hRN i hComm

/-- An open-chain sum of symmetric local interactions commutes with the global on-site action.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem openInteractionHamiltonianES_commute_onSiteTensorPow
    {R N : ℕ} (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (U : Matrix (Fin d) (Fin d) ℂ) (hRN : R ≤ N)
    (hComm : Commute h (Matrix.toEuclideanLin (onSiteTensorPow R U))) :
    Commute (openInteractionHamiltonianES h N)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  exact Commute.sum_left _ _ _ fun i _ =>
    periodicLocalInteractionES_commute_onSiteTensorPow h U hRN i.1 hComm

/-- Inverse conjugation by a commuting invertible Hermitian physical matrix preserves the
symmetry of a local interaction.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem deformedInteraction_commute_onSiteTensorPow
    (Q U : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.IsHermitian) (hUnit : IsUnit Q)
    (hQU : Commute U Q) (L : ℕ)
    (h : EuclideanSpace ℂ (Cfg d L) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d L))
    (hComm : Commute h (Matrix.toEuclideanLin (onSiteTensorPow L U))) :
    Commute (deformedInteraction L Q h)
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) := by
  rw [deformedInteraction, hQ.inv]
  exact ((onSiteTensorPow_commute (commute_matrix_inv_of_isUnit hUnit hQU) L).symm.mul_left
    hComm).mul_left (onSiteTensorPow_commute (commute_matrix_inv_of_isUnit hUnit hQU) L).symm

variable {r : ℕ} {dim : Fin r → ℕ}

/-- Supplied invariance of the original local space passes to its joint left polar blocks when
the positive factor commutes with the physical action.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem groundSpaceES_invariant_leftPolarBlocks
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A)) (L : ℕ)
    (hInv : (groundSpaceES (toTensorFromBlocks (fun _ => 1) A) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) L) :
    (groundSpaceES (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) L := by
  apply (groundSpaceES_invariant_rotatePhysical_iff_of_commute
    (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) U (leftPolarPhysicalFactor A)
      (leftPolarPhysicalFactor_posDef A).isUnit hComm L).mp
  simpa only [rotatePhysical_toTensorFromBlocks,
    rotatePhysical_leftPolarPhysicalFactor_leftPolarBlocks] using hInv

/-- Supplied invariance of the original local space persists throughout the constructed
isometric deformation when its positive factor commutes with the physical action.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem groundSpaceES_invariant_isometricDeformationBlocks
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A)) (L : ℕ)
    (hInv : (groundSpaceES (toTensorFromBlocks (fun _ => 1) A) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) L) (γ : unitInterval) :
    (groundSpaceES (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) L := by
  unfold isometricDeformationBlocks
  simpa only [rotatePhysical_toTensorFromBlocks] using
    groundSpaceES_invariant_rotatePhysical_of_commute
      (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) U
      (positivePhysicalDeformation (leftPolarPhysicalFactor A) γ)
      (commute_positivePhysicalDeformation U _ hComm γ) L
      (groundSpaceES_invariant_leftPolarBlocks A U hComm L hInv)

/-- The canonical two-site parent projections along the constructed deformation retain a
supplied symmetry of the original two-site space.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem parentInteractionES_isometricDeformationBlocks_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : (groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2) (γ : unitInterval) :
    Commute (parentInteractionES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2)
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) := by
  exact parentInteractionES_commute_onSiteTensorPow_of_invariant _ U hU 2
    (groundSpaceES_invariant_isometricDeformationBlocks A U hComm 2 hInv γ)

/-- The source inverse-conjugated positive interactions along the constructed deformation retain
a supplied symmetry of the original two-site space.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem isometricDeformationInteractionES_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : (groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2) (γ : unitInterval) :
    Commute (isometricDeformationInteractionES A γ).toLinearMap
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) := by
  exact deformedInteraction_commute_onSiteTensorPow _ U
    (positivePhysicalDeformation_posDef _ (leftPolarPhysicalFactor_posDef A) γ).isHermitian
    (positivePhysicalDeformation_isUnit _ (leftPolarPhysicalFactor_posDef A) γ)
    (commute_positivePhysicalDeformation U _ hComm γ) 2 _
    (parentInteractionES_commute_onSiteTensorPow_of_invariant _ U hU 2
      (groundSpaceES_invariant_leftPolarBlocks A U hComm 2 hInv))

/-- The canonical periodic parents along the constructed deformation retain a supplied symmetry
of the original two-site space on every ring of length at least two.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem isometricDeformation_parentHamiltonianES_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : (groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2)
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (parentHamiltonianES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  simpa only [periodicInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    periodicInteractionHamiltonianES_commute_onSiteTensorPow _ U hN
      (parentInteractionES_isometricDeformationBlocks_commute A U hU hComm hInv γ)
/-- The canonical open parents along the constructed deformation retain a supplied symmetry of
the original two-site space on every chain of length at least two.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem isometricDeformation_openParentHamiltonianES_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : (groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2)
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (openParentHamiltonianES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  simpa only [openInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    openInteractionHamiltonianES_commute_onSiteTensorPow _ U hN
      (parentInteractionES_isometricDeformationBlocks_commute A U hU hComm hInv γ)
/-- The periodic sums of the source positive interactions along the constructed deformation
retain a supplied symmetry on every ring of length at least two.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem isometricDeformation_periodicInteractionHamiltonianES_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : (groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2)
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute
      (periodicInteractionHamiltonianES (isometricDeformationInteractionES A γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  exact periodicInteractionHamiltonianES_commute_onSiteTensorPow _ U hN
    (isometricDeformationInteractionES_commute A U hU hComm hInv γ)

/-- The open sums of the source positive interactions along the constructed deformation retain a
supplied symmetry on every chain of length at least two.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem isometricDeformation_openInteractionHamiltonianES_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : (groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        groundSpaceES (toTensorFromBlocks (fun _ => 1) A) 2)
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (openInteractionHamiltonianES (isometricDeformationInteractionES A γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N U)) := by
  exact openInteractionHamiltonianES_commute_onSiteTensorPow _ U hN
    (isometricDeformationInteractionES_commute A U hU hComm hInv γ)

variable {G : Type*} [Monoid G]

/-- Exact on-site symmetry of an injective tensor preserves every local space of its singleton
block assembly.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem groundSpaceES_singletonBlocks_invariant_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (hSymm : IsOnSiteSymmetric A U)
    (g : G) (L : ℕ) :
    (groundSpaceES (toTensorFromBlocks (fun _ : Fin 1 => 1) (fun _ : Fin 1 => A)) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L (U g))) =
        groundSpaceES (toTensorFromBlocks (fun _ : Fin 1 => 1) (fun _ : Fin 1 => A)) L := by
  have hCov : GaugeEquiv A (rotatePhysical (U g) A) :=
    gaugeEquiv_twistedTensor_of_injective A hA U hSymm g
  simpa only [groundSpaceES_toTensorFromBlocks_eq_iSup _ _
    (fun _ : Fin 1 => one_ne_zero) L, iSup_const] using
      groundSpaceES_invariant_of_gauge_covariance A (U g) hCov L

variable [NeZero D]

/-- Exact state symmetry of a normalized injective tensor persists in the canonical two-site
parent projection along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) :
    Commute (parentInteractionES
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2)
      (Matrix.toEuclideanLin (onSiteTensorPow 2 (U g))) := by
  exact parentInteractionES_isometricDeformationBlocks_commute _ (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric A hA hNorm U hU hSymm g)
    (groundSpaceES_singletonBlocks_invariant_of_isOnSiteSymmetric A hA U hSymm g 2) γ

/-- Exact state symmetry of a normalized injective tensor persists in the inverse-conjugated
positive interaction along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem isometricDeformationInteractionES_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) :
    Commute (isometricDeformationInteractionES (fun _ : Fin 1 => A) γ).toLinearMap
      (Matrix.toEuclideanLin (onSiteTensorPow 2 (U g))) := by
  exact isometricDeformationInteractionES_commute _ (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric A hA hNorm U hU hSymm g)
    (groundSpaceES_singletonBlocks_invariant_of_isOnSiteSymmetric A hA U hSymm g 2) γ

/-- Exact state symmetry of a normalized injective tensor persists in the periodic canonical
parent Hamiltonian along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem isometricDeformation_parentHamiltonianES_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    Commute (parentHamiltonianES
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  simpa only [periodicInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    periodicInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
      (parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric
        A hA hNorm U hU hSymm g γ)

/-- Exact state symmetry of a normalized injective tensor persists in the open canonical
parent Hamiltonian along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem isometricDeformation_openParentHamiltonianES_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    Commute (openParentHamiltonianES
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  simpa only [openInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    openInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
      (parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric
        A hA hNorm U hU hSymm g γ)

/-- Exact state symmetry of a normalized injective tensor persists in the periodic sum of
inverse-conjugated positive interactions along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem isometricDeformation_periodicInteractionHamiltonianES_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    Commute (periodicInteractionHamiltonianES
      (isometricDeformationInteractionES (fun _ : Fin 1 => A) γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  exact periodicInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
    (isometricDeformationInteractionES_commute_of_isOnSiteSymmetric A hA hNorm U hU hSymm g γ)

/-- Exact state symmetry of a normalized injective tensor persists in the open sum of
inverse-conjugated positive interactions along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem isometricDeformation_openInteractionHamiltonianES_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    Commute (openInteractionHamiltonianES
      (isometricDeformationInteractionES (fun _ : Fin 1 => A) γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  exact openInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
    (isometricDeformationInteractionES_commute_of_isOnSiteSymmetric A hA hNorm U hU hSymm g γ)


/-- Exact state symmetry of an injective trace-preserving tensor persists in the canonical two-site
parent projection along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) :
    Commute (parentInteractionES
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2)
      (Matrix.toEuclideanLin (onSiteTensorPow 2 (U g))) := by
  exact parentInteractionES_isometricDeformationBlocks_commute _ (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_of_isTP A hA hTP U hU hSymm g)
    (groundSpaceES_singletonBlocks_invariant_of_isOnSiteSymmetric A hA U hSymm g 2) γ

/-- Exact state symmetry of an injective trace-preserving tensor persists in the inverse-conjugated
positive interaction along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem isometricDeformationInteractionES_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) :
    Commute (isometricDeformationInteractionES (fun _ : Fin 1 => A) γ).toLinearMap
      (Matrix.toEuclideanLin (onSiteTensorPow 2 (U g))) := by
  exact isometricDeformationInteractionES_commute _ (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_of_isTP A hA hTP U hU hSymm g)
    (groundSpaceES_singletonBlocks_invariant_of_isOnSiteSymmetric A hA U hSymm g 2) γ

/-- Exact state symmetry of an injective trace-preserving tensor persists in the periodic canonical
parent Hamiltonian along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem isometricDeformation_parentHamiltonianES_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    Commute (parentHamiltonianES
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  simpa only [periodicInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    periodicInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
      (parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric_of_isTP
        A hA hTP U hU hSymm g γ)

/-- Exact state symmetry of an injective trace-preserving tensor persists in the open canonical
parent Hamiltonian along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem isometricDeformation_openParentHamiltonianES_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    Commute (openParentHamiltonianES
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  simpa only [openInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    openInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
      (parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric_of_isTP
        A hA hTP U hU hSymm g γ)

/-- Exact state symmetry of an injective trace-preserving tensor persists in the periodic sum of
inverse-conjugated positive interactions along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem isometricDeformation_periodicInteractionHamiltonianES_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    Commute (periodicInteractionHamiltonianES
      (isometricDeformationInteractionES (fun _ : Fin 1 => A) γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  exact periodicInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
    (isometricDeformationInteractionES_commute_of_isOnSiteSymmetric_of_isTP A hA hTP U hU hSymm g γ)

/-- Exact state symmetry of an injective trace-preserving tensor persists in the open sum of
inverse-conjugated positive interactions along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem isometricDeformation_openInteractionHamiltonianES_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    Commute (openInteractionHamiltonianES
      (isometricDeformationInteractionES (fun _ : Fin 1 => A) γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  exact openInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
    (isometricDeformationInteractionES_commute_of_isOnSiteSymmetric_of_isTP A hA hTP U hU hSymm g γ)


end MPSTensor
