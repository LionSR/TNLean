/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Deformation.InjectiveIsometricDeformationSymmetry
import TNLean.MPS.ParentHamiltonian.BlockGroundSpace.BlockSumIntervalSpaces
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PeriodicRangeComparison
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.LocalTermTranslates
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Deformation.ParentHamiltonianSymmetry
import TNLean.MPS.Operator.Interaction.GappedInteractionPath

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

These are consequences of Schuch--Pérez-García--Cirac, arXiv:1010.3732,
lines 672--676, stated with the invariance of the original local space and
the commutation of the positive factor as explicit hypotheses. The
single-block consequences derive both hypotheses from exact state symmetry
for a one-site injective tensor in either canonical orientation:
\(\sum_i A_i A_i^\dagger=I\) or \(\sum_i A_i^\dagger A_i=I\).
The latter is the partial-trace normalization printed in the source.
For several jointly injective blocks in that normalization, where the
symmetry permutes the blocks (source lines 649--659), both hypotheses are
derived in `TNLean.MPS.ParentHamiltonian.BlockIsometricDeformationSymmetry`.

**Scope restriction (exact vector symmetry):** The single-block derived statements
here assume that the matrix product vectors are invariant, not only invariant up to
a phase. Symmetry up to a phase is derived for one or several blocks in the printed
normalization in `TNLean.MPS.ParentHamiltonian.BlockIsometricDeformationSymmetry`;
see docs/paper-gaps/spc11_isometric_symmetry_unitary_virtual.tex
(https://sirui-lu.com/TNLean/paper-gaps/spc11_isometric_symmetry_unitary_virtual.pdf).
-/

open MPTensor

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

/-- A unitary on-site action preserving the supplied local ground space commutes with the matrix
of its canonical parent projection.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem toMatrix'_parentInteraction_commute_onSiteTensorPow_of_invariant
    (A : MPSTensor d D) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (L : ℕ)
    (hInv : ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
      ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    Commute (LinearMap.toMatrix' (parentInteraction A L)) (onSiteTensorPow L U) := by
  refine Commute.of_map (Matrix.toLpLinAlgEquiv 2).injective ?_
  change Commute (Matrix.toEuclideanLin (LinearMap.toMatrix' (parentInteraction A L)))
    (Matrix.toEuclideanLin (onSiteTensorPow L U))
  rw [toEuclideanLin_toMatrix'_parentInteraction]
  let T := Matrix.toEuclideanLin (onSiteTensorPow L U)
  let G := ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)
  have hadj : T.adjoint ∘ₗ T = 1 := by
    apply LinearMap.ext
    intro v
    change T.adjoint (T v) = v
    dsimp only [T]
    have hU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, onSiteTensorPow_conjTranspose,
      toEuclideanLin_onSiteTensorPow_mul_apply, hU', onSiteTensorPow_one]
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hinner (x y : EuclideanSpace ℂ (Cfg d L)) : inner ℂ (T x) (T y) = inner ℂ x y := by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hadj, Module.End.one_apply]
  let I := T.isometryOfInner hinner
  have hG : G.map I.toLinearMap = G := by
    simpa only [I, LinearMap.isometryOfInner_toLinearMap] using hInv
  let : G.HasOrthogonalProjection := map_groundSpace_hasOrthogonalProjection A L
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
theorem map_groundSpace_invariant_rotatePhysical_of_commute
    (A : MPSTensor d D) (U Q : Matrix (Fin d) (Fin d) ℂ) (hComm : Commute U Q)
    (L : ℕ) (hInv : ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
      ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    ((groundSpace (rotatePhysical Q A) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        ((groundSpace (rotatePhysical Q A) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  rw [map_groundSpace_rotatePhysical, ← Submodule.map_comp]
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
theorem map_groundSpace_invariant_rotatePhysical_iff_of_commute
    (A : MPSTensor d D) (U Q : Matrix (Fin d) (Fin d) ℂ) (hQ : IsUnit Q)
    (hComm : Commute U Q) (L : ℕ) :
    (((groundSpace (rotatePhysical Q A) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        ((groundSpace (rotatePhysical Q A) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) ↔
      (((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        ((groundSpace A L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) := by
  constructor
  · intro hInv
    simpa only [rotatePhysical_rotatePhysical,
      Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).1 hQ),
      rotatePhysical_one] using
        map_groundSpace_invariant_rotatePhysical_of_commute (rotatePhysical Q A) U Q⁻¹
          (commute_matrix_inv_of_isUnit hQ hComm) L hInv
  · exact map_groundSpace_invariant_rotatePhysical_of_commute A U Q hComm L

private theorem placeAlong_chainWindow_commute_onSiteTensorPow {R N : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (a : ℕ) (ha : a + R ≤ N)
    (K : Matrix (Cfg d R) (Cfg d R) ℂ) (hK : Commute K (onSiteTensorPow R U)) :
    Commute (ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow a ha) K)
      (onSiteTensorPow N U) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine (commute_iff_eq _ _).2 (Matrix.ext fun σ τ ↦ ?_)
    obtain rfl : σ = default := Subsingleton.elim _ _
    obtain rfl : τ = default := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Fintype.sum_unique, mul_comm]
  by_cases haN : a < N
  · have hw : ManyBody.chainWindow a ha = ManyBody.ringWindow (by omega) ⟨a, haN⟩ :=
      Function.Embedding.ext fun j ↦ Fin.ext (by
        have hj : a + j.val < N := by have := j.isLt; omega
        simp only [ManyBody.val_chainWindow, ManyBody.ringWindow_apply, Fin.val_add,
          Fin.val_castLE, Nat.mod_eq_of_lt hj])
    rw [hw]
    exact placeAlong_ringWindow_commute_onSiteTensorPow U R _ _ K hK
  · obtain rfl : R = 0 := by omega
    have hw : ManyBody.chainWindow a ha = ManyBody.ringWindow (by omega) ⟨0, hN⟩ :=
      Function.Embedding.ext fun j ↦ j.elim0
    rw [hw]
    exact placeAlong_ringWindow_commute_onSiteTensorPow U 0 _ _ K hK

/-- The Hamiltonian of the translates on the open chain of a local matrix commuting with the
on-site action commutes with the global on-site action.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem hamiltonian_chainTranslates_commute_onSiteTensorPow {R : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (U : Matrix (Fin d) (Fin d) ℂ) (N : ℕ)
    (hComm : Commute h (onSiteTensorPow R U)) :
    Commute (ManyBody.Interaction.chainTranslates R N h).hamiltonian (onSiteTensorPow N U) :=
  Commute.sum_left _ _ _ fun i _ ↦
    placeAlong_chainWindow_commute_onSiteTensorPow U i.val (by omega) h hComm

/-- Inverse conjugation by a commuting invertible Hermitian physical matrix preserves the
symmetry of a local interaction.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem deformedInteraction_commute_onSiteTensorPow
    (Q U : Matrix (Fin d) (Fin d) ℂ) (hQ : Q.IsHermitian) (hUnit : IsUnit Q)
    (hQU : Commute U Q) (L : ℕ) (h : Matrix (Cfg d L) (Cfg d L) ℂ)
    (hComm : Commute h (onSiteTensorPow L U)) :
    Commute (deformedInteraction L Q h) (onSiteTensorPow L U) := by
  have hc : Commute (onSiteTensorPow L U) (onSiteTensorPow L Q⁻¹) := by
    rw [commute_iff_eq, ← onSiteTensorPow_mul, ← onSiteTensorPow_mul,
      (commute_matrix_inv_of_isUnit hUnit hQU).eq]
  rw [deformedInteraction, hQ.inv]
  exact (hc.symm.mul_left hComm).mul_left hc.symm

variable {r : ℕ} {dim : Fin r → ℕ}

/-- Supplied invariance of the original local space passes to its joint left polar blocks when
the positive factor commutes with the physical action.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem map_groundSpace_invariant_leftPolarBlocks
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A)) (L : ℕ)
    (hInv : ((groundSpace (toTensorFromBlocks (fun _ => 1) A) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) :
    (((groundSpace (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  apply (map_groundSpace_invariant_rotatePhysical_iff_of_commute
    (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) U (leftPolarPhysicalFactor A)
      (leftPolarPhysicalFactor_posDef A).isUnit hComm L).mp
  simpa only [rotatePhysical_toTensorFromBlocks,
    rotatePhysical_leftPolarPhysicalFactor_leftPolarBlocks] using hInv

/-- Supplied invariance of the original local space persists throughout the constructed
isometric deformation when its positive factor commutes with the physical action.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem map_groundSpace_invariant_isometricDeformationBlocks
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A)) (L : ℕ)
    (hInv : ((groundSpace (toTensorFromBlocks (fun _ => 1) A) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) (γ : unitInterval) :
    (((groundSpace (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)).map
      (Matrix.toEuclideanLin (onSiteTensorPow L U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  unfold isometricDeformationBlocks
  simpa only [rotatePhysical_toTensorFromBlocks] using
    map_groundSpace_invariant_rotatePhysical_of_commute
      (toTensorFromBlocks (fun _ => 1) (leftPolarBlocks A)) U
      (positivePhysicalDeformation (leftPolarPhysicalFactor A) γ)
      (commute_positivePhysicalDeformation U _ hComm γ) L
      (map_groundSpace_invariant_leftPolarBlocks A U hComm L hInv)

/-- The source inverse-conjugated positive interactions along the constructed deformation retain
a supplied symmetry of the original two-site space.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem isometricDeformationInteraction_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) (γ : unitInterval) :
    Commute (isometricDeformationInteraction A γ) (onSiteTensorPow 2 U) := by
  exact deformedInteraction_commute_onSiteTensorPow _ U
    (positivePhysicalDeformation_posDef _ (leftPolarPhysicalFactor_posDef A) γ).isHermitian
    (positivePhysicalDeformation_isUnit _ (leftPolarPhysicalFactor_posDef A) γ)
    (commute_positivePhysicalDeformation U _ hComm γ) 2 _
    (toMatrix'_parentInteraction_commute_onSiteTensorPow_of_invariant _ U hU 2
      (map_groundSpace_invariant_leftPolarBlocks A U hComm 2 hInv))

/-- The periodic sums of the source positive interactions along the constructed deformation
retain a supplied symmetry on every ring of length at least two.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem isometricDeformation_hamiltonian_translationInvariant_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (ManyBody.Interaction.translationInvariant N
        (isometricDeformationInteraction A γ)).hamiltonian
      (onSiteTensorPow N U) :=
  haveI : NeZero N := ⟨by omega⟩
  hamiltonian_translationInvariant_commute_onSiteTensorPow U _
    (isometricDeformationInteraction_commute A U hU hComm hInv γ)

/-- The open sums of the source positive interactions along the constructed deformation retain a
supplied symmetry on every chain of length at least two.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem isometricDeformation_hamiltonian_chainTranslates_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (γ : unitInterval) (N : ℕ) :
    Commute (ManyBody.Interaction.chainTranslates 2 N
        (isometricDeformationInteraction A γ)).hamiltonian
      (onSiteTensorPow N U) :=
  hamiltonian_chainTranslates_commute_onSiteTensorPow _ U N
    (isometricDeformationInteraction_commute A U hU hComm hInv γ)

variable {G : Type*} [Monoid G]

/-- Exact on-site symmetry of an injective tensor preserves every local space of its singleton
block assembly.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem map_groundSpace_singletonBlocks_invariant_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (hSymm : IsOnSiteSymmetric A U)
    (g : G) (L : ℕ) :
    (((groundSpace (toTensorFromBlocks (fun _ : Fin 1 => 1) (fun _ : Fin 1 => A)) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)).map
      (Matrix.toEuclideanLin (onSiteTensorPow L (U g))) =
        ((groundSpace (toTensorFromBlocks (fun _ : Fin 1 => 1) (fun _ : Fin 1 => A)) L).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  have hCov : GaugeEquiv A (rotatePhysical (U g) A) :=
    gaugeEquiv_twistedTensor_of_injective A hA U hSymm g
  simpa only [map_groundSpace_toTensorFromBlocks_eq_iSup _ _
    (fun _ : Fin 1 => one_ne_zero) L, iSup_const] using
      map_groundSpace_invariant_of_gauge_covariance A (U g) hCov L

variable [NeZero D]

/-- Exact state symmetry of a normalized injective tensor persists in the inverse-conjugated
positive interaction along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem isometricDeformationInteraction_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) :
    Commute (isometricDeformationInteraction (fun _ : Fin 1 => A) γ) (onSiteTensorPow 2 (U g)) := by
  exact isometricDeformationInteraction_commute _ (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric A hA hNorm U hU hSymm g)
    (map_groundSpace_singletonBlocks_invariant_of_isOnSiteSymmetric A hA U hSymm g 2) γ

/-- Exact state symmetry of a normalized injective tensor persists in the periodic sum of
inverse-conjugated positive interactions along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem isometricDeformation_hamiltonian_translationInvariant_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (ManyBody.Interaction.translationInvariant N
        (isometricDeformationInteraction (fun _ : Fin 1 => A) γ)).hamiltonian
      (onSiteTensorPow N (U g)) :=
  haveI : NeZero N := ⟨by omega⟩
  hamiltonian_translationInvariant_commute_onSiteTensorPow (U g) _
    (isometricDeformationInteraction_commute_of_isOnSiteSymmetric A hA hNorm U hU hSymm g γ)

/-- Exact state symmetry of a normalized injective tensor persists in the open sum of
inverse-conjugated positive interactions along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem isometricDeformation_hamiltonian_chainTranslates_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    (N : ℕ) :
    Commute (ManyBody.Interaction.chainTranslates 2 N
        (isometricDeformationInteraction (fun _ : Fin 1 => A) γ)).hamiltonian
      (onSiteTensorPow N (U g)) :=
  hamiltonian_chainTranslates_commute_onSiteTensorPow _ (U g) N
    (isometricDeformationInteraction_commute_of_isOnSiteSymmetric A hA hNorm U hU hSymm g γ)

/-- Exact state symmetry of an injective trace-preserving tensor persists in the inverse-conjugated
positive interaction along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem isometricDeformationInteraction_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) :
    Commute (isometricDeformationInteraction (fun _ : Fin 1 => A) γ) (onSiteTensorPow 2 (U g)) := by
  exact isometricDeformationInteraction_commute _ (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_of_isTP A hA hTP U hU hSymm g)
    (map_groundSpace_singletonBlocks_invariant_of_isOnSiteSymmetric A hA U hSymm g 2) γ

/-- Exact state symmetry of an injective trace-preserving tensor persists in the periodic sum of
inverse-conjugated positive interactions along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem isometricDeformation_hamiltonian_translationInvariant_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (ManyBody.Interaction.translationInvariant N
        (isometricDeformationInteraction (fun _ : Fin 1 => A) γ)).hamiltonian
      (onSiteTensorPow N (U g)) :=
  haveI : NeZero N := ⟨by omega⟩
  hamiltonian_translationInvariant_commute_onSiteTensorPow (U g) _
    (isometricDeformationInteraction_commute_of_isOnSiteSymmetric_of_isTP
        A hA hTP U hU hSymm g γ)

/-- Exact state symmetry of an injective trace-preserving tensor persists in the open sum of
inverse-conjugated positive interactions along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem isometricDeformation_hamiltonian_chainTranslates_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    (N : ℕ) :
    Commute (ManyBody.Interaction.chainTranslates 2 N
        (isometricDeformationInteraction (fun _ : Fin 1 => A) γ)).hamiltonian
      (onSiteTensorPow N (U g)) :=
  hamiltonian_chainTranslates_commute_onSiteTensorPow _ (U g) N
    (isometricDeformationInteraction_commute_of_isOnSiteSymmetric_of_isTP
        A hA hTP U hU hSymm g γ)

end MPSTensor

/-! ### The interaction Hamiltonians

The symmetry facts for the matrix of the canonical parent interaction and for the Hamiltonians
of the translates of a local matrix on the ring (`ManyBody.Interaction.translationInvariant`)
and on the open chain (`ManyBody.Interaction.chainTranslates`), in particular of the parent
interactions `parentRingInteraction` and `parentChainInteraction`. -/

namespace MPSTensor

open scoped Matrix

variable {d D : ℕ}

variable {r : ℕ} {dim : Fin r → ℕ}

/-- The matrices of the canonical two-site parent projections along the constructed deformation
retain a supplied symmetry of the original two-site space.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem toMatrix'_parentInteraction_isometricDeformation_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap)) (γ : unitInterval) :
    Commute (LinearMap.toMatrix' (parentInteraction
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2))
      (onSiteTensorPow 2 U) :=
  toMatrix'_parentInteraction_commute_onSiteTensorPow_of_invariant _ U hU 2
    (map_groundSpace_invariant_isometricDeformationBlocks A U hComm 2 hInv γ)

/-- The canonical periodic parents along the constructed deformation retain a supplied symmetry
of the original two-site space on every ring of length at least two.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem hamiltonian_parentRingInteraction_isometricDeformation_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (parentRingInteraction
        (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N).hamiltonian
      (onSiteTensorPow N U) := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.Interaction.hamiltonian_translationInvariant_of_le _ hN]
  exact Commute.sum_left _ _ _ fun i _ ↦ placeAlong_ringWindow_commute_onSiteTensorPow U 2 hN i _
    (toMatrix'_parentInteraction_isometricDeformation_commute A U hU hComm hInv γ)

/-- The canonical open parents along the constructed deformation retain a supplied symmetry of
the original two-site space on every chain.
Source: arXiv:1010.3732, lines 672--676; invariance of the local space is
supplied explicitly where required. -/
theorem hamiltonian_parentChainInteraction_isometricDeformation_commute
    (A : (j : Fin r) → MPSTensor d (dim j)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hComm : Commute U (leftPolarPhysicalFactor A))
    (hInv : ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
      (Matrix.toEuclideanLin (onSiteTensorPow 2 U)) =
        ((groundSpace (toTensorFromBlocks (fun _ => 1) A) 2).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap))
    (γ : unitInterval) (N : ℕ) :
    Commute (parentChainInteraction
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N).hamiltonian
      (onSiteTensorPow N U) :=
  hamiltonian_chainTranslates_commute_onSiteTensorPow _ U N
    (toMatrix'_parentInteraction_isometricDeformation_commute A U hU hComm hInv γ)

variable {G : Type*} [Monoid G] [NeZero D]

/-- Exact state symmetry of a normalized injective tensor persists in the matrix of the
canonical two-site parent projection along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem toMatrix'_parentInteraction_isometricDeformation_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) :
    Commute (LinearMap.toMatrix' (parentInteraction
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2))
      (onSiteTensorPow 2 (U g)) :=
  toMatrix'_parentInteraction_isometricDeformation_commute _ (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric A hA hNorm U hU hSymm g)
    (map_groundSpace_singletonBlocks_invariant_of_isOnSiteSymmetric A hA U hSymm g 2) γ

/-- Exact state symmetry of a normalized injective tensor persists in the periodic canonical
parent Hamiltonian along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem hamiltonian_parentRingInteraction_isometricDeformation_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (parentRingInteraction
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2 N).hamiltonian
      (onSiteTensorPow N (U g)) := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.Interaction.hamiltonian_translationInvariant_of_le _ hN]
  exact Commute.sum_left _ _ _ fun i _ ↦
    placeAlong_ringWindow_commute_onSiteTensorPow (U g) 2 hN i _
      (toMatrix'_parentInteraction_isometricDeformation_commute_of_isOnSiteSymmetric
        A hA hNorm U hU hSymm g γ)

/-- Exact state symmetry of a normalized injective tensor persists in the open canonical
parent Hamiltonian along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case in the unital canonical orientation. -/
theorem hamiltonian_parentChainInteraction_isometricDeformation_commute_of_isOnSiteSymmetric
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hNorm : Kraus.transferMap A 1 = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) (N : ℕ) :
    Commute (parentChainInteraction
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2 N).hamiltonian
      (onSiteTensorPow N (U g)) :=
  hamiltonian_chainTranslates_commute_onSiteTensorPow _ (U g) N
    (toMatrix'_parentInteraction_isometricDeformation_commute_of_isOnSiteSymmetric
      A hA hNorm U hU hSymm g γ)

/-- Exact state symmetry of an injective trace-preserving tensor persists in the matrix of the
canonical two-site parent projection along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem toMatrix'_parentInteraction_isometricDeformation_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) :
    Commute (LinearMap.toMatrix' (parentInteraction
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2))
      (onSiteTensorPow 2 (U g)) :=
  toMatrix'_parentInteraction_isometricDeformation_commute _ (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_of_isTP A hA hTP U hU hSymm g)
    (map_groundSpace_singletonBlocks_invariant_of_isOnSiteSymmetric A hA U hSymm g 2) γ

/-- Exact state symmetry of an injective trace-preserving tensor persists in the periodic
canonical parent Hamiltonian along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem hamiltonian_parentRingInteraction_isometricDeformation_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Commute (parentRingInteraction
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2 N).hamiltonian
      (onSiteTensorPow N (U g)) := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.Interaction.hamiltonian_translationInvariant_of_le _ hN]
  exact Commute.sum_left _ _ _ fun i _ ↦
    placeAlong_ringWindow_commute_onSiteTensorPow (U g) 2 hN i _
      (toMatrix'_parentInteraction_isometricDeformation_commute_of_isOnSiteSymmetric_of_isTP
        A hA hTP U hU hSymm g γ)

/-- Exact state symmetry of an injective trace-preserving tensor persists in the open canonical
parent Hamiltonian along its constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, in the already-blocked
single injective case with the printed trace-preserving normalization. -/
theorem hamiltonian_parentChainInteraction_isometricDeformation_commute_of_isOnSiteSymmetric_of_isTP
    (A : MPSTensor d D) (hA : Kraus.IsInjective A) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) (γ : unitInterval) (N : ℕ) :
    Commute (parentChainInteraction
      (toTensorFromBlocks (fun _ : Fin 1 => 1)
        (isometricDeformationBlocks (fun _ : Fin 1 => A) γ)) 2 N).hamiltonian
      (onSiteTensorPow N (U g)) :=
  hamiltonian_chainTranslates_commute_onSiteTensorPow _ (U g) N
    (toMatrix'_parentInteraction_isometricDeformation_commute_of_isOnSiteSymmetric_of_isTP
      A hA hTP U hU hSymm g γ)

end MPSTensor
