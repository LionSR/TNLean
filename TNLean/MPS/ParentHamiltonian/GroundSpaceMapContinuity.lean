/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.InjectiveRangeProjectorContinuity
import TNLean.MPS.ParentHamiltonian.GroundSpaceGram
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian

/-!
# Continuity of finite-window MPS ground-space maps

For fixed window length, each entry of the boundary map is a trace of a
finite product of tensor letters. Thus a continuous tensor family gives a
continuous family of boundary maps. When the tensors are block-injective at
that window, their orthogonal local ground-space projectors are continuous
by the inverse-Gram formula.

These finite-window statements are ingredients for a uniform gap argument;
they do not themselves give a gap uniform in the deformation parameter.

**Transitional (#10948).** The continuity statements for the Euclidean-space operators
(`continuous_parentInteractionES_family_of_groundProjection`,
`continuous_localTermES_family_of_groundProjection`,
`continuous_openParentHamiltonianES_family_of_groundProjection`,
`continuous_parentHamiltonianES_family_of_groundProjection`,
`continuous_parentInteractionES_family`, `continuous_openParentHamiltonianES_family`,
`continuous_parentHamiltonianES_family`) are kept
until their users are converted. The last section states continuity of the matrices: the local
parent interaction, the terms and Hamiltonian of the parent interaction on the ring, and the
Hamiltonian of the parent interaction on the open chain.
-/

open scoped Matrix

namespace MPSTensor

/-- Evaluation of a fixed virtual word varies continuously with the tensor
letters. -/
theorem continuous_evalWord_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A)
    (w : List (Fin d)) :
    Continuous fun x => Kraus.evalWord (A x) w := by
  induction w with
  | nil => simpa only [Kraus.evalWord_nil] using
      (continuous_const : Continuous fun _ : X => (1 : Matrix (Fin D) (Fin D) ℂ))
  | cons i w ih =>
      have hi : Continuous fun x => A x i := (continuous_apply i).comp hA
      simpa only [Kraus.evalWord_cons] using hi.matrix_mul ih

/-- The Hilbert-space boundary map on a fixed window is continuous as an
operator-norm-valued function of a continuous tensor family. -/
theorem continuous_groundSpaceMapES_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (L : ℕ) :
    Continuous fun x => groundSpaceMapES (A x) L := by
  apply ContinuousLinearMap.continuous_of_euclideanSingle
  rintro ⟨b, a⟩
  let e := EuclideanSpace.equiv (Cfg d L) ℂ
  apply e.symm.continuous.comp
  apply continuous_pi
  intro σ
  have hword := continuous_evalWord_family A hA (List.ofFn σ)
  have htrace : Continuous fun x =>
      Matrix.trace (Kraus.evalWord (A x) (List.ofFn σ) *
        Matrix.single a b (1 : ℂ)) :=
    (hword.matrix_mul continuous_const).matrix_trace
  convert htrace using 1
  ext x
  change (groundSpaceMapES (A x) L (EuclideanSpace.single (b, a) 1)) σ = _
  rw [groundSpaceMapES_single]
  change (groundSpaceMap (A x) L (Matrix.single a b 1)) σ = _
  rw [groundSpaceMap_apply]

/-- Along a continuously varying family of tensors that is block-injective
at one fixed length, the orthogonal projector onto that local ground space
varies continuously. This is a finite-window statement. -/
theorem continuous_groundSpaceES_starProjection_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (L : ℕ)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) L) :
    Continuous fun x => (groundSpaceES (A x) L).starProjection := by
  have hT := continuous_groundSpaceMapES_family A hA L
  have hTinj (x : X) : Function.Injective (groundSpaceMapES (A x) L) :=
    groundSpaceMapES_injective_of_isNBlkInjective (hInj x)
  have hproj := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun x => groundSpaceMapES (A x) L) hT hTinj
  have heq :
      (fun x => ContinuousLinearMap.injectiveRangeProjector
        (groundSpaceMapES (A x) L) (hTinj x)) =
      (fun x => (groundSpaceES (A x) L).starProjection) := by
    funext x
    exact injectiveRangeProjector_groundSpaceMapES_eq_starProjection (A x) L (hInj x)
  rw [← heq]
  exact hproj

/-- Continuity of the local ground-space projection implies continuity of the
canonical parent interaction. No injectivity of the full tensor is required. -/
theorem continuous_parentInteractionES_family_of_groundProjection
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (L : ℕ)
    (hProj : Continuous fun x => (groundSpaceES (A x) L).starProjection) :
    Continuous fun x => LinearMap.toContinuousLinearMap (parentInteractionES (A x) L) := by
  have hDiff : Continuous fun x =>
      (1 : EuclideanSpace ℂ (Cfg d L) →L[ℂ] EuclideanSpace ℂ (Cfg d L)) -
        (groundSpaceES (A x) L).starProjection :=
    continuous_const.sub hProj
  convert hDiff using 1
  ext x v
  simp only [parentInteractionES, Submodule.starProjection_orthogonal]
  rfl

/-- At a fixed chain length, an individual translated parent term is
continuous as an operator whenever its fixed-range ground-space projection
is continuous. -/
theorem continuous_localTermES_family_of_groundProjection
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {L N : ℕ}
    (hLN : L ≤ N)
    (hProj : Continuous fun x => (groundSpaceES (A x) L).starProjection)
    (i : Fin N) :
    Continuous fun x => LinearMap.toContinuousLinearMap (localTermES (A x) L i) := by
  have hP := continuous_parentInteractionES_family_of_groundProjection A L hProj
  have hS : ∀ τ : Cfg d N,
      Continuous fun x =>
        (LinearMap.toContinuousLinearMap
          ((cyclicRestrictES (d := d) (Fin.pos i) L i τ).adjoint)).comp
          ((LinearMap.toContinuousLinearMap (parentInteractionES (A x) L)).comp
            (LinearMap.toContinuousLinearMap
              (cyclicRestrictES (d := d) (Fin.pos i) L i τ))) := by
    intro τ
    exact continuous_const.clm_comp (hP.clm_comp continuous_const)
  have hSum : Continuous fun x =>
      ((((d ^ L : ℕ) : ℂ)⁻¹) •
        (∑ τ : Cfg d N,
          (LinearMap.toContinuousLinearMap
            ((cyclicRestrictES (d := d) (Fin.pos i) L i τ).adjoint)).comp
            ((LinearMap.toContinuousLinearMap (parentInteractionES (A x) L)).comp
              (LinearMap.toContinuousLinearMap
                (cyclicRestrictES (d := d) (Fin.pos i) L i τ))))) := by
    exact (continuous_const : Continuous fun _ : X =>
      ((((d ^ L : ℕ) : ℂ)⁻¹))).smul
        (continuous_finsetSum _ fun τ _ => hS τ)
  convert hSum using 1
  funext x
  rw [localTermES_eq_average_localTermESSummand (A x) hLN i]
  apply ContinuousLinearMap.ext
  intro v
  simp [localTermESSummand]

/-- Continuity of the local ground-space projection implies continuity of the
open parent Hamiltonian at fixed volume. -/
theorem continuous_openParentHamiltonianES_family_of_groundProjection
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {L N : ℕ}
    (hLN : L ≤ N)
    (hProj : Continuous fun x => (groundSpaceES (A x) L).starProjection) :
    Continuous fun x =>
      LinearMap.toContinuousLinearMap (openParentHamiltonianES (A x) L N) := by
  have hTerms : ∀ i : NonwrappingStart L N,
      Continuous fun x => LinearMap.toContinuousLinearMap (localTermES (A x) L i.1) :=
    fun i => continuous_localTermES_family_of_groundProjection A hLN hProj i.1
  have hSum : Continuous fun x =>
      ∑ i : NonwrappingStart L N,
        LinearMap.toContinuousLinearMap (localTermES (A x) L i.1) :=
    continuous_finsetSum _ fun i _ => hTerms i
  convert hSum using 1
  funext x
  apply ContinuousLinearMap.ext
  intro v
  simp [openParentHamiltonianES]

/-- Continuity of the local ground-space projection implies continuity of the
periodic parent Hamiltonian at fixed volume. -/
theorem continuous_parentHamiltonianES_family_of_groundProjection
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {L N : ℕ}
    (hLN : L ≤ N)
    (hProj : Continuous fun x => (groundSpaceES (A x) L).starProjection) :
    Continuous fun x =>
      LinearMap.toContinuousLinearMap (parentHamiltonianES (A x) L N) := by
  have hTerms : ∀ i : Fin N,
      Continuous fun x => LinearMap.toContinuousLinearMap (localTermES (A x) L i) :=
    fun i => continuous_localTermES_family_of_groundProjection A hLN hProj i
  have hSum : Continuous fun x =>
      ∑ i : Fin N, LinearMap.toContinuousLinearMap (localTermES (A x) L i) :=
    continuous_finsetSum _ fun i _ => hTerms i
  convert hSum using 1
  funext x
  rw [parentHamiltonianES_eq_sum_localTermES]
  apply ContinuousLinearMap.ext
  intro v
  simp

/-- For a fixed interaction range, the canonical parent term varies continuously
along a tensor family injective at that range. -/
theorem continuous_parentInteractionES_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (L : ℕ)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) L) :
    Continuous fun x => LinearMap.toContinuousLinearMap (parentInteractionES (A x) L) :=
  continuous_parentInteractionES_family_of_groundProjection A L
    (continuous_groundSpaceES_starProjection_family A hA L hInj)

/-- The open parent Hamiltonian at fixed volume varies continuously along a
tensor family injective at the interaction range. -/
theorem continuous_openParentHamiltonianES_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) {L N : ℕ}
    (hLN : L ≤ N) (hInj : ∀ x, Kraus.IsNBlkInjective (A x) L) :
    Continuous fun x =>
      LinearMap.toContinuousLinearMap (openParentHamiltonianES (A x) L N) :=
  continuous_openParentHamiltonianES_family_of_groundProjection A hLN
    (continuous_groundSpaceES_starProjection_family A hA L hInj)

/-- The periodic parent Hamiltonian at fixed volume varies continuously along
a tensor family injective at the interaction range. -/
theorem continuous_parentHamiltonianES_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) {L N : ℕ}
    (hLN : L ≤ N) (hInj : ∀ x, Kraus.IsNBlkInjective (A x) L) :
    Continuous fun x =>
      LinearMap.toContinuousLinearMap (parentHamiltonianES (A x) L N) :=
  continuous_parentHamiltonianES_family_of_groundProjection A hLN
    (continuous_groundSpaceES_starProjection_family A hA L hInj)

/-! ### Continuity of the parent matrices -/

/-- A matrix placed along an injection of sites depends continuously on the matrix. -/
private theorem continuous_placeAlong {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    {d : ℕ} (w : W ↪ V) : Continuous (ManyBody.placeAlong (X := fun _ : V ↦ Fin d) w) := by
  classical
  exact (ManyBody.placeAlongHom (X := fun _ : V ↦ Fin d) w).toAlgHom.toLinearMap
    |>.continuous_of_finiteDimensional

/-- The continuous operator of the local parent matrix is the identity minus the orthogonal
projection onto the local ground space. -/
private theorem toEuclideanCLM_toMatrix'_parentInteraction {d D : ℕ} (A : MPSTensor d D)
    (L : ℕ) :
    (Matrix.toEuclideanCLM : Matrix (Cfg d L) (Cfg d L) ℂ ≃⋆ₐ[ℂ] _)
        (LinearMap.toMatrix' (parentInteraction A L)) =
      1 - (groundSpaceES A L).starProjection := by
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_toMatrix'_parentInteraction,
    Submodule.starProjection_orthogonal]
  rfl

/-- Continuity of the local ground-space projection implies continuity of the matrix of the
canonical parent interaction. No injectivity of the full tensor is required. -/
theorem continuous_toMatrix'_parentInteraction_family_of_groundProjection
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (L : ℕ)
    (hProj : Continuous fun x => (groundSpaceES (A x) L).starProjection) :
    Continuous fun x => LinearMap.toMatrix' (parentInteraction (A x) L) := by
  let e := (Matrix.toEuclideanCLM : Matrix (Cfg d L) (Cfg d L) ℂ ≃⋆ₐ[ℂ] _).symm
  have he : Continuous e := e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  have heq : (fun x => LinearMap.toMatrix' (parentInteraction (A x) L)) =
      fun x => e (1 - (groundSpaceES (A x) L).starProjection) := by
    funext x
    rw [← toEuclideanCLM_toMatrix'_parentInteraction, StarAlgEquiv.symm_apply_apply]
  rw [heq]
  exact he.comp (continuous_const.sub hProj)

/-- At a fixed chain length, a term of the parent interaction on the ring is continuous whenever
its fixed-range ground-space projection is continuous. -/
theorem continuous_parentRingInteraction_term_family_of_groundProjection
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {L N : ℕ} (hLN : L ≤ N)
    (hProj : Continuous fun x => (groundSpaceES (A x) L).starProjection)
    (i : Fin N) :
    Continuous fun x => (parentRingInteraction (A x) hLN).term i := by
  simp only [ManyBody.Interaction.translates_term]
  exact (continuous_placeAlong _).comp
    (continuous_toMatrix'_parentInteraction_family_of_groundProjection A L hProj)

/-- Continuity of the local ground-space projection implies continuity of the Hamiltonian of
the parent interaction on the open chain at fixed volume. -/
theorem continuous_hamiltonian_parentChainInteraction_family_of_groundProjection
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {L N : ℕ}
    (hProj : Continuous fun x => (groundSpaceES (A x) L).starProjection) :
    Continuous fun x => (parentChainInteraction (A x) L N).hamiltonian := by
  simp only [ManyBody.Interaction.hamiltonian, ManyBody.Interaction.translates_term]
  exact continuous_finsetSum _ fun i _ ↦ (continuous_placeAlong _).comp
    (continuous_toMatrix'_parentInteraction_family_of_groundProjection A L hProj)

/-- Continuity of the local ground-space projection implies continuity of the Hamiltonian of
the parent interaction on the ring at fixed volume. -/
theorem continuous_hamiltonian_parentRingInteraction_family_of_groundProjection
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) {L N : ℕ} (hLN : L ≤ N)
    (hProj : Continuous fun x => (groundSpaceES (A x) L).starProjection) :
    Continuous fun x => (parentRingInteraction (A x) hLN).hamiltonian := by
  simp only [ManyBody.Interaction.hamiltonian]
  exact continuous_finsetSum _ fun i _ ↦
    continuous_parentRingInteraction_term_family_of_groundProjection A hLN hProj i

/-- For a fixed interaction range, the matrix of the canonical parent interaction varies
continuously along a tensor family injective at that range. -/
theorem continuous_toMatrix'_parentInteraction_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (L : ℕ)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) L) :
    Continuous fun x => LinearMap.toMatrix' (parentInteraction (A x) L) :=
  continuous_toMatrix'_parentInteraction_family_of_groundProjection A L
    (continuous_groundSpaceES_starProjection_family A hA L hInj)

/-- The Hamiltonian of the parent interaction on the open chain at fixed volume varies
continuously along a tensor family injective at the interaction range. -/
theorem continuous_hamiltonian_parentChainInteraction_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) {L N : ℕ}
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) L) :
    Continuous fun x => (parentChainInteraction (A x) L N).hamiltonian :=
  continuous_hamiltonian_parentChainInteraction_family_of_groundProjection A
    (continuous_groundSpaceES_starProjection_family A hA L hInj)

/-- The Hamiltonian of the parent interaction on the ring at fixed volume varies continuously
along a tensor family injective at the interaction range. -/
theorem continuous_hamiltonian_parentRingInteraction_family
    {X : Type*} [TopologicalSpace X] {d D : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) {L N : ℕ}
    (hLN : L ≤ N) (hInj : ∀ x, Kraus.IsNBlkInjective (A x) L) :
    Continuous fun x => (parentRingInteraction (A x) hLN).hamiltonian :=
  continuous_hamiltonian_parentRingInteraction_family_of_groundProjection A hLN
    (continuous_groundSpaceES_starProjection_family A hA L hInj)

end MPSTensor
