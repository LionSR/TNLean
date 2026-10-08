/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointEdgeProjectors
import TNLean.MPS.ParentHamiltonian.Martingale.DependentSpectatorProjections

/-!
# Joint normalized edge constraints as dependent spectator extensions

The actual one-sided maps Φ_L and Φ_R retain the original endpoint letters.
Their ranges decompose independently over a block label and its arbitrary
exterior coordinate. The corresponding orthogonal complement projections
are therefore dependent spectator extensions of the explicit one-block edge
constraints. This is a derived operator identity, without a physical
orthogonality assumption on the original blocks.

Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators

namespace MPSTensor.MPOSymmetry

open ContinuousLinearMap

noncomputable section

variable {r d D : ℕ} {D₀ : Fin r → ℕ}

/-- The left core edge sends an exposed virtual vector to the original
one-site tensor, leaving the inner bond index and physical letter visible. -/
def endpointLeftCoreMap (A : MPSTensor d D) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D × Fin d → ℂ) where
  toFun y := fun (b, i) ↦ (A i *ᵥ y) b
  map_add' y z := by ext ⟨b, i⟩; simp [Matrix.mulVec_add]
  map_smul' z y := by ext ⟨b, i⟩; simp [Matrix.mulVec_smul]

/-- The reflected core edge retains the original one-site tensor. -/
def endpointRightCoreMap (A : MPSTensor d D) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin d × Fin D → ℂ) where
  toFun y := fun (i, c) ↦ (y ᵥ* A i) c
  map_add' y z := by ext ⟨i, c⟩; simp [Matrix.add_vecMul]
  map_smul' z y := by ext ⟨i, c⟩; simp [Matrix.smul_vecMul]

/-- The left core edge support, with no exterior spectator. -/
def endpointLeftCoreSupportES (A : MPSTensor d D) :
    Submodule ℂ (EuclideanSpace ℂ (Fin D × Fin d)) :=
  (endpointLeftCoreMap A).range.map
    (WithLp.linearEquiv 2 ℂ (Fin D × Fin d → ℂ)).symm.toLinearMap

/-- The right core edge support, with no exterior spectator. -/
def endpointRightCoreSupportES (A : MPSTensor d D) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d × Fin D)) :=
  (endpointRightCoreMap A).range.map
    (WithLp.linearEquiv 2 ℂ (Fin d × Fin D → ℂ)).symm.toLinearMap

/-- The fixed first constraint is the orthogonal complement of the explicit
original-tensor edge support. -/
def endpointLeftCoreConstraintES (A : MPSTensor d D) :
    EuclideanSpace ℂ (Fin D × Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin D × Fin d) :=
  (endpointLeftCoreSupportES A)ᗮ.starProjection.toLinearMap

/-- The fixed last constraint is the reflected original-tensor constraint. -/
def endpointRightCoreConstraintES (A : MPSTensor d D) :
    EuclideanSpace ℂ (Fin d × Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin d × Fin D) :=
  (endpointRightCoreSupportES A)ᗮ.starProjection.toLinearMap

/-- Move each first exterior coordinate into its dependent spectator fiber. -/
def jointEndpointFirstEdgeSpectatorEquiv (d : ℕ) (D₀ E : Fin r → ℕ) :
    (((x : Fin r) × (Fin (E x) × Fin (D₀ x))) × Fin d) ≃
      ((x : Fin r) × ((Fin (D₀ x) × Fin d) × Fin (E x))) where
  toFun := fun (⟨x, a, b⟩, i) ↦ ⟨x, (b, i), a⟩
  invFun := fun ⟨x, (b, i), a⟩ ↦ (⟨x, a, b⟩, i)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Move each last exterior coordinate into its dependent spectator fiber. -/
def jointEndpointLastEdgeSpectatorEquiv (d : ℕ) (D₀ E : Fin r → ℕ) :
    (Fin d × ((x : Fin r) × (Fin (D₀ x) × Fin (E x)))) ≃
      ((x : Fin r) × ((Fin d × Fin (D₀ x)) × Fin (E x))) where
  toFun := fun (i, ⟨x, c, e⟩) ↦ ⟨x, (i, c), e⟩
  invFun := fun ⟨x, (i, c), e⟩ ↦ (i, ⟨x, c, e⟩)
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The first dependent spectator regrouping is an isometry. -/
def jointEndpointFirstEdgeSpectatorIsometry (d : ℕ) (D₀ E : Fin r → ℕ) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (jointEndpointFirstEdgeSpectatorEquiv d D₀ E)

/-- The last dependent spectator regrouping is an isometry. -/
def jointEndpointLastEdgeSpectatorIsometry (d : ℕ) (D₀ E : Fin r → ℕ) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (jointEndpointLastEdgeSpectatorEquiv d D₀ E)

private theorem mem_leftCoreSupport_iff (A : MPSTensor d D)
    (v : EuclideanSpace ℂ (Fin D × Fin d)) :
    v ∈ endpointLeftCoreSupportES A ↔
      ∃ y : Fin D → ℂ, ∀ b i, v (b, i) = (A i *ᵥ y) b := by
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, fun _ _ ↦ rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨endpointLeftCoreMap A y, ⟨y, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨b, i⟩
    exact (hy b i).symm

private theorem mem_rightCoreSupport_iff (A : MPSTensor d D)
    (v : EuclideanSpace ℂ (Fin d × Fin D)) :
    v ∈ endpointRightCoreSupportES A ↔
      ∃ y : Fin D → ℂ, ∀ i c, v (i, c) = (y ᵥ* A i) c := by
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, fun _ _ ↦ rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨endpointRightCoreMap A y, ⟨y, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨i, c⟩
    exact (hy i c).symm

private theorem mem_jointFirstCoreSupport_iff
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E : Fin r → ℕ)
    (v : EuclideanSpace ℂ (((x : Fin r) × (Fin (E x) × Fin (D₀ x))) × Fin d)) :
    v ∈ jointEndpointFirstEdgeCoreSupportES A E ↔
      ∃ Y : (x : Fin r) → Matrix (Fin (D₀ x)) (Fin (E x)) ℂ,
        ∀ x a b i, v (⟨x, a, b⟩, i) = (A x i * Y x) b a := by
  constructor
  · rintro ⟨_, ⟨Y, rfl⟩, rfl⟩
    exact ⟨Y, fun _ _ _ _ ↦ rfl⟩
  · rintro ⟨Y, hY⟩
    refine ⟨jointEndpointFirstEdgeCoreMap A E Y, ⟨Y, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨⟨x, a, b⟩, i⟩
    exact (hY x a b i).symm

private theorem mem_jointLastCoreSupport_iff
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E : Fin r → ℕ)
    (v : EuclideanSpace ℂ (Fin d × ((x : Fin r) × (Fin (D₀ x) × Fin (E x))))) :
    v ∈ jointEndpointLastEdgeCoreSupportES A E ↔
      ∃ Y : (x : Fin r) → Matrix (Fin (E x)) (Fin (D₀ x)) ℂ,
        ∀ x i c e, v (i, ⟨x, c, e⟩) = (Y x * A x i) e c := by
  constructor
  · rintro ⟨_, ⟨Y, rfl⟩, rfl⟩
    exact ⟨Y, fun _ _ _ _ ↦ rfl⟩
  · rintro ⟨Y, hY⟩
    refine ⟨jointEndpointLastEdgeCoreMap A E Y, ⟨Y, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨i, ⟨x, c, e⟩⟩
    exact (hY x i c e).symm

/-- The actual Φ_L range splits over every label and exterior value,
including empty labels and zero-dimensional exterior fibers. -/
theorem mem_jointEndpointFirstEdgeCoreSupportES_iff_fibers
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E : Fin r → ℕ)
    (v : EuclideanSpace ℂ (((x : Fin r) × (Fin (E x) × Fin (D₀ x))) × Fin d)) :
    v ∈ jointEndpointFirstEdgeCoreSupportES A E ↔ ∀ x a,
      dependentRightFiber (jointEndpointFirstEdgeSpectatorIsometry d D₀ E v) x a ∈
        endpointLeftCoreSupportES (A x) := by
  classical
  rw [mem_jointFirstCoreSupport_iff]
  simp only [mem_leftCoreSupport_iff]
  constructor
  · rintro ⟨Y, hY⟩ x a
    exact ⟨fun c ↦ Y x c a, fun b i ↦ hY x a b i⟩
  · intro h
    choose y hy using h
    exact ⟨fun x c a ↦ y x a c, fun x a b i ↦ hy x a b i⟩

/-- The actual Φ_R range has the reflected independent dependent fibers. -/
theorem mem_jointEndpointLastEdgeCoreSupportES_iff_fibers
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E : Fin r → ℕ)
    (v : EuclideanSpace ℂ (Fin d × ((x : Fin r) × (Fin (D₀ x) × Fin (E x))))) :
    v ∈ jointEndpointLastEdgeCoreSupportES A E ↔ ∀ x e,
      dependentRightFiber (jointEndpointLastEdgeSpectatorIsometry d D₀ E v) x e ∈
        endpointRightCoreSupportES (A x) := by
  classical
  rw [mem_jointLastCoreSupport_iff]
  simp only [mem_rightCoreSupport_iff]
  constructor
  · rintro ⟨Y, hY⟩ x e
    exact ⟨fun b ↦ Y x e b, fun i c ↦ hY x i c e⟩
  · intro h
    choose y hy using h
    exact ⟨fun x e b ↦ y x e b, fun x i c e ↦ hy x e i c⟩

/-- The first normalized support projector is exactly the dependent
spectator extension of the original-tensor left core projector. -/
theorem jointEndpointFirstEdgeCoreConstraint_conj_spectators
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E : Fin r → ℕ) :
    (jointEndpointFirstEdgeSpectatorIsometry d D₀ E).toLinearEquiv.conj
        (jointEndpointFirstEdgeCoreSupportES A E)ᗮ.starProjection.toLinearMap =
      (dependentRightFiberwiseMap (S := fun x ↦ Fin (E x))
        (fun x ↦ (endpointLeftCoreConstraintES (A x)).toContinuousLinearMap)).toLinearMap := by
  apply LinearIsometryEquiv.conj_eq_dependentRightFiberwiseMap_of_ker_iff
    _ _ _ (Submodule.isSymmetricProjection_starProjection _) (fun x ↦
      Submodule.isSymmetricProjection_starProjection _)
  intro v
  simpa only [endpointLeftCoreConstraintES, LinearMap.coe_toContinuousLinearMap,
    Submodule.ker_starProjection, Submodule.orthogonal_orthogonal] using
    mem_jointEndpointFirstEdgeCoreSupportES_iff_fibers A E v

/-- The last normalized support projector has the corresponding exact
spectator identity. No injectivity assumption is needed. -/
theorem jointEndpointLastEdgeCoreConstraint_conj_spectators
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E : Fin r → ℕ) :
    (jointEndpointLastEdgeSpectatorIsometry d D₀ E).toLinearEquiv.conj
        (jointEndpointLastEdgeCoreSupportES A E)ᗮ.starProjection.toLinearMap =
      (dependentRightFiberwiseMap (S := fun x ↦ Fin (E x))
        (fun x ↦ (endpointRightCoreConstraintES (A x)).toContinuousLinearMap)).toLinearMap := by
  apply LinearIsometryEquiv.conj_eq_dependentRightFiberwiseMap_of_ker_iff
    _ _ _ (Submodule.isSymmetricProjection_starProjection _) (fun x ↦
      Submodule.isSymmetricProjection_starProjection _)
  intro v
  simpa only [endpointRightCoreConstraintES, LinearMap.coe_toContinuousLinearMap,
    Submodule.ker_starProjection, Submodule.orthogonal_orthogonal] using
    mem_jointEndpointLastEdgeCoreSupportES_iff_fibers A E v

/-- Entrywise form of the derived first-edge identity, useful for placing
this actual Φ_L support projector on a longer chain. -/
theorem jointEndpointFirstEdgeCoreConstraint_apply_fiber
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E : Fin r → ℕ)
    (v : EuclideanSpace ℂ (((x : Fin r) × (Fin (E x) × Fin (D₀ x))) × Fin d))
    (x : Fin r) (a : Fin (E x)) (b : Fin (D₀ x)) (i : Fin d) :
    (jointEndpointFirstEdgeCoreSupportES A E)ᗮ.starProjection v (⟨x, a, b⟩, i) =
      endpointLeftCoreConstraintES (A x)
        (WithLp.toLp 2 fun η ↦ v (⟨x, a, η.1⟩, η.2)) (b, i) := by
  let U := jointEndpointFirstEdgeSpectatorIsometry d D₀ E
  have h := LinearMap.congr_fun (jointEndpointFirstEdgeCoreConstraint_conj_spectators A E) (U v)
  change U ((jointEndpointFirstEdgeCoreSupportES A E)ᗮ.starProjection (U.symm (U v))) = _ at h
  simp only [U.symm_apply_apply] at h
  exact congrArg (fun w ↦ w ⟨x, (b, i), a⟩) h

/-- Entrywise form of the derived reflected edge identity. -/
theorem jointEndpointLastEdgeCoreConstraint_apply_fiber
    (A : (x : Fin r) → MPSTensor d (D₀ x)) (E : Fin r → ℕ)
    (v : EuclideanSpace ℂ (Fin d × ((x : Fin r) × (Fin (D₀ x) × Fin (E x)))))
    (x : Fin r) (i : Fin d) (c : Fin (D₀ x)) (e : Fin (E x)) :
    (jointEndpointLastEdgeCoreSupportES A E)ᗮ.starProjection v (i, ⟨x, c, e⟩) =
      endpointRightCoreConstraintES (A x)
        (WithLp.toLp 2 fun η ↦ v (η.1, ⟨x, η.2, e⟩)) (i, c) := by
  let U := jointEndpointLastEdgeSpectatorIsometry d D₀ E
  have h := LinearMap.congr_fun (jointEndpointLastEdgeCoreConstraint_conj_spectators A E) (U v)
  change U ((jointEndpointLastEdgeCoreSupportES A E)ᗮ.starProjection (U.symm (U v))) = _ at h
  simp only [U.symm_apply_apply] at h
  exact congrArg (fun w ↦ w ⟨x, (i, c), e⟩) h

end

end MPSTensor.MPOSymmetry
