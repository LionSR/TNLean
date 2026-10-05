/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularIsometricRegionProjector

/-!
# Nonzero physical site images of regular G-isometries

The normalized local adjoint gives an orthogonal projector onto the actual
physical site image. Its nonzero range follows from the nonzero regular
invariant subspace. Regional range projectors are supported on the products
of these site-image projectors, without requiring ambient surjectivity.
Source: SCP10, arXiv:1001.3807, Definition 6.1 and Theorem 6.12.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The regular invariant subspace is nonzero, even for an empty incident-leg set. -/
theorem regularLegProjector_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    regularLegProjector (G := G) ι ≠ 0 := by
  intro hzero
  let ρ := regularLegRepresentation (G := G) ι
  have hinv : (fun _ : ι → G => (1 : ℂ)) ∈ ρ.invariants := by
    intro g
    funext η
    simp only [ρ, regularLegRepresentation_apply]
  have hfix : regularLegProjector (G := G) ι *ᵥ (fun _ => 1) = fun _ => 1 := by
    change Matrix.toLin' (LinearMap.toMatrix' ρ.averageMap) _ = _
    rw [Matrix.toLin'_toMatrix']
    exact ρ.averageMap_id _ hinv
  rw [hzero, Matrix.zero_mulVec] at hfix
  have h := congrFun hfix (fun _ => 1)
  exact zero_ne_one h

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

omit [DecidableEq G] in
/-- Local regular G-isometry supplies nonzero orthogonal physical image
projectors and explicit right factors through the original site maps. -/
theorem exists_regularIsometric_siteImageProjectors
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) :
    ∃ L : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ,
      ∃ J : V → Matrix (Fin d) (Fin d) ℂ,
        (∀ v, (Matrix.of fun s α => a v α s) * L v = J v) ∧
        (∀ v, IsStarProjection (J v)) ∧ (∀ v, J v ≠ 0) ∧
        (∀ v, J v * (Matrix.of fun s α => a v α s) = Matrix.of fun s α => a v α s) := by
  classical
  choose c hc hcoeff using fun v => (ha v).exists_regularProjectorCoefficients
  let A (v : V) : Matrix (Fin d) (IncidentEdge Γ v → G) ℂ := Matrix.of fun s α => a v α s
  let L (v : V) : Matrix (IncidentEdge Γ v → G) (Fin d) ℂ := (c v : ℂ)⁻¹ • (A v)ᴴ
  let J (v : V) := A v * L v
  have hLA (v : V) : L v * A v = regularLegProjector (IncidentEdge Γ v) := by
    ext α η
    simpa only [L, A, Matrix.mul_apply, Matrix.smul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, smul_eq_mul] using hcoeff v α η
  have hAE (v : V) : A v * regularLegProjector (IncidentEdge Γ v) = A v := by
    ext s η
    exact (ha v).toIsGInjective.regularSiteMap_projector_coefficients s η
  have hJA (v : V) : J v * A v = A v := by
    dsimp only [J]
    rw [Matrix.mul_assoc, hLA, hAE]
  refine ⟨L, J, fun _ => rfl, ?_, ?_, hJA⟩
  · intro v
    apply (isStarProjection_iff').mpr
    constructor
    · change (A v * L v) * (A v * L v) = _
      rw [← Matrix.mul_assoc, hJA]
    · change (A v * ((c v : ℂ)⁻¹ • (A v)ᴴ))ᴴ = A v * ((c v : ℂ)⁻¹ • (A v)ᴴ)
      simp [Matrix.mul_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]
  · intro v hzero
    have hA : A v = 0 := by
      have h := hJA v
      rw [hzero, Matrix.zero_mul] at h
      exact h.symm
    apply regularLegProjector_ne_zero (G := G) (ι := IncidentEdge Γ v)
    rw [← hLA, hA, Matrix.mul_zero]

omit [DecidableEq G] in
/-- A physical regional range projector is supported on the product of its
actual site images. The support is derived from the original regional range. -/
theorem product_siteImages_mul_regionRangeProjector
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (J : V → Matrix (Fin d) (Fin d) ℂ)
    (hJA : ∀ v, J v * (Matrix.of fun s α => a v α s) = Matrix.of fun s α => a v α s)
    (R : Finset V) :
    regionPhysicalProductMatrix R J * coordinateRangeProjector
        (regionGroundSpace (groupBondTensor a) R) =
      coordinateRangeProjector (regionGroundSpace (groupBondTensor a) R) := by
  classical
  apply matrix_mul_eq_right_of_fixes_range
  intro x hx
  rw [range_coordinateRangeProjector,
    ← regularProjectorOpenRegionRange_map_physical a ha R] at hx
  obtain ⟨z, -, rfl⟩ := hx
  change regionPhysicalProductMatrix R J *ᵥ
      (regionPhysicalProductMatrix R (fun v => Matrix.of fun s α => a v α s) *ᵥ z) = _
  rw [Matrix.mulVec_mulVec, regionPhysicalProductMatrix_mul
    (In := fun v => IncidentEdge Γ v → G) (Mid := fun _ => Fin d)
    (Out := fun _ => Fin d)]
  simp_rw [hJA]
  rfl

end TNLean.PEPS
