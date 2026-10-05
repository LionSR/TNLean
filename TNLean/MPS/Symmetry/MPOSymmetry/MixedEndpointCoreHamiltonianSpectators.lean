/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveEdgeNormalization
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointCoreEdgeSpectators
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorGapEquivalence

/-!
# The normalized open chain as one common core with exterior spectators

Removing the two free exterior registers leaves a single Hilbert space
with coordinates `(b, σ, c)`. Its first and last constraints are the
one-spectator edge constraints, and its interior constraints are the
ordinary two-site `A₀` parent terms. Their placements are defined by
explicit core-only coordinate splits.

Each actually normalized mixed-chain term is the corresponding common-core
term independently on every pair of exterior registers. Hence the entire
normalized Hamiltonian is unitarily the right-fiberwise extension of one
common core operator. Replacing the nonempty exterior spectator space by
the zero-second-sector spectator space therefore preserves every nonnegative
norm-gap bound exactly.

No operator equality, kernel identification, or spectral gap is assumed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped Matrix InnerProductSpace BigOperators

namespace MPSTensor
namespace MPOSymmetry

open ContinuousLinearMap

noncomputable section

variable {D₀ D₁ N : ℕ}

/-- Expose the two free exterior registers as a single spectator pair.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreSpectatorConfigEquiv (ι : Type*) (D N : ℕ) :
    endpointActiveCfg ι D N ≃ endpointCoreCfg D N × (ι × ι) where
  toFun := fun (a, κ, e) => (κ, (a, e))
  invFun := fun (κ, (a, e)) => (a, κ, e)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The whole-chain exterior regrouping is a Euclidean isometry.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreSpectatorIsometry (ι : Type*) [Fintype ι] (D N : ℕ) :
    EuclideanSpace ℂ (endpointActiveCfg ι D N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (endpointCoreCfg D N × (ι × ι)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (endpointCoreSpectatorConfigEquiv ι D N)

/-- A fixed pair of exterior registers selects a vector on the common core.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointExteriorFiber {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ (endpointActiveCfg ι D₀ N)) (a e : ι) :
    EuclideanSpace ℂ (endpointCoreCfg D₀ N) :=
  WithLp.toLp 2 fun κ => v (a, κ, e)

/-- The first common-core edge and its remaining core coordinates.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreFirstEdgeConfigEquiv (D N : ℕ) :
    endpointCoreCfg D (N + 1) ≃ endpointFirstEdgeCfg PUnit D × (Cfg (D * D) N × Fin D) where
  toFun κ := (((PUnit.unit, κ.1), κ.2.1 0), (Fin.tail κ.2.1, κ.2.2))
  invFun x := (x.1.1.2, Fin.cons x.1.2 x.2.1, x.2.2)
  left_inv := by rintro ⟨b, σ, c⟩; simp only [Fin.cons_self_tail]
  right_inv := by rintro ⟨⟨⟨⟨⟩, b⟩, q⟩, σ, c⟩; simp only [Fin.cons_zero, Fin.tail_cons]

/-- The last common-core edge and its remaining core coordinates.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreLastEdgeConfigEquiv (D N : ℕ) :
    endpointCoreCfg D (N + 1) ≃ endpointLastEdgeCfg PUnit D × (Fin D × Cfg (D * D) N) where
  toFun κ := ((κ.2.1 (Fin.last N), (κ.2.2, PUnit.unit)), (κ.1, Fin.init κ.2.1))
  invFun x := (x.2.1, Fin.snoc x.2.2 x.1.1, x.1.2.1)
  left_inv := by rintro ⟨b, σ, c⟩; simp only [Fin.snoc_init_self]
  right_inv := by rintro ⟨⟨q, c, ⟨⟩⟩, b, σ⟩; simp only [Fin.snoc_last, Fin.init_snoc]

/-- An interior common-core edge with the remaining bulk and exposed bond
registers as spectators. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreInteriorEdgeConfigEquiv (D : ℕ) (i : NonwrappingStart 2 (N + 1)) :
    endpointCoreCfg D (N + 1) ≃ Cfg (D * D) 2 × endpointCoreCfg D (N + 1 - 2) := by
  let f := cyclicActiveBlockConfigEquiv (D * D) 2 (by have := i.2; omega) i.1
  exact
    { toFun := fun κ => ((f κ.2.1).1, (κ.1, (f κ.2.1).2, κ.2.2))
      invFun := fun x => (x.2.1, f.symm (x.1, x.2.2.1), x.2.2.2)
      left_inv := by rintro ⟨b, σ, c⟩; simp only [Prod.mk.eta, Equiv.symm_apply_apply]
      right_inv := by rintro ⟨ω, b, σ, c⟩; simp only [Equiv.apply_symm_apply] }

/-- The local coordinate types of the common-core constraints.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
abbrev endpointCoreEdgeCfg (D : ℕ) : MixedEndpointEdgePosition → Type
  | .first => endpointFirstEdgeCfg PUnit D
  | .interior => Cfg (D * D) 2
  | .last => endpointLastEdgeCfg PUnit D

instance (k : MixedEndpointEdgePosition) : Fintype (endpointCoreEdgeCfg D₀ k) := by
  cases k <;> dsimp [endpointCoreEdgeCfg] <;> infer_instance

/-- Only core coordinates remain as spectators in a common-core placement.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreEdgeSpectator (D : ℕ) (p : MixedEndpointActiveEdgeSite N) : Type :=
  match p with
  | .first => Cfg (D * D) N × Fin D
  | .interior _ => endpointCoreCfg D (N + 1 - 2)
  | .last => Fin D × Cfg (D * D) N

instance (p : MixedEndpointActiveEdgeSite N) : Fintype (endpointCoreEdgeSpectator D₀ p) := by
  cases p <;> dsimp [endpointCoreEdgeSpectator] <;> infer_instance

/-- The common-core edge/spectator coordinate split.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreEdgeConfigEquiv (D : ℕ) (p : MixedEndpointActiveEdgeSite N) :
    endpointCoreCfg D (N + 1) ≃
      endpointCoreEdgeCfg D (mixedEndpointActiveEdgePosition p) × endpointCoreEdgeSpectator D p :=
  match p with
  | .first => endpointCoreFirstEdgeConfigEquiv D N
  | .interior i => endpointCoreInteriorEdgeConfigEquiv D i
  | .last => endpointCoreLastEdgeConfigEquiv D N

/-- The Euclidean version of the common-core split.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreEdgeIsometry (D : ℕ) (p : MixedEndpointActiveEdgeSite N) :
    EuclideanSpace ℂ (endpointCoreCfg D (N + 1)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (endpointCoreEdgeCfg D (mixedEndpointActiveEdgePosition p) × endpointCoreEdgeSpectator D p) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (endpointCoreEdgeConfigEquiv D p)

/-- The fixed first/interior/last constraints of the common core.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreEdgeConstraint (A₀ : MPSTensor (D₀ * D₀) D₀) (k : MixedEndpointEdgePosition) :
    EuclideanSpace ℂ (endpointCoreEdgeCfg D₀ k) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointCoreEdgeCfg D₀ k) :=
  match k with
  | .first => endpointFirstEdgeCoreConstraintES A₀ PUnit
  | .interior => parentInteractionES A₀ 2
  | .last => endpointLastEdgeCoreConstraintES A₀ PUnit

/-- The selected local fiber of a common-core vector.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreEdgeFiber (p : MixedEndpointActiveEdgeSite N)
    (v : EuclideanSpace ℂ (endpointCoreCfg D₀ (N + 1)))
    (s : endpointCoreEdgeSpectator D₀ p) :
    EuclideanSpace ℂ (endpointCoreEdgeCfg D₀ (mixedEndpointActiveEdgePosition p)) :=
  WithLp.toLp 2 fun η => v ((endpointCoreEdgeConfigEquiv D₀ p).symm (η, s))

/-- Place each fixed core constraint on the full common-core Hilbert space.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreLocalInteraction (A₀ : MPSTensor (D₀ * D₀) D₀)
    (p : MixedEndpointActiveEdgeSite N) :
    EuclideanSpace ℂ (endpointCoreCfg D₀ (N + 1)) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointCoreCfg D₀ (N + 1)) :=
  (endpointCoreEdgeIsometry D₀ p).symm.toLinearEquiv.conj
    (rightFiberwiseMap (S := endpointCoreEdgeSpectator D₀ p)
      (endpointCoreEdgeConstraint A₀ (mixedEndpointActiveEdgePosition p)).toContinuousLinearMap).toLinearMap

/-- The common-core placement acts on exactly its selected core fiber.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem endpointCoreLocalInteraction_apply
    (A₀ : MPSTensor (D₀ * D₀) D₀) (p : MixedEndpointActiveEdgeSite N)
    (v : EuclideanSpace ℂ (endpointCoreCfg D₀ (N + 1))) (κ : endpointCoreCfg D₀ (N + 1)) :
    endpointCoreLocalInteraction A₀ p v κ =
      endpointCoreEdgeConstraint A₀ (mixedEndpointActiveEdgePosition p)
        (endpointCoreEdgeFiber p v (endpointCoreEdgeConfigEquiv D₀ p κ).2)
        (endpointCoreEdgeConfigEquiv D₀ p κ).1 := by
  simp only [endpointCoreLocalInteraction, LinearEquiv.conj_apply, LinearMap.comp_apply]
  rw [endpointCoreEdgeIsometry, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  change endpointCoreEdgeConstraint A₀ (mixedEndpointActiveEdgePosition p)
    (rightFiber (endpointCoreEdgeIsometry D₀ p v) (endpointCoreEdgeConfigEquiv D₀ p κ).2)
      (endpointCoreEdgeConfigEquiv D₀ p κ).1 = _
  congr 2
  apply PiLp.ext
  intro η
  simp [rightFiber, endpointCoreEdgeFiber, endpointCoreEdgeIsometry,
    LinearIsometryEquiv.piLpCongrLeft_apply]

/-- The single common-core operator, independent of both exterior dimensions.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def endpointCoreHamiltonian (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) :
    EuclideanSpace ℂ (endpointCoreCfg D₀ (N + 1)) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointCoreCfg D₀ (N + 1)) :=
  ∑ p : MixedEndpointActiveEdgeSite N, endpointCoreLocalInteraction A₀ p

private theorem firstCoreConstraint_apply_exterior
    {ι : Type*} [Fintype ι] (A₀ : MPSTensor (D₀ * D₀) D₀)
    (v : EuclideanSpace ℂ (endpointFirstEdgeCfg ι D₀)) (a : ι) (b : Fin D₀)
    (q : Fin (D₀ * D₀)) :
    endpointFirstEdgeCoreConstraintES A₀ ι v ((a, b), q) =
      endpointFirstEdgeCoreConstraintES A₀ PUnit
        (WithLp.toLp 2 fun η => v ((a, η.1.2), η.2)) ((PUnit.unit, b), q) := by
  let U := endpointFirstEdgeSpectatorIsometry ι D₀
  have h := LinearMap.congr_fun (endpointFirstEdgeCoreConstraintES_conj_spectator A₀ ι) (U v)
  have h' : U (endpointFirstEdgeCoreConstraintES A₀ ι v) =
      rightFiberwiseMap (S := ι) (endpointFirstEdgeCoreConstraintES A₀ PUnit).toContinuousLinearMap
        (U v) := by
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_apply, U.symm_apply_apply] using h
  simpa [U, endpointFirstEdgeSpectatorIsometry, endpointFirstEdgeSpectatorEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply, rightFiber] using
    congrArg (fun w => w (((PUnit.unit, b), q), a)) h'

private theorem lastCoreConstraint_apply_exterior
    {ι : Type*} [Fintype ι] (A₀ : MPSTensor (D₀ * D₀) D₀)
    (v : EuclideanSpace ℂ (endpointLastEdgeCfg ι D₀)) (q : Fin (D₀ * D₀))
    (c : Fin D₀) (e : ι) :
    endpointLastEdgeCoreConstraintES A₀ ι v (q, (c, e)) =
      endpointLastEdgeCoreConstraintES A₀ PUnit
        (WithLp.toLp 2 fun η => v (η.1, (η.2.1, e))) (q, (c, PUnit.unit)) := by
  let U := endpointLastEdgeSpectatorIsometry ι D₀
  have h := LinearMap.congr_fun (endpointLastEdgeCoreConstraintES_conj_spectator A₀ ι) (U v)
  have h' : U (endpointLastEdgeCoreConstraintES A₀ ι v) =
      rightFiberwiseMap (S := ι) (endpointLastEdgeCoreConstraintES A₀ PUnit).toContinuousLinearMap
        (U v) := by
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_apply, U.symm_apply_apply] using h
  simpa [U, endpointLastEdgeSpectatorIsometry, endpointLastEdgeSpectatorEquiv,
    LinearIsometryEquiv.piLpCongrLeft_apply, rightFiber] using
    congrArg (fun w => w ((q, (c, PUnit.unit)), e)) h'

/-- Every actually normalized placed term acts only on the common-core
coordinates and leaves each pair of exterior registers independent.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveNormalizedLocalInteraction_apply_exteriorFiber
    (A₀ : MPSTensor (D₀ * D₀) D₀) (p : MixedEndpointActiveEdgeSite N)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (a e : Fin D₀ ⊕ Fin D₁) (κ : endpointCoreCfg D₀ (N + 1)) :
    mixedEndpointActiveNormalizedLocalInteraction A₀ p v (a, κ, e) =
      endpointCoreLocalInteraction A₀ p (endpointExteriorFiber v a e) κ := by
  rcases κ with ⟨b, σ, c⟩
  cases p with
  | first =>
      rw [mixedEndpointActiveNormalizedLocalInteraction, mixedEndpointActiveEdgePlacement_apply,
        endpointCoreLocalInteraction_apply]
      change endpointFirstEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)
          (mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N) v
            (Fin.tail σ, c, e)) ((a, b), σ 0) = _
      rw [firstCoreConstraint_apply_exterior]
      apply congrArg (fun w => endpointFirstEdgeCoreConstraintES A₀ PUnit w
        ((PUnit.unit, b), σ 0))
      apply PiLp.ext
      rintro ⟨⟨⟨⟩, b'⟩, q⟩
      rfl
  | last =>
      rw [mixedEndpointActiveNormalizedLocalInteraction, mixedEndpointActiveEdgePlacement_apply,
        endpointCoreLocalInteraction_apply]
      change endpointLastEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)
          (mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N) v
            (a, b, Fin.init σ)) (σ (Fin.last N), (c, e)) = _
      rw [lastCoreConstraint_apply_exterior]
      apply congrArg (fun w => endpointLastEdgeCoreConstraintES A₀ PUnit w
        (σ (Fin.last N), (c, PUnit.unit)))
      apply PiLp.ext
      rintro ⟨q, c', ⟨⟩⟩
      rfl
  | interior i =>
      let f := cyclicActiveBlockConfigEquiv (D₀ * D₀) 2 (by have := i.2; omega) i.1
      rw [mixedEndpointActiveNormalizedLocalInteraction, mixedEndpointActiveEdgePlacement_apply,
        endpointCoreLocalInteraction_apply]
      change parentInteractionES A₀ 2
          (mixedEndpointActiveEdgeFiber (.interior i) v (a, (b, (f σ).2, c), e)) (f σ).1 =
        parentInteractionES A₀ 2
          (endpointCoreEdgeFiber (.interior i) (endpointExteriorFiber v a e)
            (b, (f σ).2, c)) (f σ).1
      apply congrArg (fun w => parentInteractionES A₀ 2 w (f σ).1)
      apply PiLp.ext
      intro η
      rfl

/-- The exterior-regrouping isometry intertwines each normalized placed
term with the spectator extension of its explicitly constructed core term.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveNormalizedLocalInteraction_intertwines_coreSpectators
    (A₀ : MPSTensor (D₀ * D₀) D₀) (p : MixedEndpointActiveEdgeSite N)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1)) :
    endpointCoreSpectatorIsometry (Fin D₀ ⊕ Fin D₁) D₀ (N + 1)
        (mixedEndpointActiveNormalizedLocalInteraction A₀ p v) =
      rightFiberwiseMap (S := (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁))
        (endpointCoreLocalInteraction A₀ p).toContinuousLinearMap
        (endpointCoreSpectatorIsometry (Fin D₀ ⊕ Fin D₁) D₀ (N + 1) v) := by
  apply PiLp.ext
  rintro ⟨κ, a, e⟩
  change mixedEndpointActiveNormalizedLocalInteraction A₀ p v (a, κ, e) =
    endpointCoreLocalInteraction A₀ p
      (rightFiber (endpointCoreSpectatorIsometry (Fin D₀ ⊕ Fin D₁) D₀ (N + 1) v) (a, e)) κ
  rw [mixedEndpointActiveNormalizedLocalInteraction_apply_exteriorFiber]
  rfl

/-- Each normalized placed constraint is unitarily the exterior extension
of the corresponding common-core constraint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveNormalizedLocalInteraction_conj_coreSpectators
    (A₀ : MPSTensor (D₀ * D₀) D₀) (p : MixedEndpointActiveEdgeSite N) :
    (endpointCoreSpectatorIsometry (Fin D₀ ⊕ Fin D₁) D₀ (N + 1)).toLinearEquiv.conj
        (mixedEndpointActiveNormalizedLocalInteraction A₀ p) =
      (rightFiberwiseMap (S := (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁))
        (endpointCoreLocalInteraction A₀ p).toContinuousLinearMap).toLinearMap := by
  let U := endpointCoreSpectatorIsometry (Fin D₀ ⊕ Fin D₁) D₀ (N + 1)
  apply LinearMap.ext
  intro v
  have h := mixedEndpointActiveNormalizedLocalInteraction_intertwines_coreSpectators
    A₀ p (U.symm v)
  simpa only [LinearEquiv.conj_apply, LinearMap.comp_apply, U.apply_symm_apply] using h

private theorem euclidean_sum_apply {I J : Type*} [Fintype I] [Fintype J]
    (v : J → EuclideanSpace ℂ I) (i : I) :
    (∑ j, v j) i = ∑ j, v j i :=
  map_sum (PiLp.projₗ (𝕜 := ℂ) 2 i) v Finset.univ

/-- The complete normalized Hamiltonian is the spectator extension of one
common core operator, with exactly the actually placed interaction sum.
This equality is derived term by term and is independent of injectivity.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveNormalizedHamiltonian_conj_coreSpectators
    (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) :
    (endpointCoreSpectatorIsometry (Fin D₀ ⊕ Fin D₁) D₀ (N + 1)).toLinearEquiv.conj
        (mixedEndpointActiveNormalizedHamiltonian A₀ N) =
      (rightFiberwiseMap (S := (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁))
        (endpointCoreHamiltonian A₀ N).toContinuousLinearMap).toLinearMap := by
  rw [mixedEndpointActiveNormalizedHamiltonian, map_sum]
  simp_rw [mixedEndpointActiveNormalizedLocalInteraction_conj_coreSpectators]
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨κ, s⟩
  rw [LinearMap.sum_apply]
  change (∑ p : MixedEndpointActiveEdgeSite N,
      rightFiberwiseMap (S := (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁))
        (endpointCoreLocalInteraction A₀ p).toContinuousLinearMap v) (κ, s) =
    (∑ p : MixedEndpointActiveEdgeSite N, endpointCoreLocalInteraction A₀ p)
      (rightFiber v s) κ
  rw [euclidean_sum_apply, LinearMap.sum_apply, euclidean_sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  rfl

private theorem norm_gap_iff_of_isometric_conj
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (P : E →ₗ[ℂ] E) (Q : F →ₗ[ℂ] F)
    (hPQ : U.toLinearEquiv.conj P = Q) (δ : ℝ) :
    (∀ x ∈ (LinearMap.ker P)ᗮ, δ * ‖x‖ ≤ ‖P x‖) ↔
      ∀ y ∈ (LinearMap.ker Q)ᗮ, δ * ‖y‖ ≤ ‖Q y‖ := by
  have hintertwine (x : E) : U (P x) = Q (U x) := by
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_apply, U.symm_apply_apply] using
      LinearMap.congr_fun hPQ (U x)
  have hker (x : E) : x ∈ LinearMap.ker P ↔ U x ∈ LinearMap.ker Q := by
    change P x = 0 ↔ Q (U x) = 0
    rw [← hintertwine]
    exact U.map_eq_zero_iff.symm
  have horth (x : E) : x ∈ (LinearMap.ker P)ᗮ ↔ U x ∈ (LinearMap.ker Q)ᗮ := by
    constructor
    · intro hx
      apply Submodule.mem_orthogonal.mpr
      intro y hy
      obtain ⟨z, rfl⟩ := U.surjective y
      rw [U.inner_map_map]
      exact (Submodule.mem_orthogonal.mp hx) z ((hker z).mpr hy)
    · intro hx
      apply Submodule.mem_orthogonal.mpr
      intro z hz
      simpa only [U.inner_map_map] using
        (Submodule.mem_orthogonal.mp hx) (U z) ((hker z).mp hz)
  constructor
  · intro hGap y hy
    obtain ⟨x, rfl⟩ := U.surjective y
    rw [← hintertwine, U.norm_map, U.norm_map]
    exact hGap x ((horth x).mpr hy)
  · intro hGap x hx
    have h := hGap (U x) ((horth x).mp hx)
    simpa only [← hintertwine x, U.norm_map] using h

/-- A normalized mixed chain and its common core have exactly the same
nonnegative norm-gap bounds when the exterior spectator space is nonempty.
The hypothesis on dimension only supplies that nonempty spectator.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveNormalizedHamiltonian_norm_gap_iff_core
    [NeZero D₀] (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ v ∈ (LinearMap.ker (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N))ᗮ,
      δ * ‖v‖ ≤ ‖mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N v‖) ↔
      ∀ v ∈ (LinearMap.ker (endpointCoreHamiltonian A₀ N))ᗮ,
        δ * ‖v‖ ≤ ‖endpointCoreHamiltonian A₀ N v‖ := by
  have hconj := norm_gap_iff_of_isometric_conj
    (endpointCoreSpectatorIsometry (Fin D₀ ⊕ Fin D₁) D₀ (N + 1))
    (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N)
    (rightFiberwiseMap (S := (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁))
      (endpointCoreHamiltonian A₀ N).toContinuousLinearMap).toLinearMap
    (mixedEndpointActiveNormalizedHamiltonian_conj_coreSpectators A₀ N) δ
  exact hconj.trans (norm_gap_rightFiberwiseMap_iff
    (S := (Fin D₀ ⊕ Fin D₁) × (Fin D₀ ⊕ Fin D₁))
    (endpointCoreHamiltonian A₀ N).toContinuousLinearMap hδ)

/-- Replacing the two exterior spectator registers by their zero-second-
sector versions preserves the actual normalized Hamiltonian's norm gap
exactly. In particular `.mpr` transfers an intrinsic zero-sector estimate
to an arbitrary second-sector dimension with the same constant.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveNormalizedHamiltonian_norm_gap_iff_zeroSector
    [NeZero D₀] (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ v ∈ (LinearMap.ker (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N))ᗮ,
      δ * ‖v‖ ≤ ‖mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N v‖) ↔
      ∀ v ∈ (LinearMap.ker (mixedEndpointActiveNormalizedHamiltonian (D₁ := 0) A₀ N))ᗮ,
        δ * ‖v‖ ≤ ‖mixedEndpointActiveNormalizedHamiltonian (D₁ := 0) A₀ N v‖ :=
  (mixedEndpointActiveNormalizedHamiltonian_norm_gap_iff_core (D₁ := D₁) A₀ N hδ).trans
    (mixedEndpointActiveNormalizedHamiltonian_norm_gap_iff_core (D₁ := 0) A₀ N hδ).symm

end

end MPOSymmetry
end MPSTensor
