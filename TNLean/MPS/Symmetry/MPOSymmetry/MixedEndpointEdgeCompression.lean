/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointEdgeProjectors
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenSectors

/-!
# Actual compression into the smaller edge coordinate spaces

The first, interior, and last active edges have explicit coordinate
inclusions into the original two-site physical space. Their range
projections are products of the actual row and column sector projections.
Those products reduce the actual zero-parameter interaction.

Consequently cropping the actual boundary range by the adjoint inclusion
is the same as pulling it back by the inclusion. This closes the distinction
between a cropped boundary map and a compressed Hamiltonian kernel.
The compressed actual interactions are exactly the canonical edge constraints.
No global Hamiltonian identification or spectral estimate is asserted.
Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped Matrix InnerProductSpace BigOperators

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ : ℕ}

/-- The three distinct types of active two-site edge.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
inductive MixedEndpointEdgePosition
  | first
  | interior
  | last
  deriving DecidableEq

/-- The corresponding smaller physical coordinate type.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
abbrev mixedEndpointEdgeCfg (D₀ D₁ : ℕ) : MixedEndpointEdgePosition → Type
  | .first => endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀
  | .interior => Cfg (D₀ * D₀) 2
  | .last => endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀

instance (k : MixedEndpointEdgePosition) : Fintype (mixedEndpointEdgeCfg D₀ D₁ k) := by
  cases k <;> dsimp [mixedEndpointEdgeCfg] <;> infer_instance

/-- Encode each smaller edge into the actual two-site physical alphabet.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointEdgePhysicalCfg (k : MixedEndpointEdgePosition) :
    mixedEndpointEdgeCfg D₀ D₁ k → Cfg ((D₀ + D₁) * (D₀ + D₁)) 2 :=
  match k with
  | .first => fun ((a, b), q) =>
      ![mixedEndpointPhysicalIndex a (.inl b), mixedEndpointFirstPhysicalIndex D₁ q]
  | .interior => fun σ i => mixedEndpointFirstPhysicalIndex D₁ (σ i)
  | .last => fun (q, (c, e)) =>
      ![mixedEndpointFirstPhysicalIndex D₁ q, mixedEndpointPhysicalIndex (.inl c) e]

private theorem physicalIndex_eq_iff
    (a b c e : Fin D₀ ⊕ Fin D₁) :
    mixedEndpointPhysicalIndex a b = mixedEndpointPhysicalIndex c e ↔ a = c ∧ b = e := by
  simp [mixedEndpointPhysicalIndex]

private theorem firstPhysicalIndex_injective :
    Function.Injective (mixedEndpointFirstPhysicalIndex (D₀ := D₀) D₁) := by
  intro p q h
  have hpq := (physicalIndex_eq_iff _ _ _ _).mp h
  apply finProdFinEquiv.symm.injective
  exact Prod.ext (Sum.inl.inj hpq.1) (Sum.inl.inj hpq.2)

/-- None of the three smaller-edge encodings loses a coordinate.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgePhysicalCfg_injective (k : MixedEndpointEdgePosition) :
    Function.Injective (mixedEndpointEdgePhysicalCfg (D₀ := D₀) (D₁ := D₁) k) := by
  cases k with
  | first =>
      rintro ⟨⟨a, b⟩, q⟩ ⟨⟨a', b'⟩, q'⟩ h
      have h₀ := congrFun h 0
      have h₁ := congrFun h 1
      have hab : a = a' ∧ b = b' := by
        simpa [mixedEndpointEdgePhysicalCfg, physicalIndex_eq_iff] using h₀
      have hq : q = q' := firstPhysicalIndex_injective (by
        simpa [mixedEndpointEdgePhysicalCfg] using h₁)
      rcases hab with ⟨rfl, rfl⟩
      subst q'
      rfl
  | interior =>
      intro σ τ h
      exact funext fun i => firstPhysicalIndex_injective (congrFun h i)
  | last =>
      rintro ⟨q, ⟨c, e⟩⟩ ⟨q', ⟨c', e'⟩⟩ h
      have h₀ := congrFun h 0
      have h₁ := congrFun h 1
      have hq : q = q' := firstPhysicalIndex_injective (by
        simpa [mixedEndpointEdgePhysicalCfg] using h₀)
      have hce : c = c' ∧ e = e' := by
        simpa [mixedEndpointEdgePhysicalCfg, physicalIndex_eq_iff] using h₁
      rcases hce with ⟨rfl, rfl⟩
      subst q'
      rfl

/-- The concrete configuration embedding of a smaller edge.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointEdgeConfigEmbedding (D₀ D₁ : ℕ) (k : MixedEndpointEdgePosition) :
    mixedEndpointEdgeCfg D₀ D₁ k ↪ Cfg ((D₀ + D₁) * (D₀ + D₁)) 2 :=
  ⟨mixedEndpointEdgePhysicalCfg k, mixedEndpointEdgePhysicalCfg_injective k⟩

private def coordinateLin {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ := by
  classical
  exact Matrix.toEuclideanLin (Matrix.coordinateInclusion f)

private theorem coordinateLin_adjoint_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι ↪ κ) (v : EuclideanSpace ℂ κ) (i : ι) :
    (coordinateLin f).adjoint v i = v (f i) := by
  classical
  rw [coordinateLin, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Matrix.coordinateInclusion]

private theorem coordinateLin_apply_image {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι ↪ κ) (v : EuclideanSpace ℂ ι) (i : ι) :
    coordinateLin f v (f i) = v i := by
  classical
  simp [coordinateLin, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Matrix.coordinateInclusion, f.injective.eq_iff]

private theorem coordinateLin_apply_outside {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι ↪ κ) (v : EuclideanSpace ℂ ι) (j : κ) (hj : j ∉ Set.range f) :
    coordinateLin f v j = 0 := by
  classical
  have hne : ∀ i, j ≠ f i := fun i h => hj ⟨i, h.symm⟩
  simp [coordinateLin, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Matrix.coordinateInclusion, hne]

private theorem coordinateLin_adjoint_comp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι ↪ κ) : (coordinateLin f).adjoint ∘ₗ coordinateLin f = LinearMap.id := by
  ext v i
  rw [LinearMap.comp_apply, coordinateLin_adjoint_apply, coordinateLin_apply_image]
  rfl

private def coordinateIsometry {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
  (coordinateLin f).isometryOfInner fun v w => by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
      coordinateLin_adjoint_comp, LinearMap.id_apply]

open Classical in
private theorem coordinateLin_projection_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι ↪ κ) (v : EuclideanSpace ℂ κ) (j : κ) :
    (coordinateLin f ∘ₗ (coordinateLin f).adjoint) v j =
      if j ∈ Set.range f then v j else 0 := by
  classical
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    simp [LinearMap.comp_apply, coordinateLin_apply_image, coordinateLin_adjoint_apply]
  · simp [LinearMap.comp_apply, coordinateLin_apply_outside f _ j hj, hj]

/-- The actual smaller-edge zero-extension isometry.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointEdgeLinearIsometry (D₀ D₁ : ℕ) (k : MixedEndpointEdgePosition) :
    EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) :=
  coordinateIsometry (mixedEndpointEdgeConfigEmbedding D₀ D₁ k)

/-- Cropping by the Hilbert adjoint reads the actual encoded coordinate.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeLinearIsometry_adjoint_apply
    (k : MixedEndpointEdgePosition)
    (v : EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2))
    (ξ : mixedEndpointEdgeCfg D₀ D₁ k) :
    (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap.adjoint v ξ =
      v (mixedEndpointEdgePhysicalCfg k ξ) :=
  coordinateLin_adjoint_apply _ _ _


/-- Zero extension recovers the original coefficient on every encoded
smaller-edge configuration. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeLinearIsometry_apply_active
    (k : MixedEndpointEdgePosition) (v : EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k))
    (ξ : mixedEndpointEdgeCfg D₀ D₁ k) :
    mixedEndpointEdgeLinearIsometry D₀ D₁ k v (mixedEndpointEdgePhysicalCfg k ξ) = v ξ :=
  coordinateLin_apply_image _ _ _

/-- Zero extension vanishes at a physical configuration outside the
smaller-edge encoding range. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeLinearIsometry_apply_of_not_mem_range
    (k : MixedEndpointEdgePosition) (v : EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k))
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) 2)
    (hσ : σ ∉ Set.range (mixedEndpointEdgePhysicalCfg (D₀ := D₀) (D₁ := D₁) k)) :
    mixedEndpointEdgeLinearIsometry D₀ D₁ k v σ = 0 :=
  coordinateLin_apply_outside _ _ _ hσ

/-- The adjoint is a left inverse to every smaller-edge inclusion.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeLinearIsometry_adjoint_comp (k : MixedEndpointEdgePosition) :
    (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap.adjoint ∘ₗ
      (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap = LinearMap.id :=
  coordinateLin_adjoint_comp _

/-- Membership in a smaller-edge encoding is exactly its selected inner
and outer sector conditions. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mem_range_mixedEndpointEdgePhysicalCfg_iff
    (k : MixedEndpointEdgePosition) (a b c e : Fin D₀ ⊕ Fin D₁) :
    ![mixedEndpointPhysicalIndex a b, mixedEndpointPhysicalIndex c e] ∈
        Set.range (mixedEndpointEdgePhysicalCfg (D₀ := D₀) (D₁ := D₁) k) ↔
      (∃ b₀, b = Sum.inl b₀) ∧ (∃ c₀, c = Sum.inl c₀) ∧
        (match k with
        | .first => ∃ e₀, e = Sum.inl e₀
        | .last => ∃ a₀, a = Sum.inl a₀
        | .interior => (∃ a₀, a = Sum.inl a₀) ∧ (∃ e₀, e = Sum.inl e₀)) := by
  cases k with
  | first =>
      constructor
      · rintro ⟨⟨⟨a', b'⟩, q⟩, h⟩
        have h₀ := congrFun h 0
        have h₁ := congrFun h 1
        simp only [mixedEndpointEdgePhysicalCfg, Matrix.cons_val_zero,
          Matrix.cons_val_one, mixedEndpointFirstPhysicalIndex, physicalIndex_eq_iff] at h₀ h₁
        exact ⟨⟨b', h₀.2.symm⟩, ⟨_, h₁.1.symm⟩, ⟨_, h₁.2.symm⟩⟩
      · rintro ⟨⟨b₀, rfl⟩, ⟨c₀, rfl⟩, ⟨e₀, rfl⟩⟩
        exact ⟨((a, b₀), finProdFinEquiv (c₀, e₀)), by
          simp [mixedEndpointEdgePhysicalCfg, mixedEndpointFirstPhysicalIndex]⟩
  | last =>
      constructor
      · rintro ⟨⟨q, ⟨c', e'⟩⟩, h⟩
        have h₀ := congrFun h 0
        have h₁ := congrFun h 1
        simp only [mixedEndpointEdgePhysicalCfg, Matrix.cons_val_zero,
          Matrix.cons_val_one, mixedEndpointFirstPhysicalIndex, physicalIndex_eq_iff] at h₀ h₁
        exact ⟨⟨_, h₀.2.symm⟩, ⟨c', h₁.1.symm⟩, ⟨_, h₀.1.symm⟩⟩
      · rintro ⟨⟨b₀, rfl⟩, ⟨c₀, rfl⟩, ⟨a₀, rfl⟩⟩
        exact ⟨(finProdFinEquiv (a₀, b₀), (c₀, e)), by
          simp [mixedEndpointEdgePhysicalCfg, mixedEndpointFirstPhysicalIndex]⟩
  | interior =>
      constructor
      · rintro ⟨σ, h⟩
        have h₀ := congrFun h 0
        have h₁ := congrFun h 1
        simp only [mixedEndpointEdgePhysicalCfg, Matrix.cons_val_zero,
          Matrix.cons_val_one, mixedEndpointFirstPhysicalIndex, physicalIndex_eq_iff] at h₀ h₁
        exact ⟨⟨_, h₀.2.symm⟩, ⟨_, h₁.1.symm⟩, ⟨_, h₀.1.symm⟩, ⟨_, h₁.2.symm⟩⟩
      · rintro ⟨⟨b₀, rfl⟩, ⟨c₀, rfl⟩, ⟨a₀, rfl⟩, ⟨e₀, rfl⟩⟩
        refine ⟨![finProdFinEquiv (a₀, b₀), finProdFinEquiv (c₀, e₀)], ?_⟩
        funext i
        fin_cases i <;> simp [mixedEndpointEdgePhysicalCfg, mixedEndpointFirstPhysicalIndex]

/-- The exact product of physical register selectors for a smaller edge.
The two compulsory inner selectors occur in all three cases.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointEdgeSectorProjection (D₀ D₁ : ℕ) (k : MixedEndpointEdgePosition) :
    EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) :=
  mixedEndpointColumnSector D₀ D₁ 0 * mixedEndpointRowSector D₀ D₁ 1 *
    (match k with
    | .first => mixedEndpointColumnSector D₀ D₁ 1
    | .last => mixedEndpointRowSector D₀ D₁ 0
    | .interior => mixedEndpointRowSector D₀ D₁ 0 * mixedEndpointColumnSector D₀ D₁ 1)

/-- The inclusion range projection is the displayed product of actual
local sector projections. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeLinearIsometry_comp_adjoint (k : MixedEndpointEdgePosition) :
    (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap ∘ₗ
        (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap.adjoint =
      mixedEndpointEdgeSectorProjection D₀ D₁ k := by
  classical
  ext v σ
  obtain ⟨a, ha⟩ := finSumFinEquiv.surjective (finProdFinEquiv.symm (σ 0)).1
  obtain ⟨b, hb⟩ := finSumFinEquiv.surjective (finProdFinEquiv.symm (σ 0)).2
  obtain ⟨c, hc⟩ := finSumFinEquiv.surjective (finProdFinEquiv.symm (σ 1)).1
  obtain ⟨e, he⟩ := finSumFinEquiv.surjective (finProdFinEquiv.symm (σ 1)).2
  have hσ : σ = ![mixedEndpointPhysicalIndex a b, mixedEndpointPhysicalIndex c e] := by
    funext i
    fin_cases i <;> apply finProdFinEquiv.symm.injective <;>
      simp [mixedEndpointPhysicalIndex, ha, hb, hc, he]
  rw [hσ]
  change (coordinateLin (mixedEndpointEdgeConfigEmbedding D₀ D₁ k) ∘ₗ
    (coordinateLin (mixedEndpointEdgeConfigEmbedding D₀ D₁ k)).adjoint) v _ = _
  rw [coordinateLin_projection_apply]
  have hmem := mem_range_mixedEndpointEdgePhysicalCfg_iff k a b c e
  change (![mixedEndpointPhysicalIndex a b, mixedEndpointPhysicalIndex c e] ∈
    Set.range (mixedEndpointEdgeConfigEmbedding D₀ D₁ k)) ↔ _ at hmem
  simp only [hmem]
  cases k <;> cases a <;> cases b <;> cases c <;> cases e <;>
    simp [mixedEndpointEdgeSectorProjection, Module.End.mul_apply,
      mixedEndpointRowSector_apply, mixedEndpointColumnSector_apply,
      mixedEndpointPhysicalIndex, bondInterpolationWeight]

/-- Every smaller-edge range projection commutes with the actual extended
interaction. This is derived from the individual local sector symmetries.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeSectorProjection_commute_actualInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    Commute (mixedEndpointEdgeSectorProjection D₀ D₁ k)
      (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap := by
  have hinner := (mixedEndpointColumnSector_commute_parentInteraction_zero A₀ A₁ 0).mul_left
    (mixedEndpointRowSector_commute_parentInteraction_zero A₀ A₁ 1)
  cases k with
  | first =>
      exact hinner.mul_left (mixedEndpointColumnSector_commute_parentInteraction_zero A₀ A₁ 1)
  | last => exact hinner.mul_left (mixedEndpointRowSector_commute_parentInteraction_zero A₀ A₁ 0)
  | interior =>
      exact hinner.mul_left
        ((mixedEndpointRowSector_commute_parentInteraction_zero A₀ A₁ 0).mul_left
          (mixedEndpointColumnSector_commute_parentInteraction_zero A₀ A₁ 1))

/-- The three already derived smaller boundary maps, uniformly indexed by
edge position. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointEdgeBoundaryMap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ]
      (mixedEndpointEdgeCfg D₀ D₁ k → ℂ) :=
  match k with
  | .first => mixedEndpointFirstEdgeBoundaryMap A₀ A₁
  | .interior => mixedEndpointInteriorEdgeBoundaryMap A₀ A₁
  | .last => mixedEndpointLastEdgeBoundaryMap A₀ A₁

/-- The corresponding derived cropped range in Euclidean coordinates.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointEdgeSupportES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    Submodule ℂ (EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k)) :=
  (mixedEndpointEdgeBoundaryMap A₀ A₁ k).range.map
    (WithLp.linearEquiv 2 ℂ (mixedEndpointEdgeCfg D₀ D₁ k → ℂ)).symm.toLinearMap


/-- The common spelling of the three canonical smaller-edge constraints.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointEdgeConstraintES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k) →ₗ[ℂ]
      EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k) :=
  (mixedEndpointEdgeSupportES A₀ A₁ k)ᗮ.starProjection.toLinearMap

private def twoSiteBoundaryMapSum
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) 2) := by
  let V : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (D₀ + D₁) × Fin (D₀ + D₁)) :=
    { toFun X := WithLp.toLp 2 fun p =>
        X (finSumFinEquiv.symm p.1) (finSumFinEquiv.symm p.2)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact (insertedTwoSiteMap (mixedEndpointBase A₀ A₁)
    (bondInterpolationMatrix D₀ D₁ 0)).toLinearMap.comp V

private theorem range_twoSiteBoundaryMapSum
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    (twoSiteBoundaryMapSum A₀ A₁).range =
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range := by
  ext v
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨w, rfl⟩
    let X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ :=
      fun a b => w (finSumFinEquiv a, finSumFinEquiv b)
    refine ⟨X, ?_⟩
    have hw : WithLp.toLp 2 (fun p =>
        X (finSumFinEquiv.symm p.1) (finSumFinEquiv.symm p.2)) = w := by
      apply PiLp.ext
      rintro ⟨a, b⟩
      change w (finSumFinEquiv (finSumFinEquiv.symm a),
        finSumFinEquiv (finSumFinEquiv.symm b)) = w (a, b)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact congrArg
      (fun z : EuclideanSpace ℂ (Fin (D₀ + D₁) × Fin (D₀ + D₁)) =>
        insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0) z) hw

private def edgeActiveCfg (k : MixedEndpointEdgePosition) :
    mixedEndpointEdgeCfg D₀ D₁ k → endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ 0 :=
  match k with
  | .first => fun ((a, b), q) =>
      (a, (b, Fin.elim0, (finProdFinEquiv.symm q).1), .inl (finProdFinEquiv.symm q).2)
  | .interior => fun σ =>
      (.inl (finProdFinEquiv.symm (σ 0)).1,
        ((finProdFinEquiv.symm (σ 0)).2, Fin.elim0, (finProdFinEquiv.symm (σ 1)).1),
        .inl (finProdFinEquiv.symm (σ 1)).2)
  | .last => fun (q, (c, e)) =>
      (.inl (finProdFinEquiv.symm q).1, ((finProdFinEquiv.symm q).2, Fin.elim0, c), e)

private theorem edgePhysicalCfg_eq_activeCfg (k : MixedEndpointEdgePosition)
    (ξ : mixedEndpointEdgeCfg D₀ D₁ k) :
    mixedEndpointEdgePhysicalCfg k ξ = mixedEndpointActivePhysicalCfg (edgeActiveCfg k ξ) := by
  cases k with
  | first =>
      rcases ξ with ⟨⟨a, b⟩, q⟩
      funext i
      fin_cases i <;> simp [mixedEndpointEdgePhysicalCfg, mixedEndpointActivePhysicalCfg,
        edgeActiveCfg, mixedEndpointFirstPhysicalIndex, Fin.snoc_zero]
  | interior =>
      funext i
      fin_cases i <;> simp [mixedEndpointEdgePhysicalCfg, mixedEndpointActivePhysicalCfg,
        edgeActiveCfg, mixedEndpointFirstPhysicalIndex, Fin.snoc_zero]
  | last =>
      rcases ξ with ⟨q, ⟨c, e⟩⟩
      funext i
      fin_cases i <;> simp [mixedEndpointEdgePhysicalCfg, mixedEndpointActivePhysicalCfg,
        edgeActiveCfg, mixedEndpointFirstPhysicalIndex, Fin.snoc_zero]

private theorem twoSiteBoundaryMapSum_apply_activeCfg
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (X : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀ ⊕ Fin D₁) ℂ)
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ 0) :
    twoSiteBoundaryMapSum A₀ A₁ X (mixedEndpointActivePhysicalCfg ξ) =
      mixedEndpointActiveBoundaryMap A₀ A₁ 0 X ξ := by
  rcases ξ with ⟨a, ⟨b, σ, c⟩, e⟩
  change insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)
      (WithLp.toLp 2 fun p => X (finSumFinEquiv.symm p.1) (finSumFinEquiv.symm p.2))
      (mixedEndpointActivePhysicalCfg (a, (b, σ, c), e)) =
    mixedEndpointActiveBoundaryMap A₀ A₁ 0 X (a, (b, σ, c), e)
  simp [mixedEndpointActiveBoundaryMap, mixedEndpointActivePhysicalCfg,
    insertedTwoSiteMap_apply, insertedGroundSpaceMap_apply, insertedEvalWord,
    List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc, Fin.snoc_zero, Matrix.submatrix]

private theorem edgeAdjoint_comp_twoSiteBoundaryMapSum
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap.adjoint.comp
        (twoSiteBoundaryMapSum A₀ A₁) =
      (WithLp.linearEquiv 2 ℂ (mixedEndpointEdgeCfg D₀ D₁ k → ℂ)).symm.toLinearMap.comp
        (mixedEndpointEdgeBoundaryMap A₀ A₁ k) := by
  apply LinearMap.ext
  intro X
  apply PiLp.ext
  intro ξ
  rw [LinearMap.comp_apply, mixedEndpointEdgeLinearIsometry_adjoint_apply,
    edgePhysicalCfg_eq_activeCfg, twoSiteBoundaryMapSum_apply_activeCfg]
  cases k <;> rfl

/-- The adjoint crop of the actual two-site support is exactly the smaller
boundary-map range already used to define each edge constraint.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem map_actualSupport_edgeAdjoint_eq_edgeSupport
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range.map
        (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap.adjoint =
      mixedEndpointEdgeSupportES A₀ A₁ k := by
  rw [← range_twoSiteBoundaryMapSum, ← LinearMap.range_comp,
    edgeAdjoint_comp_twoSiteBoundaryMapSum, LinearMap.range_comp]
  rfl

private theorem ker_actualInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    LinearMap.ker (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap =
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range := by
  ext v
  exact mem_ker_insertedParentInteraction_iff _ _ v

/-- The actual boundary range is invariant under each explicitly derived
smaller-edge range projection. No invariant-support hypothesis is assumed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeSectorProjection_invariant_actualSupport
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range.map
        (mixedEndpointEdgeSectorProjection D₀ D₁ k) ≤
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range := by
  rw [← ker_actualInteraction]
  rintro _ ⟨v, hv, rfl⟩
  have hc := congrArg (fun T => T v)
    (mixedEndpointEdgeSectorProjection_commute_actualInteraction A₀ A₁ k).eq.symm
  change (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap
      (mixedEndpointEdgeSectorProjection D₀ D₁ k v) =
    mixedEndpointEdgeSectorProjection D₀ D₁ k
      ((mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap v) at hc
  rw [LinearMap.mem_ker.mp hv, map_zero] at hc
  exact hc

private theorem map_adjoint_eq_comap_of_invariant
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (J : E →ₗ[ℂ] F) (hJ : J.adjoint ∘ₗ J = LinearMap.id)
    (S : Submodule ℂ F) (hS : S.map (J ∘ₗ J.adjoint) ≤ S) :
    S.map J.adjoint = S.comap J := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hS ⟨w, hw, rfl⟩
  · intro hv
    exact ⟨J v, hv, LinearMap.congr_fun hJ v⟩

/-- For each actual smaller edge, cropping the support equals pulling it
back through zero extension. The reverse direction uses the proved sector
reduction, not merely coordinate restriction.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem map_actualSupport_edgeAdjoint_eq_comap
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range.map
        (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap.adjoint =
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range.comap
        (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap := by
  apply map_adjoint_eq_comap_of_invariant _ (mixedEndpointEdgeLinearIsometry_adjoint_comp k)
  rw [mixedEndpointEdgeLinearIsometry_comp_adjoint]
  exact mixedEndpointEdgeSectorProjection_invariant_actualSupport A₀ A₁ k

/-- The previously defined smaller support is precisely the actual
support pulled back by its genuine coordinate isometry.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeSupportES_eq_comap_actualSupport
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    mixedEndpointEdgeSupportES A₀ A₁ k =
      (insertedTwoSiteMap (mixedEndpointBase A₀ A₁) (bondInterpolationMatrix D₀ D₁ 0)).range.comap
        (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap := by
  rw [← map_actualSupport_edgeAdjoint_eq_edgeSupport, map_actualSupport_edgeAdjoint_eq_comap]

/-- The actual two-site interaction compressed into a smaller edge.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointEdgeCompression
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k) →ₗ[ℂ]
      EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k) :=
  (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap.adjoint ∘ₗ
    (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap ∘ₗ
      (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap

/-- The actual edge compression intertwines with the original interaction.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeCompression_intertwines
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) (v : EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k)) :
    mixedEndpointEdgeLinearIsometry D₀ D₁ k (mixedEndpointEdgeCompression A₀ A₁ k v) =
      mixedEndpointParentInteraction A₀ A₁ 0 (mixedEndpointEdgeLinearIsometry D₀ D₁ k v) := by
  let J := (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap
  have hfix : mixedEndpointEdgeSectorProjection D₀ D₁ k (J v) = J v := by
    rw [← mixedEndpointEdgeLinearIsometry_comp_adjoint]
    change J ((J.adjoint ∘ₗ J) v) = J v
    rw [mixedEndpointEdgeLinearIsometry_adjoint_comp, LinearMap.id_apply]
  change (J ∘ₗ J.adjoint) ((mixedEndpointParentInteraction A₀ A₁ 0) (J v)) =
    (mixedEndpointParentInteraction A₀ A₁ 0) (J v)
  rw [mixedEndpointEdgeLinearIsometry_comp_adjoint]
  have hc := congrArg (fun T => T (J v))
    (mixedEndpointEdgeSectorProjection_commute_actualInteraction A₀ A₁ k).eq
  change mixedEndpointEdgeSectorProjection D₀ D₁ k
      ((mixedEndpointParentInteraction A₀ A₁ 0) (J v)) =
    (mixedEndpointParentInteraction A₀ A₁ 0) (mixedEndpointEdgeSectorProjection D₀ D₁ k (J v)) at hc
  rw [hfix] at hc
  exact hc

/-- The actual compressed smaller-edge interaction is a symmetric projection.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdgeCompression_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    (mixedEndpointEdgeCompression A₀ A₁ k).IsSymmetricProjection := by
  have hP : (mixedEndpointParentInteraction A₀ A₁ 0).toLinearMap.IsSymmetricProjection :=
    ⟨(Submodule.isSymmetricProjection_starProjection _).isIdempotentElem.one_sub,
      (mixedEndpointParentInteraction_isPositive A₀ A₁ 0).isSymmetric⟩
  constructor
  · apply LinearMap.ext
    intro v
    apply (mixedEndpointEdgeLinearIsometry D₀ D₁ k).injective
    simp only [Module.End.mul_apply, mixedEndpointEdgeCompression_intertwines]
    exact LinearMap.congr_fun hP.isIdempotentElem.eq (mixedEndpointEdgeLinearIsometry D₀ D₁ k v)
  · exact (hP.isPositive.adjoint_conj
      (mixedEndpointEdgeLinearIsometry D₀ D₁ k).toLinearMap).isSymmetric

/-- The actual compressed kernel is the proved smaller boundary support.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem ker_mixedEndpointEdgeCompression
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    LinearMap.ker (mixedEndpointEdgeCompression A₀ A₁ k) = mixedEndpointEdgeSupportES A₀ A₁ k := by
  rw [mixedEndpointEdgeSupportES_eq_comap_actualSupport, ← ker_actualInteraction]
  ext v
  change mixedEndpointEdgeCompression A₀ A₁ k v = 0 ↔
    mixedEndpointParentInteraction A₀ A₁ 0 (mixedEndpointEdgeLinearIsometry D₀ D₁ k v) = 0
  rw [← mixedEndpointEdgeCompression_intertwines]
  constructor
  · intro hv
    rw [hv, map_zero]
  · intro hv
    apply (mixedEndpointEdgeLinearIsometry D₀ D₁ k).injective
    simpa only [map_zero] using hv

/-- The actual smaller-edge compression is exactly its canonical support
complement projection. This is the local operator link, not merely a range
or global-kernel statement.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointEdge_compression_eq_constraint
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (k : MixedEndpointEdgePosition) :
    mixedEndpointEdgeCompression A₀ A₁ k = mixedEndpointEdgeConstraintES A₀ A₁ k := by
  let P := mixedEndpointEdgeCompression A₀ A₁ k
  have hP := mixedEndpointEdgeCompression_isSymmetricProjection A₀ A₁ k
  have hrange : LinearMap.range P = (LinearMap.ker P)ᗮ := by
    rw [← hP.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  obtain ⟨_, h⟩ := P.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hP
  simpa only [hrange, P, ker_mixedEndpointEdgeCompression, mixedEndpointEdgeConstraintES] using h

/-- The actual compressed first interaction is the first canonical edge
constraint used in the derived normalization identities.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointFirstEdge_compression_eq_constraint
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    mixedEndpointEdgeCompression A₀ A₁ .first = mixedEndpointFirstEdgeConstraintES A₀ A₁ :=
  mixedEndpointEdge_compression_eq_constraint A₀ A₁ .first

/-- The actual compressed last interaction is the last canonical edge
constraint used in the derived normalization identities.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointLastEdge_compression_eq_constraint
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    mixedEndpointEdgeCompression A₀ A₁ .last = mixedEndpointLastEdgeConstraintES A₀ A₁ :=
  mixedEndpointEdge_compression_eq_constraint A₀ A₁ .last

/-- The actual compressed interior interaction is the ordinary endpoint
parent term. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointInteriorEdge_compression_eq_parentInteractionES
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) :
    mixedEndpointEdgeCompression A₀ A₁ .interior = parentInteractionES A₀ 2 := by
  rw [mixedEndpointEdge_compression_eq_constraint]
  exact mixedEndpointInteriorEdgeConstraintES_eq_parentInteractionES A₀ A₁

end

end MPOSymmetry
end MPSTensor
