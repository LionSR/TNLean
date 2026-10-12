/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveBoundaryTransport
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointOpenSectors

/-!
# Isometric coordinates for the active mixed endpoint sector

The explicit configuration encoding with two free exterior registers and
first-sector interior registers is a bijection onto the active physical
configurations. Extending coefficients by zero gives a Euclidean isometry
whose range is exactly the active-sector projection's range.

No tensor injectivity or Hamiltonian comparison is assumed. These coordinates
provide the concrete inclusion needed to transport the actual local terms.
Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped Matrix BigOperators

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ N : ℕ}

private theorem physicalIndex_eq_iff
    (a b a' b' : Fin D₀ ⊕ Fin D₁) :
    mixedEndpointPhysicalIndex a b = mixedEndpointPhysicalIndex a' b' ↔
      a = a' ∧ b = b' := by
  simp only [mixedEndpointPhysicalIndex, Equiv.apply_eq_iff_eq, Prod.mk.injEq]

private theorem firstPhysicalIndex_injective :
    Function.Injective (mixedEndpointFirstPhysicalIndex (D₀ := D₀) D₁) := by
  intro p q hpq
  have h := (physicalIndex_eq_iff _ _ _ _).mp hpq
  apply finProdFinEquiv.symm.injective
  exact Prod.ext (Sum.inl.inj h.1) (Sum.inl.inj h.2)

/-- The explicit active physical encoding loses no boundary or bulk
coordinate. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActivePhysicalCfg_injective :
    Function.Injective (mixedEndpointActivePhysicalCfg (D₀ := D₀) (D₁ := D₁) (N := N)) := by
  rintro ⟨a, ⟨b, σ, c⟩, e⟩ ⟨a', ⟨b', σ', c'⟩, e'⟩ h
  have hcons := Fin.cons_inj.mp h
  have hsnoc := Fin.snoc_inj.mp hcons.2
  have hab : a = a' ∧ b = b' := by
    simpa only [physicalIndex_eq_iff, Sum.inl.injEq] using hcons.1
  have hce : c = c' ∧ e = e' := by
    simpa only [physicalIndex_eq_iff, Sum.inl.injEq] using hsnoc.2
  have hσ : σ = σ' := funext fun k => firstPhysicalIndex_injective (congrFun hsnoc.1 k)
  rcases hab with ⟨rfl, rfl⟩
  rcases hce with ⟨rfl, rfl⟩
  subst σ'
  rfl

private theorem bondWeight_zero_eq_one_iff (p : Fin (D₀ + D₁)) :
    bondInterpolationWeight D₀ D₁ 0 p = 1 ↔
      ∃ a : Fin D₀, p = finSumFinEquiv (.inl a) := by
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective p
  simp only [Equiv.apply_eq_iff_eq]
  cases p <;> simp [bondInterpolationWeight]

private theorem exists_first_boundary_index
    (p : Fin ((D₀ + D₁) * (D₀ + D₁)))
    (hp : bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).2 = 1) :
    ∃ (a : Fin D₀ ⊕ Fin D₁) (b : Fin D₀),
      mixedEndpointPhysicalIndex a (.inl b) = p := by
  obtain ⟨b, hb⟩ := (bondWeight_zero_eq_one_iff _).mp hp
  refine ⟨finSumFinEquiv.symm (finProdFinEquiv.symm p).1, b, ?_⟩
  apply finProdFinEquiv.symm.injective
  simp only [mixedEndpointPhysicalIndex, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  exact Prod.ext rfl hb.symm

private theorem exists_last_boundary_index
    (p : Fin ((D₀ + D₁) * (D₀ + D₁)))
    (hp : bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).1 = 1) :
    ∃ (c : Fin D₀) (e : Fin D₀ ⊕ Fin D₁),
      mixedEndpointPhysicalIndex (.inl c) e = p := by
  obtain ⟨c, hc⟩ := (bondWeight_zero_eq_one_iff _).mp hp
  refine ⟨c, finSumFinEquiv.symm (finProdFinEquiv.symm p).2, ?_⟩
  apply finProdFinEquiv.symm.injective
  simp only [mixedEndpointPhysicalIndex, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  exact Prod.ext hc.symm rfl

private theorem exists_bulk_index
    (p : Fin ((D₀ + D₁) * (D₀ + D₁)))
    (hr : bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).1 = 1)
    (hc : bondInterpolationWeight D₀ D₁ 0 (finProdFinEquiv.symm p).2 = 1) :
    ∃ q : Fin (D₀ * D₀), mixedEndpointFirstPhysicalIndex D₁ q = p := by
  obtain ⟨a, ha⟩ := (bondWeight_zero_eq_one_iff _).mp hr
  obtain ⟨b, hb⟩ := (bondWeight_zero_eq_one_iff _).mp hc
  refine ⟨finProdFinEquiv (a, b), ?_⟩
  apply finProdFinEquiv.symm.injective
  simp only [mixedEndpointFirstPhysicalIndex, mixedEndpointPhysicalIndex,
    Equiv.symm_apply_apply]
  exact Prod.ext ha.symm hb.symm

/-- Every encoded active configuration satisfies all the actual inner
physical-sector constraints. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointOpenInnerActive_activePhysicalCfg
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :
    MixedEndpointOpenInnerActive (mixedEndpointActivePhysicalCfg ξ) := by
  obtain ⟨a, ⟨b, σ, c⟩, e⟩ := ξ
  rw [mixedEndpointOpenInnerActive_iff]
  constructor
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro _
      simp only [mixedEndpointActivePhysicalCfg, Fin.cons_zero, mixedEndpointPhysicalIndex,
        Equiv.symm_apply_apply]
      simp [bondInterpolationWeight]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hk
        simp at hk
      · intro _
        simp only [mixedEndpointActivePhysicalCfg, Fin.cons_succ, Fin.snoc_castSucc,
          mixedEndpointFirstPhysicalIndex, mixedEndpointPhysicalIndex, Equiv.symm_apply_apply]
        simp [bondInterpolationWeight]
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hk
      simp at hk
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        simp only [mixedEndpointActivePhysicalCfg, Fin.cons_succ, Fin.snoc_last,
          mixedEndpointPhysicalIndex, Equiv.symm_apply_apply]
        simp [bondInterpolationWeight]
      · intro _
        simp only [mixedEndpointActivePhysicalCfg, Fin.cons_succ, Fin.snoc_castSucc,
          mixedEndpointFirstPhysicalIndex, mixedEndpointPhysicalIndex, Equiv.symm_apply_apply]
        simp [bondInterpolationWeight]

/-- A physical configuration is active exactly when it has the explicit
boundary-and-bulk encoding. This includes all active configurations, rather
than only configurations appearing in an MPS support.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mem_range_mixedEndpointActivePhysicalCfg_iff
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1)) :
    σ ∈ Set.range mixedEndpointActivePhysicalCfg ↔ MixedEndpointOpenInnerActive σ := by
  constructor
  · rintro ⟨ξ, rfl⟩
    exact mixedEndpointOpenInnerActive_activePhysicalCfg ξ
  · intro hσ
    obtain ⟨hcol, hrow⟩ := (mixedEndpointOpenInnerActive_iff σ).mp hσ
    obtain ⟨a, b, hab⟩ := exists_first_boundary_index (σ 0) (hcol 0 (by simp))
    obtain ⟨c, e, hce⟩ := exists_last_boundary_index (σ (Fin.last N).succ)
      (hrow (Fin.last N).succ (by simp))
    have hbulk (k : Fin N) : ∃ p : Fin (D₀ * D₀),
        mixedEndpointFirstPhysicalIndex D₁ p = σ k.castSucc.succ :=
      exists_bulk_index _ (hrow _ (by simp)) (hcol _ (by simp))
    choose τ hτ using hbulk
    refine ⟨(a, (b, τ, c), e), ?_⟩
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa only [mixedEndpointActivePhysicalCfg, Fin.cons_zero] using hab
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [mixedEndpointActivePhysicalCfg, Fin.cons_succ, Fin.snoc_last] using hce
      · simpa only [mixedEndpointActivePhysicalCfg, Fin.cons_succ, Fin.snoc_castSucc] using hτ j

/-- Equivalence from explicit exterior-and-core coordinates onto the
actual active-configuration subtype.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointActiveConfigEquiv (D₀ D₁ N : ℕ) :
    endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N ≃
      {σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1) // MixedEndpointOpenInnerActive σ} :=
  Equiv.ofBijective
    (fun ξ => ⟨mixedEndpointActivePhysicalCfg ξ, mixedEndpointOpenInnerActive_activePhysicalCfg ξ⟩)
    ⟨fun ξ η h => mixedEndpointActivePhysicalCfg_injective (congrArg Subtype.val h),
      fun σ => by
        obtain ⟨ξ, hξ⟩ := (mem_range_mixedEndpointActivePhysicalCfg_iff σ.1).mpr σ.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩

/-- The active subtype equivalence has the original explicit encoding
as its forward map. -/
@[simp] theorem mixedEndpointActiveConfigEquiv_apply
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :
    (mixedEndpointActiveConfigEquiv D₀ D₁ N ξ).1 = mixedEndpointActivePhysicalCfg ξ := rfl

/-- The physical configuration injection underlying the active inclusion.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointActiveConfigEmbedding (D₀ D₁ N : ℕ) :
    endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N ↪
      Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1) :=
  ⟨mixedEndpointActivePhysicalCfg, mixedEndpointActivePhysicalCfg_injective⟩

/-- Include active coefficient vectors into the full physical Euclidean
space, putting zero in every inactive configuration.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointActiveInclusion (D₀ D₁ N : ℕ) :
    EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) →ₗ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1)) :=
  Matrix.toEuclideanLin (Matrix.coordinateInclusion (mixedEndpointActiveConfigEmbedding D₀ D₁ N))

/-- The active inclusion reproduces the supplied coefficient at every
encoded configuration. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveInclusion_apply_active
    (v : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N))
    (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :
    mixedEndpointActiveInclusion D₀ D₁ N v (mixedEndpointActivePhysicalCfg ξ) = v ξ := by
  classical
  simp [mixedEndpointActiveInclusion, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Matrix.coordinateInclusion, mixedEndpointActiveConfigEmbedding,
    mixedEndpointActivePhysicalCfg_injective.eq_iff]

/-- The active inclusion has zero coefficient at every inactive physical
configuration. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveInclusion_apply_inactive
    (v : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N))
    (σ : Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1))
    (hσ : ¬ MixedEndpointOpenInnerActive σ) :
    mixedEndpointActiveInclusion D₀ D₁ N v σ = 0 := by
  classical
  have hne (ξ : endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :
      σ ≠ mixedEndpointActivePhysicalCfg ξ := by
    intro h
    exact hσ (h.symm ▸ mixedEndpointOpenInnerActive_activePhysicalCfg ξ)
  simp [mixedEndpointActiveInclusion, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Matrix.coordinateInclusion, mixedEndpointActiveConfigEmbedding, hne]

/-- The inclusion preserves inner products because its columns are the
distinct physical coordinate vectors.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem mixedEndpointActiveInclusion_inner
    (v w : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N)) :
    inner ℂ (mixedEndpointActiveInclusion D₀ D₁ N v) (mixedEndpointActiveInclusion D₀ D₁ N w) =
      inner ℂ v w := by
  let T := mixedEndpointActiveInclusion D₀ D₁ N
  have hT : T.adjoint ∘ₗ T = LinearMap.id := by
    simpa only [T, mixedEndpointActiveInclusion, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using
      congrArg Matrix.toEuclideanLin
        (Matrix.coordinateInclusion_isometry (mixedEndpointActiveConfigEmbedding D₀ D₁ N))
  change inner ℂ (T v) (T w) = _
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hT, LinearMap.id_apply]

/-- The concrete active-coordinate Euclidean isometry into the full
physical chain. Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
def mixedEndpointActiveLinearIsometry (D₀ D₁ N : ℕ) :
    EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg ((D₀ + D₁) * (D₀ + D₁)) (N + 1 + 1)) :=
  (mixedEndpointActiveInclusion D₀ D₁ N).isometryOfInner mixedEndpointActiveInclusion_inner

/-- The concrete active isometry uses precisely the coordinate-inclusion
linear map, with no further normalization. -/
@[simp] theorem mixedEndpointActiveLinearIsometry_toLinearMap :
    (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap =
      mixedEndpointActiveInclusion D₀ D₁ N := rfl

/-- The inclusion's range is exactly the range of the previously derived
active-sector orthogonal projection on the full physical chain.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem range_mixedEndpointActiveInclusion :
    LinearMap.range (mixedEndpointActiveInclusion D₀ D₁ N) =
      LinearMap.range (mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1)) := by
  classical
  rw [range_mixedEndpointOpenActiveProjection (by omega)]
  ext v
  rw [mem_ker_mixedEndpointOpenInnerPenalty_iff (by omega)]
  constructor
  · rintro ⟨w, rfl⟩ σ hσ
    exact mixedEndpointActiveInclusion_apply_inactive w σ hσ
  · intro hv
    let w : EuclideanSpace ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ N) :=
      WithLp.toLp 2 fun ξ => v (mixedEndpointActivePhysicalCfg ξ)
    refine ⟨w, ?_⟩
    apply PiLp.ext
    intro σ
    by_cases hσ : MixedEndpointOpenInnerActive σ
    · obtain ⟨ξ, rfl⟩ := (mem_range_mixedEndpointActivePhysicalCfg_iff σ).mpr hσ
      exact mixedEndpointActiveInclusion_apply_active w ξ
    · rw [mixedEndpointActiveInclusion_apply_inactive w σ hσ, hv σ hσ]

/-- The active Euclidean isometry lands onto exactly the reducing active
sector, not merely into it.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem range_mixedEndpointActiveLinearIsometry :
    LinearMap.range (mixedEndpointActiveLinearIsometry D₀ D₁ N).toLinearMap =
      LinearMap.range (mixedEndpointOpenActiveProjection D₀ D₁ (N + 1 + 1)) :=
  range_mixedEndpointActiveInclusion

end

end MPOSymmetry
end MPSTensor
