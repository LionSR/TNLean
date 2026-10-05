/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointActiveEdgePlacement
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointBoundaryNormBounds

/-!
# Boundary normalization of the actual active-edge interactions

The two fixed boundary coordinate changes transport each actual compressed
edge kernel to its normalized core constraint. Boundary changes away from
an edge commute with its placement, while the change at a boundary edge
acts through the derived local support transport.

These termwise identities identify both orientations of the canonical
projection deformation. Summing over the exact edge indexing equivalence
then gives the normalized Hamiltonian and its global kernel transport.
No local kernel identity or spectral gap is assumed.
Source: arXiv:2203.12563, Section 5, lines 1690–1692.
-/

open scoped BigOperators ComplexOrder Matrix InnerProductSpace

namespace MPSTensor
namespace MPOSymmetry

noncomputable section

variable {D₀ D₁ N : ℕ}

/-- A first-boundary physical change on the active Euclidean space. -/
def mixedEndpointActiveFirstBoundaryMapES
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) (L : ℕ) :
    mixedEndpointActiveSpace D₀ D₁ L →ₗ[ℂ] mixedEndpointActiveSpace D₀ D₁ L :=
  LinearMap.withLpMap 2 (activeFirstBoundaryMap F L)

/-- A last-boundary physical change on the active Euclidean space. -/
def mixedEndpointActiveLastBoundaryMapES
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) (L : ℕ) :
    mixedEndpointActiveSpace D₀ D₁ L →ₗ[ℂ] mixedEndpointActiveSpace D₀ D₁ L :=
  LinearMap.withLpMap 2 (activeLastBoundaryMap F L)

private theorem firstEdgeFiber_lastBoundaryMap
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (σ : Cfg (D₀ * D₀) N) (c : Fin D₀) (e : Fin D₀ ⊕ Fin D₁) :
    mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N)
        (mixedEndpointActiveLastBoundaryMapES F (N + 1) v) (σ, c, e) =
      lastBoundaryCoordinateMap F
        (fun r => mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N)
          v (σ, r.1, r.2)) (c, e) := by
  apply PiLp.ext
  intro η
  exact lastBoundaryCoordinateMap_map F (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ => ℂ) η)
    (fun r => mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N)
      v (σ, r.1, r.2)) (c, e)

private theorem lastEdgeFiber_firstBoundaryMap
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (a : Fin D₀ ⊕ Fin D₁) (b : Fin D₀) (σ : Cfg (D₀ * D₀) N) :
    mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N)
        (mixedEndpointActiveFirstBoundaryMapES F (N + 1) v) (a, b, σ) =
      firstBoundaryCoordinateMap F
        (fun r => mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N)
          v (r.1, r.2, σ)) (a, b) := by
  apply PiLp.ext
  intro η
  exact firstBoundaryCoordinateMap_map F (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ => ℂ) η)
    (fun r => mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N)
      v (r.1, r.2, σ)) (a, b)

private theorem interiorEdgeFiber_firstBoundaryMap
    (i : NonwrappingStart 2 (N + 1))
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (a e : Fin D₀ ⊕ Fin D₁) (b c : Fin D₀) (σ : Cfg (D₀ * D₀) (N + 1 - 2)) :
    mixedEndpointActiveEdgeFiber (.interior i)
        (mixedEndpointActiveFirstBoundaryMapES F (N + 1) v) (a, (b, σ, c), e) =
      firstBoundaryCoordinateMap F
        (fun r => mixedEndpointActiveEdgeFiber (.interior i) v (r.1, (r.2, σ, c), e))
        (a, b) := by
  apply PiLp.ext
  intro η
  exact firstBoundaryCoordinateMap_map F (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ => ℂ) η)
    (fun r => mixedEndpointActiveEdgeFiber (.interior i) v (r.1, (r.2, σ, c), e)) (a, b)

private theorem interiorEdgeFiber_lastBoundaryMap
    (i : NonwrappingStart 2 (N + 1))
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (a e : Fin D₀ ⊕ Fin D₁) (b c : Fin D₀) (σ : Cfg (D₀ * D₀) (N + 1 - 2)) :
    mixedEndpointActiveEdgeFiber (.interior i)
        (mixedEndpointActiveLastBoundaryMapES F (N + 1) v) (a, (b, σ, c), e) =
      lastBoundaryCoordinateMap F
        (fun r => mixedEndpointActiveEdgeFiber (.interior i) v (a, (b, σ, r.1), r.2))
        (c, e) := by
  apply PiLp.ext
  intro η
  exact lastBoundaryCoordinateMap_map F (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ => ℂ) η)
    (fun r => mixedEndpointActiveEdgeFiber (.interior i) v (a, (b, σ, r.1), r.2)) (c, e)

/-- A last-boundary change commutes with every first-edge operator, because
it acts only on the explicitly identified spectator coordinates. -/
theorem mixedEndpointActiveFirstEdgePlacement_commute_lastBoundaryMap
    (T : EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀))
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    Commute (mixedEndpointActiveLastBoundaryMapES (D₁ := D₁) F (N + 1))
      (mixedEndpointActiveEdgePlacement (.first : MixedEndpointActiveEdgeSite N) T) := by
  apply (commute_iff_eq _ _).mpr
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨a, ⟨b, σ, c⟩, e⟩
  change lastBoundaryCoordinateMap F
      (fun r => mixedEndpointActiveEdgePlacement (.first : MixedEndpointActiveEdgeSite N)
        T v (a, (b, σ, r.1), r.2)) (c, e) =
    mixedEndpointActiveEdgePlacement (.first : MixedEndpointActiveEdgeSite N) T
      (mixedEndpointActiveLastBoundaryMapES F (N + 1) v) (a, (b, σ, c), e)
  change lastBoundaryCoordinateMap F
      (fun r => T (mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N)
        v (Fin.tail σ, r.1, r.2)) ((a, b), σ 0)) (c, e) =
    T (mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N)
      (mixedEndpointActiveLastBoundaryMapES F (N + 1) v) (Fin.tail σ, c, e)) ((a, b), σ 0)
  exact (lastBoundaryCoordinateMap_map F
    ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ => ℂ) ((a, b), σ 0)).comp T)
    (fun r => mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N)
      v (Fin.tail σ, r.1, r.2)) (c, e)).trans
    (congrArg (fun w => T w ((a, b), σ 0))
      (firstEdgeFiber_lastBoundaryMap F v (Fin.tail σ) c e).symm)

/-- A first-boundary change commutes with every last-edge operator. -/
theorem mixedEndpointActiveLastEdgePlacement_commute_firstBoundaryMap
    (T : EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) →ₗ[ℂ]
      EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀))
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    Commute (mixedEndpointActiveFirstBoundaryMapES (D₁ := D₁) F (N + 1))
      (mixedEndpointActiveEdgePlacement (.last : MixedEndpointActiveEdgeSite N) T) := by
  apply (commute_iff_eq _ _).mpr
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨a, ⟨b, σ, c⟩, e⟩
  change firstBoundaryCoordinateMap F
      (fun r => mixedEndpointActiveEdgePlacement (.last : MixedEndpointActiveEdgeSite N)
        T v (r.1, (r.2, σ, c), e)) (a, b) =
    mixedEndpointActiveEdgePlacement (.last : MixedEndpointActiveEdgeSite N) T
      (mixedEndpointActiveFirstBoundaryMapES F (N + 1) v) (a, (b, σ, c), e)
  change firstBoundaryCoordinateMap F
      (fun r => T (mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N)
        v (r.1, r.2, Fin.init σ)) (σ (Fin.last N), (c, e))) (a, b) =
    T (mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N)
      (mixedEndpointActiveFirstBoundaryMapES F (N + 1) v) (a, b, Fin.init σ))
        (σ (Fin.last N), (c, e))
  exact (firstBoundaryCoordinateMap_map F
    ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ => ℂ) (σ (Fin.last N), (c, e))).comp T)
    (fun r => mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N)
      v (r.1, r.2, Fin.init σ)) (a, b)).trans
    (congrArg (fun w => T w (σ (Fin.last N), (c, e)))
      (lastEdgeFiber_firstBoundaryMap F v a b (Fin.init σ)).symm)

/-- Both boundary changes commute with every interior-edge operator. -/
theorem mixedEndpointActiveInteriorEdgePlacement_commute_boundaryMaps
    (i : NonwrappingStart 2 (N + 1))
    (T : EuclideanSpace ℂ (Cfg (D₀ * D₀) 2) →ₗ[ℂ] EuclideanSpace ℂ (Cfg (D₀ * D₀) 2))
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ) :
    Commute (mixedEndpointActiveFirstBoundaryMapES (D₁ := D₁) F (N + 1))
        (mixedEndpointActiveEdgePlacement (.interior i) T) ∧
      Commute (mixedEndpointActiveLastBoundaryMapES (D₁ := D₁) F (N + 1))
        (mixedEndpointActiveEdgePlacement (.interior i) T) := by
  let f := cyclicActiveBlockConfigEquiv (D₀ * D₀) 2 (by have := i.2; omega) i.1
  constructor
  · apply (commute_iff_eq _ _).mpr
    apply LinearMap.ext
    intro v
    apply PiLp.ext
    rintro ⟨a, ⟨b, σ, c⟩, e⟩
    change firstBoundaryCoordinateMap F
        (fun r => mixedEndpointActiveEdgePlacement (.interior i) T v
          (r.1, (r.2, σ, c), e)) (a, b) =
      mixedEndpointActiveEdgePlacement (.interior i) T
        (mixedEndpointActiveFirstBoundaryMapES F (N + 1) v) (a, (b, σ, c), e)
    change firstBoundaryCoordinateMap F
        (fun r => T (mixedEndpointActiveEdgeFiber (.interior i)
          v (r.1, (r.2, (f σ).2, c), e)) (f σ).1) (a, b) =
      T (mixedEndpointActiveEdgeFiber (.interior i)
        (mixedEndpointActiveFirstBoundaryMapES F (N + 1) v)
          (a, (b, (f σ).2, c), e)) (f σ).1
    exact (firstBoundaryCoordinateMap_map F
      ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ => ℂ) (f σ).1).comp T)
      (fun r => mixedEndpointActiveEdgeFiber (.interior i)
        v (r.1, (r.2, (f σ).2, c), e)) (a, b)).trans
      (congrArg (fun w => T w (f σ).1)
        (interiorEdgeFiber_firstBoundaryMap i F v a e b c (f σ).2).symm)
  · apply (commute_iff_eq _ _).mpr
    apply LinearMap.ext
    intro v
    apply PiLp.ext
    rintro ⟨a, ⟨b, σ, c⟩, e⟩
    change lastBoundaryCoordinateMap F
        (fun r => mixedEndpointActiveEdgePlacement (.interior i) T v
          (a, (b, σ, r.1), r.2)) (c, e) =
      mixedEndpointActiveEdgePlacement (.interior i) T
        (mixedEndpointActiveLastBoundaryMapES F (N + 1) v) (a, (b, σ, c), e)
    change lastBoundaryCoordinateMap F
        (fun r => T (mixedEndpointActiveEdgeFiber (.interior i)
          v (a, (b, (f σ).2, r.1), r.2)) (f σ).1) (c, e) =
      T (mixedEndpointActiveEdgeFiber (.interior i)
        (mixedEndpointActiveLastBoundaryMapES F (N + 1) v)
          (a, (b, (f σ).2, c), e)) (f σ).1
    exact (lastBoundaryCoordinateMap_map F
      ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ => ℂ) (f σ).1).comp T)
      (fun r => mixedEndpointActiveEdgeFiber (.interior i)
        v (a, (b, (f σ).2, r.1), r.2)) (c, e)).trans
      (congrArg (fun w => T w (f σ).1)
        (interiorEdgeFiber_lastBoundaryMap i F v a e b c (f σ).2).symm)

private theorem firstEdgeFiber_firstBoundaryMap
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (s : mixedEndpointActiveEdgeSpectator D₀ D₁ (.first : MixedEndpointActiveEdgeSite N)) :
    mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N)
        (mixedEndpointActiveFirstBoundaryMapES F (N + 1) v) s =
      LinearMap.withLpMap 2 (firstEdgePhysicalMap F)
        (mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N) v s) := by
  apply PiLp.ext
  rintro ⟨⟨a, b⟩, q⟩
  rfl

private theorem lastEdgeFiber_lastBoundaryMap
    (F : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (s : mixedEndpointActiveEdgeSpectator D₀ D₁ (.last : MixedEndpointActiveEdgeSite N)) :
    mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N)
        (mixedEndpointActiveLastBoundaryMapES F (N + 1) v) s =
      LinearMap.withLpMap 2 (lastEdgePhysicalMap F)
        (mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N) v s) := by
  apply PiLp.ext
  rintro ⟨q, c, e⟩
  rfl

private theorem boundaryFirstMap_injective
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1) (L : ℕ) :
    Function.Injective (mixedEndpointActiveFirstBoundaryMapES (D₁ := D₁) F L) := by
  let U := WithLp.linearEquiv 2 ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ L → ℂ)
  let e := U.trans ((activeFirstBoundaryEquiv F G hFG hGF L).trans U.symm)
  exact e.injective

private theorem boundaryLastMap_injective
    (F G : Matrix (Fin (D₀ * D₀)) (Fin (D₀ * D₀)) ℂ)
    (hFG : F * G = 1) (hGF : G * F = 1) (L : ℕ) :
    Function.Injective (mixedEndpointActiveLastBoundaryMapES (D₁ := D₁) F L) := by
  let U := WithLp.linearEquiv 2 ℂ (endpointActiveCfg (Fin D₀ ⊕ Fin D₁) D₀ L → ℂ)
  let e := U.trans ((activeLastBoundaryEquiv F G hFG hGF L).trans U.symm)
  exact e.injective

private theorem mem_ker_commuting_map_iff
    {E : Type*} [AddCommGroup E] [Module ℂ E] (P B : E →ₗ[ℂ] E)
    (hcomm : Commute B P) (hB : Function.Injective B) (v : E) :
    B v ∈ LinearMap.ker P ↔ v ∈ LinearMap.ker P := by
  change P (B v) = 0 ↔ P v = 0
  have hc : B (P v) = P (B v) := LinearMap.congr_fun hcomm.eq v
  rw [← hc]
  constructor
  · intro hv
    apply hB
    simpa only [map_zero] using hv
  · intro hv
    rw [hv, map_zero]

private theorem mem_map_equiv_iff
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (S : Submodule ℂ E) (T : Submodule ℂ F)
    (h : S.map e.toLinearMap = T) (v : E) :
    e v ∈ T ↔ v ∈ S := by
  rw [← h]
  constructor
  · rintro ⟨w, hw, hEq⟩
    have : w = v := e.injective hEq
    subst w
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- The core constraint used after normalizing the boundary site of each
edge. The interior is the unchanged ordinary two-site parent interaction. -/
def mixedEndpointNormalizedEdgeConstraint
    (A₀ : MPSTensor (D₀ * D₀) D₀) (k : MixedEndpointEdgePosition) :
    EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k) →ₗ[ℂ]
      EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ k) :=
  match k with
  | .first => endpointFirstEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)
  | .interior => parentInteractionES A₀ 2
  | .last => endpointLastEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)

/-- The concrete normalized local constraint with all chain spectators. -/
def mixedEndpointActiveNormalizedLocalInteraction
    (A₀ : MPSTensor (D₀ * D₀) D₀) (p : MixedEndpointActiveEdgeSite N) :
    mixedEndpointActiveSpace D₀ D₁ (N + 1) →ₗ[ℂ]
      mixedEndpointActiveSpace D₀ D₁ (N + 1) :=
  mixedEndpointActiveEdgePlacement p
    (mixedEndpointNormalizedEdgeConstraint A₀ (mixedEndpointActiveEdgePosition p))

private theorem mem_ker_edgePlacement_iff
    (p : MixedEndpointActiveEdgeSite N)
    (T : EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)) →ₗ[ℂ]
      EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)))
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1)) :
    v ∈ LinearMap.ker (mixedEndpointActiveEdgePlacement p T) ↔
      ∀ s, mixedEndpointActiveEdgeFiber p v s ∈ LinearMap.ker T := by
  change mixedEndpointActiveEdgePlacement p T v = 0 ↔ _
  constructor
  · intro hv s
    apply PiLp.ext
    intro η
    have h := congrArg (fun w =>
      w ((mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p).symm (η, s))) hv
    rw [mixedEndpointActiveEdgePlacement_apply] at h
    simpa only [Equiv.apply_symm_apply, PiLp.zero_apply] using h
  · intro hv
    apply PiLp.ext
    intro ξ
    rw [mixedEndpointActiveEdgePlacement_apply]
    exact congrArg (fun w => w (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).1)
      (hv (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).2)

private theorem firstEdge_kernel_normalization
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (v : mixedEndpointActiveSpace D₀ D₁ (N + 1)) :
    v ∈ LinearMap.ker (mixedEndpointActiveLocalInteraction A₀ A₁
        (mixedEndpointActiveEdgeStart (.first : MixedEndpointActiveEdgeSite N))) ↔
      mixedEndpointActiveFirstBoundaryMapES (squarePhysicalCoordinates A₀)⁻¹ (N + 1) v ∈
        LinearMap.ker (mixedEndpointActiveNormalizedLocalInteraction A₀
          (.first : MixedEndpointActiveEdgeSite N)) := by
  rw [mem_ker_mixedEndpointActiveLocalInteraction_iff_edgeFibers,
    mixedEndpointActiveNormalizedLocalInteraction, mem_ker_edgePlacement_iff]
  apply forall_congr'
  intro s
  let w : EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) :=
    mixedEndpointActiveEdgeFiber (.first : MixedEndpointActiveEdgeSite N) v s
  have hmem : w ∈ mixedEndpointFirstEdgeSupportES A₀ A₁ ↔
      firstEdgeNormalizationEquivES A₀ hA₀ w ∈
        LinearMap.ker (endpointFirstEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)) := by
    rw [endpointFirstEdgeCoreConstraintES, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal]
    exact (mem_map_equiv_iff (firstEdgeNormalizationEquivES A₀ hA₀) _ _
      (map_firstEdgeNormalizationEquivES_actualSupport A₀ A₁ hA₀) w).symm
  exact hmem.trans (Iff.of_eq (congrArg
    (fun x : EuclideanSpace ℂ (endpointFirstEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) =>
      x ∈ LinearMap.ker (endpointFirstEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)))
    (firstEdgeFiber_firstBoundaryMap (squarePhysicalCoordinates A₀)⁻¹ v s).symm))

private theorem lastEdge_kernel_normalization
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (v : mixedEndpointActiveSpace D₀ D₁ (N + 1)) :
    v ∈ LinearMap.ker (mixedEndpointActiveLocalInteraction A₀ A₁
        (mixedEndpointActiveEdgeStart (.last : MixedEndpointActiveEdgeSite N))) ↔
      mixedEndpointActiveLastBoundaryMapES (squarePhysicalCoordinates A₀)⁻¹ (N + 1) v ∈
        LinearMap.ker (mixedEndpointActiveNormalizedLocalInteraction A₀
          (.last : MixedEndpointActiveEdgeSite N)) := by
  rw [mem_ker_mixedEndpointActiveLocalInteraction_iff_edgeFibers,
    mixedEndpointActiveNormalizedLocalInteraction, mem_ker_edgePlacement_iff]
  apply forall_congr'
  intro s
  let w : EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) :=
    mixedEndpointActiveEdgeFiber (.last : MixedEndpointActiveEdgeSite N) v s
  have hmem : w ∈ mixedEndpointLastEdgeSupportES A₀ A₁ ↔
      lastEdgeNormalizationEquivES A₀ hA₀ w ∈
        LinearMap.ker (endpointLastEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)) := by
    rw [endpointLastEdgeCoreConstraintES, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal]
    exact (mem_map_equiv_iff (lastEdgeNormalizationEquivES A₀ hA₀) _ _
      (map_lastEdgeNormalizationEquivES_actualSupport A₀ A₁ hA₀) w).symm
  exact hmem.trans (Iff.of_eq (congrArg
    (fun x : EuclideanSpace ℂ (endpointLastEdgeCfg (Fin D₀ ⊕ Fin D₁) D₀) =>
      x ∈ LinearMap.ker (endpointLastEdgeCoreConstraintES A₀ (Fin D₀ ⊕ Fin D₁)))
    (lastEdgeFiber_lastBoundaryMap (squarePhysicalCoordinates A₀)⁻¹ v s).symm))

/-- The full two-boundary normalization transports each actual local
kernel to the corresponding placed common-core kernel. Remote boundary
changes commute with that constraint and are invertible. -/
theorem mem_ker_mixedEndpointActiveLocalInteraction_iff_normalized
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (p : MixedEndpointActiveEdgeSite N)
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1)) :
    v ∈ LinearMap.ker
        (mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)) ↔
      activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1) v ∈
        LinearMap.ker (mixedEndpointActiveNormalizedLocalInteraction A₀ p) := by
  let G := squarePhysicalCoordinates A₀
  let F := G⁻¹
  have hG : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp
    (isUnit_squarePhysicalCoordinates A₀ hA₀)
  have hFG : F * G = 1 := Matrix.nonsing_inv_mul _ hG
  have hGF : G * F = 1 := Matrix.mul_nonsing_inv _ hG
  have hFirst := boundaryFirstMap_injective (D₁ := D₁) F G hFG hGF (N + 1)
  have hLast := boundaryLastMap_injective (D₁ := D₁) F G hFG hGF (N + 1)
  have hnorm : activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1) v =
      mixedEndpointActiveFirstBoundaryMapES F (N + 1)
        (mixedEndpointActiveLastBoundaryMapES F (N + 1) v) := rfl
  rw [hnorm]
  cases p with
  | first =>
    rw [← firstEdge_kernel_normalization A₀ A₁ hA₀]
    symm
    apply mem_ker_commuting_map_iff _ _ _ hLast
    rw [mixedEndpointActiveLocalInteraction_eq_edgePlacement]
    exact mixedEndpointActiveFirstEdgePlacement_commute_lastBoundaryMap _ F
  | last =>
    have hremote : mixedEndpointActiveFirstBoundaryMapES F (N + 1)
        (mixedEndpointActiveLastBoundaryMapES F (N + 1) v) ∈
          LinearMap.ker (mixedEndpointActiveNormalizedLocalInteraction A₀ .last) ↔
        mixedEndpointActiveLastBoundaryMapES F (N + 1) v ∈
          LinearMap.ker (mixedEndpointActiveNormalizedLocalInteraction A₀ .last) :=
      mem_ker_commuting_map_iff _ _
        (mixedEndpointActiveLastEdgePlacement_commute_firstBoundaryMap _ F) hFirst _
    rw [hremote]
    exact lastEdge_kernel_normalization A₀ A₁ hA₀ v
  | interior i =>
    have heq : mixedEndpointActiveLocalInteraction A₀ A₁
        (mixedEndpointActiveEdgeStart (.interior i)) =
      mixedEndpointActiveNormalizedLocalInteraction A₀ (.interior i) := by
      rw [mixedEndpointActiveLocalInteraction_eq_edgePlacement]
      change mixedEndpointActiveEdgePlacement (.interior i)
          (mixedEndpointEdgeConstraintES A₀ A₁ .interior) =
        mixedEndpointActiveEdgePlacement (.interior i) (parentInteractionES A₀ 2)
      rw [← mixedEndpointEdge_compression_eq_constraint,
        mixedEndpointInteriorEdge_compression_eq_parentInteractionES]
    rw [heq]
    have hcomm := mixedEndpointActiveInteriorEdgePlacement_commute_boundaryMaps
      (D₁ := D₁) i (parentInteractionES A₀ 2) F
    exact ((mem_ker_commuting_map_iff _ _ hcomm.1 hFirst _).trans
      (mem_ker_commuting_map_iff _ _ hcomm.2 hLast v)).symm

private theorem edgeFiber_placement
    (p : MixedEndpointActiveEdgeSite N)
    (T : EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)) →ₗ[ℂ]
      EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)))
    (v : mixedEndpointActiveSpace D₀ D₁ (N + 1))
    (s : mixedEndpointActiveEdgeSpectator D₀ D₁ p) :
    mixedEndpointActiveEdgeFiber p (mixedEndpointActiveEdgePlacement p T v) s =
      T (mixedEndpointActiveEdgeFiber p v s) := by
  apply PiLp.ext
  intro η
  change mixedEndpointActiveEdgePlacement p T v
    ((mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p).symm (η, s)) = _
  rw [mixedEndpointActiveEdgePlacement_apply]
  simp only [Equiv.apply_symm_apply]

private theorem edgePlacement_isSymmetricProjection
    (p : MixedEndpointActiveEdgeSite N)
    (T : EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)) →ₗ[ℂ]
      EuclideanSpace ℂ (mixedEndpointEdgeCfg D₀ D₁ (mixedEndpointActiveEdgePosition p)))
    (hT : T.IsSymmetricProjection) :
    (mixedEndpointActiveEdgePlacement p T).IsSymmetricProjection := by
  constructor
  · apply LinearMap.ext
    intro v
    apply PiLp.ext
    intro ξ
    simp only [Module.End.mul_apply, mixedEndpointActiveEdgePlacement_apply,
      edgeFiber_placement]
    exact congrArg (fun L =>
      L (mixedEndpointActiveEdgeFiber p v (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).2)
        (mixedEndpointActiveEdgeConfigEquiv D₀ D₁ p ξ).1) hT.isIdempotentElem.eq
  · have hG := ContinuousLinearMap.isSymmetricProjection_rightFiberwiseMap
      (S := mixedEndpointActiveEdgeSpectator D₀ D₁ p) (LinearMap.toContinuousLinearMap T) hT
    have hpos := ((mixedEndpointActiveEdgeLinearIsometryEquiv D₀ D₁ p).symm.conj_le_conj_iff
      0 (ContinuousLinearMap.rightFiberwiseMap
        (S := mixedEndpointActiveEdgeSpectator D₀ D₁ p)
        (LinearMap.toContinuousLinearMap T)).toLinearMap).mpr
          (LinearMap.nonneg_iff_isPositive.mpr hG.isPositive)
    have hnonneg : 0 ≤ mixedEndpointActiveEdgePlacement p T := by
      simpa only [map_zero, mixedEndpointActiveEdgePlacement] using hpos
    exact (LinearMap.nonneg_iff_isPositive.mp hnonneg).isSymmetric

/-- Every placed normalized core constraint is an orthogonal projection. -/
theorem mixedEndpointActiveNormalizedLocalInteraction_isSymmetricProjection
    (A₀ : MPSTensor (D₀ * D₀) D₀) (p : MixedEndpointActiveEdgeSite N) :
    (mixedEndpointActiveNormalizedLocalInteraction (D₁ := D₁) A₀ p).IsSymmetricProjection := by
  apply edgePlacement_isSymmetricProjection
  cases p with
  | first => exact endpointFirstEdgeCoreConstraintES_isSymmetricProjection A₀ _
  | last => exact endpointLastEdgeCoreConstraintES_isSymmetricProjection A₀ _
  | interior _ => exact parentInteractionES_isSymmetricProjection A₀ 2

private theorem symmetricProjections_eq_of_ker_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {P Q : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) (hQ : Q.IsSymmetricProjection)
    (hker : LinearMap.ker P = LinearMap.ker Q) : P = Q := by
  apply hP.ext hQ
  have hrangeP : LinearMap.range P = (LinearMap.ker P)ᗮ := by
    rw [← hP.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  have hrangeQ : LinearMap.range Q = (LinearMap.ker Q)ᗮ := by
    rw [← hQ.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  rw [hrangeP, hrangeQ, hker]

/-- The full boundary normalization pulls the placed core kernel back to
the actual local kernel. This is the termwise input for bounded deformation. -/
theorem ker_mixedEndpointActiveLocalInteraction_eq_comap_normalized
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (p : MixedEndpointActiveEdgeSite N) :
    LinearMap.ker (mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)) =
      (LinearMap.ker (mixedEndpointActiveNormalizedLocalInteraction A₀ p)).comap
        (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)).toLinearMap := by
  ext v
  exact mem_ker_mixedEndpointActiveLocalInteraction_iff_normalized A₀ A₁ hA₀ p v

/-- Deforming the actual local constraint by the inverse full boundary
normalization gives exactly its placed normalized core constraint. -/
theorem activeBoundaryNormalization_symm_deformed_actualLocal_eq_normalized
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (p : MixedEndpointActiveEdgeSite N) :
    (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)).symm.deformedConstraintProjection
        (mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)) =
      mixedEndpointActiveNormalizedLocalInteraction A₀ p := by
  apply symmetricProjections_eq_of_ker_eq
    (LinearEquiv.deformedConstraintProjection_isSymmetricProjection
      (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)).symm _)
    (mixedEndpointActiveNormalizedLocalInteraction_isSymmetricProjection A₀ p)
  rw [LinearEquiv.ker_deformedConstraintProjection]
  ext v
  change (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)).symm v ∈
      LinearMap.ker
        (mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)) ↔ _
  rw [mem_ker_mixedEndpointActiveLocalInteraction_iff_normalized A₀ A₁ hA₀,
    LinearEquiv.apply_symm_apply]

/-- The reverse canonical deformation recovers the actual compressed
local interaction, with its actual orthogonal-projection normalization. -/
theorem activeBoundaryNormalization_deformed_normalizedLocal_eq_actual
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (p : MixedEndpointActiveEdgeSite N) :
    (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)).deformedConstraintProjection
        (mixedEndpointActiveNormalizedLocalInteraction A₀ p) =
      mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p) := by
  apply symmetricProjections_eq_of_ker_eq
    (LinearEquiv.deformedConstraintProjection_isSymmetricProjection
      (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)) _)
    (mixedEndpointActiveLocalInteraction_isSymmetricProjection A₀ A₁ _)
  rw [LinearEquiv.ker_deformedConstraintProjection,
    ker_mixedEndpointActiveLocalInteraction_eq_comap_normalized A₀ A₁ hA₀ p]

/-- Distinct active-edge coordinates label distinct physical nonwrapping
bonds. Together with surjectivity this excludes missing or repeated terms. -/
theorem mixedEndpointActiveEdgeStart_injective :
    Function.Injective (mixedEndpointActiveEdgeStart (N := N)) := by
  intro p q hpq
  have h := congrArg (fun i => i.1.val) hpq
  cases p with
  | first =>
    cases q with
    | first => rfl
    | interior j => simp only [mixedEndpointActiveEdgeStart, Fin.val_zero, Fin.val_mk] at h; omega
    | last => simp only [mixedEndpointActiveEdgeStart, Fin.val_zero, Fin.val_mk] at h; omega
  | interior i =>
    cases q with
    | first => simp only [mixedEndpointActiveEdgeStart, Fin.val_zero, Fin.val_mk] at h; omega
    | interior j =>
      congr 1
      apply Subtype.ext
      apply Fin.ext
      simp only [mixedEndpointActiveEdgeStart, Fin.val_mk] at h
      omega
    | last =>
      have hi := i.2
      simp only [mixedEndpointActiveEdgeStart, Fin.val_mk] at h
      omega
  | last =>
    cases q with
    | first => simp only [mixedEndpointActiveEdgeStart, Fin.val_zero, Fin.val_mk] at h; omega
    | interior j =>
      have hj := j.2
      simp only [mixedEndpointActiveEdgeStart, Fin.val_mk] at h
      omega
    | last => rfl

/-- Exact indexing equivalence between the edge split and the actual
nonwrapping interaction sum. -/
def mixedEndpointActiveEdgeStartEquiv (N : ℕ) :
    MixedEndpointActiveEdgeSite N ≃ NonwrappingStart 2 (N + 1 + 1 + 1) :=
  Equiv.ofBijective mixedEndpointActiveEdgeStart
    ⟨mixedEndpointActiveEdgeStart_injective, mixedEndpointActiveEdgeStart_surjective⟩

instance : Fintype (MixedEndpointActiveEdgeSite N) :=
  Fintype.ofEquiv (NonwrappingStart 2 (N + 1 + 1 + 1))
    (mixedEndpointActiveEdgeStartEquiv N).symm

/-- The sum of the explicitly placed common-core local constraints. -/
def mixedEndpointActiveNormalizedHamiltonian
    (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) :
    mixedEndpointActiveSpace D₀ D₁ (N + 1) →ₗ[ℂ]
      mixedEndpointActiveSpace D₀ D₁ (N + 1) :=
  ∑ p : MixedEndpointActiveEdgeSite N, mixedEndpointActiveNormalizedLocalInteraction A₀ p

/-- Reindexing by the edge split gives exactly the original active sum. -/
theorem mixedEndpointActiveHamiltonian_eq_sum_edges
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁) (N : ℕ) :
    mixedEndpointActiveHamiltonian A₀ A₁ (N + 1) =
      ∑ p : MixedEndpointActiveEdgeSite N,
        mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p) := by
  exact (Fintype.sum_equiv (mixedEndpointActiveEdgeStartEquiv N)
    (fun p => mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p))
    (fun i => mixedEndpointActiveLocalInteraction A₀ A₁ i) (fun _ => rfl)).symm

/-- The normalized sum is exactly the sum of the canonical deformations
of the actual terms, in the inverse-boundary-normalization orientation. -/
theorem mixedEndpointActiveNormalizedHamiltonian_eq_sum_deformed
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N =
      ∑ p : MixedEndpointActiveEdgeSite N,
        (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)).symm.deformedConstraintProjection
          (mixedEndpointActiveLocalInteraction A₀ A₁ (mixedEndpointActiveEdgeStart p)) := by
  simp only [activeBoundaryNormalization_symm_deformed_actualLocal_eq_normalized,
    mixedEndpointActiveNormalizedHamiltonian]

/-- In the forward-normalization orientation, the actual active sum is
exactly the sum of canonical deformations of the normalized core terms. -/
theorem mixedEndpointActiveHamiltonian_eq_sum_deformed_normalized
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    mixedEndpointActiveHamiltonian A₀ A₁ (N + 1) =
      ∑ p : MixedEndpointActiveEdgeSite N,
        (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)).deformedConstraintProjection
          (mixedEndpointActiveNormalizedLocalInteraction A₀ p) := by
  simpa only [activeBoundaryNormalization_deformed_normalizedLocal_eq_actual A₀ A₁ hA₀] using
    mixedEndpointActiveHamiltonian_eq_sum_edges A₀ A₁ N

/-- The normalized sum is positive as a sum of the concrete placed core
constraint projections. -/
theorem mixedEndpointActiveNormalizedHamiltonian_isPositive
    (A₀ : MPSTensor (D₀ * D₀) D₀) (N : ℕ) :
    (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N).IsPositive := by
  apply LinearMap.nonneg_iff_isPositive.mp
  exact Finset.sum_nonneg fun p _ => LinearMap.nonneg_iff_isPositive.mpr
    (mixedEndpointActiveNormalizedLocalInteraction_isSymmetricProjection A₀ p).isPositive

/-- The global kernel transport follows from the proved termwise transport
and positivity of both concrete sums. -/
theorem ker_mixedEndpointActiveHamiltonian_eq_comap_normalized
    (A₀ : MPSTensor (D₀ * D₀) D₀) (A₁ : MPSTensor (D₁ * D₁) D₁)
    (hA₀ : Kraus.IsInjective A₀) (N : ℕ) :
    LinearMap.ker (mixedEndpointActiveHamiltonian A₀ A₁ (N + 1)) =
      (LinearMap.ker (mixedEndpointActiveNormalizedHamiltonian (D₁ := D₁) A₀ N)).comap
        (activeBoundaryNormalizationEquivES A₀ hA₀ (N + 1)).toLinearMap := by
  rw [mixedEndpointActiveHamiltonian_eq_sum_edges, mixedEndpointActiveNormalizedHamiltonian,
    WeightedPositiveKernel.ker_sum_eq_iInf
      (fun p => (mixedEndpointActiveLocalInteraction_isSymmetricProjection A₀ A₁
        (mixedEndpointActiveEdgeStart p)).isPositive),
    WeightedPositiveKernel.ker_sum_eq_iInf
      (fun p =>
        (mixedEndpointActiveNormalizedLocalInteraction_isSymmetricProjection A₀ p).isPositive),
    Submodule.comap_iInf]
  simp only [ker_mixedEndpointActiveLocalInteraction_eq_comap_normalized A₀ A₁ hA₀]

end

end MPOSymmetry
end MPSTensor
