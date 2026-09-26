/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryCoordinates

/-!
# Overlap bounds with spectator sites

An overlap bound on a common interval is unchanged when the configurations
outside that interval are allowed to vary. This supplies the overlap bounds
used for the extended block spaces in Nachtergaele,
arXiv:cond-mat/9410110, proof of Lemma `commutation` (ii), lines 2533--2577.
-/

open scoped BigOperators InnerProductSpace

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
private theorem norm_inner_le_of_fibers (x y : PiLp 2 E) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, ‖⟪x i, y i⟫_ℂ‖ ≤ ε * ‖x i‖ * ‖y i‖) :
    ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  rw [PiLp.inner_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ h i).trans ?_)
  simpa only [mul_assoc, ← Finset.mul_sum, PiLp.norm_eq_of_L2] using
    mul_le_mul_of_nonneg_left
      (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i ↦ ‖x i‖) (fun i ↦ ‖y i‖)) hε

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

private theorem norm_inner_le_of_reindexed_fibers
    (e : α × β ≃ γ) (x y : EuclideanSpace ℂ γ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, ‖⟪(WithLp.toLp 2 (fun j ↦ x (e (i, j))) : EuclideanSpace ℂ β),
      (WithLp.toLp 2 (fun j ↦ y (e (i, j))) : EuclideanSpace ℂ β)⟫_ℂ‖ ≤
      ε * ‖(WithLp.toLp 2 (fun j ↦ x (e (i, j))) : EuclideanSpace ℂ β)‖ *
        ‖(WithLp.toLp 2 (fun j ↦ y (e (i, j))) : EuclideanSpace ℂ β)‖) :
    ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  let F := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (e.symm.trans (Equiv.sigmaEquivProd α β).symm)).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : α) (_ : β) ↦ ℂ))
  have hF : ∀ i, ‖⟪F x i, F y i⟫_ℂ‖ ≤ ε * ‖F x i‖ * ‖F y i‖ := h
  simpa only [F.inner_map_map, F.norm_map] using norm_inner_le_of_fibers (F x) (F y) hε hF

namespace MPSTensor
variable {d D₁ D₂ : ℕ}

/-- An overlap bound on the common middle interval controls vectors whose
restrictions to that interval lie in the two ground spaces, uniformly in
both spectator lengths. This is the finite-sum form of the overlap bound
in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem norm_inner_le_of_middle_groundSpaceES
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (K L Q : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hAB : ∀ x ∈ groundSpaceES A L, ∀ y ∈ groundSpaceES B L,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖)
    (x y : EuclideanSpace ℂ (Cfg d (K + L + Q)))
    (hx : ∀ u : Cfg d K, ∀ v : Cfg d Q,
      (WithLp.toLp 2 (fun w ↦ x (Fin.append (Fin.append u w) v)) :
        EuclideanSpace ℂ (Cfg d L)) ∈ groundSpaceES A L)
    (hy : ∀ u : Cfg d K, ∀ v : Cfg d Q,
      (WithLp.toLp 2 (fun w ↦ y (Fin.append (Fin.append u w) v)) :
        EuclideanSpace ℂ (Cfg d L)) ∈ groundSpaceES B L) :
    ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := by
  apply norm_inner_le_of_reindexed_fibers
    ((Equiv.prodComm (Cfg d Q) (Cfg d (K + L))).trans (Fin.appendEquiv (K + L) Q))
    x y hε
  exact fun v ↦ norm_inner_le_of_reindexed_fibers (Fin.appendEquiv K L) _ _ hε
    (fun u ↦ hAB _ (hx u v) _ (hy u v))

private theorem leftBoundaryMapES_middle_mem
    (A : MPSTensor d D₁) (K L Q : ℕ)
    (x : BoundaryFamilySpace (D := D₁) (Cfg d Q))
    (u : Cfg d K) (v : Cfg d Q) :
    (WithLp.toLp 2 (fun w ↦ leftBoundaryMapES A (K + L) Q x
      (Fin.append (Fin.append u w) v)) : EuclideanSpace ℂ (Cfg d L)) ∈
      groundSpaceES A L := by
  rw [mem_groundSpaceES_iff]
  change (fun w ↦ leftBoundaryMap A (K + L) Q
    (boundaryFamilyEquiv (D := D₁) (Cfg d Q) x) (Fin.append (Fin.append u w) v)) ∈ _
  simpa only [tailRestrictₗ,
    LinearMap.coe_mk, AddHom.coe_mk, leftBoundaryMap_append] using
      (groundSpace_inTailGround A K L
        (show groundSpaceMap A (K + L)
          (boundaryFamilyEquiv (D := D₁) (Cfg d Q) x v) ∈ groundSpace A (K + L) from
            ⟨_, rfl⟩) u)

private theorem reassocTailBoundaryMapES_middle_mem
    (A : MPSTensor d D₁) (K L Q : ℕ)
    (x : BoundaryFamilySpace (D := D₁) (Cfg d K))
    (u : Cfg d K) (v : Cfg d Q) :
    (WithLp.toLp 2 (fun w ↦ reassocTailBoundaryMapES A K L Q x
      (Fin.append (Fin.append u w) v)) : EuclideanSpace ℂ (Cfg d L)) ∈
      groundSpaceES A L := by
  rw [mem_groundSpaceES_iff]
  change (fun w ↦ reassocTailBoundaryMapES A K L Q x
    (Fin.append (Fin.append u w) v)) ∈ groundSpace A L
  simpa only [prefixRestrictₗ, LinearMap.coe_mk, AddHom.coe_mk,
    reassocTailBoundaryMapES_apply_threeBlock] using
      (show prefixRestrictₗ v (groundSpaceMap A (L + Q)
        (boundaryFamilyEquiv (D := D₁) (Cfg d K) x u)) ∈ groundSpace A L from
          (prefixRestrictₗ_groundSpaceMap A v _).symm ▸ ⟨_, rfl⟩)

/-- The middle-interval overlap bound also bounds two left boundary vectors,
independently of both spectator lengths. This supplies the within-family
bound in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem norm_inner_leftBoundaryMapES_le
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (K L Q : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hAB : ∀ x ∈ groundSpaceES A L, ∀ y ∈ groundSpaceES B L,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖)
    (x : BoundaryFamilySpace (D := D₁) (Cfg d Q))
    (y : BoundaryFamilySpace (D := D₂) (Cfg d Q)) :
    ‖⟪leftBoundaryMapES A (K + L) Q x, leftBoundaryMapES B (K + L) Q y⟫_ℂ‖ ≤
      ε * ‖leftBoundaryMapES A (K + L) Q x‖ * ‖leftBoundaryMapES B (K + L) Q y‖ := by
  exact norm_inner_le_of_middle_groundSpaceES A B K L Q hε hAB _ _
    (leftBoundaryMapES_middle_mem A K L Q x) (leftBoundaryMapES_middle_mem B K L Q y)

/-- The middle-interval overlap bound also bounds two right boundary vectors,
independently of both spectator lengths. This is the other within-family
bound in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem norm_inner_reassocTailBoundaryMapES_le
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (K L Q : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hAB : ∀ x ∈ groundSpaceES A L, ∀ y ∈ groundSpaceES B L,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖)
    (x : BoundaryFamilySpace (D := D₁) (Cfg d K))
    (y : BoundaryFamilySpace (D := D₂) (Cfg d K)) :
    ‖⟪reassocTailBoundaryMapES A K L Q x, reassocTailBoundaryMapES B K L Q y⟫_ℂ‖ ≤
      ε * ‖reassocTailBoundaryMapES A K L Q x‖ * ‖reassocTailBoundaryMapES B K L Q y‖ := by
  exact norm_inner_le_of_middle_groundSpaceES A B K L Q hε hAB _ _
    (reassocTailBoundaryMapES_middle_mem A K L Q x)
    (reassocTailBoundaryMapES_middle_mem B K L Q y)

/-- The middle-interval overlap bound controls a left boundary vector and a
right boundary vector of another tensor. This is the cross-family bound
in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii). -/
theorem norm_inner_left_reassocTailBoundaryMapES_le
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (K L Q : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hAB : ∀ x ∈ groundSpaceES A L, ∀ y ∈ groundSpaceES B L,
      ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖)
    (x : BoundaryFamilySpace (D := D₁) (Cfg d Q))
    (y : BoundaryFamilySpace (D := D₂) (Cfg d K)) :
    ‖⟪leftBoundaryMapES A (K + L) Q x, reassocTailBoundaryMapES B K L Q y⟫_ℂ‖ ≤
      ε * ‖leftBoundaryMapES A (K + L) Q x‖ * ‖reassocTailBoundaryMapES B K L Q y‖ := by
  exact norm_inner_le_of_middle_groundSpaceES A B K L Q hε hAB _ _
    (leftBoundaryMapES_middle_mem A K L Q x)
    (reassocTailBoundaryMapES_middle_mem B K L Q y)

end MPSTensor
