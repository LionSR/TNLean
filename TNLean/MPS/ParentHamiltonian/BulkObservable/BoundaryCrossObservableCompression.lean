/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BoundaryMap.BlockGroundSpaceOverlap
import TNLean.MPS.ParentHamiltonian.BulkObservable.BulkObservableCommutator
import QICLean.Analysis.Projection.TwoProjectionCompression

/-!
# Decay of cross-sector compression by prefix locality

Every open MPS ground vector belongs to the ground space on its prefix,
extended by the full Hilbert space on the remaining sites. An observable
supported beyond that prefix commutes with its ground projection. Consequently,
the cross compression of the observable between two full-chain ground spaces
is bounded by the overlap of their prefix ground projections times the
observable norm.

For inequivalent normalized primitive tensors, prefix overlaps tend to zero.
Thus cross compression tends to zero when the left free interval expands;
the right free interval may vary arbitrarily. This is a locality consequence
of the sector-overlap estimate in Nachtergaele, arXiv:cond-mat/9410110,
proof of Lemma disjoint, lines 1744--1820. It is an intermediate statement
for the ground-projection subtraction in lines 2649--2675.
-/

open Filter
open scoped Topology Matrix ComplexOrder InnerProductSpace
open ManyBody (placeAlong chainWindow)

namespace MPSTensor
variable {d D₁ D₂ : ℕ}

/-- The ground projection of the first `L` sites of a chain of `N` sites, extended by the
identity on the remaining sites. -/
private noncomputable def prefixGroundProjection (A : MPSTensor d D₁) {L N : ℕ} (hLN : L ≤ N) :
    EuclideanSpace ℂ (Cfg d N) →L[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
    (placeAlong (X := fun _ ↦ Fin d) (chainWindow 0 (by omega))
      ((Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
        (groundSpaceES A L).starProjection))

private theorem prefixGroundProjection_eq_id_sub_term
    (A : MPSTensor d D₁) {L N : ℕ} (hLN : L ≤ N) :
    prefixGroundProjection A hLN = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Cfg d N)) -
      Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
        ((parentChainInteraction A L N).term ⟨0, by omega⟩) := by
  let p := (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
    (groundSpaceES A L).starProjection
  have hc : 1 - p = LinearMap.toMatrix' (parentInteraction A L) := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_toMatrix'_parentInteraction]
    change (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ) (1 - p)).toLinearMap = _
    rw [map_sub, map_one, StarAlgEquiv.apply_symm_apply, Submodule.starProjection_orthogonal]
    rfl
  rw [ManyBody.Interaction.ofPlaceAlong_term, ← hc]
  change Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (placeAlong (X := fun _ ↦ Fin d) (chainWindow 0 (by omega)) p) =
    1 - Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (placeAlong (X := fun _ ↦ Fin d) (chainWindow 0 (by omega)) (1 - p))
  rw [ManyBody.placeAlong_sub, ManyBody.placeAlong_one, map_sub, map_one, sub_sub_cancel]

private theorem prefixGroundProjection_comp_groundSpaceProjection
    (A : MPSTensor d D₁) {L N : ℕ} (hLN : L ≤ N) :
    (prefixGroundProjection A hLN).comp (groundSpaceES A N).starProjection =
      (groundSpaceES A N).starProjection := by
  rw [prefixGroundProjection_eq_id_sub_term A hLN]
  apply ContinuousLinearMap.ext
  intro v
  have hv := groundSpaceES_le_ker_hamiltonian_parentChainInteraction A L N
    ((groundSpaceES A N).starProjection_apply_mem v)
  have hkill : Matrix.toEuclideanLin ((parentChainInteraction A L N).term ⟨0, by omega⟩)
      ((groundSpaceES A N).starProjection v) = 0 := by
    rw [Matrix.toLpLin_apply, WithLp.toLp_eq_zero]
    exact (parentChainInteraction_term_mulVec_eq_zero_iff A _ _).mpr fun τ ↦
      contiguousRestrictₗ_mem_groundSpace_of_mem_ker_hamiltonian_parentChainInteraction A hv
        0 (by omega) τ
  change (groundSpaceES A N).starProjection v -
    Matrix.toEuclideanLin ((parentChainInteraction A L N).term ⟨0, by omega⟩)
      ((groundSpaceES A N).starProjection v) = _
  rw [hkill, sub_zero]

private theorem groundSpaceProjection_comp_prefixGroundProjection
    (A : MPSTensor d D₁) {L N : ℕ} (hLN : L ≤ N) :
    (groundSpaceES A N).starProjection.comp (prefixGroundProjection A hLN) =
      (groundSpaceES A N).starProjection := by
  have hp : ((Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
      (groundSpaceES A L).starProjection).IsHermitian :=
    (isSelfAdjoint_starProjection (groundSpaceES A L)).map
      (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
  have hQ : (prefixGroundProjection A hLN).adjoint = prefixGroundProjection A hLN := by
    rw [prefixGroundProjection, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      Matrix.star_eq_conjTranspose, (ManyBody.isHermitian_placeAlong _ hp).eq]
  have h := congrArg ContinuousLinearMap.adjoint
    (prefixGroundProjection_comp_groundSpaceProjection A hLN)
  simpa only [ContinuousLinearMap.adjoint_comp, hQ,
    LinearMap.IsSymmetric.clm_adjoint_eq
      (A := (groundSpaceES A N).starProjection)
      (Submodule.isSymmetricProjection_starProjection (groundSpaceES A N)).isSymmetric] using h

/-- The prefix ground projection, extended by the identity, fixes the full-chain
ground projection on both sides. No injectivity hypothesis is needed. -/
theorem placeAlong_chainWindow_groundSpaceProjection_comp_groundSpaceProjection
    (A : MPSTensor d D₁) {L N : ℕ} (hLN : L ≤ N) :
    (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (placeAlong (X := fun _ ↦ Fin d) (chainWindow 0 (by omega))
        ((Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
          (groundSpaceES A L).starProjection))).comp
            (groundSpaceES A N).starProjection = (groundSpaceES A N).starProjection ∧
    (groundSpaceES A N).starProjection.comp
      (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
        (placeAlong (X := fun _ ↦ Fin d) (chainWindow 0 (by omega))
          ((Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
            (groundSpaceES A L).starProjection))) = (groundSpaceES A N).starProjection :=
  ⟨prefixGroundProjection_comp_groundSpaceProjection A hLN,
    groundSpaceProjection_comp_prefixGroundProjection A hLN⟩

private theorem norm_prefixGroundProjection_comp_le
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {L N : ℕ} (hLN : L ≤ N) :
    ‖(prefixGroundProjection A hLN).comp (prefixGroundProjection B hLN)‖ ≤
      ‖(groundSpaceES A L).starProjection.comp (groundSpaceES B L).starProjection‖ := by
  let pA := (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
    (groundSpaceES A L).starProjection
  let pB := (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
    (groundSpaceES B L).starProjection
  have h0 : 0 + L ≤ N := by omega
  change ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (placeAlong (X := fun _ ↦ Fin d) (chainWindow 0 h0) pA) *
    Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (placeAlong (X := fun _ ↦ Fin d) (chainWindow 0 h0) pB)‖ ≤ _
  rw [← map_mul, ← ManyBody.placeAlong_mul]
  open scoped Matrix.Norms.L2Operator in
  have h := ManyBody.norm_placeAlong_le (X := fun _ ↦ Fin d) (chainWindow 0 h0) (pA * pB)
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def] at h
  simpa only [map_mul, pA, pB, StarAlgEquiv.apply_symm_apply,
    ContinuousLinearMap.mul_def] using h

private theorem prefixGroundProjection_commute_bulkObservable
    (A : MPSTensor d D₁) {ℓ k r : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    (prefixGroundProjection A (show ℓ ≤ (ℓ + k) + r by omega)).comp
      (Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
        (bulkObservable X ℓ r)) =
      (Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
        (bulkObservable X ℓ r)).comp
          (prefixGroundProjection A (show ℓ ≤ (ℓ + k) + r by omega)) := by
  have h := ManyBody.commute_placeAlong_of_disjoint (X := fun _ ↦ Fin d)
    (chainWindow 0 (show 0 + ℓ ≤ (ℓ + k) + r by omega))
    (w' := chainWindow ℓ (Nat.le_add_right (ℓ + k) r))
    (by
      rw [ManyBody.map_chainWindow, ManyBody.map_chainWindow, Nat.zero_add]
      exact ManyBody.disjoint_interval_interval 0 ℓ (ℓ + k))
    ((Matrix.toEuclideanCLM (n := Cfg d ℓ) (𝕜 := ℂ)).symm
      (groundSpaceES A ℓ).starProjection) X
  have hmap := congrArg (Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)) h.eq
  simpa only [map_mul, ContinuousLinearMap.mul_def, prefixGroundProjection,
    bulkObservable_eq_placeAlong_chainWindow] using hmap

/-- A local observable beyond a prefix has cross compression bounded
by the overlap of the prefix ground projections times its operator norm.
This finite-volume locality estimate requires no normalization or primitivity. -/
theorem norm_groundSpaceES_bulkObservable_cross_compression_le
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {ℓ k r : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    ‖(groundSpaceES A ((ℓ + k) + r)).starProjection.comp
      ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
        (bulkObservable X ℓ r)).comp (groundSpaceES B ((ℓ + k) + r)).starProjection)‖ ≤
      ‖(groundSpaceES A ℓ).starProjection.comp (groundSpaceES B ℓ).starProjection‖ *
        ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖ := by
  let PA := (groundSpaceES A ((ℓ + k) + r)).starProjection
  let PB := (groundSpaceES B ((ℓ + k) + r)).starProjection
  have hℓN : ℓ ≤ (ℓ + k) + r := by omega
  let QA := prefixGroundProjection A hℓN
  let QB := prefixGroundProjection B hℓN
  let Y := Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
    (bulkObservable X ℓ r)
  have hA : PA * QA = PA := groundSpaceProjection_comp_prefixGroundProjection A hℓN
  have hB : QB * PB = PB := prefixGroundProjection_comp_groundSpaceProjection B hℓN
  have hcomm : QB * Y = Y * QB := prefixGroundProjection_commute_bulkObservable B X
  have heq : PA * Y * PB = PA * (QA * QB) * Y * PB := by
    rw [← mul_assoc PA QA QB, mul_assoc (PA * QA) QB Y, hA, hcomm,
      ← mul_assoc PA Y QB, mul_assoc (PA * Y) QB PB, hB]
  have hn : ‖PA * (QA * QB) * Y * PB‖ ≤ ‖PA‖ * ‖QA * QB‖ * ‖Y‖ * ‖PB‖ := by
    exact norm_mul_le_of_le norm_mul₃_le le_rfl
  have hPA : ‖PA‖ ≤ 1 := (groundSpaceES A ((ℓ + k) + r)).starProjection_norm_le
  have hPB : ‖PB‖ ≤ 1 := (groundSpaceES B ((ℓ + k) + r)).starProjection_norm_le
  have hPair : ‖QA * QB‖ ≤
      ‖(groundSpaceES A ℓ).starProjection.comp (groundSpaceES B ℓ).starProjection‖ :=
    norm_prefixGroundProjection_comp_le A B hℓN
  have hY : ‖Y‖ ≤ ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖ :=
    norm_toEuclideanCLM_bulkObservable_le X ℓ r
  change ‖PA * (Y * PB)‖ ≤ _
  rw [← mul_assoc, heq]
  refine hn.trans ?_
  calc
    _ ≤ 1 * ‖(groundSpaceES A ℓ).starProjection.comp (groundSpaceES B ℓ).starProjection‖ *
        ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖ * 1 := by gcongr
    _ = _ := by simp only [one_mul, mul_one]

end MPSTensor

namespace Kraus.HasComplementaryFixedPointGap

open MPSTensor

variable {d D₁ D₂ : ℕ}

/-- The products of the ground projections of inequivalent normalized primitive
tensors tend to zero in operator norm. Source: Nachtergaele,
arXiv:cond-mat/9410110, proof of Lemma disjoint, equations C1C2 and limP12. -/
theorem groundSpaceES_starProjection_comp_tendsto_zero_of_inequivalent
    [NeZero D₁] [NeZero D₂] {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} {σ : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : Kraus.HasComplementaryFixedPointGap A ρ) (hB : Kraus.HasComplementaryFixedPointGap B σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hDistinct : ∀ h : D₂ = D₁, ¬ MPTensor.GaugePhaseEquiv (h ▸ B) A) :
    Tendsto (fun n =>
      ‖(groundSpaceES A n).starProjection.comp (groundSpaceES B n).starProjection‖)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · exact fun a ha => Eventually.of_forall fun _ => ha.trans_le (norm_nonneg _)
  · intro ε hε
    filter_upwards [hA.eventually_norm_inner_groundSpaceES_le_of_inequivalent
      hB hρ hσ hDistinct (half_pos hε)] with n hn
    have h := Submodule.norm_starProjection_comp_sub_starProjection_le_of_relative_overlap
      (groundSpaceES A n) (groundSpaceES B n) ⊥ bot_le bot_le (le_of_lt (half_pos hε))
      (fun x hx _ y hy _ => hn x hx y hy)
    simp only [Submodule.starProjection_bot, sub_zero] at h
    exact h.trans_lt (half_lt_self hε)

/-- Cross compression of a fixed nonempty local observable between inequivalent
primitive sectors tends to zero as the left free interval expands. The right
free interval may vary arbitrarily. This follows by prefix locality from the
sector-overlap estimate in Nachtergaele, arXiv:cond-mat/9410110,
proof of Lemma disjoint, lines 1744--1820. -/
theorem bulkObservable_cross_groundSpace_compression_tendsto_zero_of_inequivalent
    [NeZero D₁] [NeZero D₂] {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} {σ : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : Kraus.HasComplementaryFixedPointGap A ρ) (hB : Kraus.HasComplementaryFixedPointGap B σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hDistinct : ∀ h : D₂ = D₁, ¬ MPTensor.GaugePhaseEquiv (h ▸ B) A)
    {k : ℕ} (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ} (hℓ : Tendsto ℓ f atTop) :
    Tendsto (fun n =>
      ‖(groundSpaceES A ((ℓ n + k) + r n)).starProjection.comp
        ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ)
          (bulkObservable X (ℓ n) (r n))).comp
            (groundSpaceES B ((ℓ n + k) + r n)).starProjection)‖) f (𝓝 0) := by
  have hUpper : Tendsto (fun n =>
      ‖(groundSpaceES A (ℓ n)).starProjection.comp (groundSpaceES B (ℓ n)).starProjection‖ *
        ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖) f (𝓝 0) := by
    simpa only [zero_mul, Function.comp_def] using
      ((hA.groundSpaceES_starProjection_comp_tendsto_zero_of_inequivalent
        hB hρ hσ hDistinct).comp hℓ).mul_const
          ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun _ => norm_groundSpaceES_bulkObservable_cross_compression_le A B X) hUpper

end Kraus.HasComplementaryFixedPointGap
