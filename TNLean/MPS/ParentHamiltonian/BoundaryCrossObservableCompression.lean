/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockGroundSpaceOverlap
import TNLean.MPS.ParentHamiltonian.BulkObservableCommutator
import QICLean.Analysis.TwoProjectionCompression

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

namespace MPSTensor
variable {d D₁ D₂ : ℕ}

private noncomputable def prefixGroundProjection (A : MPSTensor d D₁) (L N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →L[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
    (chainWindowOperator N 0
      ((Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
        (groundSpaceES A L).starProjection))

private theorem prefixGroundProjection_eq_id_sub_localTerm
    (A : MPSTensor d D₁) {L N : ℕ} (hL : 0 < L) (hLN : L ≤ N) :
    prefixGroundProjection A L N = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Cfg d N)) -
      (localTermES A L (⟨0, by omega⟩ : Fin N)).toContinuousLinearMap := by
  let p := (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
    (groundSpaceES A L).starProjection
  have hc : Matrix.toEuclideanLin (1 - p) = parentInteractionES A L := by
    change (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ) (1 - p)).toLinearMap = _
    rw [map_sub, map_one, StarAlgEquiv.apply_symm_apply]
    rw [parentInteractionES, Submodule.starProjection_orthogonal]
    rfl
  have hlocal := periodicLocalInteractionES_eq_toEuclideanLin_embedLocalOperator
    hLN (⟨0, by omega⟩ : Fin N) (1 - p)
  rw [hc, periodicLocalInteractionES_parentInteractionES A hL] at hlocal
  have hwindow : localTermES A L (⟨0, by omega⟩ : Fin N) =
      Matrix.toEuclideanLin (chainWindowOperator N 0 (1 - p)) := by
    simpa only [chainWindowOperator,
      dite_eq_left (show L ≤ N ∧ 0 < N from ⟨hLN, by omega⟩)] using hlocal
  rw [hwindow]
  change Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (chainWindowOperator N 0 p) =
    1 - Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (chainWindowOperator N 0 (1 - p))
  rw [chainWindowOperator_sub (by omega) (by omega), chainWindowOperator_one (by omega) (by omega),
    map_sub, map_one, sub_sub_cancel]

private theorem prefixGroundProjection_comp_groundSpaceProjection
    (A : MPSTensor d D₁) {L N : ℕ} (hL : 0 < L) (hLN : L ≤ N) :
    (prefixGroundProjection A L N).comp (groundSpaceES A N).starProjection =
      (groundSpaceES A N).starProjection := by
  rw [prefixGroundProjection_eq_id_sub_localTerm A hL hLN]
  apply ContinuousLinearMap.ext
  intro v
  have hv := (groundSpaceES_le_ker_openParentHamiltonianES A L N)
    ((groundSpaceES A N).starProjection_apply_mem v)
  have hkill := localTermES_eq_zero_of_openParentHamiltonianES_eq_zero A L N hv
    (⟨(⟨0, by omega⟩ : Fin N), by change 0 + L ≤ N; omega⟩ : NonwrappingStart L N)
  change (groundSpaceES A N).starProjection v -
    localTermES A L (⟨0, by omega⟩ : Fin N) ((groundSpaceES A N).starProjection v) = _
  rw [hkill, sub_zero]

private theorem groundSpaceProjection_comp_prefixGroundProjection
    (A : MPSTensor d D₁) {L N : ℕ} (hL : 0 < L) (hLN : L ≤ N) :
    (groundSpaceES A N).starProjection.comp (prefixGroundProjection A L N) =
      (groundSpaceES A N).starProjection := by
  have hQ : (prefixGroundProjection A L N).adjoint = prefixGroundProjection A L N := by
    rw [prefixGroundProjection_eq_id_sub_localTerm A hL hLN, map_sub,
      ContinuousLinearMap.adjoint_id]
    rw [LinearMap.IsSymmetric.clm_adjoint_eq
      (A := (localTermES A L (⟨0, by omega⟩ : Fin N)).toContinuousLinearMap)
      (localTermES_isSymmetricProjection A L (⟨0, by omega⟩ : Fin N)).isSymmetric]
  have h := congrArg ContinuousLinearMap.adjoint
    (prefixGroundProjection_comp_groundSpaceProjection A hL hLN)
  simpa only [ContinuousLinearMap.adjoint_comp, hQ,
    LinearMap.IsSymmetric.clm_adjoint_eq
      (A := (groundSpaceES A N).starProjection)
      (Submodule.isSymmetricProjection_starProjection (groundSpaceES A N)).isSymmetric] using h


/-- The prefix ground projection, extended by the identity, fixes the full-chain
ground projection on both sides. No injectivity hypothesis is needed. -/
theorem chainWindowOperator_groundSpaceProjection_comp_groundSpaceProjection
    (A : MPSTensor d D₁) {L N : ℕ} (hL : 0 < L) (hLN : L ≤ N) :
    (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
      (chainWindowOperator N 0
        ((Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
          (groundSpaceES A L).starProjection))).comp
            (groundSpaceES A N).starProjection = (groundSpaceES A N).starProjection ∧
    (groundSpaceES A N).starProjection.comp
      (Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ)
        (chainWindowOperator N 0
          ((Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
            (groundSpaceES A L).starProjection))) = (groundSpaceES A N).starProjection :=
  ⟨prefixGroundProjection_comp_groundSpaceProjection A hL hLN,
    groundSpaceProjection_comp_prefixGroundProjection A hL hLN⟩

private theorem norm_prefixGroundProjection_comp_le
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {L N : ℕ}
    (hL : 0 < L) (hLN : L ≤ N) :
    ‖(prefixGroundProjection A L N).comp (prefixGroundProjection B L N)‖ ≤
      ‖(groundSpaceES A L).starProjection.comp (groundSpaceES B L).starProjection‖ := by
  let pA := (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
    (groundSpaceES A L).starProjection
  let pB := (Matrix.toEuclideanCLM (n := Cfg d L) (𝕜 := ℂ)).symm
    (groundSpaceES B L).starProjection
  change ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (chainWindowOperator N 0 pA) *
    Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (chainWindowOperator N 0 pB)‖ ≤ _
  rw [← map_mul, ← chainWindowOperator_mul (by omega) (by omega)]
  have h := norm_toEuclideanCLM_chainWindowOperator_le (N := N) (a := 0)
    (by omega) (by omega) (pA * pB)
  simpa only [map_mul, pA, pB, StarAlgEquiv.apply_symm_apply,
    ContinuousLinearMap.mul_def] using h

private theorem prefixGroundProjection_commute_bulkObservable
    (A : MPSTensor d D₁) {ℓ k r : ℕ} (hℓ : 0 < ℓ) (hk : 0 < k)
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    (prefixGroundProjection A ℓ ((ℓ + k) + r)).comp
      (Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
        (bulkObservable X ℓ r)) =
      (Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
        (bulkObservable X ℓ r)).comp (prefixGroundProjection A ℓ ((ℓ + k) + r)) := by
  have h := chainWindowOperator_commute_of_disjoint (N := (ℓ + k) + r)
    (a := 0) (b := ℓ) (by omega) (by omega) (by omega) (by omega)
    (Or.inl (show 0 + ℓ ≤ ℓ by omega))
    ((Matrix.toEuclideanCLM (n := Cfg d ℓ) (𝕜 := ℂ)).symm
      (groundSpaceES A ℓ).starProjection) X
  have hmap := congrArg (Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)) h.eq
  simpa only [map_mul, ContinuousLinearMap.mul_def, prefixGroundProjection,
    bulkObservable_eq_chainWindowOperator hk] using hmap

/-- A local observable beyond a nonempty prefix has cross compression bounded
by the overlap of the prefix ground projections times its operator norm.
This finite-volume locality estimate requires no normalization or primitivity. -/
theorem norm_groundSpaceES_bulkObservable_cross_compression_le
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) {ℓ k r : ℕ}
    (hℓ : 0 < ℓ) (hk : 0 < k) (X : Matrix (Cfg d k) (Cfg d k) ℂ) :
    ‖(groundSpaceES A ((ℓ + k) + r)).starProjection.comp
      ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
        (bulkObservable X ℓ r)).comp (groundSpaceES B ((ℓ + k) + r)).starProjection)‖ ≤
      ‖(groundSpaceES A ℓ).starProjection.comp (groundSpaceES B ℓ).starProjection‖ *
        ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖ := by
  let PA := (groundSpaceES A ((ℓ + k) + r)).starProjection
  let PB := (groundSpaceES B ((ℓ + k) + r)).starProjection
  let QA := prefixGroundProjection A ℓ ((ℓ + k) + r)
  let QB := prefixGroundProjection B ℓ ((ℓ + k) + r)
  let Y := Matrix.toEuclideanCLM (n := Cfg d ((ℓ + k) + r)) (𝕜 := ℂ)
    (bulkObservable X ℓ r)
  have hA : PA * QA = PA := groundSpaceProjection_comp_prefixGroundProjection A hℓ (by omega)
  have hB : QB * PB = PB := prefixGroundProjection_comp_groundSpaceProjection B hℓ (by omega)
  have hcomm : QB * Y = Y * QB := prefixGroundProjection_commute_bulkObservable B hℓ hk X
  have heq : PA * Y * PB = PA * (QA * QB) * Y * PB := by
    rw [← mul_assoc PA QA QB, mul_assoc (PA * QA) QB Y, hA, hcomm,
      ← mul_assoc PA Y QB, mul_assoc (PA * Y) QB PB, hB]
  have hn : ‖PA * (QA * QB) * Y * PB‖ ≤ ‖PA‖ * ‖QA * QB‖ * ‖Y‖ * ‖PB‖ := by
    exact norm_mul_le_of_le norm_mul₃_le le_rfl
  have hPA : ‖PA‖ ≤ 1 := (groundSpaceES A ((ℓ + k) + r)).starProjection_norm_le
  have hPB : ‖PB‖ ≤ 1 := (groundSpaceES B ((ℓ + k) + r)).starProjection_norm_le
  have hPair : ‖QA * QB‖ ≤
      ‖(groundSpaceES A ℓ).starProjection.comp (groundSpaceES B ℓ).starProjection‖ :=
    norm_prefixGroundProjection_comp_le A B hℓ (by omega)
  have hY : ‖Y‖ ≤ ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖ :=
    norm_toEuclideanCLM_bulkObservable_le hk X ℓ r
  change ‖PA * (Y * PB)‖ ≤ _
  rw [← mul_assoc, heq]
  refine hn.trans ?_
  calc
    _ ≤ 1 * ‖(groundSpaceES A ℓ).starProjection.comp (groundSpaceES B ℓ).starProjection‖ *
        ‖Matrix.toEuclideanCLM (n := Cfg d k) (𝕜 := ℂ) X‖ * 1 := by gcongr
    _ = _ := by simp only [one_mul, mul_one]

/-- The products of the ground projections of inequivalent normalized primitive
tensors tend to zero in operator norm. Source: Nachtergaele,
arXiv:cond-mat/9410110, proof of Lemma disjoint, equations C1C2 and limP12. -/
theorem IsPrimitiveMPS.groundSpaceES_starProjection_comp_tendsto_zero_of_inequivalent
    [NeZero D₁] [NeZero D₂] {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} {σ : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsPrimitiveMPS A ρ) (hB : IsPrimitiveMPS B σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hDistinct : ∀ h : D₂ = D₁, ¬ GaugePhaseEquiv (h ▸ B) A) :
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
theorem IsPrimitiveMPS.bulkObservable_cross_groundSpace_compression_tendsto_zero_of_inequivalent
    [NeZero D₁] [NeZero D₂] {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ρ : Matrix (Fin D₁) (Fin D₁) ℂ} {σ : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsPrimitiveMPS A ρ) (hB : IsPrimitiveMPS B σ)
    (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (hDistinct : ∀ h : D₂ = D₁, ¬ GaugePhaseEquiv (h ▸ B) A)
    {k : ℕ} (hk : 0 < k) (X : Matrix (Cfg d k) (Cfg d k) ℂ)
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
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hUpper
  filter_upwards [hℓ.eventually (eventually_ge_atTop (1 : ℕ))] with n hn
  exact norm_groundSpaceES_bulkObservable_cross_compression_le A B (by omega) hk X

end MPSTensor
