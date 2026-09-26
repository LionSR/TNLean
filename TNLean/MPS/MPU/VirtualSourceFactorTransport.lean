/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryKronecker
import TNLean.MPS.MPU.SourceUV
import TNLean.MPS.MPU.VirtualSandwich

/-!
# Source factors under a unitary virtual gauge

A unitary change of virtual coordinates transports the two source-cut
factorizations with different Kronecker actions on their physical and virtual
legs. The contracted source gate $u$ is unchanged, while the source ranks
are identified by the rank invariance of the two cuts. These identities prepare
the normalized comparison with the source factors selected for the transformed
tensor. No relation between the recorded fixed points is used.

## References

* CPSV17, arXiv:1703.09188, Theorem `FundamentalMPU` (lines 624–648),
  for the source-gate diagrams; Proposition IV.5 (lines 786–812) for raw
  source-cut rank preservation under a virtual sandwich.
* FBC25, arXiv:2502.20257, Lemma `lem:deco` (lines 1052–1066).
-/

open scoped Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

private theorem transported_source_u_contraction
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (l : Fin ℓ[U]) (r : Fin r[U]) (p q : Fin d) :
    (∑ β : Fin D,
      (Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        star (z : Matrix (Fin D) (Fin D) ℂ))) l (p, β) *
      (Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ))) r (β, q)) =
      ∑ β : Fin D, Y₂ l (p, β) * Y₁ r (β, q) := by
  let A : Matrix (Fin ℓ[U]) (Fin D) ℂ := fun l β => Y₂ l (p, β)
  let B : Matrix (Fin D) (Fin r[U]) ℂ := fun β r => Y₁ r (β, q)
  have hmain : ((A * (z : Matrix (Fin D) (Fin D) ℂ)ᴴ) *
      ((z : Matrix (Fin D) (Fin D) ℂ) * B)) l r = (A * B) l r := by
    have hz : (z : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (z : Matrix (Fin D) (Fin D) ℂ) = 1 := z.2.1
    calc
      _ = (A * ((z : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          (z : Matrix (Fin D) (Fin D) ℂ)) * B) l r := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hz]; simp
  calc
    _ = ((A * (z : Matrix (Fin D) (Fin D) ℂ)ᴴ) *
        ((z : Matrix (Fin D) (Fin D) ℂ) * B)) l r := by
          simp only [Matrix.mul_apply, Matrix.kronecker_apply, Matrix.one_apply,
            Matrix.transpose_apply, Fintype.sum_prod_type]
          simp only [Matrix.conjTranspose_apply, A, B]
          simp only [star_apply, RCLike.star_def, ite_mul, one_mul, zero_mul,
            mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one]
          apply Finset.sum_congr rfl
          intro x _
          congr 1
          apply Finset.sum_congr rfl
          intro x₁ _
          ring
    _ = (A * B) l r := hmain
    _ = _ := by rw [Matrix.mul_apply]

/-- A unitary virtual conjugation transports both source-cut factorizations.
The second left factor remains an isometry, and the contraction defining the
source gate $u$ is unchanged before source-rank reindexing.

Source: CPSV17, arXiv:1703.09188, Proposition IV.5 (lines 786–812). -/
theorem source_factors_virtual_unitary_sandwich
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    (X₁ : Matrix (Fin d × Fin D) (Fin r[U]) ℂ)
    (Y₁ : Matrix (Fin r[U]) (Fin D × Fin d) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin ℓ[U]) ℂ)
    (Y₂ : Matrix (Fin ℓ[U]) (Fin d × Fin D) ℂ)
    (hfac₁ : X₁ * Y₁ = sourceCutM₁ U)
    (hfac₂ : X₂ * Y₂ = sourceCutM₂ U)
    (hX₂ : X₂.IsIsometry) :
    sourceCutM₁ (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))) =
        (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * X₁) *
          (Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
            (1 : Matrix (Fin d) (Fin d) ℂ))) ∧
    sourceCutM₂ (virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))) =
        (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ)) * X₂) *
          (Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
            star (z : Matrix (Fin D) (Fin D) ℂ))) ∧
    (((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℂ)) * X₂).IsIsometry ∧
    (fun ((l, r) : Fin ℓ[U] × Fin r[U]) ((p, q) : Fin d × Fin d) ↦
      ∑ β : Fin D,
        (Y₂ * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
          star (z : Matrix (Fin D) (Fin D) ℂ))) l (p, β) *
        (Y₁ * ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
          (1 : Matrix (Fin d) (Fin d) ℂ))) r (β, q)) =
      (fun ((l, r) : Fin ℓ[U] × Fin r[U]) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D, Y₂ l (p, β) * Y₁ r (β, q)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sourceCutM₁_virtualSandwich, ← hfac₁]
    simp only [Matrix.mul_assoc]
  · rw [sourceCutM₂_virtualSandwich, ← hfac₂]
    simp only [Matrix.mul_assoc]
  · have hz : (z : Matrix (Fin D) (Fin D) ℂ).IsIsometry := z.2.1
    have hI : (1 : Matrix (Fin d) (Fin d) ℂ).IsIsometry := by
      simp [Matrix.IsIsometry]
    have hK : ((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)).IsIsometry :=
      Matrix.IsIsometry.kronecker _ _ hz hI
    exact Matrix.IsIsometry.mul _ X₂ hK hX₂
  · funext ⟨l, r⟩ ⟨p, q⟩
    exact transported_source_u_contraction z Y₁ Y₂ l r p q

end MPOTensor
namespace MPOTensor

private theorem reindex_two_source_factorizations
    {d D a b : ℕ} (V : MPOTensor d D)
    (er : Fin a ≃ Fin r[V]) (el : Fin b ≃ Fin ℓ[V])
    (X₁ : Matrix (Fin d × Fin D) (Fin a) ℂ)
    (Y₁ : Matrix (Fin a) (Fin D × Fin d) ℂ)
    (Z₁ : Matrix (Fin D × Fin d) (Fin a) ℂ)
    (X₂ : Matrix (Fin D × Fin d) (Fin b) ℂ)
    (Y₂ : Matrix (Fin b) (Fin d × Fin D) ℂ)
    (Z₂ : Matrix (Fin d × Fin D) (Fin b) ℂ)
    (hfac₁ : X₁ * Y₁ = sourceCutM₁ V)
    (hfac₂ : X₂ * Y₂ = sourceCutM₂ V)
    (hYZ₁ : Y₁ * Z₁ = 1) (hYZ₂ : Y₂ * Z₂ = 1)
    (hX₂ : X₂.IsIsometry) :
    let X₁' := Matrix.reindex (Equiv.refl _) er X₁
    let Y₁' := Matrix.reindex er (Equiv.refl _) Y₁
    let Z₁' := Matrix.reindex (Equiv.refl _) er Z₁
    let X₂' := Matrix.reindex (Equiv.refl _) el X₂
    let Y₂' := Matrix.reindex el (Equiv.refl _) Y₂
    let Z₂' := Matrix.reindex (Equiv.refl _) el Z₂
    X₁' * Y₁' = sourceCutM₁ V ∧
    X₂' * Y₂' = sourceCutM₂ V ∧
    Y₁' * Z₁' = 1 ∧ Y₂' * Z₂' = 1 ∧ X₂'.IsIsometry := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) er X₁ *
      Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl _) Y₁ = sourceCutM₁ V
    rw [Matrix.reindexLinearEquiv_mul, hfac₁]
    simp
  · change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) el X₂ *
      Matrix.reindexLinearEquiv ℂ ℂ el (Equiv.refl _) Y₂ = sourceCutM₂ V
    rw [Matrix.reindexLinearEquiv_mul, hfac₂]
    simp
  · change Matrix.reindexLinearEquiv ℂ ℂ er (Equiv.refl _) Y₁ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) er Z₁ = 1
    rw [Matrix.reindexLinearEquiv_mul, hYZ₁, Matrix.reindexLinearEquiv_one]
  · change Matrix.reindexLinearEquiv ℂ ℂ el (Equiv.refl _) Y₂ *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) el Z₂ = 1
    rw [Matrix.reindexLinearEquiv_mul, hYZ₂, Matrix.reindexLinearEquiv_one]
  · exact Matrix.IsIsometry.reindex X₂ hX₂ (Equiv.refl _) el

private theorem reindex_source_u_is_unitary
    {d D a b c e : ℕ}
    (er : Fin a ≃ Fin c) (el : Fin b ≃ Fin e)
    (Y₁ : Matrix (Fin a) (Fin D × Fin d) ℂ)
    (Y₂ : Matrix (Fin b) (Fin d × Fin D) ℂ)
    (hu : Matrix.IsUnitaryBetween
      (fun ((l, r) : Fin b × Fin a) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D, Y₂ l (p, β) * Y₁ r (β, q))) :
    Matrix.IsUnitaryBetween
      (fun ((l, r) : Fin e × Fin c) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D,
          (Matrix.reindex el (Equiv.refl _) Y₂) l (p, β) *
          (Matrix.reindex er (Equiv.refl _) Y₁) r (β, q)) := by
  have h := hu.reindex _ (Equiv.prodCongr el er) (Equiv.refl _)
  have hEq :
      (fun ((l, r) : Fin e × Fin c) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D,
          (Matrix.reindex el (Equiv.refl _) Y₂) l (p, β) *
          (Matrix.reindex er (Equiv.refl _) Y₁) r (β, q)) =
      Matrix.reindex (Equiv.prodCongr el er) (Equiv.refl _)
        (fun ((l, r) : Fin b × Fin a) ((p, q) : Fin d × Fin d) ↦
          ∑ β : Fin D, Y₂ l (p, β) * Y₁ r (β, q)) := by
    ext ⟨l, r⟩ ⟨p, q⟩
    rfl
  rw [hEq]
  exact h

end MPOTensor

private theorem right_inverse_after_unitary_right_mul
    {a b : Type*} [Fintype b]
    [DecidableEq a] [DecidableEq b]
    (Y : Matrix a b ℂ) (Z : Matrix b a ℂ)
    (R : Matrix b b ℂ) (hYZ : Y * Z = 1)
    (hR : R * Rᴴ = 1) :
    (Y * R) * (Rᴴ * Z) = 1 := by
  calc
    _ = Y * (R * Rᴴ) * Z := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hR, Matrix.mul_one, hYZ]

namespace MPOTensor

private theorem source_right_gauge_one_coisometry {d D : ℕ}
    (z : Matrix.unitaryGroup (Fin D) ℂ) :
    (((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℂ)) *
      ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ))ᴴ) = 1 := by
  have hz : (z : Matrix (Fin D) (Fin D) ℂ).transpose *
      (z : Matrix (Fin D) (Fin D) ℂ).transposeᴴ = 1 :=
    (Matrix.transpose_mem_unitaryGroup_iff.mpr z.property).2
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, hz, Matrix.one_mul, Matrix.one_kronecker_one]

private theorem source_right_gauge_two_coisometry {d D : ℕ}
    (z : Matrix.unitaryGroup (Fin D) ℂ) :
    (((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      star (z : Matrix (Fin D) (Fin D) ℂ)) *
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        star (z : Matrix (Fin D) (Fin D) ℂ))ᴴ) = 1 := by
  have hz : (star (z : Matrix (Fin D) (Fin D) ℂ)) *
      (star (z : Matrix (Fin D) (Fin D) ℂ))ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using z.2.1
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, hz, Matrix.one_mul, Matrix.one_kronecker_one]

end MPOTensor


namespace MPOTensor

private theorem unitary_matrix_isUnit {D : ℕ}
    (z : Matrix.unitaryGroup (Fin D) ℂ) :
    IsUnit (z : Matrix (Fin D) (Fin D) ℂ) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact Matrix.isUnit_det_of_left_inverse z.2.1

private theorem unitary_adjoint_isUnit {D : ℕ}
    (z : Matrix.unitaryGroup (Fin D) ℂ) :
    IsUnit (star (z : Matrix (Fin D) (Fin D) ℂ)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact Matrix.isUnit_det_of_left_inverse z.2.2

/-- A unitary virtual conjugation preserves both source-cut ranks.

Source: CPSV17, arXiv:1703.09188, Proposition IV.5 (lines 786–812). -/
theorem source_rank_virtual_unitary_sandwich
    {d D : ℕ} (U : MPOTensor d D)
    (z : Matrix.unitaryGroup (Fin D) ℂ) :
    r[virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))] = r[U] ∧
    ℓ[virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))] = ℓ[U] := by
  exact ⟨rightRank_virtualSandwich _ U _ (unitary_matrix_isUnit z)
    (unitary_adjoint_isUnit z),
    leftRank_virtualSandwich _ U _ (unitary_matrix_isUnit z)
    (unitary_adjoint_isUnit z)⟩

end MPOTensor

namespace MPOTensor

/-- The transported factors, reindexed to the source ranks selected for the
conjugated tensor, give both cut factorizations and right inverses. Their
second left factor is an isometry, and their $u$ contraction is unitary
whenever the original contraction is unitary.

Source: CPSV17, arXiv:1703.09188, Proposition IV.5 (lines 786–812), and
FBC25, arXiv:2502.20257, Lemma `lem:deco` (lines 1052–1066). -/
theorem transported_source_factor_premises_at_selected_ranks
    {d D : ℕ} (U : MPOTensor d D)
    (z : Matrix.unitaryGroup (Fin D) ℂ)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (S : SourceFactors U ρ)
    (hu : (SourceFactors.sourceU U S).IsUnitaryBetween) :
    let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))
    let er : Fin r[U] ≃ Fin r[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
    let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
      (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
    let R₁ := ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℂ))
    let R₂ := ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      star (z : Matrix (Fin D) (Fin D) ℂ))
    let X₁ := Matrix.reindex (Equiv.refl _) er
      ((((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
        (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁))
    let Y₁ := Matrix.reindex er (Equiv.refl _) (S.Y₁ * R₁)
    let Z₁ := Matrix.reindex (Equiv.refl _) er (R₁ᴴ * S.Z₁)
    let X₂ := Matrix.reindex (Equiv.refl _) el
      ((((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂))
    let Y₂ := Matrix.reindex el (Equiv.refl _) (S.Y₂ * R₂)
    let Z₂ := Matrix.reindex (Equiv.refl _) el (R₂ᴴ * S.Z₂)
    sourceCutM₁ V = X₁ * Y₁ ∧ sourceCutM₂ V = X₂ * Y₂ ∧
    Y₁ * Z₁ = 1 ∧ Y₂ * Z₂ = 1 ∧ X₂.IsIsometry ∧
    Matrix.IsUnitaryBetween
      (fun ((l, r) : Fin ℓ[V] × Fin r[V]) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D, Y₂ l (p, β) * Y₁ r (β, q)) := by
  dsimp only
  let V := virtualSandwich (z : Matrix (Fin D) (Fin D) ℂ) U
      (star (z : Matrix (Fin D) (Fin D) ℂ))
  let er : Fin r[U] ≃ Fin r[V] :=
    (finCongr (source_rank_virtual_unitary_sandwich U z).1).symm
  let el : Fin ℓ[U] ≃ Fin ℓ[V] :=
    (finCongr (source_rank_virtual_unitary_sandwich U z).2).symm
  let R₁ := ((z : Matrix (Fin D) (Fin D) ℂ).transpose ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℂ))
  let R₂ := ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      star (z : Matrix (Fin D) (Fin D) ℂ))
  let X₁raw := ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ
      (star (z : Matrix (Fin D) (Fin D) ℂ)).transpose) * S.X₁
  let Y₁raw := S.Y₁ * R₁
  let Z₁raw := R₁ᴴ * S.Z₁
  let X₂raw := ((z : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ
      (1 : Matrix (Fin d) (Fin d) ℂ)) * S.X₂
  let Y₂raw := S.Y₂ * R₂
  let Z₂raw := R₂ᴴ * S.Z₂
  have htransport := source_factors_virtual_unitary_sandwich z
    S.X₁ S.Y₁ S.X₂ S.Y₂ S.sourceCutM₁_eq.symm
    S.sourceCutM₂_eq.symm S.X₂_isometry
  have hYZ₁ : Y₁raw * Z₁raw = 1 :=
    right_inverse_after_unitary_right_mul S.Y₁ S.Z₁ R₁
      S.Y₁_mul_Z₁ (source_right_gauge_one_coisometry z)
  have hYZ₂ : Y₂raw * Z₂raw = 1 :=
    right_inverse_after_unitary_right_mul S.Y₂ S.Z₂ R₂
      S.Y₂_mul_Z₂ (source_right_gauge_two_coisometry z)
  have hp := reindex_two_source_factorizations V er el
    X₁raw Y₁raw Z₁raw X₂raw Y₂raw Z₂raw
    htransport.1.symm htransport.2.1.symm hYZ₁ hYZ₂ htransport.2.2.1
  have huraw : Matrix.IsUnitaryBetween
      (fun ((l, r) : Fin ℓ[U] × Fin r[U]) ((p, q) : Fin d × Fin d) ↦
        ∑ β : Fin D, Y₂raw l (p, β) * Y₁raw r (β, q)) := by
    rw [htransport.2.2.2]
    exact hu
  have hu' := reindex_source_u_is_unitary er el Y₁raw Y₂raw huraw
  exact ⟨hp.1.symm, hp.2.1.symm, hp.2.2.1, hp.2.2.2.1,
    hp.2.2.2.2, hu'⟩

end MPOTensor
