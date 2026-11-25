/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Isometry.UnitaryKronecker
import TNLean.MPS.MPU.StandardForm.TwoSiteStandardForm

/-!
# The standard form of the doubled block

If a tensor `W` on pairs of sites is in standard form with gates `u, v`, then its
two-site block is in standard form with the gates
`u⁽²⁾ = (1_ℓ ⊗ v ⊗ 1_r)(u ⊗ u)` and `v⁽²⁾ = 1_d ⊗ v ⊗ 1_d`, of left rank `ℓ d`
and right rank `d r`. In the indices of arXiv:1703.09188, lines 1456--1458 and
1556--1558, these are `u⁽²⁾_{11',22'} = v_{1'2} u_{11'} u_{22'}` and
`v⁽²⁾_{11',22'} = v_{1'2}`.

## Main definitions

* `MPOTensor.doubledU`, `MPOTensor.doubledV`: the doubled gates.
* `MPOTensor.TwoSiteStandardFormData.doubled`: the standard form of `blockTwo W` with
  these gates.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D ℓ r : ℕ}

/-- The output coordinates `ℓ ⊗ (d ⊗ d) ⊗ r` of the doubled unshifted gate,
grouped as the left rank `ℓ d` and the right rank `d r`. -/
def doubledOutEquiv (ℓ d r : ℕ) :
    Fin ℓ × ((Fin d × Fin d) × Fin r) ≃ Fin (ℓ * d) × Fin (d * r) where
  toFun x := (finProdFinEquiv (x.1, x.2.1.1), finProdFinEquiv (x.2.1.2, x.2.2))
  invFun y := ((finProdFinEquiv.symm y.1).1,
    (((finProdFinEquiv.symm y.1).2, (finProdFinEquiv.symm y.2).1), (finProdFinEquiv.symm y.2).2))
  left_inv x := by simp
  right_inv y := Prod.ext (finProdFinEquiv.apply_symm_apply y.1)
    (finProdFinEquiv.apply_symm_apply y.2)

/-- The input coordinates of the doubled gates: a pair of pairs of sites. -/
def doubledInEquiv (d : ℕ) :
    (Fin d × Fin d) × (Fin d × Fin d) ≃ Fin (d * d) × Fin (d * d) :=
  Equiv.prodCongr finProdFinEquiv finProdFinEquiv

/-- Regrouping `(ℓ ⊗ r) ⊗ (ℓ ⊗ r)` as `ℓ ⊗ (r ⊗ ℓ) ⊗ r`, the middle factor
being the input of the shifted gate. -/
def doubledMidEquiv (ℓ r : ℕ) :
    (Fin ℓ × Fin r) × (Fin ℓ × Fin r) ≃ Fin ℓ × ((Fin r × Fin ℓ) × Fin r) where
  toFun x := (x.1.1, ((x.1.2, x.2.1), x.2.2))
  invFun y := ((y.1, y.2.1.1), (y.2.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The input coordinates `d ⊗ (r ⊗ ℓ) ⊗ d` of the doubled shifted gate, grouped
as the right rank `d r` and the left rank `ℓ d`. -/
def doubledShiftInEquiv (ℓ d r : ℕ) :
    Fin d × ((Fin r × Fin ℓ) × Fin d) ≃ Fin (d * r) × Fin (ℓ * d) where
  toFun x := (finProdFinEquiv (x.1, x.2.1.1), finProdFinEquiv (x.2.1.2, x.2.2))
  invFun y := ((finProdFinEquiv.symm y.1).1,
    (((finProdFinEquiv.symm y.1).2, (finProdFinEquiv.symm y.2).1), (finProdFinEquiv.symm y.2).2))
  left_inv x := by simp
  right_inv y := Prod.ext (finProdFinEquiv.apply_symm_apply y.1)
    (finProdFinEquiv.apply_symm_apply y.2)

/-- The output coordinates `d ⊗ (d ⊗ d) ⊗ d` of the doubled shifted gate, a
pair of pairs of sites. -/
def doubledShiftOutEquiv (d : ℕ) :
    Fin d × ((Fin d × Fin d) × Fin d) ≃ Fin (d * d) × Fin (d * d) where
  toFun x := (finProdFinEquiv (x.1, x.2.1.1), finProdFinEquiv (x.2.1.2, x.2.2))
  invFun y := ((finProdFinEquiv.symm y.1).1,
    (((finProdFinEquiv.symm y.1).2, (finProdFinEquiv.symm y.2).1), (finProdFinEquiv.symm y.2).2))
  left_inv x := by simp
  right_inv y := Prod.ext (finProdFinEquiv.apply_symm_apply y.1)
    (finProdFinEquiv.apply_symm_apply y.2)

/-- The doubled unshifted gate `u⁽²⁾ = (1_ℓ ⊗ v ⊗ 1_r)(u ⊗ u)`.
Source: arXiv:1703.09188, lines 1456--1458 and 1556--1558. -/
noncomputable def doubledU (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    Matrix (Fin (ℓ * d) × Fin (d * r)) (Fin (d * d) × Fin (d * d)) ℂ :=
  Matrix.reindex (doubledOutEquiv ℓ d r) (doubledInEquiv d)
    (((1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))) *
      Matrix.reindex (doubledMidEquiv ℓ r) (Equiv.refl _) (u ⊗ₖ u))

/-- The doubled shifted gate `v⁽²⁾ = 1_d ⊗ v ⊗ 1_d`.
Source: arXiv:1703.09188, lines 1456--1458 and 1556--1558. -/
noncomputable def doubledV (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * r) × Fin (ℓ * d)) ℂ :=
  Matrix.reindex (doubledShiftOutEquiv d) (doubledShiftInEquiv ℓ d r)
    ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)))

theorem doubledU_apply (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (t : Fin ℓ) (a b : Fin d) (s : Fin r)
    (i₁ i₁' i₂ i₂' : Fin d) :
    doubledU u v (finProdFinEquiv (t, a), finProdFinEquiv (b, s))
        (finProdFinEquiv (i₁, i₁'), finProdFinEquiv (i₂, i₂')) =
      ∑ s₁ : Fin r, ∑ t₂ : Fin ℓ,
        v (a, b) (s₁, t₂) * (u (t, s₁) (i₁, i₁') * u (t₂, s) (i₂, i₂')) := by
  simp only [doubledU, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp [doubledOutEquiv, doubledInEquiv, doubledMidEquiv, Finset.sum_ite_eq]

theorem doubledV_apply (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (j₁ j₁' j₂ j₂' b : Fin d)
    (s : Fin r) (t : Fin ℓ) (a : Fin d) :
    doubledV v (finProdFinEquiv (j₁, j₁'), finProdFinEquiv (j₂, j₂'))
        (finProdFinEquiv (b, s), finProdFinEquiv (t, a)) =
      (if j₁ = b then 1 else 0) * (v (j₁', j₂) (s, t) * (if j₂' = a then 1 else 0)) := by
  simp [doubledV, doubledShiftOutEquiv, doubledShiftInEquiv, Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem isUnitaryBetween_doubledU {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (hu : u.IsUnitaryBetween)
    (hv : v.IsUnitaryBetween) : (doubledU u v).IsUnitaryBetween := by
  have h1 : ∀ n : ℕ, (1 : Matrix (Fin n) (Fin n) ℂ).IsUnitaryBetween := fun n ↦
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr (one_mem _)
  have hmid := Matrix.IsUnitaryBetween.kronecker _ _ (h1 ℓ)
    (Matrix.IsUnitaryBetween.kronecker _ _ hv (h1 r))
  have huu := (Matrix.IsUnitaryBetween.kronecker _ _ hu hu).reindex _ (doubledMidEquiv ℓ r)
    (Equiv.refl _)
  exact (hmid.mul _ _ huu).reindex _ _ _

theorem isUnitaryBetween_doubledV {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hv : v.IsUnitaryBetween) : (doubledV v).IsUnitaryBetween := by
  have h1 : ∀ n : ℕ, (1 : Matrix (Fin n) (Fin n) ℂ).IsUnitaryBetween := fun n ↦
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr (one_mem _)
  exact (Matrix.IsUnitaryBetween.kronecker _ _ (h1 d)
    (Matrix.IsUnitaryBetween.kronecker _ _ hv (h1 d))).reindex _ _ _

/-- Reordering five nested finite sums as `(a, b, c, p, q) ↦ (p, c, q, b, a)`. -/
private theorem sum_reorder_five {A B C P Q R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype Q] [AddCommMonoid R]
    (f : A → B → C → P → Q → R) :
    (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, f a b c p q) =
      ∑ p, ∑ c, ∑ q, ∑ b, ∑ a, f a b c p q := by
  let e : ((((A × B) × C) × P) × Q) ≃ ((((P × C) × Q) × B) × A) :=
    { toFun := fun x ↦ ((((x.1.2, x.1.1.2), x.2), x.1.1.1.2), x.1.1.1.1)
      invFun := fun y ↦ ((((y.2, y.1.2), y.1.1.1.2), y.1.1.1.1), y.1.1.2)
      left_inv := by rintro ⟨⟨⟨⟨a, b⟩, c⟩, p⟩, q⟩; rfl
      right_inv := by rintro ⟨⟨⟨⟨p, c⟩, q⟩, b⟩, a⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2)
    (fun y ↦ f y.2 y.1.2 y.1.1.1.2 y.1.1.1.1 y.1.1.2)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

/-! ### Determinants and reality of the doubled gates -/

/-- The identification of the doubled ranks with the doubled physical pair
induced by an identification `e` of `ℂ^ℓ ⊗ ℂ^r` with `ℂ^d ⊗ ℂ^d`. -/
def doubledIdent (e : Fin ℓ × Fin r ≃ Fin d × Fin d) :
    Fin (ℓ * d) × Fin (d * r) ≃ Fin (d * d) × Fin (d * d) :=
  (doubledOutEquiv ℓ d r).symm.trans
    (((Equiv.prodCongr (Equiv.refl _)
        (Equiv.prodCongr (e.symm.trans (Equiv.prodComm _ _)) (Equiv.refl _))).trans
      ((doubledMidEquiv ℓ r).symm.trans (Equiv.prodCongr e e))).trans (doubledInEquiv d))

/-- The identification of the doubled physical pair with the doubled ranks
induced by an identification `f` of `ℂ^d ⊗ ℂ^d` with `ℂ^r ⊗ ℂ^ℓ`. -/
def doubledShiftIdent (f : Fin d × Fin d ≃ Fin r × Fin ℓ) :
    Fin (d * d) × Fin (d * d) ≃ Fin (d * r) × Fin (ℓ * d) :=
  (doubledShiftOutEquiv d).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr f (Equiv.refl _))).trans
      (doubledShiftInEquiv ℓ d r))

/-- The determinant of the doubled unshifted gate:
`det u⁽²⁾ = det(v)^{rℓ} det(u)^{2ℓr}`, read through the induced identifications.
Source: arXiv:1703.09188, lines 1556--1560. -/
theorem det_doubledU_submatrix (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (e : Fin ℓ × Fin r ≃ Fin d × Fin d) :
    ((doubledU u v).submatrix id (doubledIdent e)).det =
      (v.submatrix id (e.symm.trans (Equiv.prodComm _ _))).det ^ (r * ℓ) *
        (u.submatrix id e).det ^ (2 * (ℓ * r)) := by
  set f := e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r))
  set H : Fin ℓ × ((Fin d × Fin d) × Fin r) ≃ Fin ℓ × ((Fin r × Fin ℓ) × Fin r) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr f (Equiv.refl _))
  set K := H.trans (doubledMidEquiv ℓ r).symm
  set M₁ := (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))
  set N := Matrix.reindex (doubledMidEquiv ℓ r) (Equiv.refl _) (u ⊗ₖ u)
  have h₀ : (doubledU u v).submatrix id (doubledIdent e) =
      ((M₁ * N).submatrix id (K.trans (Equiv.prodCongr e e))).submatrix
        (doubledOutEquiv ℓ d r).symm (doubledOutEquiv ℓ d r).symm := by
    ext x y
    simp [doubledU, doubledIdent, Matrix.reindex_apply, M₁, N, K, H, f]
  have h₁ : M₁.submatrix id H = (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ
      ((v.submatrix id f) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) := by
    ext ⟨t, ⟨a, s⟩⟩ ⟨t', ⟨b, s'⟩⟩
    simp [M₁, H, Matrix.kroneckerMap_apply]
  have h₂ : N.submatrix H (K.trans (Equiv.prodCongr e e)) =
      ((u.submatrix id e) ⊗ₖ (u.submatrix id e)).submatrix K K := by
    ext x y
    simp [N, K, Matrix.reindex_apply, Matrix.kroneckerMap_apply]
  rw [h₀, Matrix.det_submatrix_equiv_self, ← Matrix.submatrix_mul_equiv M₁ N id H,
    Matrix.det_mul, h₁, h₂, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker,
    Matrix.det_kronecker, Matrix.det_kronecker]
  simp only [Matrix.det_one, one_pow, mul_one, one_mul, Fintype.card_prod, Fintype.card_fin]
  rw [← pow_mul, ← pow_add]
  ring_nf

/-- The determinant of the doubled shifted gate: `det v⁽²⁾ = det(v)^{d²}`, read
through the induced identification. Source: arXiv:1703.09188, lines 1556--1561. -/
theorem det_doubledV_submatrix (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (f : Fin d × Fin d ≃ Fin r × Fin ℓ) :
    ((doubledV v).submatrix id (doubledShiftIdent f)).det =
      (v.submatrix id f).det ^ (d * d) := by
  have h₀ : (doubledV v).submatrix id (doubledShiftIdent f) =
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ ((v.submatrix id f) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ))).submatrix
        (doubledShiftOutEquiv d).symm (doubledShiftOutEquiv d).symm := by
    ext x y
    simp only [doubledV, doubledShiftIdent, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Equiv.trans_apply, Equiv.symm_apply_apply, id_eq]
    rfl
  rw [h₀, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, Matrix.det_kronecker]
  simp only [Matrix.det_one, one_pow, mul_one, one_mul, Fintype.card_prod, Fintype.card_fin]
  rw [← pow_mul]

/-- The doubled gates of real gates are real. Source: arXiv:1703.09188,
line 1562 ("`u⁽²⁾` and `v⁽²⁾` still satisfy (ortuv)"). -/
theorem doubledU_map_star (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    (doubledU u v).map (starRingEnd ℂ) =
      doubledU (u.map (starRingEnd ℂ)) (v.map (starRingEnd ℂ)) := by
  ext x y
  simp [doubledU, Matrix.reindex_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, map_sum, apply_ite]

theorem doubledV_map_star (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    (doubledV v).map (starRingEnd ℂ) = doubledV (v.map (starRingEnd ℂ)) := by
  ext x y
  simp only [doubledV, Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- Changing the identification of the coordinate spaces multiplies the
determinant by the sign of the change, which does not depend on the matrix. -/
theorem det_submatrix_eq_sign_mul {m n : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n ℂ) (g g' : m ≃ n) :
    (A.submatrix id g).det = (Equiv.Perm.sign (g.trans g'.symm) : ℂ) * (A.submatrix id g').det := by
  rw [← Matrix.det_permute']
  congr 1
  ext i j
  simp

namespace TwoSiteStandardFormData

variable {W : MPOTensor (d * d) D} {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
  {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}

/-- The half factor of the doubled block joining the second output pair to the
right virtual end: `X₁'((j, j'), γ)_{(b, s)} = δ_{j b} X₁(j', γ)_s`. -/
def doubledX₁ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin (d * d) × Fin D) (Fin (d * r)) ℂ :=
  fun p q ↦ (if (finProdFinEquiv.symm p.1).1 = (finProdFinEquiv.symm q).1 then 1 else 0) *
    S.X₁ ((finProdFinEquiv.symm p.1).2, p.2) (finProdFinEquiv.symm q).2

/-- The half factor of the doubled block joining the left virtual end to the
first output pair: `X₂'(α, (i, i'))_{(t, a)} = X₂(α, i)_t δ_{i' a}`. -/
def doubledX₂ (S : TwoSiteStandardFormData W u v) :
    Matrix (Fin D × Fin (d * d)) (Fin (ℓ * d)) ℂ :=
  fun p q ↦ S.X₂ (p.1, (finProdFinEquiv.symm p.2).1) (finProdFinEquiv.symm q).1 *
    (if (finProdFinEquiv.symm p.2).2 = (finProdFinEquiv.symm q).2 then 1 else 0)

theorem doubled_v_apply (S : TwoSiteStandardFormData W u v) (i₁ i₂ : Fin (d * d))
    (s : Fin (d * r)) (t : Fin (ℓ * d)) :
    doubledV v (i₁, i₂) (s, t) = ∑ β : Fin D, S.doubledX₁ (i₁, β) s * S.doubledX₂ (β, i₂) t := by
  obtain ⟨⟨j₁, j₁'⟩, rfl⟩ := finProdFinEquiv.surjective i₁
  obtain ⟨⟨j₂, j₂'⟩, rfl⟩ := finProdFinEquiv.surjective i₂
  obtain ⟨⟨b, s⟩, rfl⟩ := finProdFinEquiv.surjective s
  obtain ⟨⟨t, a⟩, rfl⟩ := finProdFinEquiv.surjective t
  rw [doubledV_apply, S.v_apply]
  simp only [doubledX₁, doubledX₂, Equiv.symm_apply_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  ring

theorem doubled_W_apply (S : TwoSiteStandardFormData W u v) (i j : Fin ((d * d) * (d * d)))
    (α γ : Fin D) :
    blockTwo W (i, j) α γ = ∑ t : Fin (ℓ * d), ∑ s : Fin (d * r),
      S.doubledX₂ (α, (finProdFinEquiv.symm i).1) t *
        doubledU u v (t, s) (finProdFinEquiv.symm j) *
          S.doubledX₁ ((finProdFinEquiv.symm i).2, γ) s := by
  obtain ⟨⟨I₁, I₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨J₁, J₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨i₁, i₁'⟩, rfl⟩ := finProdFinEquiv.surjective I₁
  obtain ⟨⟨i₂, i₂'⟩, rfl⟩ := finProdFinEquiv.surjective I₂
  obtain ⟨⟨j₁, j₁'⟩, rfl⟩ := finProdFinEquiv.surjective J₁
  obtain ⟨⟨j₂, j₂'⟩, rfl⟩ := finProdFinEquiv.surjective J₂
  simp only [Equiv.symm_apply_apply]
  rw [← finProdFinEquiv.sum_comp]
  simp_rw [← finProdFinEquiv.sum_comp (fun s ↦ _ * doubledU u v _ _ * S.doubledX₁ _ s)]
  simp only [Fintype.sum_prod_type, doubledU_apply, doubledX₁, doubledX₂, Equiv.symm_apply_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [blockTwo_apply, Matrix.mul_apply, Equiv.symm_apply_apply, S.W_apply, S.v_apply]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, one_mul]
  rw [sum_reorder_five]
  refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun s₀ _ ↦ Finset.sum_congr rfl
    fun s₁ _ ↦ Finset.sum_congr rfl fun t₂ _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  ring

/-- **The standard form of the doubled block.** If `W` is in standard form with
gates `u, v`, then its two-site block is in standard form with the gates
`u⁽²⁾ = (1_ℓ ⊗ v ⊗ 1_r)(u ⊗ u)` and `v⁽²⁾ = 1_d ⊗ v ⊗ 1_d`.

Source: arXiv:1703.09188, proof of Corollary `cor:all-equivalent-under-conjugation`,
lines 1456--1458 ("if we block once we will have that the new `u⁽²⁾, v⁽²⁾` can be
written as `u⁽²⁾_{11',22'} = v_{1'2} u_{11'} u_{22'}` and `v⁽²⁾_{11',22'} = v_{1'2}`"),
and of Corollary `cor:equiv-under-conjugation`, lines 1556--1558. -/
noncomputable def doubled (S : TwoSiteStandardFormData W u v) :
    TwoSiteStandardFormData (blockTwo W) (doubledU u v) (doubledV v) where
  phys_pos := Nat.mul_pos S.phys_pos S.phys_pos
  bond_pos := S.bond_pos
  left_pos := Nat.mul_pos S.left_pos S.phys_pos
  right_pos := Nat.mul_pos S.phys_pos S.right_pos
  X₁ := S.doubledX₁
  X₂ := S.doubledX₂
  u_unitary := isUnitaryBetween_doubledU S.u_unitary S.v_unitary
  v_unitary := isUnitaryBetween_doubledV S.v_unitary
  v_apply := S.doubled_v_apply
  W_apply := S.doubled_W_apply

end TwoSiteStandardFormData

end MPOTensor
