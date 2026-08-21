/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FinSum
import TNLean.MPS.CanonicalForm.Definitions

/-!
# Active blocks of a CPSV canonical form

This module restricts a literal CPSV canonical-form decomposition to the displayed blocks with
nonzero weight. Zero-weight blocks do not contribute to any positive-length matrix product
vector.

Source: arXiv:1606.00608, lines 237--301 and 1135--1146; arXiv:2011.12127,
lines 1831--1885.
-/
open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- A finite enumeration of the nonzero-weight displayed blocks. -/
noncomputable def activeEquiv (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) ≃ data.Active :=
  (Fintype.equivFin data.Active).symm

/-- Bond dimensions of the enumerated active blocks. -/
noncomputable def activeDim (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) → ℕ :=
  fun k => data.dim (data.activeEquiv k)

/-- Weights of the enumerated active blocks. -/
noncomputable def activeWeight (data : CPSVCanonicalFormData A) :
    Fin (Fintype.card data.Active) → ℂ :=
  fun k => data.weights (data.activeEquiv k)

/-- Normal tensors of the enumerated active blocks. -/
noncomputable def activeBlocks (data : CPSVCanonicalFormData A) :
    (k : Fin (Fintype.card data.Active)) → MPSTensor d (data.activeDim k) :=
  fun k => data.blocks (data.activeEquiv k)

end CPSVCanonicalFormData

/-- Removing zero-weight blocks preserves every positive-length matrix product vector.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 237--246 and 271--301. -/
theorem sameMPV₂Pos_toTensorFromBlocks_active
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (blocks : (k : Fin r) → MPSTensor d (dim k))
    (e : Fin (Fintype.card {k : Fin r // μ k ≠ 0}) ≃ {k : Fin r // μ k ≠ 0}) :
    SameMPV₂Pos (toTensorFromBlocks (d := d) μ blocks)
      (toTensorFromBlocks (d := d) (fun k => μ (e k)) (fun k => blocks (e k))) := by
  classical
  intro N hN σ
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  simp only [smul_eq_mul]
  let f : Fin r → ℂ := fun k => μ k ^ N * mpv (blocks k) σ
  have hInactive : ∑ k : {k : Fin r // ¬ μ k ≠ 0}, f k = 0 := by
    apply Fintype.sum_eq_zero
    intro k
    simp [f, not_ne_iff.mp k.property, Nat.ne_of_gt hN]
  have hSplit :=
    Fintype.sum_subtype_add_sum_subtype (fun k : Fin r => μ k ≠ 0) f
  have hActiveSum : (∑ k : Fin r, f k) = ∑ k : {k : Fin r // μ k ≠ 0}, f k := by
    rw [hInactive, add_zero] at hSplit
    exact hSplit.symm
  change (∑ k : Fin r, f k) =
    ∑ k : Fin (Fintype.card {k : Fin r // μ k ≠ 0}), f (e k)
  rw [hActiveSum]
  exact (e.sum_comp (fun k : {k : Fin r // μ k ≠ 0} => f k)).symm

namespace CPSVCanonicalFormData

/-- Literal CPSV canonical-form data agree at every positive length with their active weighted
block sum.

This is the active part of the canonical-form and BNT decompositions in arXiv:1606.00608,
lines 237--301 and 1135--1146, and arXiv:2011.12127, lines 1831--1885. -/
theorem sameMPV₂Pos_activeBlocks (data : CPSVCanonicalFormData A) :
    SameMPV₂Pos A
      (toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks) :=
  data.sameMPV₂Pos_toTensorFromBlocks.trans <| by
    change SameMPV₂Pos (toTensorFromBlocks (d := d) data.weights data.blocks)
      (toTensorFromBlocks (d := d) (fun k => data.weights (data.activeEquiv k))
        (fun k => data.blocks (data.activeEquiv k)))
    exact sameMPV₂Pos_toTensorFromBlocks_active data.weights data.blocks data.activeEquiv

end CPSVCanonicalFormData

end MPSTensor

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- The flattened active-block coordinates included into the full retained direct sum.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 214--246 and 271--301. -/
noncomputable def activeCoordinateMap (data : CPSVCanonicalFormData A) :
    Fin (∑ k, data.activeDim k) → Fin (∑ k, data.dim k) := fun x =>
  let km := finSigmaFinEquiv.symm x
  finSigmaFinEquiv ⟨(data.activeEquiv km.1).1, km.2⟩

/-- The active-coordinate inclusion sends a flattened active block coordinate to the
same coordinate in its original displayed block. -/
@[simp] theorem activeCoordinateMap_finSigmaFinEquiv
    (data : CPSVCanonicalFormData A)
    (k : Fin (Fintype.card data.Active)) (m : Fin (data.activeDim k)) :
    data.activeCoordinateMap (finSigmaFinEquiv ⟨k, m⟩) =
      finSigmaFinEquiv ⟨(data.activeEquiv k).1, m⟩ := by
  dsimp [activeCoordinateMap]
  rw [finSigmaFinEquiv.symm_apply_apply]

/-- Distinct active direct-sum coordinates remain distinct in the full retained space. -/
theorem activeCoordinateMap_injective (data : CPSVCanonicalFormData A) :
    Function.Injective data.activeCoordinateMap := by
  intro x y hxy
  generalize hx : finSigmaFinEquiv.symm x = sx
  generalize hy : finSigmaFinEquiv.symm y = sy
  rcases sx with ⟨kx, mx⟩
  rcases sy with ⟨ky, my⟩
  have hsig :
      (⟨(data.activeEquiv kx).1, mx⟩ : Σ k, Fin (data.dim k)) =
        ⟨(data.activeEquiv ky).1, my⟩ := by
    apply finSigmaFinEquiv.injective
    change finSigmaFinEquiv
        ⟨(data.activeEquiv (finSigmaFinEquiv.symm x).1).1,
          (finSigmaFinEquiv.symm x).2⟩ =
      finSigmaFinEquiv
        ⟨(data.activeEquiv (finSigmaFinEquiv.symm y).1).1,
          (finSigmaFinEquiv.symm y).2⟩ at hxy
    rw [hx, hy] at hxy
    exact hxy
  have hkActive : data.activeEquiv kx = data.activeEquiv ky := by
    apply Subtype.ext
    exact congrArg Sigma.fst hsig
  have hk : kx = ky := data.activeEquiv.injective hkActive
  subst ky
  have hm : mx = my := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
  subst my
  rw [← finSigmaFinEquiv.apply_symm_apply x, hx,
    ← finSigmaFinEquiv.apply_symm_apply y, hy]

/-- The row-selection matrix from all retained coordinates to active coordinates.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 214--246. -/
noncomputable def activeCoordinateCoisometry (data : CPSVCanonicalFormData A) :
    Matrix (Fin (∑ k, data.activeDim k)) (Fin (∑ k, data.dim k)) ℂ :=
  fun x y => if data.activeCoordinateMap x = y then 1 else 0

/-- Entrywise formula for the active-coordinate row selector. -/
@[simp] theorem activeCoordinateCoisometry_apply (data : CPSVCanonicalFormData A)
    (x : Fin (∑ k, data.activeDim k)) (y : Fin (∑ k, data.dim k)) :
    data.activeCoordinateCoisometry x y =
      if data.activeCoordinateMap x = y then 1 else 0 := rfl

/-- Selecting all active rows gives a coisometry in the orientation $U U^\dagger=1$. -/
theorem activeCoordinateCoisometry_mul_conjTranspose
    (data : CPSVCanonicalFormData A) :
    data.activeCoordinateCoisometry * data.activeCoordinateCoisometryᴴ = 1 := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    activeCoordinateCoisometry_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · simp only [Matrix.one_apply, hxy, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hxz : data.activeCoordinateMap x = z
    · have hyz : ¬ data.activeCoordinateMap y = z := by
        intro hyz
        exact hxy (data.activeCoordinateMap_injective (hxz.trans hyz.symm))
      simp [hxz, hyz]
    · simp [hxz]

end CPSVCanonicalFormData
end MPSTensor

namespace Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

private noncomputable def rowSelection (f : α ↪ β) : Matrix α β ℂ :=
  fun x y => if f x = y then 1 else 0

omit [Fintype α] [DecidableEq α] [Fintype β] in
@[simp] private theorem rowSelection_apply (f : α ↪ β) (x : α) (y : β) :
    rowSelection f x y = if f x = y then 1 else 0 := rfl

omit [Fintype α] in
private theorem rowSelection_mul_conjTranspose (f : α ↪ β) :
    rowSelection f * (rowSelection f)ᴴ = 1 := by
  ext x y
  simp only [mul_apply, conjTranspose_apply, rowSelection_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · simp only [one_apply, hxy, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hxz : f x = z
    · have hyz : ¬ f y = z := by
        intro hyz
        exact hxy (f.injective (hxz.trans hyz.symm))
      simp [hxz, hyz]
    · simp [hxz]

omit [DecidableEq α] [Fintype β] in
private theorem eq_conjTranspose_rowSelection_mul_submatrix_mul_rowSelection
    (f : α ↪ β) (B : Matrix β β ℂ)
    (hrow : ∀ x, x ∉ Set.range f → ∀ y, B x y = 0)
    (hcol : ∀ y, y ∉ Set.range f → ∀ x, B x y = 0) :
    B = (rowSelection f)ᴴ * B.submatrix f f * rowSelection f := by
  classical
  ext x y
  by_cases hx : x ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hx
    by_cases hy : y ∈ Set.range f
    · obtain ⟨b, rfl⟩ := hy
      simp only [mul_apply, conjTranspose_apply, rowSelection_apply,
        submatrix_apply]
      simp [f.injective.eq_iff]
    · rw [hcol y hy]
      simp only [mul_apply, conjTranspose_apply, rowSelection_apply,
        submatrix_apply]
      have hnot : ∀ b : α, f b ≠ y := by
        intro b hby
        exact hy ⟨b, hby⟩
      simp [hnot]
  · rw [hrow x hx]
    simp only [mul_apply, conjTranspose_apply, rowSelection_apply,
      submatrix_apply]
    have hnot : ∀ a : α, f a ≠ x := by
      intro a hax
      exact hx ⟨a, hax⟩
    simp [hnot]


end Matrix

namespace MPSTensor.CPSVCanonicalFormData

variable {d D : ℕ} {A : MPSTensor d D}

private noncomputable def activeCoordinateEmbedding (data : CPSVCanonicalFormData A) :
    Fin (∑ k, data.activeDim k) ↪ Fin (∑ k, data.dim k) :=
  ⟨data.activeCoordinateMap, data.activeCoordinateMap_injective⟩

/-- The active weighted direct sum is the active-coordinate submatrix of the displayed
weighted direct sum.

The omitted displayed blocks have zero weight. Source: arXiv:1606.00608, eq. `II_CF1`,
lines 237--301. -/
theorem toTensorFromBlocks_active_eq_submatrix
    (data : CPSVCanonicalFormData A) (i : Fin d) :
    toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks i =
      (toTensorFromBlocks (d := d) data.weights data.blocks i).submatrix
        data.activeCoordinateMap data.activeCoordinateMap := by
  classical
  ext x y
  generalize hx : finSigmaFinEquiv.symm x = sx
  generalize hy : finSigmaFinEquiv.symm y = sy
  rcases sx with ⟨kx, mx⟩
  rcases sy with ⟨ky, my⟩
  have hx' : x = finSigmaFinEquiv ⟨kx, mx⟩ := by
    rw [← finSigmaFinEquiv.apply_symm_apply x, hx]
  have hy' : y = finSigmaFinEquiv ⟨ky, my⟩ := by
    rw [← finSigmaFinEquiv.apply_symm_apply y, hy]
  rw [hx', hy']
  simp only [toTensorFromBlocks, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [data.activeCoordinateMap_finSigmaFinEquiv,
    data.activeCoordinateMap_finSigmaFinEquiv,
    finSigmaFinEquiv.symm_apply_apply, finSigmaFinEquiv.symm_apply_apply]
  change Matrix.blockDiagonal' (fun k => data.activeWeight k • data.activeBlocks k i)
      ⟨kx, mx⟩ ⟨ky, my⟩ =
    Matrix.blockDiagonal' (fun k => data.weights k • data.blocks k i)
      ⟨(data.activeEquiv kx).1, mx⟩ ⟨(data.activeEquiv ky).1, my⟩
  by_cases h : kx = ky
  · subst ky
    calc
      Matrix.blockDiagonal' (fun k => data.activeWeight k • data.activeBlocks k i)
          ⟨kx, mx⟩ ⟨kx, my⟩ =
        (data.activeWeight kx • data.activeBlocks kx i) mx my :=
          Matrix.blockDiagonal'_apply_eq _ _ _ _
      _ = (data.weights (data.activeEquiv kx).1 • data.blocks (data.activeEquiv kx).1 i)
          mx my := rfl
      _ = Matrix.blockDiagonal' (fun k => data.weights k • data.blocks k i)
          ⟨(data.activeEquiv kx).1, mx⟩ ⟨(data.activeEquiv kx).1, my⟩ :=
        (Matrix.blockDiagonal'_apply_eq
          (fun k => data.weights k • data.blocks k i)
          (data.activeEquiv kx).1 mx my).symm
  · have hactive : (data.activeEquiv kx).1 ≠ (data.activeEquiv ky).1 :=
      fun he => h (data.activeEquiv.injective (Subtype.ext he))
    calc
      Matrix.blockDiagonal' (fun k => data.activeWeight k • data.activeBlocks k i)
          ⟨kx, mx⟩ ⟨ky, my⟩ = 0 := Matrix.blockDiagonal'_apply_ne _ _ _ h
      _ = Matrix.blockDiagonal' (fun k => data.weights k • data.blocks k i)
          ⟨(data.activeEquiv kx).1, mx⟩ ⟨(data.activeEquiv ky).1, my⟩ :=
        (Matrix.blockDiagonal'_apply_ne _ _ _ hactive).symm

private theorem weight_eq_zero_of_coordinate_not_active
    (data : CPSVCanonicalFormData A)
    (x : Fin (∑ k, data.dim k))
    (hx : x ∉ Set.range data.activeCoordinateMap) :
    data.weights (finSigmaFinEquiv.symm x).1 = 0 := by
  by_contra hk
  let k := (finSigmaFinEquiv.symm x).1
  let m := (finSigmaFinEquiv.symm x).2
  let ka : data.Active := ⟨k, hk⟩
  let l := data.activeEquiv.symm ka
  let z : Fin (∑ k, data.activeDim k) := finSigmaFinEquiv
    ⟨l, Fin.cast (by simp [activeDim, l, ka, k]) m⟩
  apply hx
  refine ⟨z, ?_⟩
  apply finSigmaFinEquiv.symm.injective
  dsimp only [z]
  rw [data.activeCoordinateMap_finSigmaFinEquiv,
    finSigmaFinEquiv.symm_apply_apply]
  apply Sigma.ext
  · exact congrArg Subtype.val (data.activeEquiv.apply_symm_apply ka)
  · rw [Fin.heq_ext_iff]
    constructor
    · change data.dim (data.activeEquiv l).1 = data.dim k
      exact congrArg data.dim <|
        congrArg Subtype.val (data.activeEquiv.apply_symm_apply ka)

private theorem toTensorFromBlocks_row_outside_active_eq_zero
    (data : CPSVCanonicalFormData A) (i : Fin d)
    (x : Fin (∑ k, data.dim k))
    (hx : x ∉ Set.range data.activeCoordinateMap)
    (y : Fin (∑ k, data.dim k)) :
    toTensorFromBlocks (d := d) data.weights data.blocks i x y = 0 := by
  classical
  simp only [toTensorFromBlocks, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize hcoordx : finSigmaFinEquiv.symm x = sx
  generalize hcoordy : finSigmaFinEquiv.symm y = sy
  rcases sx with ⟨kx, mx⟩
  rcases sy with ⟨ky, my⟩
  by_cases hxy : kx = ky
  · subst ky
    have hw := weight_eq_zero_of_coordinate_not_active data x hx
    rw [hcoordx] at hw
    rw [Matrix.blockDiagonal'_apply_eq]
    simp [hw]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hxy]

private theorem toTensorFromBlocks_col_outside_active_eq_zero
    (data : CPSVCanonicalFormData A) (i : Fin d)
    (y : Fin (∑ k, data.dim k))
    (hy : y ∉ Set.range data.activeCoordinateMap)
    (x : Fin (∑ k, data.dim k)) :
    toTensorFromBlocks (d := d) data.weights data.blocks i x y = 0 := by
  classical
  simp only [toTensorFromBlocks, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize hcoordx : finSigmaFinEquiv.symm x = sx
  generalize hcoordy : finSigmaFinEquiv.symm y = sy
  rcases sx with ⟨kx, mx⟩
  rcases sy with ⟨ky, my⟩
  by_cases hxy : kx = ky
  · subst ky
    have hw := weight_eq_zero_of_coordinate_not_active data y hy
    rw [hcoordy] at hw
    rw [Matrix.blockDiagonal'_apply_eq]
    simp [hw]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hxy]

/-- Exact reconstruction of a literal CPSV canonical form from only its nonzero-weight
blocks through a coisometry.

Zero-weight displayed blocks and unused ambient coordinates are omitted. The retained row
count is exactly the sum of active block dimensions.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 214--246 and 271--301;
arXiv:2011.12127, lines 1831--1885. -/
theorem exact_active_reconstruction (data : CPSVCanonicalFormData A) :
    ∃ U : Matrix (Fin (∑ k, data.activeDim k)) (Fin D) ℂ,
      U * Uᴴ = 1 ∧
      ∀ i, A i = Uᴴ *
        toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks i * U := by
  classical
  let S := data.activeCoordinateCoisometry
  let U := S * data.ambient_coisometry
  have hS : S * Sᴴ = 1 := data.activeCoordinateCoisometry_mul_conjTranspose
  refine ⟨U, ?_, ?_⟩
  · simp only [U, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc data.ambient_coisometry data.ambient_coisometryᴴ,
      data.coisometric, Matrix.one_mul, hS]
  · intro i
    rw [data.reconstruct i]
    have hExpand :
        toTensorFromBlocks (d := d) data.weights data.blocks i = Sᴴ *
          toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks i * S := by
      let f := data.activeCoordinateEmbedding
      have hgeneric := Matrix.eq_conjTranspose_rowSelection_mul_submatrix_mul_rowSelection
        f (toTensorFromBlocks (d := d) data.weights data.blocks i)
        (data.toTensorFromBlocks_row_outside_active_eq_zero i)
        (data.toTensorFromBlocks_col_outside_active_eq_zero i)
      change toTensorFromBlocks (d := d) data.weights data.blocks i =
        Sᴴ * (toTensorFromBlocks (d := d) data.weights data.blocks i).submatrix
          data.activeCoordinateMap data.activeCoordinateMap * S at hgeneric
      rw [← data.toTensorFromBlocks_active_eq_submatrix i] at hgeneric
      exact hgeneric
    rw [hExpand]
    simp only [U, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end MPSTensor.CPSVCanonicalFormData
