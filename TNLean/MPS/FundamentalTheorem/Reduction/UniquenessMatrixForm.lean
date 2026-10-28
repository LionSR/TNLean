/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessCommonBasis

/-!
# The matching and Theorem C in matrices

Let `(σ, g)` and `(σ̃, g̃)` be reductions of the same tensor `B` onto two families of normal blocks
of positive bond dimension, with flags `M_k` and `M̃_{k'}`. Write `G_{≤k}` for the matrix of the
columns of `g⁻¹` at the slots of the positions before `k`, so that its column span is `M_k`, and
likewise `G̃_{≤k'}`. Then (lecture note AsymmetricFT, Remark 5.3 and Corollary 6.4; milestone V,
V2.8 and V2.9):

* `rank (G_{≤k} G̃_{≤k'}) = dim (M_k + M̃_{k'})`;
* the position `π(k)` matched with `k` is the least `k'` at which the column block of the
  position `k` does not raise the rank of `(G_{≤k-1} G̃_{≤k'})`;
* `M_k ∩ M̃_{k'}` consists of the vectors `G_{≤k} a` with `G_{≤k} a = G̃_{≤k'} a'` for some `a'`;
* for the intertwiner `X` of Theorem C at the matched slots `b`, `b'` and any matrix `Y_U` whose
  columns lie in `U = M_k ∩ M̃_{π(k)}`, `W̃_{b'} Y_U = X W_b Y_U`, and
  `Ṽ_{b'} - V_b X⁻¹ = (G_{≤k-1} G̃_{≤π(k)-1}) R` for some matrix `R`.

## Main definitions

* `MPSTensor.MultiBlockCompression.leadingCols`: the matrix `G_{≤k}`.

## Main results

* `MPSTensor.MultiBlockCompression.range_leadingCols`: the column span of `G_{≤k}` is `M_k`.
* `MPSTensor.MultiBlockCompression.range_fromCols_leadingCols`,
  `MPSTensor.MultiBlockCompression.rank_fromCols_leadingCols`: V2.8(a).
* `MPSTensor.MultiBlockCompression.isLeast_rank_fromCols_leadingCols_eq`: V2.8(b).
* `MPSTensor.MultiBlockCompression.coe_map_inf_eq_leadingCols`: V2.8(c).
* `MPSTensor.MultiBlockCompression.leftRow_mul_eq_mul_leftRow_mul`,
  `MPSTensor.MultiBlockCompression.exists_rightCol_sub_mul_eq_fromCols_mul`: V2.9.
-/

open scoped Matrix

namespace Matrix

variable {m n₁ n₂ R : Type*} [CommSemiring R] [Fintype n₁] [Fintype n₂]

/-- The column span of a matrix with two column blocks is the sum of the column spans of the
blocks. -/
theorem range_mulVecLin_fromCols (A₁ : Matrix m n₁ R) (A₂ : Matrix m n₂ R) :
    LinearMap.range (fromCols A₁ A₂).mulVecLin =
      LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    rw [mulVecLin_apply, fromCols_mulVec]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · intro hv
    obtain ⟨_, ⟨a₁, rfl⟩, _, ⟨a₂, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    exact ⟨Sum.elim a₁ a₂, fromCols_mulVec_sumElim A₁ A₂ a₁ a₂⟩

end Matrix

namespace MPSTensor

open WordAlgebra

namespace MultiBlockCompression

variable {d DB : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {D : ι → ℕ} {D' : κ → ℕ}
  {B : MPSTensor d DB} {S : Finset ι} {S' : Finset κ} {C : ∀ s, MPSTensor d (D s)}
  {C' : ∀ t, MPSTensor d (D' t)}

/-! ### The leading columns of the inverse change of coordinates -/

section LeadingCols

variable (P : MultiBlockCompression B S C)

/-- **The matrix `G_{≤k}`** (lecture note AsymmetricFT, Section 5; milestone V, V2.8): the
columns of `g⁻¹` at the slots of the positions before `k`. Its column span is the member `M_k`
of the flag (`range_leadingCols`). -/
noncomputable def leadingCols (k : Fin (S.card + P.z + 1)) :
    Matrix (Fin DB) {y : BlockSpace D S P.z // (P.ord y.1).castSucc < k} ℂ :=
  (gaugeMatrixInv P.gauge).submatrix id Subtype.val

/-- `G_{≤k} a` is `g⁻¹` applied to `a` extended by zero to the other slots. -/
theorem leadingCols_mulVec (k : Fin (S.card + P.z + 1))
    (a : {y : BlockSpace D S P.z // (P.ord y.1).castSucc < k} → ℂ) :
    P.leadingCols k *ᵥ a = P.gauge.symm
      (fun y => if h : (P.ord y.1).castSucc < k then a ⟨y, h⟩ else 0) := by
  have h : P.leadingCols k *ᵥ a = gaugeMatrixInv P.gauge *ᵥ
      (fun y => if h : (P.ord y.1).castSucc < k then a ⟨y, h⟩ else 0) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, leadingCols, Matrix.submatrix_apply, id_eq]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun y : BlockSpace D S P.z =>
      (P.ord y.1).castSucc < k)]
    refine (add_zero _).symm.trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun y _ => ?_)
      (Finset.sum_eq_zero fun y _ => ?_).symm)
    · simp only [dite_eq_left y.2, Subtype.coe_eta]
    · simp only [dite_eq_right y.2, mul_zero]
  rw [h, gaugeMatrixInv, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]

/-- **The column span of `G_{≤k}` is `M_k`** (lecture note AsymmetricFT, Section 5; milestone V,
V2.8): the vectors of the bond space whose coordinates vanish on the slots at positions `≥ k`. -/
theorem range_leadingCols (k : Fin (S.card + P.z + 1)) :
    LinearMap.range (P.leadingCols k).mulVecLin =
      ((P.flag k).restrictScalars ℂ).map (WordModule.toVec B).toLinearMap := by
  ext v
  rw [Submodule.mem_map_equiv, Submodule.restrictScalars_mem, P.mem_flag_iff_toVec_mem_comap,
    LinearEquiv.apply_symm_apply, Submodule.mem_comap, LinearEquiv.coe_coe, P.mem_leadingSpace]
  constructor
  · rintro ⟨a, rfl⟩ y hy
    rw [Matrix.mulVecLin_apply, leadingCols_mulVec, LinearEquiv.apply_symm_apply]
    exact dite_eq_right (not_lt.2 hy)
  · intro hv
    refine ⟨fun y => P.gauge v y.1, ?_⟩
    rw [Matrix.mulVecLin_apply, leadingCols_mulVec, LinearEquiv.symm_apply_eq]
    funext y
    by_cases h : (P.ord y.1).castSucc < k
    · simp only [dite_eq_left h]
    · simp only [dite_eq_right h, hv y (not_lt.1 h)]

end LeadingCols

section TwoReductions

variable (P : MultiBlockCompression B S C) (Q : MultiBlockCompression B S' C')

/-- **V2.8(a), the column span** (lecture note AsymmetricFT, Remark 5.3; milestone V, V2.8(a)):
the column span of `(G_{≤k} G̃_{≤k'})` is `M_k + M̃_{k'}`. -/
theorem range_fromCols_leadingCols (k : Fin (S.card + P.z + 1)) (k' : Fin (S'.card + Q.z + 1)) :
    LinearMap.range (Matrix.fromCols (P.leadingCols k) (Q.leadingCols k')).mulVecLin =
      ((P.flag k ⊔ Q.flag k').restrictScalars ℂ).map (WordModule.toVec B).toLinearMap := by
  rw [Matrix.range_mulVecLin_fromCols, range_leadingCols, range_leadingCols,
    Submodule.restrictScalars_sup, Submodule.map_sup]

/-- **V2.8(a), the rank** (lecture note AsymmetricFT, Remark 5.3; milestone V, V2.8(a)):
`rank (G_{≤k} G̃_{≤k'}) = dim (M_k + M̃_{k'})`. -/
theorem rank_fromCols_leadingCols (k : Fin (S.card + P.z + 1)) (k' : Fin (S'.card + Q.z + 1)) :
    (Matrix.fromCols (P.leadingCols k) (Q.leadingCols k')).rank =
      Module.finrank ℂ ↥(P.flag k ⊔ Q.flag k') := by
  rw [Matrix.rank, range_fromCols_leadingCols, LinearEquiv.finrank_map_eq]
  rfl

/-- **V2.8(c)** (lecture note AsymmetricFT, Remark 5.3; milestone V, V2.8(c)): for all `k`,
`k'`, `M_k ∩ M̃_{k'}` consists of the vectors `G_{≤k} a` with `G_{≤k} a = G̃_{≤k'} a'` for some
`a'`; for the matched `k' = π(k)` this is `U`, and with `k - 1` in place of `k` it is `K`. -/
theorem coe_map_inf_eq_leadingCols (k : Fin (S.card + P.z + 1))
    (k' : Fin (S'.card + Q.z + 1)) :
    ((((P.flag k ⊓ Q.flag k').restrictScalars ℂ).map (WordModule.toVec B).toLinearMap :
        Submodule ℂ (Fin DB → ℂ)) : Set (Fin DB → ℂ)) =
      {v | ∃ a a', v = P.leadingCols k *ᵥ a ∧ P.leadingCols k *ᵥ a = Q.leadingCols k' *ᵥ a'} := by
  ext v
  have hP := SetLike.ext_iff.1 (P.range_leadingCols k) v
  have hQ := SetLike.ext_iff.1 (Q.range_leadingCols k') v
  rw [Submodule.mem_map_equiv] at hP hQ
  rw [SetLike.mem_coe, Submodule.mem_map_equiv]
  change _ ∈ P.flag k ⊓ Q.flag k' ↔ _
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := hP.2 (Submodule.mem_inf.1 hv).1
    obtain ⟨a', ha'⟩ := hQ.2 (Submodule.mem_inf.1 hv).2
    exact ⟨a, a', ha.symm, ha.trans ha'.symm⟩
  · rintro ⟨a, a', rfl, h⟩
    exact Submodule.mem_inf.2 ⟨hP.1 ⟨a, rfl⟩, hQ.1 ⟨a', h.symm⟩⟩

variable (hC : ∀ s ∈ S, Kraus.IsNormal (C s)) (hD : ∀ s ∈ S, 0 < D s)
  (hC' : ∀ t ∈ S', Kraus.IsNormal (C' t)) (hD' : ∀ t ∈ S', 0 < D' t)

include hC hD in
/-- Adding the column block of the position `k` to `(G_{≤k-1} G̃_{≤j})` keeps the rank exactly
when `M_k ∩ M̃_j ⊄ M_{k-1}` (lecture note AsymmetricFT, Remark 5.3; milestone V, V2.8(b)): equal
ranks mean `M_k ⊆ M_{k-1} + M̃_j`, which by the modular law and the covering `M_{k-1} ⋖ M_k` is
`M_k ∩ M̃_j ⊄ M_{k-1}`. -/
theorem rank_fromCols_leadingCols_eq_iff (k : Fin (S.card + P.z))
    (j : Fin (S'.card + Q.z + 1)) :
    (Matrix.fromCols (P.leadingCols k.castSucc) (Q.leadingCols j)).rank =
        (Matrix.fromCols (P.leadingCols k.succ) (Q.leadingCols j)).rank ↔
      ¬ P.flag k.succ ⊓ Q.flag j ≤ P.flag k.castSucc := by
  rw [rank_fromCols_leadingCols, rank_fromCols_leadingCols]
  have hle : P.flag k.castSucc ⊔ Q.flag j ≤ P.flag k.succ ⊔ Q.flag j :=
    sup_le_sup_right (P.flag_mono (Fin.castSucc_le_succ k)) _
  have hcov := P.flag_covBy hC hD k
  constructor
  · intro hrank hinf
    have heq : P.flag k.castSucc ⊔ Q.flag j = P.flag k.succ ⊔ Q.flag j :=
      Submodule.restrictScalars_injective ℂ _ _ (Submodule.eq_of_le_of_finrank_eq
        (Submodule.restrictScalars_mono ℂ hle) hrank)
    have h1 : P.flag k.succ ≤ P.flag k.castSucc ⊔ Q.flag j := heq ▸ le_sup_left
    have h2 : P.flag k.succ ≤ P.flag k.castSucc :=
      calc P.flag k.succ = (P.flag k.castSucc ⊔ Q.flag j) ⊓ P.flag k.succ :=
            (inf_eq_right.2 h1).symm
        _ = P.flag k.castSucc ⊔ Q.flag j ⊓ P.flag k.succ := sup_inf_assoc_of_le _ hcov.le
        _ ≤ P.flag k.castSucc := sup_le le_rfl (inf_comm (Q.flag j) (P.flag k.succ) ▸ hinf)
    exact hcov.lt.not_ge h2
  · intro hinf
    have h1 : P.flag k.castSucc < P.flag k.castSucc ⊔ P.flag k.succ ⊓ Q.flag j :=
      lt_of_le_not_ge le_sup_left fun h => hinf (le_sup_right.trans h)
    have h2 : P.flag k.succ ≤ P.flag k.castSucc ⊔ Q.flag j := by
      rcases hcov.eq_or_eq h1.le (sup_le hcov.le inf_le_left) with h | h
      · exact absurd h h1.ne'
      · exact h.symm.le.trans (sup_le_sup_left inf_le_right _)
    exact congrArg (fun N : Submodule (WordAlgebra d) B.WordModule => Module.finrank ℂ ↥N)
      (le_antisymm hle (sup_le h2 le_sup_right))

/-- **V2.8(b)** (lecture note AsymmetricFT, Remark 5.3; milestone V, V2.8(b)): the position
`π(k)` matched with `k` is the least `k'` at which adding the column block of the position `k`
to `(G_{≤k-1} G̃_{≤k'})` does not raise the rank (positions counted from `0`, so the matched
member of the second flag is `π(k) + 1`). -/
theorem isLeast_rank_fromCols_leadingCols_eq (k : Fin (S.card + P.z)) :
    IsLeast {j : Fin (S'.card + Q.z + 1) |
        (Matrix.fromCols (P.leadingCols k.castSucc) (Q.leadingCols j)).rank =
          (Matrix.fromCols (P.leadingCols k.succ) (Q.leadingCols j)).rank}
      (P.matching Q hC hD hC' hD' k).succ := by
  refine ⟨(P.rank_fromCols_leadingCols_eq_iff Q hC hD k _).2 ?_, fun j hj => ?_⟩
  · exact CoveringMatching.CoveringChain.not_inf_jump_succ_le (P.coveringChain hC hD)
      (Q.coveringChain hC' hD') k
  · have hinf := (P.rank_fromCols_leadingCols_eq_iff Q hC hD k j).1 hj
    by_contra hlt
    rw [not_le, ← Fin.le_castSucc_iff] at hlt
    exact hinf ((inf_le_inf_left _ (Q.flag_mono hlt)).trans
      (CoveringMatching.CoveringChain.inf_jump_castSucc_le (P.coveringChain hC hD)
        (Q.coveringChain hC' hD') k))

/-- **V2.9, the reading maps** (lecture note AsymmetricFT, Corollary 6.4; milestone V, V2.9): if
`X` relates the reading maps on `U = M_k ∩ M̃_{π(k)}`, as the intertwiner of Theorem C
(`exists_intertwiner_of_matching`) does, then `W̃_{b'} Y_U = X W_b Y_U` for every matrix `Y_U`
whose columns lie in `U`. -/
theorem leftRow_mul_eq_mul_leftRow_mul (k : Fin (S.card + P.z)) {b : BlockIndex S P.z}
    {b' : BlockIndex S' Q.z} {X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ}
    (hread : ∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
      Q.leftRow b' *ᵥ WordModule.toVec B x = X *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x))
    {n : ℕ} (YU : Matrix (Fin DB) (Fin n) ℂ)
    (hYU : ∀ j, (WordModule.toVec B).symm (fun i => YU i j) ∈
      P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ) :
    Q.leftRow b' * YU = X * P.leftRow b * YU := by
  ext i j
  have h := congrFun (hread _ (hYU j)) i
  rw [LinearEquiv.apply_symm_apply] at h
  rw [Matrix.mul_assoc]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- **V2.9, the injections** (lecture note AsymmetricFT, Corollary 6.4; milestone V, V2.9): for
the matched slots `b` at `k` and `b'` at `π(k)`, an `X` relating the reading maps on
`U = M_k ∩ M̃_{π(k)}` is the intertwiner of Theorem C, and for its inverse `Y = X⁻¹`,
`Ṽ_{b'} - V_b X⁻¹ = (G_{≤k-1} G̃_{≤π(k)-1}) R` for some matrix `R`: every column of the left side
lies in `M_{k-1} + M̃_{π(k)-1}`, the column span of `(G_{≤k-1} G̃_{≤π(k)-1})`. -/
theorem exists_rightCol_sub_mul_eq_fromCols_mul (k : Fin (S.card + P.z))
    {b : BlockIndex S P.z} (hb : P.ord b = k) {b' : BlockIndex S' Q.z}
    (hb' : Q.ord b' = P.matching Q hC hD hC' hD' k)
    {X : Matrix (Fin (slotSize D' b')) (Fin (slotSize D b)) ℂ}
    {Y : Matrix (Fin (slotSize D b)) (Fin (slotSize D' b')) ℂ} (hYX : Y * X = 1)
    (hread : ∀ x ∈ P.flag k.succ ⊓ Q.flag (P.matching Q hC hD hC' hD' k).succ,
      Q.leftRow b' *ᵥ WordModule.toVec B x = X *ᵥ (P.leftRow b *ᵥ WordModule.toVec B x)) :
    ∃ R, Q.rightCol b' - P.rightCol b * Y =
      Matrix.fromCols (P.leadingCols k.castSucc)
        (Q.leadingCols (P.matching Q hC hD hC' hD' k).castSucc) * R := by
  obtain ⟨X₀, Y₀, hXY₀, -, -, hX₀, hV⟩ :=
    P.exists_intertwiner_of_matching Q hC hD hC' hD' k hb hb'
  have hXX₀ : X = X₀ := by
    subst hb
    have hs := P.leftRow_surjOn_of_sup_eq (P.flag_sup_inf_eq Q hC hD hC' hD' (P.ord b))
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    obtain ⟨x, hx, rfl⟩ := hs (Set.mem_univ v)
    rw [← hread x hx, hX₀ x hx]
  have hYY₀ : Y = Y₀ := by
    rw [← Matrix.mul_one Y, ← hXY₀, ← Matrix.mul_assoc, ← hXX₀, hYX, Matrix.one_mul]
  subst hYY₀
  have hcol : ∀ c, ∃ r, Matrix.fromCols (P.leadingCols k.castSucc)
      (Q.leadingCols (P.matching Q hC hD hC' hD' k).castSucc) *ᵥ r =
        (Q.rightCol b' - P.rightCol b * Y) *ᵥ Pi.single c 1 := by
    intro c
    have hmem : (Q.rightCol b' - P.rightCol b * Y) *ᵥ Pi.single c 1 ∈
        LinearMap.range (Matrix.fromCols (P.leadingCols k.castSucc)
          (Q.leadingCols (P.matching Q hC hD hC' hD' k).castSucc)).mulVecLin := by
      rw [range_fromCols_leadingCols, Submodule.mem_map_equiv, Matrix.sub_mulVec,
        ← Matrix.mulVec_mulVec]
      exact hV _
    exact hmem
  choose r hr using hcol
  refine ⟨Matrix.of fun i c => r c i, ?_⟩
  ext i c
  have h1 := congrFun (hr c) i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at h1
  rw [← h1]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct]

end TwoReductions

end MultiBlockCompression

end MPSTensor
