/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.LeftCoordinates
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveTrimming
import TNLean.MPS.AreaLaw.ViableSet.CollectiveTrimming
import TNLean.MPS.AreaLaw.ViableSet.LeftColumns
import QICLean.Analysis.IsometricDomainExtension
import QICLean.Analysis.OverlapTriangle

/-!
# Bond trimming of a finite left family

Trim every member of a finite left family independently through its internal bonds. The
resulting finite family is chosen before any ground vector and has no more members than the
input family. Every output vector has the prescribed matrix product state bond bound.

The operation is the bond-trimming step of Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`algo53.tex`, Claim `c:trim`, lines 549–559.

**Local fix (trimming radius):** The source's retained dimension `48 L r` is replaced by
`(48 L)² r`, using the corrected single-cut estimate. The correction is recorded at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
-/

open Matrix
open scoped InnerProductSpace Kronecker

namespace TNLean.MPS.AreaLaw

variable {L q i : ℕ}

/-- The quadratic-radius correction of the bond budget in LVV13, `algo53.tex`,
Claim `c:trim`, lines 549–559; see the module docstring. -/
def bondTrimmingRadius (L D : ℕ) : ℕ := (48 * L) ^ 2 * D

/-- The corrected radius makes the accumulated loss at most `1 / 48`.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559, with the module's correction. -/
theorem mul_sqrt_bondTrimmingRadius_le (L D : ℕ) :
    (L : ℝ) * √((D : ℝ) / (bondTrimmingRadius L D + 1)) ≤ 1 / 48 := by
  apply (sq_le_sq₀ (by positivity) (by norm_num)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  simp only [bondTrimmingRadius, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

/-- Successive Schmidt trimming of a vector on the first `i ≤ L` sites.
Source: LVV13, `algo53.tex`, the bond-trimming step, lines 549–559. -/
noncomputable def leftSchmidtTrim (hi : i ≤ L) (m : ℕ) (u : LeftBlockVector L q i) :
    LeftBlockVector L q i :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv hi))
    (successiveSchmidtTrim m (WithLp.toLp 2 fun x ↦ u (leftConfigOfFin x)) (i - 1))

/-- The numbered coefficients of the trimmed left vector.
Source: LVV13, `algo53.tex`, the bond-trimming step, lines 549–559. -/
theorem leftSchmidtTrim_leftConfigOfFin (hi : i ≤ L) (m : ℕ) (u : LeftBlockVector L q i)
    (x : Fin i → Fin q) :
    leftSchmidtTrim hi m u (leftConfigOfFin x) =
      successiveSchmidtTrim m (WithLp.toLp 2 fun x ↦ u (leftConfigOfFin x)) (i - 1) x :=
  rfl

/-- Every trimmed left vector has the prescribed matrix product state bond bound.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem isLeftOpenMPS_leftSchmidtTrim (hi : i ≤ L) (m : ℕ) (u : LeftBlockVector L q i) :
    IsLeftOpenMPS m (leftSchmidtTrim hi m u) := by
  change IsOpenMPS i q (max 1 m)
    (fun x ↦ successiveSchmidtTrim m (WithLp.toLp 2 fun x ↦ u (leftConfigOfFin x)) (i - 1) x)
  unfold IsOpenMPS
  rw [max_eq_right (le_max_left 1 m)]
  obtain ⟨A, c, hA, hcoeff⟩ :=
    isOpenMPS_successiveSchmidtTrim m (WithLp.toLp 2 fun x ↦ u (leftConfigOfFin x))
  exact ⟨A, c, fun k hk0 hki ↦ (hA k hk0 hki).trans (le_max_right 1 m), hcoeff⟩

/-- Left-vector trimming does not increase the norm.
Source: LVV13, `algo53.tex`, Lemma `l:trim1`, lines 531–542. -/
theorem norm_leftSchmidtTrim_le (hi : i ≤ L) (m : ℕ) (u : LeftBlockVector L q i) :
    ‖leftSchmidtTrim hi m u‖ ≤ ‖u‖ := by
  rw [leftSchmidtTrim, (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (leftConfigOfFinEquiv hi)).norm_map]
  exact (norm_successiveSchmidtTrim_le m _ (i - 1)).trans_eq
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv hi).symm).norm_map u)

/-- The finite family obtained by independently trimming every input vector.
Source: LVV13, `algo53.tex`, Algorithm steps 2 and 3 and Claim `c:trim`, lines 549–559. -/
noncomputable def bondTrimSet (hi : i ≤ L) (m : ℕ) (S : Finset (LeftBlockVector L q i)) :
    Finset (LeftBlockVector L q i) :=
  open Classical in S.image (leftSchmidtTrim hi m)

/-- Independent bond trimming does not increase the cardinality of a family.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem card_bondTrimSet_le (hi : i ≤ L) (m : ℕ) (S : Finset (LeftBlockVector L q i)) :
    (bondTrimSet hi m S).card ≤ S.card := by
  classical
  exact Finset.card_image_le

/-- Every member of the trimmed family has the prescribed bond bound.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem isLeftOpenMPS_of_mem_bondTrimSet (hi : i ≤ L) (m : ℕ)
    (S : Finset (LeftBlockVector L q i)) {u : LeftBlockVector L q i}
    (hu : u ∈ bondTrimSet hi m S) : IsLeftOpenMPS m u := by
  classical
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
  exact isLeftOpenMPS_leftSchmidtTrim hi m v

variable {β : Type*} [Fintype β]

/-- Independent trimming of the left columns with an orthonormal environment coordinate.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
noncomputable def leftColumnwiseSchmidtTrim (hi : i ≤ L) (m : ℕ)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β)) :
    EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β) :=
  WithLp.toLp 2 fun p ↦ leftSchmidtTrim hi m (WithLp.toLp 2 fun x ↦ u (x, p.2)) p.1

private theorem leftColumnwiseSchmidtTrim_numbering (hi : i ≤ L) (m : ℕ)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β)) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((leftConfigOfFinEquiv hi).prodCongr (Equiv.refl β)).symm)
      (leftColumnwiseSchmidtTrim hi m u) =
    columnwiseSchmidtTrim m ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((leftConfigOfFinEquiv hi).prodCongr (Equiv.refl β)).symm) u) :=
  rfl

/-- Independent trimming of the left columns contracts the joint norm.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem norm_leftColumnwiseSchmidtTrim_le (hi : i ≤ L) (m : ℕ)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β)) :
    ‖leftColumnwiseSchmidtTrim hi m u‖ ≤ ‖u‖ := by
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((leftConfigOfFinEquiv (q := q) hi).prodCongr (Equiv.refl β)).symm
  have h := norm_columnwiseSchmidtTrim_le m (E u)
  rw [← leftColumnwiseSchmidtTrim_numbering hi m u, E.norm_map, E.norm_map] at h
  exact h

/-- The overlap loss for independently trimmed left columns.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559, with the corrected quadratic
trimming radius. The reference-column rank bounds are in the numbered left coordinates. -/
theorem norm_inner_sub_leftColumnwiseSchmidtTrim_le (hi : i ≤ L) (m : ℕ)
    (u v : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β)) (D : ℕ)
    (hv : ∀ a k, 0 < k → k < i →
      (cutMatrix (WithLp.toLp 2 fun x ↦ v (leftConfigOfFin x, a)) k).rank ≤ D) :
    ‖⟪u - leftColumnwiseSchmidtTrim hi m u, v⟫_ℂ‖ ≤
      (i - 1 : ℕ) * ‖u‖ * ‖v‖ * √((D : ℝ) / (m + 1)) := by
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((leftConfigOfFinEquiv (q := q) hi).prodCongr (Equiv.refl β)).symm
  have h := norm_inner_sub_columnwiseSchmidtTrim_le m (E u) (E v) D hv
  have htrim : E (leftColumnwiseSchmidtTrim hi m u) = columnwiseSchmidtTrim m (E u) :=
    leftColumnwiseSchmidtTrim_numbering hi m u
  rw [← htrim, ← map_sub, E.inner_map_map, E.norm_map, E.norm_map] at h
  exact h

omit [Fintype β] in
/-- The independently trimmed columns of a retained vector belong to the trimmed family.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem leftColumnwiseSchmidtTrim_column_mem (hi : i ≤ L) (m : ℕ)
    (S : Finset (LeftBlockVector L q i))
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β))
    (hu : ∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ S) (a : β) :
    WithLp.toLp 2 (fun x ↦ leftColumnwiseSchmidtTrim hi m u (x, a)) ∈
      bondTrimSet hi m S := by
  classical
  exact Finset.mem_image.mpr ⟨_, hu a, rfl⟩

/-- Contracting a reference vector against a right boundary vector cannot increase any
internal left cut rank. Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem rank_cutMatrix_rightApply_blockSplit_column_le (hi : i ≤ L) {j : ℕ}
    (hj : j + 1 ≤ i)
    (W : Matrix (((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q)) β ℂ)
    (v : EuclideanSpace ℂ (Fin L → Fin q)) (a : β) :
    (cutMatrix (WithLp.toLp 2 fun x ↦
      rightApply Wᴴ (blockSplit L q i v) (leftConfigOfFin x, a)) (j + 1)).rank ≤
      (cutMatrix v (j + 1)).rank := by
  rw [rank_cutMatrix_leftConfigOfFin hi
    (WithLp.toLp 2 fun x ↦ rightApply Wᴴ (blockSplit L q i v) (x, a)) (j + 1)]
  exact (Entropy.schmidtRank_cutVector_slice_le (blockCut L i j)
    (rightApply Wᴴ (blockSplit L q i v)) a).trans
      ((Entropy.schmidtRank_cutEnvVector_rightApply_le (blockCut L i j) Wᴴ
        (blockSplit L q i v)).trans (rank_cutEnvVector_blockSplit hj v).le)

private theorem norm_rightApply_of_isometry {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq β]
    (W : Matrix γ β ℂ) (hW : Wᴴ * W = 1) (u : EuclideanSpace ℂ (α × β)) :
    ‖rightApply W u‖ = ‖u‖ := by
  classical
  let J := (1 : Matrix α α ℂ) ⊗ₖ W
  have hJ : Jᴴ * J = 1 := by
    simp only [J, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hW, Matrix.one_kronecker_one]
  have h : rightApply W u = WithLp.toLp 2 (J *ᵥ WithLp.ofLp u) := by
    ext ⟨x, a⟩
    exact (congrFun (congrFun
      (schmidtCoeffMatrix_one_kronecker_mulVec W (WithLp.ofLp u)) x) a).symm
  rw [h]
  exact norm_toLp_mulVec_of_isometry J hJ u

private theorem norm_rightApply_conjTranspose_le_of_isometry {α γ : Type*}
    [Fintype α] [Fintype γ] [DecidableEq β] (W : Matrix γ β ℂ) (hW : Wᴴ * W = 1)
    (v : EuclideanSpace ℂ (α × γ)) : ‖rightApply Wᴴ v‖ ≤ ‖v‖ := by
  have heq := Matrix.inner_rightApply_left W (rightApply Wᴴ v) v
  have hsq : ‖rightApply Wᴴ v‖ ^ 2 =
      (⟪rightApply W (rightApply Wᴴ v), v⟫_ℂ).re := by
    rw [heq]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (rightApply W (rightApply Wᴴ v)) v
  rw [norm_rightApply_of_isometry W hW] at hcs
  have hre := Complex.re_le_norm ⟪rightApply W (rightApply Wᴴ v), v⟫_ℂ
  rcases (norm_nonneg (rightApply Wᴴ v)).eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact norm_nonneg v
  · nlinarith

/-- The right extension of independently trimmed columns is supported on the trimmed family.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem leftColumnwiseSchmidtTrim_mem_leftSupportSubmodule (hi : i ≤ L) (m : ℕ)
    (S : Finset (LeftBlockVector L q i))
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β))
    (W : Matrix (((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q)) β ℂ)
    (hu : ∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ S) :
    (blockSplit L q i).symm (rightApply W (leftColumnwiseSchmidtTrim hi m u)) ∈
      leftSupportSubmodule (bondTrimSet hi m S : Set (LeftBlockVector L q i)) := by
  rw [blockSplit_symm_eq]
  exact rightApply_mem_leftSupportSubmodule_of_columns _ _ W
    (fun a ↦ Submodule.subset_span (leftColumnwiseSchmidtTrim_column_mem hi m S u hu a))

/-- Independent column trimming loses at most the corrected accumulated overlap against a
physical reference vector of bounded cut rank. The reference columns are obtained by
contracting its environment against the given right isometry.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem norm_inner_sub_leftColumnwiseSchmidtTrim_rightApply_le [DecidableEq β]
    (hi : i ≤ L) (m : ℕ)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β))
    (W : Matrix (((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q)) β ℂ)
    (hW : Wᴴ * W = 1) (v : EuclideanSpace ℂ (Fin L → Fin q)) (D : ℕ)
    (hv : ∀ k, 0 < k → k < i → (cutMatrix v k).rank ≤ D) :
    ‖⟪(blockSplit L q i).symm (rightApply W u) -
        (blockSplit L q i).symm (rightApply W (leftColumnwiseSchmidtTrim hi m u)), v⟫_ℂ‖ ≤
      (i - 1 : ℕ) * ‖u‖ * ‖v‖ * √((D : ℝ) / (m + 1)) := by
  let P := blockSplit L q i
  let v' := rightApply Wᴴ (P v)
  have hcol : ∀ a k, 0 < k → k < i →
      (cutMatrix (WithLp.toLp 2 fun x ↦ v' (leftConfigOfFin x, a)) k).rank ≤ D := by
    intro a k hk0 hki
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    exact (rank_cutMatrix_rightApply_blockSplit_column_le hi (by omega) W v a).trans
      (hv (j + 1) (Nat.succ_pos j) hki)
  have herr := norm_inner_sub_leftColumnwiseSchmidtTrim_le hi m u v' D hcol
  have hinner : ⟪P.symm (rightApply W u) -
      P.symm (rightApply W (leftColumnwiseSchmidtTrim hi m u)), v⟫_ℂ =
      ⟪u - leftColumnwiseSchmidtTrim hi m u, v'⟫_ℂ := by
    rw [← P.inner_map_map, map_sub, P.apply_symm_apply, P.apply_symm_apply]
    have hsub : rightApply W u - rightApply W (leftColumnwiseSchmidtTrim hi m u) =
        rightApply W (u - leftColumnwiseSchmidtTrim hi m u) := by
      ext ⟨x, a⟩
      change (∑ b, u (x, b) * W a b) -
        (∑ b, leftColumnwiseSchmidtTrim hi m u (x, b) * W a b) =
          ∑ b, (u (x, b) - leftColumnwiseSchmidtTrim hi m u (x, b)) * W a b
      simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hsub, Matrix.inner_rightApply_left]
  rw [← hinner] at herr
  have hnv : ‖v'‖ ≤ ‖v‖ :=
    (norm_rightApply_conjTranspose_le_of_isometry W hW (P v)).trans_eq (P.norm_map v)
  exact herr.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnv (by positivity)) (Real.sqrt_nonneg _))

/-- Independent bond trimming preserves `1 / 2`-viability when the input contains the columns
of the size-trimming witness. The reference is a unit matrix product state of overlap at
least `47 / 48` with the ground vector, as supplied by LVV13, Lemma `l:mpsapprox`.
Source: `algo53.tex`, Claim `c:trim`, lines 549–559, with the quadratic radius correction. -/
theorem isViableMPS_bondTrimSet_of_columns [DecidableEq β] (hi : i ≤ L)
    (S : Finset (LeftBlockVector L q i))
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L i) × β))
    (W : Matrix (((v : {v : Fin L // v ∉ leftBlock L i}) → Fin q)) β ℂ)
    (hW : Wᴴ * W = 1) (hu : ‖u‖ = 1)
    (hcols : ∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ S)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (hΓ : ‖Γ‖ = 1)
    (hΓu : 1 - 1 / 12 ≤ ‖⟪Γ, (blockSplit L q i).symm (rightApply W u)⟫_ℂ‖)
    (v : EuclideanSpace ℂ (Fin L → Fin q)) (hv : ‖v‖ = 1)
    (hΓv : 1 - 1 / 48 ≤ ‖⟪Γ, v⟫_ℂ‖) (D : ℕ)
    (hvrank : ∀ k, 0 < k → k < i → (cutMatrix v k).rank ≤ D) :
    IsViableMPS Γ S.card (bondTrimmingRadius L D) (1 / 2)
      (bondTrimSet hi (bondTrimmingRadius L D) S) := by
  let m := bondTrimmingRadius L D
  let P := blockSplit L q i
  let φ := P.symm (rightApply W u)
  let w := P.symm (rightApply W (leftColumnwiseSchmidtTrim hi m u))
  have hφ : ‖φ‖ = 1 := by
    rw [P.symm.norm_map, norm_rightApply_of_isometry W hW, hu]
  have hw : ‖w‖ ≤ 1 := by
    rw [P.symm.norm_map, norm_rightApply_of_isometry W hW]
    exact (norm_leftColumnwiseSchmidtTrim_le hi m u).trans_eq hu
  have hφv : 1 - 2 * (1 / 12 + 1 / 48) ≤ ‖⟪φ, v⟫_ℂ‖ :=
    one_sub_two_mul_add_le_norm_inner hφ hv hΓ
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rwa [norm_inner_symm]) (by rwa [norm_inner_symm])
  have herr := norm_inner_sub_leftColumnwiseSchmidtTrim_rightApply_le hi m u W hW v D hvrank
  rw [hu, hv, mul_one, mul_one] at herr
  have hbudget : (i - 1 : ℕ) * √((D : ℝ) / (m + 1)) ≤ 1 / 48 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (show i - 1 ≤ L by omega))
      (Real.sqrt_nonneg _)).trans (mul_sqrt_bondTrimmingRadius_le L D)
  have herr' : ‖⟪φ - w, v⟫_ℂ‖ ≤ 1 / 48 := herr.trans hbudget
  have htri := norm_sub_norm_le ⟪φ, v⟫_ℂ ⟪w, v⟫_ℂ
  rw [← inner_sub_left] at htri
  have hwv : 1 - 11 / 48 ≤ ‖⟪w, v⟫_ℂ‖ := by linarith
  have hw0 : 0 < ‖w‖ := by
    have hcs := norm_inner_le_norm (𝕜 := ℂ) w v
    rw [hv, mul_one] at hcs
    linarith
  let z := ((‖w‖⁻¹ : ℝ) : ℂ) • w
  have hz : ‖z‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hw0,
      inv_mul_cancel₀ hw0.ne']
  have hzv : 1 - 11 / 48 ≤ ‖⟪z, v⟫_ℂ‖ := by
    rw [norm_inner_symm, inner_smul_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_pos hw0, inv_mul_eq_div,
      norm_inner_symm v w, le_div_iff₀ hw0]
    nlinarith
  have hΓz : 1 - 2 * (1 / 48 + 11 / 48) ≤ ‖⟪Γ, z⟫_ℂ‖ :=
    one_sub_two_mul_add_le_norm_inner hΓ hz hv
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hΓv hzv
  refine ⟨card_bondTrimSet_le hi m S,
    fun t ht ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m S ht, z, hz, ?_, ?_⟩
  · rw [norm_inner_symm]
    linarith
  · exact (leftSupportSubmodule _).smul_mem _
      (leftColumnwiseSchmidtTrim_mem_leftSupportSubmodule hi m S u W hcols)

end TNLean.MPS.AreaLaw
