/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Trimming
import TNLean.MPS.AreaLaw.OpenMPSCutRank

/-!
# Successive Schmidt trimming of a chain vector

Starting from a vector, trim its first bond, then the second, and so forth. At each step the
projection is computed from the vector remaining after the preceding steps. Each projection
keeps at most `m` leading Schmidt vectors. Thus the final vector has a matrix product state
representation of bond dimension at most `m`.

**Local fix (trimming radius):** The overlap lost against a vector of cut rank at most `D`
is bounded per step by `‖ψ‖ ‖v‖ √(D / (m + 1))`, so a prescribed error requires the quadratic
trimming radius. The companion-library note records the correction:
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, Lemmas `l:trim1` and
`l:trim2`, lines 531–553, and Claim `c:trim`, lines 549–559.
-/

open Matrix
open scoped InnerProductSpace

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- A projection onto at most `m` leading Schmidt vectors at a prescribed cut.
Source: LVV13, `algo53.tex`, the definition of trimming, lines 330–333. -/
noncomputable def chainTrimmingProjection (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (k m : ℕ) : LeftBlockMatrix L q k :=
  Classical.choose (exists_isTrimmingProjection
    (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ) m)

/-- The chosen projection is a Schmidt trimming projection.
Source: LVV13, `algo53.tex`, the definition of trimming, lines 330–333. -/
theorem isTrimmingProjection_chainTrimmingProjection
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (k m : ℕ) :
    IsTrimmingProjection (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ)
      m (chainTrimmingProjection ψ k m) :=
  Classical.choose_spec (exists_isTrimmingProjection
    (Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ) m)

/-- Trim the bonds after the first `j` sites successively from left to right.
Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
noncomputable def successiveSchmidtTrim (m : ℕ) (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    ℕ → EuclideanSpace ℂ (Fin L → Fin q)
  | 0 => ψ
  | j + 1 => chainTrim (successiveSchmidtTrim m ψ j) (j + 1)
      (chainTrimmingProjection (successiveSchmidtTrim m ψ j) (j + 1) m)

/-- Successive Schmidt trimming does not increase the norm.
Source: LVV13, `algo53.tex`, Lemma `l:trim1`, lines 531–542. -/
theorem norm_successiveSchmidtTrim_le (m : ℕ) (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (j : ℕ) : ‖successiveSchmidtTrim m ψ j‖ ≤ ‖ψ‖ := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    exact (norm_chainTrim_le (isTrimmingProjection_chainTrimmingProjection _ _ _)).trans ih

/-- Successive Schmidt trimming does not increase the rank at any cut.
Source: LVV13, `algo53.tex`, Lemma `l:trim2`, lines 544–553. -/
theorem rank_cutMatrix_successiveSchmidtTrim_le (m : ℕ)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (j k : ℕ) :
    (cutMatrix (successiveSchmidtTrim m ψ j) k).rank ≤ (cutMatrix ψ k).rank := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    exact (rank_cutMatrix_chainTrim_le
      (isTrimmingProjection_chainTrimmingProjection _ _ _) k).trans ih

/-- Once a bond has been trimmed, its rank stays at most the retained dimension.
Source: LVV13, `algo53.tex`, Lemma `l:trim2` and Claim `c:trim`, lines 544–559. -/
theorem rank_cutMatrix_successiveSchmidtTrim_le_of_le (m : ℕ)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) {j k : ℕ} (hk0 : 0 < k) (hkj : k ≤ j) :
    (cutMatrix (successiveSchmidtTrim m ψ j) k).rank ≤ m := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hk : k = j + 1
    · subst k
      exact rank_cutMatrix_chainTrim_self_le
        (isTrimmingProjection_chainTrimmingProjection _ _ _)
    · exact (rank_cutMatrix_chainTrim_le
        (isTrimmingProjection_chainTrimmingProjection _ _ _) k).trans (ih (by omega))

/-- Trimming all internal bonds gives an open matrix product state with the retained bond
dimension. Source: LVV13, `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem isOpenMPS_successiveSchmidtTrim (m : ℕ) (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    IsOpenMPS L q m (fun x ↦ successiveSchmidtTrim m ψ (L - 1) x) :=
  isOpenMPS_of_internal_cutMatrix_rank_le _ fun _ hk0 hkL ↦
    rank_cutMatrix_successiveSchmidtTrim_le_of_le m ψ hk0 (by omega)

/-- The losses of overlap against a vector of bounded rank add along the trimmed bonds.
Source: LVV13, `algo53.tex`, Lemma `l:trim1` and Claim `c:trim`, lines 531–559, with the
quadratic-radius correction stated in the module docstring. -/
theorem norm_inner_sub_successiveSchmidtTrim_le (m : ℕ)
    (ψ v : EuclideanSpace ℂ (Fin L → Fin q)) (j D : ℕ)
    (hv : ∀ k, 0 < k → k ≤ j → (cutMatrix v k).rank ≤ D) :
    ‖⟪ψ - successiveSchmidtTrim m ψ j, v⟫_ℂ‖ ≤
      j * ‖ψ‖ * ‖v‖ * √((D : ℝ) / (m + 1)) := by
  induction j with
  | zero => simp [successiveSchmidtTrim]
  | succ j ih =>
    have hstep := norm_inner_sub_chainTrim_le
      (isTrimmingProjection_chainTrimmingProjection
        (successiveSchmidtTrim m ψ j) (j + 1) m) v
      (hv (j + 1) (Nat.succ_pos j) le_rfl)
    have hstep' : ‖⟪successiveSchmidtTrim m ψ j -
        successiveSchmidtTrim m ψ (j + 1), v⟫_ℂ‖ ≤
        ‖ψ‖ * ‖v‖ * √((D : ℝ) / (m + 1)) :=
      hstep.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_successiveSchmidtTrim_le m ψ j) (norm_nonneg v))
        (Real.sqrt_nonneg _))
    have hsplit : ψ - successiveSchmidtTrim m ψ (j + 1) =
        (ψ - successiveSchmidtTrim m ψ j) +
          (successiveSchmidtTrim m ψ j - successiveSchmidtTrim m ψ (j + 1)) := by abel
    rw [hsplit, inner_add_left]
    calc
      _ ≤ ‖⟪ψ - successiveSchmidtTrim m ψ j, v⟫_ℂ‖ +
          ‖⟪successiveSchmidtTrim m ψ j - successiveSchmidtTrim m ψ (j + 1), v⟫_ℂ‖ :=
        norm_add_le _ _
      _ ≤ j * ‖ψ‖ * ‖v‖ * √((D : ℝ) / (m + 1)) +
          ‖ψ‖ * ‖v‖ * √((D : ℝ) / (m + 1)) :=
        add_le_add (ih (fun k hk0 hkj ↦ hv k hk0 (hkj.trans (Nat.le_succ j)))) hstep'
      _ = (j + 1 : ℕ) * ‖ψ‖ * ‖v‖ * √((D : ℝ) / (m + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring

variable {β : Type*} [Fintype β]

/-- Trim every left column independently, as in the bond-trimming step of LVV13,
`algo53.tex`, lines 549–559. The environment index does not enter the individual trimming
projections. -/
noncomputable def columnwiseSchmidtTrim (m : ℕ)
    (u : EuclideanSpace ℂ ((Fin L → Fin q) × β)) :
    EuclideanSpace ℂ ((Fin L → Fin q) × β) :=
  WithLp.toLp 2 fun p ↦
    successiveSchmidtTrim m (WithLp.toLp 2 fun x ↦ u (x, p.2)) (L - 1) p.1

private theorem sum_sq_norm_columns (u : EuclideanSpace ℂ ((Fin L → Fin q) × β)) :
    ∑ a, ‖(WithLp.toLp 2 fun x ↦ u (x, a) : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 =
      ‖u‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  change (∑ a, ∑ x, ‖u (x, a)‖ ^ 2) = ∑ p, ‖u p‖ ^ 2
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Independently trimming all columns does not increase their joint norm.
Source: LVV13, `algo53.tex`, the bond-trimming step, lines 549–559. -/
theorem norm_columnwiseSchmidtTrim_le (m : ℕ)
    (u : EuclideanSpace ℂ ((Fin L → Fin q) × β)) :
    ‖columnwiseSchmidtTrim m u‖ ≤ ‖u‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  calc
    ‖columnwiseSchmidtTrim m u‖ ^ 2 =
        ∑ a, ‖(WithLp.toLp 2 fun x ↦ columnwiseSchmidtTrim m u (x, a) :
          EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 :=
      (sum_sq_norm_columns (columnwiseSchmidtTrim m u)).symm
    _ ≤ ∑ a, ‖(WithLp.toLp 2 fun x ↦ u (x, a) :
        EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_successiveSchmidtTrim_le m (WithLp.toLp 2 fun x ↦ u (x, a)) (L - 1)) 2
    _ = ‖u‖ ^ 2 := sum_sq_norm_columns u

/-- The independent column trimmings have the same joint overlap-loss bound as one vector.
The proof sums the corrected LVV13 single-cut estimate by Cauchy–Schwarz over the orthonormal
environment coordinates. Source: `algo53.tex`, Claim `c:trim`, lines 549–559. -/
theorem norm_inner_sub_columnwiseSchmidtTrim_le (m : ℕ)
    (u v : EuclideanSpace ℂ ((Fin L → Fin q) × β)) (D : ℕ)
    (hv : ∀ a k, 0 < k → k < L →
      (cutMatrix (WithLp.toLp 2 fun x ↦ v (x, a)) k).rank ≤ D) :
    ‖⟪u - columnwiseSchmidtTrim m u, v⟫_ℂ‖ ≤
      (L - 1 : ℕ) * ‖u‖ * ‖v‖ * √((D : ℝ) / (m + 1)) := by
  classical
  let u₀ (a : β) : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2 fun x ↦ u (x, a)
  let v₀ (a : β) : EuclideanSpace ℂ (Fin L → Fin q) := WithLp.toLp 2 fun x ↦ v (x, a)
  have hinner : ⟪u - columnwiseSchmidtTrim m u, v⟫_ℂ =
      ∑ a, ⟪u₀ a - successiveSchmidtTrim m (u₀ a) (L - 1), v₀ a⟫_ℂ := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hcs : (∑ a, ‖u₀ a‖ * ‖v₀ a‖) ≤ ‖u‖ * ‖v‖ := by
    calc
      _ ≤ √(∑ a, ‖u₀ a‖ ^ 2) * √(∑ a, ‖v₀ a‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = ‖u‖ * ‖v‖ := by
        rw [sum_sq_norm_columns u, sum_sq_norm_columns v,
          Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg v)]
  rw [hinner]
  calc
    _ ≤ ∑ a, ‖⟪u₀ a - successiveSchmidtTrim m (u₀ a) (L - 1), v₀ a⟫_ℂ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a, (L - 1 : ℕ) * ‖u₀ a‖ * ‖v₀ a‖ * √((D : ℝ) / (m + 1)) := by
      refine Finset.sum_le_sum fun a _ ↦ ?_
      exact norm_inner_sub_successiveSchmidtTrim_le m (u₀ a) (v₀ a) (L - 1) D
        (fun k hk0 hkj ↦ hv a k hk0 (by omega))
    _ = ((L - 1 : ℕ) * √((D : ℝ) / (m + 1))) * ∑ a, ‖u₀ a‖ * ‖v₀ a‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ((L - 1 : ℕ) * √((D : ℝ) / (m + 1))) * (‖u‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (L - 1 : ℕ) * ‖u‖ * ‖v‖ * √((D : ℝ) / (m + 1)) := by ring

end TNLean.MPS.AreaLaw
