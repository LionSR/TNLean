/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SpanEncodings

/-!
# Stability of viability under column approximation

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- Viability is stable under replacing a unit witness by a nearby supported vector.
After normalizing the replacement, the overlap loss is at most twice the vector error.
This elementary estimate is the bridge from exact LVV columns to their rational
approximations. -/
theorem isViable_of_close_supported_vector
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ ε : ℝ} (hε1 : ε < 1)
    {T : Set (LeftBlockVector L q k)}
    {φ ψ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : ‖φ‖ = 1) (hoverlap : 1 - δ ≤ ‖⟪φ, Γ⟫_ℂ‖)
    (hψT : ψ ∈ leftSupportSubmodule T) (hclose : ‖φ - ψ‖ ≤ ε) :
    IsViable Γ (δ + 2 * ε) T := by
  have hnormdiff : |‖φ‖ - ‖ψ‖| ≤ ε :=
    (abs_norm_sub_norm_le φ ψ).trans hclose
  have hnormdiff' : |1 - ‖ψ‖| ≤ ε := by
    simpa only [hφ] using hnormdiff
  have hψpos : 0 < ‖ψ‖ := by
    have : 1 - ε ≤ ‖ψ‖ := by
      have := (le_abs_self (1 - ‖ψ‖)).trans hnormdiff'
      linarith
    linarith
  let χ : EuclideanSpace ℂ (Fin L → Fin q) := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
  have hχ : ‖χ‖ = 1 := by
    simp only [χ, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hψpos]
    exact inv_mul_cancel₀ hψpos.ne'
  have hχT : χ ∈ leftSupportSubmodule T :=
    (leftSupportSubmodule T).smul_mem _ hψT
  have hχψ : ‖χ - ψ‖ = |1 - ‖ψ‖| := by
    rw [show χ - ψ = (((‖ψ‖⁻¹ - 1 : ℝ) : ℂ) • ψ) by
      simp only [χ, sub_smul, one_smul, Complex.ofReal_sub, Complex.ofReal_one]]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have heq : ‖ψ‖⁻¹ - 1 = (1 - ‖ψ‖) / ‖ψ‖ := by
      field_simp [hψpos.ne']
    rw [heq, abs_div, abs_of_pos hψpos, div_mul_cancel₀ _ hψpos.ne']
  have hχφ : ‖χ - φ‖ ≤ 2 * ε := by
    calc
      ‖χ - φ‖ ≤ ‖χ - ψ‖ + ‖ψ - φ‖ := norm_sub_le_norm_sub_add_norm_sub χ ψ φ
      _ = |1 - ‖ψ‖| + ‖φ - ψ‖ := by rw [hχψ, norm_sub_rev]
      _ ≤ ε + ε := add_le_add hnormdiff' hclose
      _ = 2 * ε := by ring
  refine ⟨χ, hχ, ?_, hχT⟩
  have hinner : ‖⟪φ, Γ⟫_ℂ‖ ≤ ‖⟪χ, Γ⟫_ℂ‖ + 2 * ε := by
    calc
      ‖⟪φ, Γ⟫_ℂ‖ ≤ ‖⟪χ, Γ⟫_ℂ‖ + ‖⟪φ - χ, Γ⟫_ℂ‖ := by
        rw [show ⟪φ, Γ⟫_ℂ = ⟪χ, Γ⟫_ℂ + ⟪φ - χ, Γ⟫_ℂ by
          rw [inner_sub_left]
          abel]
        exact norm_add_le _ _
      _ ≤ ‖⟪χ, Γ⟫_ℂ‖ + ‖φ - χ‖ * ‖Γ‖ := by
        gcongr
        exact norm_inner_le_norm _ _
      _ ≤ ‖⟪χ, Γ⟫_ℂ‖ + 2 * ε := by
        rw [hΓ, mul_one, norm_sub_rev]
        gcongr
  linarith

/-- Increasing the permitted overlap error preserves viability. -/
theorem IsViable.mono_error
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {δ δ' : ℝ}
    {T : Set (LeftBlockVector L q k)} (h : IsViable Γ δ T) (hδ : δ ≤ δ') :
    IsViable Γ δ' T := by
  obtain ⟨φ, hφ, hoverlap, hsupport⟩ := h
  exact ⟨φ, hφ, hoverlap.trans' (by linarith), hsupport⟩

/-- Assemble a finite collection of left-block columns into one vector with an auxiliary
right index. -/
noncomputable def assembleLeftColumns (w : Fin m → LeftBlockVector L q k) :
    EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m) :=
  WithLp.toLp 2 fun p ↦ w p.2 p.1

/-- Uniform column error `θ` gives joint Euclidean error at most `√m θ`. -/
theorem norm_sub_assembleLeftColumns_le
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (w : Fin m → LeftBlockVector L q k) {θ : ℝ} (hθ : 0 ≤ θ)
    (hclose : ∀ a,
      ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - w a‖ ≤ θ) :
    ‖u - assembleLeftColumns w‖ ≤ Real.sqrt m * θ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hθ)).mp
  calc
    ‖u - assembleLeftColumns w‖ ^ 2 =
        ∑ a : Fin m, ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - w a‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq]
      change (∑ p, ‖u p - w p.2 p.1‖ ^ 2) =
        ∑ a, ∑ x, ‖u (x, a) - w a x‖ ^ 2
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ ≤ ∑ _a : Fin m, θ ^ 2 := by
      apply Finset.sum_le_sum
      intro a _ha
      exact pow_le_pow_left₀ (norm_nonneg _) (hclose a) 2
    _ = (m : ℝ) * θ ^ 2 := by simp
    _ = (Real.sqrt m * θ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m)]

/-- Applying an isometry on the auxiliary right factor preserves the Euclidean norm. -/
theorem norm_rightApply_eq_of_isometry
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β]
    (W : Matrix γ β ℂ) (hW : Wᴴ * W = 1) (u : EuclideanSpace ℂ (α × β)) :
    ‖rightApply W u‖ = ‖u‖ := by
  classical
  let J := (1 : Matrix α α ℂ) ⊗ₖ W
  have hJ : Jᴴ * J = 1 := by
    simp only [J, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hW, Matrix.one_kronecker_one]
  have h : rightApply W u = WithLp.toLp 2 (J *ᵥ WithLp.ofLp u) := by
    ext ⟨x, a⟩
    simp [J, rightApply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.one_apply, Matrix.kroneckerMap_apply, mul_comm]
  rw [h]
  exact norm_toLp_mulVec_of_isometry J hJ u

/-- Transport a right-extended cut vector back to the physical chain coordinates. -/
noncomputable def physicalRightApply
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    EuclideanSpace ℂ (Fin L → Fin q) :=
  WithLp.toLp 2 fun z ↦ rightApply W u
    (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z)

/-- Applying the right isometry after joining the two left regions is the physical
three-cut reconstruction used in the LVV leading-vector theorem. -/
theorem physicalRightApply_gluingLeftCoordinates
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (u : EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m)) :
    physicalRightApply W (gluingLeftCoordinates L q k m u) =
      WithLp.toLp 2
        ((((1 : Matrix (CutLeft L q k × CutSite L q k)
          (CutLeft L q k × CutSite L q k) ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp u) ∘
            gluingCut L q k) := by
  exact (gluingLeftCoordinates_rightApply W u).symm

/-- In cut coordinates, `physicalRightApply` is exactly the corresponding right
extension. -/
theorem cutVector_physicalRightApply
    (W : Matrix (CutRight L q k) (Fin m) ℂ)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    Entropy.cutVector (n := fun _ : Fin L ↦ q) (leftBlock L k)
      (physicalRightApply W u) = rightApply W u := by
  ext p
  change rightApply W u
    (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)
      ((Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k)).symm p)) =
        rightApply W u p
  rw [Equiv.apply_symm_apply]

/-- A right isometry preserves the norm after returning to physical coordinates. -/
theorem norm_physicalRightApply_eq_of_isometry
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    ‖physicalRightApply W u‖ = ‖u‖ := by
  rw [← Entropy.norm_cutVector (leftBlock L k), cutVector_physicalRightApply,
    norm_rightApply_eq_of_isometry W hW]

/-- A right isometry also preserves distances between two cut vectors. -/
theorem norm_physicalRightApply_sub_eq_of_isometry
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u v : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m)) :
    ‖physicalRightApply W u - physicalRightApply W v‖ = ‖u - v‖ := by
  rw [show physicalRightApply W u - physicalRightApply W v =
      physicalRightApply W (u - v) by
    ext z
    let p := Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k) z
    change (∑ j, u (p.1, j) * W p.2 j) - (∑ j, v (p.1, j) * W p.2 j) =
      ∑ j, (u (p.1, j) - v (p.1, j)) * W p.2 j
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [sub_mul]]
  exact norm_physicalRightApply_eq_of_isometry W hW (u - v)

/-- Replacing every left column of an exact LVV witness within `θ` preserves viability,
with overlap error enlarged by at most `2 √m θ`. -/
theorem isViable_of_close_leftColumns
    {m : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ : ℝ} (hθ : 0 ≤ θ) (hsmall : Real.sqrt m * θ < 1)
    {T : Set (LeftBlockVector L q k)}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hunit : ‖physicalRightApply W u‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W u, Γ⟫_ℂ‖)
    (w : Fin m → LeftBlockVector L q k)
    (hwT : ∀ a, w a ∈ Submodule.span ℂ T)
    (hclose : ∀ a, ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - w a‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * θ)) T := by
  let u' := assembleLeftColumns w
  let ψ := physicalRightApply W u'
  have hψT : ψ ∈ leftSupportSubmodule T := by
    exact rightApply_mem_leftSupportSubmodule_of_columns T u' W (fun a ↦ by
      change w a ∈ Submodule.span ℂ T
      exact hwT a)
  have hclose' : ‖physicalRightApply W u - ψ‖ ≤ Real.sqrt m * θ := by
    rw [show ψ = physicalRightApply W u' from rfl,
      norm_physicalRightApply_sub_eq_of_isometry W hW]
    exact norm_sub_assembleLeftColumns_le u w hθ hclose
  exact isViable_of_close_supported_vector hΓ hsmall hunit hoverlap hψT hclose'

/-- Rounding subnormalized columns costs at most twice their joint error divided by
a lower bound for the original joint norm. This permits rationalization after Schmidt
trimming without requiring the rounded parameters to preserve normalization. -/
theorem isViable_of_close_subnormalized_leftColumns
    {m : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ c : ℝ} (hθ : 0 ≤ θ) (hc : 0 < c)
    (hsmall : Real.sqrt m * θ / c < 1)
    {T : Set (LeftBlockVector L q k)}
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hnorm : c ≤ ‖u‖)
    (hoverlap : 1 - δ ≤
      ‖⟪((‖u‖⁻¹ : ℝ) : ℂ) • physicalRightApply W u, Γ⟫_ℂ‖)
    (w : Fin m → LeftBlockVector L q k)
    (hwT : ∀ a, w a ∈ Submodule.span ℂ T)
    (hclose : ∀ a, ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - w a‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * θ / c)) T := by
  have hu : 0 < ‖u‖ := hc.trans_le hnorm
  let a : ℂ := (‖u‖⁻¹ : ℝ)
  have hanorm : ‖a‖ = ‖u‖⁻¹ := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hu]
  have hunit : ‖a • physicalRightApply W u‖ = 1 := by
    rw [norm_smul, hanorm, norm_physicalRightApply_eq_of_isometry W hW,
      inv_mul_cancel₀ hu.ne']
  have hsupport : a • physicalRightApply W (assembleLeftColumns w) ∈
      leftSupportSubmodule T := by
    apply (leftSupportSubmodule T).smul_mem
    exact rightApply_mem_leftSupportSubmodule_of_columns T (assembleLeftColumns w) W hwT
  have herror : ‖a • physicalRightApply W u -
      a • physicalRightApply W (assembleLeftColumns w)‖ ≤ Real.sqrt m * θ / c := by
    rw [← smul_sub, norm_smul, hanorm, norm_physicalRightApply_sub_eq_of_isometry W hW]
    calc
      ‖u‖⁻¹ * ‖u - assembleLeftColumns w‖ ≤
          ‖u‖⁻¹ * (Real.sqrt m * θ) :=
        mul_le_mul_of_nonneg_left (norm_sub_assembleLeftColumns_le u w hθ hclose)
          (inv_nonneg.mpr hu.le)
      _ = Real.sqrt m * θ / ‖u‖ := by rw [div_eq_mul_inv]; ring
      _ ≤ Real.sqrt m * θ / c :=
        div_le_div_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) hθ) hc hnorm
  exact isViable_of_close_supported_vector hΓ hsmall hunit hoverlap hsupport herror

/-- A family chosen before the target vector preserves the viability of every
subnormalized column witness whose columns it uniformly approximates. -/
theorem isViable_of_approximating_leftFamily
    {m : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ c : ℝ} (hθ : 0 ≤ θ) (hc : 0 < c)
    (hsmall : Real.sqrt m * θ / c < 1)
    (S T : Finset (LeftBlockVector L q k))
    (hcover : ∀ v ∈ S, ∃ w ∈ T, ‖v - w‖ ≤ θ)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hcols : ∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ S)
    (hnorm : c ≤ ‖u‖)
    (hoverlap : 1 - δ ≤
      ‖⟪((‖u‖⁻¹ : ℝ) : ℂ) • physicalRightApply W u, Γ⟫_ℂ‖) :
    IsViable Γ (δ + 2 * (Real.sqrt m * θ / c))
      (T : Set (LeftBlockVector L q k)) := by
  choose w hwT hclose using fun a ↦ hcover _ (hcols a)
  exact isViable_of_close_subnormalized_leftColumns hΓ hθ hc hsmall W hW u
    hnorm hoverlap w (fun a ↦ Submodule.subset_span (hwT a)) hclose

/-- The reserve in the Schmidt-trimmed witness absorbs a uniform column
approximation at the stated mesh, leaving half-viability for error reduction.
The extra unit in the denominator handles an empty column type. -/
theorem isViable_half_of_approximating_trimmed_leftFamily
    {m : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hmesh : θ ≤ 37 / (1152 * (Real.sqrt m + 1)))
    (S T : Finset (LeftBlockVector L q k))
    (hcover : ∀ v ∈ S, ∃ w ∈ T, ‖v - w‖ ≤ θ)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hcols : ∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) ∈ S)
    (hnorm : 37 / 48 ≤ ‖u‖)
    (hoverlap : 7 / 12 ≤
      ‖⟪((‖u‖⁻¹ : ℝ) : ℂ) • physicalRightApply W u, Γ⟫_ℂ‖) :
    IsViable Γ (1 / 2) (T : Set (LeftBlockVector L q k)) := by
  have hbudget : Real.sqrt m * θ / (37 / 48) ≤ 1 / 24 := by
    have hdenom : 0 < 1152 * (Real.sqrt (m : ℝ) + 1) := by positivity
    have h := (le_div_iff₀ hdenom).mp hmesh
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 37 / 48)).mpr
    nlinarith [Real.sqrt_nonneg (m : ℝ)]
  have hviable := isViable_of_approximating_leftFamily (δ := 5 / 12) hΓ hθ
    (by norm_num : (0 : ℝ) < 37 / 48)
    (lt_of_le_of_lt hbudget (by norm_num)) S T hcover W hW u hcols hnorm
    (by linarith only [hoverlap])
  exact hviable.mono_error (by linarith only [hbudget])

/-- A rational decoded column family is viable whenever it approximates all columns of
one exact LVV witness.  This is the stability statement needed to turn certificate
coordinates into an actual finite viable output family. -/
theorem isViable_spanColumnFamily_of_close
    {m n : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ : ℝ} (hθ : 0 ≤ θ) (hsmall : Real.sqrt m * θ < 1)
    (S : Finset (LeftBlockVector L q k))
    (c : Fin n → Fin m → S → ℂ) (j : Fin n)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hunit : ‖physicalRightApply W u‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W u, Γ⟫_ℂ‖)
    (hclose : ∀ a,
      ‖WithLp.toLp 2 (fun x ↦ u (x, a)) - ∑ s : S, c j a s • s.1‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * θ))
      (spanColumnFamily S m c : Set (LeftBlockVector L q k)) := by
  apply isViable_of_close_leftColumns hΓ hθ hsmall W hW u hunit hoverlap
    (fun a ↦ ∑ s : S, c j a s • s.1)
  · intro a
    exact Submodule.subset_span (sum_mem_spanColumnFamily S m c j a)
  · exact hclose

/-- A linear combination of `n` uniformly approximated columns has error at most
`n θ` when every coefficient has norm at most one.  The deliberately elementary
bound is sufficient for the polynomial mesh estimate in LVV13, `algo53.tex`,
lines 472--478. -/
theorem norm_sum_smul_sub_sum_smul_le
    {n : ℕ} (z : Fin n → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (v w : Fin n → LeftBlockVector L q k) {θ : ℝ}
    (hclose : ∀ j, ‖v j - w j‖ ≤ θ) :
    ‖(∑ j, z j • v j) - ∑ j, z j • w j‖ ≤ n * θ := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ j, (z j • v j - z j • w j)‖ ≤
        ∑ j, ‖z j • v j - z j • w j‖ := norm_sum_le Finset.univ _
    _ = ∑ j, ‖z j‖ * ‖v j - w j‖ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← smul_sub, norm_smul]
    _ ≤ ∑ _j : Fin n, θ := by
      apply Finset.sum_le_sum
      intro j _hj
      calc
        ‖z j‖ * ‖v j - w j‖ ≤ 1 * ‖v j - w j‖ :=
          mul_le_mul_of_nonneg_right (hz j) (norm_nonneg _)
        _ ≤ 1 * θ := mul_le_mul_of_nonneg_left (hclose j) zero_le_one
        _ = θ := one_mul θ
    _ = n * θ := by simp

/-- For unit coefficients in Euclidean norm, Cauchy--Schwarz improves the accumulated
error of `n` uniformly approximated columns from `n θ` to `√n θ`. -/
theorem norm_sum_smul_sub_sum_smul_le_sqrt
    {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ = 1)
    (v w : Fin n → LeftBlockVector L q k) {θ : ℝ} (hθ : 0 ≤ θ)
    (hclose : ∀ j, ‖v j - w j‖ ≤ θ) :
    ‖(∑ j, z j • v j) - ∑ j, z j • w j‖ ≤ Real.sqrt n * θ := by
  rw [← Finset.sum_sub_distrib]
  have hcs := Finset.norm_sum_le_mul_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin n))
    (fun j ↦ z j • v j - z j • w j) (fun j ↦ ‖z j‖) (fun _ ↦ 1) hθ
    (fun j _hj ↦ by
      rw [← smul_sub, norm_smul]
      nlinarith only [hclose j, norm_nonneg (z j)])
  rw [show ∑ j : Fin n, ‖z j‖ ^ 2 = ‖z‖ ^ 2 by
      simp only [EuclideanSpace.norm_sq_eq],
    hz, one_pow, Real.sqrt_one] at hcs
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul, mul_comm] using hcs

/-- The decoded rational column family remains viable for an arbitrary linear
combination of exact compressed columns.  Thus the stability argument applies to a
leading vector of the compressed density matrix, rather than only to one coordinate
column.  This is the form used in LVV13, `algo53.tex`, lines 472--478 and 520--527. -/
theorem isViable_spanColumnFamily_of_close_linearCombination
    {m n : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ : ℝ} (hθ : 0 ≤ θ) (hsmall : Real.sqrt m * (n * θ) < 1)
    (S : Finset (LeftBlockVector L q k))
    (c : Fin n → Fin m → S → ℂ) (z : Fin n → ℂ)
    (hz : ∀ j, ‖z j‖ ≤ 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (u : EuclideanSpace ℂ
      (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k) × Fin m))
    (hunit : ‖physicalRightApply W u‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W u, Γ⟫_ℂ‖)
    (v : Fin n → Fin m → LeftBlockVector L q k)
    (hu : ∀ a, WithLp.toLp 2 (fun x ↦ u (x, a)) = ∑ j, z j • v j a)
    (hclose : ∀ j a, ‖v j a - ∑ s : S, c j a s • s.1‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * (n * θ)))
      (spanColumnFamily S m c : Set (LeftBlockVector L q k)) := by
  apply isViable_of_close_leftColumns hΓ (mul_nonneg (Nat.cast_nonneg n) hθ)
    hsmall W hW u hunit hoverlap
    (fun a ↦ ∑ j, z j • ∑ s : S, c j a s • s.1)
  · intro a
    apply Submodule.sum_mem
    intro j _hj
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (sum_mem_spanColumnFamily S m c j a))
  · intro a
    rw [hu a]
    exact norm_sum_smul_sub_sum_smul_le z hz (fun j ↦ v j a)
      (fun j ↦ ∑ s : S, c j a s • s.1) (fun j ↦ hclose j a)

/-- Specialization of the preceding stability theorem to the compressed vector `Z z`.
It removes the coordinate bookkeeping between matrix-vector multiplication and the
linear combination of the columns of `Z`.  This is the exact interface used by the
compressed leading vector in LVV13, `algo53.tex`, lines 477--478 and 493--505. -/
theorem isViable_spanColumnFamily_of_close_mulVec
    {m n : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hΓ : ‖Γ‖ = 1)
    {δ θ : ℝ} (hθ : 0 ≤ θ)
    (hsmall : Real.sqrt m * (Real.sqrt n * θ) < 1)
    (S : Finset (LeftBlockVector L q k))
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (c : Fin n → Fin m → S → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hz : ‖z‖ = 1)
    (W : Matrix (CutRight L q k) (Fin m) ℂ) (hW : Wᴴ * W = 1)
    (hunit : ‖physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z)))‖ = 1)
    (hoverlap : 1 - δ ≤ ‖⟪physicalRightApply W
      (gluingLeftCoordinates L q k m
        (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))), Γ⟫_ℂ‖)
    (hclose : ∀ j a,
      ‖WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
        ∑ s : S, c j a s • s.1‖ ≤ θ) :
    IsViable Γ (δ + 2 * (Real.sqrt m * (Real.sqrt n * θ)))
      (spanColumnFamily S m c : Set (LeftBlockVector L q k)) := by
  let u := gluingLeftCoordinates L q k m
    (WithLp.toLp 2 (Z *ᵥ WithLp.ofLp z))
  let v : Fin n → Fin m → LeftBlockVector L q k := fun j a ↦
    WithLp.toLp 2 (fun x ↦
      gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))
  apply isViable_of_close_leftColumns hΓ
    (mul_nonneg (Real.sqrt_nonneg n) hθ) hsmall W hW u hunit hoverlap
    (fun a ↦ ∑ j, z j • ∑ s : S, c j a s • s.1)
  · intro a
    apply Submodule.sum_mem
    intro j _hj
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (sum_mem_spanColumnFamily S m c j a))
  · intro a
    rw [show WithLp.toLp 2 (fun x ↦ u (x, a)) = ∑ j, z j • v j a by
      ext x
      simp [u, v, gluingLeftCoordinates, Matrix.mulVec, dotProduct, mul_comm]]
    exact norm_sum_smul_sub_sum_smul_le_sqrt z hz (fun j ↦ v j a)
      (fun j ↦ ∑ s : S, c j a s • s.1) hθ (fun j ↦ hclose j a)

end TNLean.MPS.AreaLaw
