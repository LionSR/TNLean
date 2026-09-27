/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Topology.Instances.Matrix
import QICLean.Topology.CompactConvexFixedPoint

/-!
# Spectral radius of a nonnegative real matrix

**Source.** The Perron–Frobenius theorem for nonnegative matrices, as used in
arXiv:2204.05940, `References/2204.05940/source/mpo.tex` line 6068: a nonnegative matrix has a
nonnegative eigenvector for the eigenvalue equal to its spectral radius, and a positive
eigenvector of a nonnegative matrix has the spectral radius as its eigenvalue.

**Formalized here.** For a real matrix `M` with nonnegative entries, with spectral radius
taken over `ℂ` (Mathlib's `spectralRadius`):

* the weak Perron–Frobenius theorem: `ρ(M)` is an eigenvalue of `M` with an eigenvector whose
  entries are nonnegative and not all zero. The proof takes a complex eigenvalue `μ` of maximal
  modulus and an eigenvector `u`; the entrywise moduli `|u|` satisfy `M |u| ≥ ρ |u|`, so the
  compact convex set of probability vectors `x` with `M x ≥ ρ x` is nonempty. The map
  `x ↦ (M + 1) x / ∑ ((M + 1) x)_i` sends it into itself, and a Brouwer fixed point
  (`fixedPoint_of_compact_convex` of QICLean) is an eigenvector of `M` whose eigenvalue is at
  least `ρ` and at most `ρ`;
* a positive left eigenvector `δ M = r δ` forces `ρ(M) = r`, by pairing `δ` with the entrywise
  moduli of an arbitrary complex eigenvector.

## Main results

* `Matrix.exists_nonneg_mulVec_eq_spectralRadius_smul`: the weak Perron–Frobenius theorem.
* `Matrix.spectralRadius_map_ofReal_eq_of_pos_vecMul_eq`: the spectral radius equals the
  eigenvalue of a positive left eigenvector.
-/

open scoped Matrix ENNReal NNReal

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Brouwer's fixed-point theorem on `ι → ℝ`, transported from QICLean's
`fixedPoint_of_compact_convex` along the identification with Euclidean space. -/
theorem exists_fixedPoint_of_compact_convex_pi [Finite ι] {K : Set (ι → ℝ)} (hne : K.Nonempty)
    (hcomp : IsCompact K) (hconv : Convex ℝ K) {f : (ι → ℝ) → ι → ℝ} (hf : ContinuousOn f K)
    (hmaps : Set.MapsTo f K K) : ∃ x ∈ K, f x = x := by
  have := Fintype.ofFinite ι
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := EuclideanSpace.equiv ι ℝ
  obtain ⟨y, hy, hfy⟩ := fixedPoint_of_compact_convex (K := e ⁻¹' K)
    (f := fun y => e.symm (f (e y)))
    (by obtain ⟨x, hx⟩ := hne; exact ⟨e.symm x, by simpa using hx⟩)
    (by rw [← e.image_symm_eq_preimage]; exact hcomp.image e.symm.continuous)
    (hconv.linear_preimage e.toLinearEquiv.toLinearMap)
    (e.symm.continuous.comp_continuousOn (hf.comp e.continuous.continuousOn fun _ hy => hy))
    (fun y hy => by simpa using hmaps hy)
  exact ⟨e y, hy, by simpa using congrArg e hfy⟩

/-- A complex eigenvalue of a real matrix has a complex eigenvector. -/
theorem exists_eigenvector_of_mem_spectrum {M : Matrix ι ι ℝ} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (M.map ((↑) : ℝ → ℂ))) :
    ∃ v : ι → ℂ, v ≠ 0 ∧ ∀ i, ∑ j, (M i j : ℂ) * v j = μ * v i := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hμ
  refine ⟨v, hv0, fun i => ?_⟩
  have := congrFun hv i
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    sub_eq_zero] at this
  simpa [Matrix.mulVec, dotProduct] using this.symm

omit [DecidableEq ι] in
/-- The entrywise moduli of an eigenvector `M v = μ v` of a nonnegative matrix satisfy
`‖μ‖ ‖v_i‖ ≤ ∑_j M_{ij} ‖v_j‖`. -/
theorem norm_mul_norm_le_of_eigenvector {M : Matrix ι ι ℝ} (hM : ∀ i j, 0 ≤ M i j) {μ : ℂ}
    {v : ι → ℂ} (hev : ∀ i, ∑ j, (M i j : ℂ) * v j = μ * v i) (i : ι) :
    ‖μ‖ * ‖v i‖ ≤ ∑ j, M i j * ‖v j‖ :=
  calc ‖μ‖ * ‖v i‖ = ‖∑ j, (M i j : ℂ) * v j‖ := by rw [hev i, norm_mul]
    _ ≤ ∑ j, ‖(M i j : ℂ) * v j‖ := norm_sum_le _ _
    _ = ∑ j, M i j * ‖v j‖ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hM i j)]

/-- A real eigenvector `M w = s w`, `w ≠ 0`, makes `s` an eigenvalue of `M` over `ℂ`. -/
theorem ofReal_mem_spectrum_of_mulVec_eq {M : Matrix ι ι ℝ} {w : ι → ℝ} (hw : w ≠ 0) {s : ℝ}
    (h : M *ᵥ w = s • w) : (s : ℂ) ∈ spectrum ℂ (M.map ((↑) : ℝ → ℂ)) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨fun i => (w i : ℂ), ?_, ?_⟩
  · intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    have := congrFun h0 i
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
    exact hi this
  · ext i
    have hi := congrFun h i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact_mod_cast hi.symm

/-- A complex matrix over a nonempty index type has an eigenvalue of maximal modulus, and the
spectral radius is that modulus. -/
theorem exists_mem_spectrum_spectralRadius_eq [Nonempty ι] (A : Matrix ι ι ℂ) :
    ∃ μ ∈ spectrum ℂ A, (∀ ν ∈ spectrum ℂ A, ‖ν‖ ≤ ‖μ‖) ∧
      spectralRadius ℂ A = ENNReal.ofReal ‖μ‖ := by
  obtain ⟨μ, hμ, hmax⟩ := Set.exists_max_image (spectrum ℂ A) (‖·‖) A.finite_spectrum
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A)
  refine ⟨μ, hμ, hmax, ?_⟩
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun ν hν => ?_) (le_iSup₂_of_le μ hμ ?_)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal (hmax ν hν)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

omit [DecidableEq ι] in
/-- **Weak Perron–Frobenius theorem.** A real matrix `M` with nonnegative entries over a
nonempty index type has an eigenvector with nonnegative entries, not all zero, for the
eigenvalue `ρ(M)`, its spectral radius over `ℂ`. -/
theorem exists_nonneg_mulVec_eq_spectralRadius_smul [Nonempty ι] {M : Matrix ι ι ℝ}
    (hM : ∀ i j, 0 ≤ M i j) :
    ∃ v : ι → ℝ, v ≠ 0 ∧ (∀ i, 0 ≤ v i) ∧
      M *ᵥ v = (spectralRadius ℂ (M.map ((↑) : ℝ → ℂ))).toReal • v := by
  classical
  obtain ⟨μ, hμ, hmax, hρ⟩ := exists_mem_spectrum_spectralRadius_eq (M.map ((↑) : ℝ → ℂ))
  rw [hρ, ENNReal.toReal_ofReal (norm_nonneg _)]
  set ρ := ‖μ‖ with hρdef
  have hmulVec : ∀ (x : ι → ℝ) i, (M *ᵥ x) i = ∑ j, M i j * x j := fun _ _ => rfl
  -- a nonnegative vector `w = |u|` with `M w ≥ ρ w`
  obtain ⟨u, hu0, hu⟩ := exists_eigenvector_of_mem_spectrum hμ
  set w : ι → ℝ := fun i => ‖u i‖ with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => norm_nonneg _
  have hwM : ∀ i, ρ * w i ≤ (M *ᵥ w) i := fun i => by
    rw [hmulVec]; exact norm_mul_norm_le_of_eigenvector hM hu i
  have hwsum : 0 < ∑ i, w i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu0
    exact Finset.sum_pos' (fun j _ => hw0 j) ⟨i, Finset.mem_univ _, norm_pos_iff.2 hi⟩
  -- the compact convex set `K` and the map `f`
  set B : Matrix ι ι ℝ := M + 1 with hB
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j => by
    rw [hB, Matrix.add_apply, Matrix.one_apply]
    exact add_nonneg (hM i j) (by split_ifs <;> norm_num)
  have hBx : ∀ (x : ι → ℝ) i, (B *ᵥ x) i = (M *ᵥ x) i + x i := fun x i => by
    rw [hB, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  have hBnonneg : ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → ∀ i, 0 ≤ (B *ᵥ y) i := fun y hy i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hB0 i j) (hy j)
  have hMnonneg : ∀ y : ι → ℝ, (∀ j, 0 ≤ y j) → ∀ i, 0 ≤ (M *ᵥ y) i := fun y hy i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hM i j) (hy j)
  let K : Set (ι → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 ∧ ∀ i, ρ * x i ≤ (M *ᵥ x) i}
  let g : (ι → ℝ) → ℝ := fun x => ∑ i, (B *ᵥ x) i
  let f : (ι → ℝ) → (ι → ℝ) := fun x => (g x)⁻¹ • (B *ᵥ x)
  have hg : ∀ x ∈ K, 1 ≤ g x := fun x hx => by
    calc (1 : ℝ) = ∑ i, x i := hx.2.1.symm
      _ ≤ g x := Finset.sum_le_sum fun i _ => by
          rw [hBx]; linarith [hMnonneg x hx.1 i]
  have hcontMul : ∀ A : Matrix ι ι ℝ, Continuous fun x : ι → ℝ => A *ᵥ x := fun A =>
    Continuous.matrix_mulVec continuous_const continuous_id
  have hgcont : Continuous g :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).comp (hcontMul B)
  -- `K` is nonempty
  have hK_ne : K.Nonempty := by
    refine ⟨(∑ i, w i)⁻¹ • w, fun i => ?_, ?_, fun i => ?_⟩
    · exact mul_nonneg (inv_nonneg.2 hwsum.le) (hw0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hwsum.ne'
    · rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hwM i) (inv_nonneg.2 hwsum.le)
  -- `K` is compact
  have hK_closed : IsClosed K := by
    have h1 : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
      rw [show {x : ι → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} by ext; simp]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {x : ι → ℝ | ∑ i, x i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    have h3 : IsClosed {x : ι → ℝ | ∀ i, ρ * x i ≤ (M *ᵥ x) i} := by
      rw [show {x : ι → ℝ | ∀ i, ρ * x i ≤ (M *ᵥ x) i} = ⋂ i, {x | ρ * x i ≤ (M *ᵥ x) i} by
        ext; simp]
      exact isClosed_iInter fun i =>
        isClosed_le (continuous_const.mul (continuous_apply i))
          ((continuous_apply i).comp (hcontMul M))
    exact h1.inter (h2.inter h3)
  have hK_comp : IsCompact K := by
    refine (isCompact_univ_pi fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      hK_closed fun x hx i _ => ⟨hx.1 i, ?_⟩
    rw [← hx.2.1]
    exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  -- `K` is convex
  have hK_conv : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx.2.1, hy.2.1, mul_one, hab]
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hx.2.2 i) ha,
        mul_le_mul_of_nonneg_left (hy.2.2 i) hb]
  -- `f` maps `K` into itself
  have hmaps : Set.MapsTo f K K := by
    intro x hx
    have hgx := hg x hx
    have hgpos : 0 < g x := by linarith
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · exact mul_nonneg (inv_nonneg.2 hgpos.le) (hBnonneg x hx.1 i)
    · simp only [f, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hgpos.ne'
    · -- `M B x - ρ B x = B (M x - ρ x) ≥ 0`
      have hcomm : M * B = B * M := by rw [hB, mul_add, add_mul, mul_one, one_mul]
      have hdiff : ∀ j, 0 ≤ (M *ᵥ x - ρ • x) j := fun j => by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; linarith [hx.2.2 j]
      have key : 0 ≤ (M *ᵥ (B *ᵥ x)) i - ρ * (B *ᵥ x) i := by
        have := hBnonneg _ hdiff i
        rwa [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hcomm,
          ← Matrix.mulVec_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [f, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hgpos.le)
  -- `f` is continuous on `K`
  have hfcont : ContinuousOn f K :=
    ContinuousOn.smul (hgcont.continuousOn.inv₀ fun x hx => (by linarith [hg x hx] : g x ≠ 0))
      (hcontMul B).continuousOn
  obtain ⟨x, hx, hfx⟩ := exists_fixedPoint_of_compact_convex_pi hK_ne hK_comp hK_conv hfcont hmaps
  -- the fixed point is an eigenvector with eigenvalue `g x - 1 = ρ`
  have hgpos : 0 < g x := by linarith [hg x hx]
  have hBeig : B *ᵥ x = g x • x := by
    have := congrArg (fun y => g x • y) hfx
    simpa [f, smul_smul, mul_inv_cancel₀ hgpos.ne'] using this
  have hMeig : M *ᵥ x = (g x - 1) • x := by
    ext i
    have := congrFun hBeig i
    rw [hBx, Pi.smul_apply, smul_eq_mul] at this
    rw [Pi.smul_apply, smul_eq_mul, sub_mul, one_mul]
    linarith
  have hx0 : x ≠ 0 := by
    intro h0
    have := hx.2.1
    simp [h0] at this
  have hle : g x - 1 ≤ ρ := by
    have := hmax _ (ofReal_mem_spectrum_of_mulVec_eq hx0 hMeig)
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hge : ρ ≤ g x - 1 := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      by_contra hcon
      push Not at hcon
      have : ∀ i, x i = 0 := fun i => le_antisymm (hcon i) (hx.1 i)
      exact hx0 (funext this)
    have h1 := hx.2.2 i
    rw [hMeig, Pi.smul_apply, smul_eq_mul] at h1
    exact le_of_mul_le_mul_right h1 hi
  exact ⟨x, hx0, hx.1, by rw [hMeig, le_antisymm hle hge]⟩

/-- Every complex eigenvalue `μ` of a nonnegative real matrix `M` with a positive left
eigenvector `δ ᵥ* M = r • δ` satisfies `‖μ‖ ≤ r`: pairing `δ` with the entrywise moduli of an
eigenvector `v` gives `‖μ‖ ∑ δ_i ‖v_i‖ ≤ ∑_{i,j} δ_i M_{ij} ‖v_j‖ = r ∑ δ_j ‖v_j‖`. -/
theorem norm_le_of_mem_spectrum_of_pos_vecMul_eq {M : Matrix ι ι ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (M.map ((↑) : ℝ → ℂ))) : ‖μ‖ ≤ r := by
  obtain ⟨v, hv0, hev⟩ := exists_eigenvector_of_mem_spectrum hμ
  have hrow := norm_mul_norm_le_of_eigenvector hM hev
  have hcol : ∀ j, ∑ i, δ i * M i j = r * δ j := by
    intro j
    simpa [Matrix.vecMul, dotProduct] using congrFun h j
  set S := ∑ i, δ i * ‖v i‖ with hS
  have hSpos : 0 < S := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hδ j).le (norm_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (hδ i) (norm_pos_iff.2 hi)⟩
  have hbound : ‖μ‖ * S ≤ r * S := by
    calc ‖μ‖ * S = ∑ i, δ i * (‖μ‖ * ‖v i‖) := by
          rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, δ i * ∑ j, M i j * ‖v j‖ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hδ i).le
      _ = ∑ j, (∑ i, δ i * M i j) * ‖v j‖ := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = r * S := by
          simp_rw [hcol, hS, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  exact le_of_mul_le_mul_right hbound hSpos

/-- A positive left eigenvector `δ ᵥ* M = r • δ` of a real matrix makes `r` an eigenvalue of `M`
over `ℂ`. -/
theorem ofReal_mem_spectrum_of_pos_vecMul_eq [Nonempty ι] {M : Matrix ι ι ℝ} {δ : ι → ℝ}
    (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) :
    (r : ℂ) ∈ spectrum ℂ (M.map ((↑) : ℝ → ℂ)) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨fun i => (δ i : ℂ), ?_, ?_⟩
  · intro h0
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun h0 i
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
    exact (hδ i).ne' this
  · ext j
    have hj := congrFun h j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hj
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.vecMul_sub, Matrix.vecMul_smul,
      Matrix.vecMul_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    exact_mod_cast hj.symm

omit [DecidableEq ι] in
/-- **Spectral radius from a positive left eigenvector.** A nonnegative real matrix `M` with a
positive left eigenvector `δ ᵥ* M = r • δ` has spectral radius `r` over `ℂ`. -/
theorem spectralRadius_map_ofReal_eq_of_pos_vecMul_eq [Nonempty ι] {M : Matrix ι ι ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) :
    spectralRadius ℂ (M.map ((↑) : ℝ → ℂ)) = ENNReal.ofReal r := by
  classical
  have hr := ofReal_mem_spectrum_of_pos_vecMul_eq hδ h
  have hr0 : 0 ≤ r := by
    have := norm_le_of_mem_spectrum_of_pos_vecMul_eq hM hδ h hr
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact (abs_nonneg r).trans this
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (le_iSup₂_of_le (r : ℂ) hr ?_)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal (norm_le_of_mem_spectrum_of_pos_vecMul_eq hM hδ h hμ)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg hr0]

end Matrix
