/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleKernelConditions
import TNLean.MPS.Overlap.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The finite variational spectral step for the uncle Hamiltonian

A positive operator with a vector orthogonal to its kernel and Rayleigh
quotient below epsilon has an actual positive eigenvalue below epsilon.
Applied to the explicit finite uncle Hamiltonian, this is the spectral step
in arXiv:1210.6613, proof of Theorem thm:gapless, lines 1302–1314.
The preceding norm, energy, and ground-overlap estimates must still supply
such a vector; they are not assumed as a gaplessness conclusion here.
-/

noncomputable section

open scoped InnerProductSpace BigOperators

namespace MPSTensor

private theorem exists_small_pos_eigenvalue_of_rayleigh
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (v : E) (hv : v ∈ (LinearMap.ker T)ᗮ)
    (ε : ℝ) (hRayleigh : (⟪T v, v⟫_ℂ).re < ε * ‖v‖ ^ 2) :
    ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧ Module.End.HasEigenvalue T (μ : ℂ) := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
    hT.isSymmetric.eigenvectorBasis rfl
  let lam : Fin (Module.finrank ℂ E) → ℝ := hT.isSymmetric.eigenvalues rfl
  have hnonneg (i) : 0 ≤ lam i := hT.nonneg_eigenvalues rfl i
  have heig (i) : Module.End.HasEigenvalue T (lam i : ℂ) :=
    hT.isSymmetric.hasEigenvalue_eigenvalues rfl i
  have hcoord_zero (i) (hi : lam i = 0) : b.repr v i = 0 := by
    have hker : b i ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker]
      change T (hT.isSymmetric.eigenvectorBasis rfl i) = 0
      rw [hT.isSymmetric.apply_eigenvectorBasis]
      change (lam i : ℂ) • b i = 0
      rw [hi, Complex.ofReal_zero, zero_smul]
    rw [b.repr_apply_apply]
    exact ((LinearMap.ker T).mem_orthogonal v).mp hv (b i) hker
  have hnorm : ‖v‖ ^ 2 = ∑ i, ‖b.repr v i‖ ^ 2 := by
    rw [← b.repr.norm_map v, PiLp.norm_sq_eq_of_L2]
  have henergy : (⟪T v, v⟫_ℂ).re = ∑ i, lam i * ‖b.repr v i‖ ^ 2 := by
    rw [← b.repr.inner_map_map (T v) v, PiLp.inner_apply]
    change Complex.reCLM (∑ i, inner ℂ (b.repr (T v) i) (b.repr v i)) = _
    rw [map_sum Complex.reCLM]
    apply Finset.sum_congr rfl
    intro i _
    have hdia : b.repr (T v) i = (lam i : ℂ) * b.repr v i :=
      hT.isSymmetric.eigenvectorBasis_apply_self_apply rfl v i
    rw [hdia]
    change (inner ℂ ((lam i : ℂ) • b.repr v i) (b.repr v i)).re = _
    rw [inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
      inner_self_eq_norm_sq]
  suffices ∃ i, 0 < lam i ∧ lam i < ε by
    obtain ⟨i, hi, hε⟩ := this
    exact ⟨lam i, hi, hε, heig i⟩
  by_contra hnone
  have hweight (i) : ε * ‖b.repr v i‖ ^ 2 ≤ lam i * ‖b.repr v i‖ ^ 2 := by
    by_cases hi : lam i = 0
    · rw [hcoord_zero i hi]
      simp
    · have hpos : 0 < lam i := lt_of_le_of_ne (hnonneg i) (Ne.symm hi)
      have hlarge : ε ≤ lam i := by
        by_contra hlt
        exact hnone ⟨i, hpos, lt_of_not_ge hlt⟩
      exact mul_le_mul_of_nonneg_right hlarge (sq_nonneg _)
  have hlower : ε * ‖v‖ ^ 2 ≤ (⟪T v, v⟫_ℂ).re := by
    rw [hnorm, henergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hweight i
  exact (not_lt_of_ge hlower) hRayleigh

private theorem norm_span_pair_projection_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (u v φ : E) (hu : (1 / 2 : ℝ) ≤ ‖u‖ ^ 2) (hv : (1 / 2 : ℝ) ≤ ‖v‖ ^ 2)
    (huv : ‖inner ℂ u v‖ ≤ 1 / 4) :
    ‖(Submodule.span ℂ ({u, v} : Set E)).starProjection φ‖ ^ 2 ≤
      4 * (‖inner ℂ u φ‖ ^ 2 + ‖inner ℂ v φ‖ ^ 2) := by
  classical
  let K := Submodule.span ℂ ({u, v} : Set E)
  let w := K.starProjection φ
  obtain ⟨α, β, hw⟩ := Submodule.mem_span_pair.mp (K.starProjection_apply_mem φ)
  have hw' : w = α • u + β • v := hw.symm
  have hcross : |(inner ℂ (α • u) (β • v)).re| ≤ ‖α‖ * ‖β‖ / 4 := by
    calc
      _ ≤ ‖inner ℂ (α • u) (β • v)‖ := Complex.abs_re_le_norm _
      _ = ‖α‖ * ‖β‖ * ‖inner ℂ u v‖ := by
        rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, norm_star]
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left huv
        (mul_nonneg (norm_nonneg α) (norm_nonneg β))]
  have hexpand : ‖w‖ ^ 2 = ‖α‖ ^ 2 * ‖u‖ ^ 2 +
      2 * (inner ℂ (α • u) (β • v)).re + ‖β‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [hw', norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, mul_pow, mul_pow]
  have hcoefs : ‖α‖ ^ 2 + ‖β‖ ^ 2 ≤ 4 * ‖w‖ ^ 2 := by
    have hα := mul_le_mul_of_nonneg_left hu (sq_nonneg ‖α‖)
    have hβ := mul_le_mul_of_nonneg_left hv (sq_nonneg ‖β‖)
    have hlow := (abs_le.mp hcross).1
    nlinarith [sq_nonneg (‖α‖ - ‖β‖)]
  have hinner : ‖w‖ ^ 2 ≤
      ‖α‖ * ‖inner ℂ u φ‖ + ‖β‖ * ‖inner ℂ v φ‖ := by
    calc
      _ = (inner ℂ w φ).re := (K.re_inner_starProjection_eq_normSq φ).symm
      _ ≤ ‖inner ℂ w φ‖ := Complex.re_le_norm _
      _ ≤ _ := by
        rw [hw', inner_add_left, inner_smul_left, inner_smul_left]
        simpa only [norm_mul, norm_star] using
          norm_add_le (star α * inner ℂ u φ) (star β * inner ℂ v φ)
  have hCS : (‖α‖ * ‖inner ℂ u φ‖ + ‖β‖ * ‖inner ℂ v φ‖) ^ 2 ≤
      (‖α‖ ^ 2 + ‖β‖ ^ 2) * (‖inner ℂ u φ‖ ^ 2 + ‖inner ℂ v φ‖ ^ 2) := by
    nlinarith [sq_nonneg (‖α‖ * ‖inner ℂ v φ‖ - ‖β‖ * ‖inner ℂ u φ‖)]
  have hsquare : (‖w‖ ^ 2) ^ 2 ≤
      4 * ‖w‖ ^ 2 * (‖inner ℂ u φ‖ ^ 2 + ‖inner ℂ v φ‖ ^ 2) := by
    calc
      _ ≤ (‖α‖ * ‖inner ℂ u φ‖ + ‖β‖ * ‖inner ℂ v φ‖) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg ‖w‖) (by positivity)).mpr hinner
      _ ≤ _ := hCS.trans (mul_le_mul_of_nonneg_right hcoefs (by positivity))
  change ‖w‖ ^ 2 ≤ _
  by_cases hwzero : ‖w‖ ^ 2 = 0
  · rw [hwzero]
    positivity
  have hwpos : 0 < ‖w‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hwzero)
  apply (mul_le_mul_iff_left₀ hwpos).mp
  nlinarith only [hsquare]

/-- The actual two periodic MPS sectors give a controlled ground-space
projection once their Gram matrix is close to the identity. The hypotheses
are finite scalar inequalities, to be supplied by the canonical transfer
limits and the actual mixed-overlap decay. Source application:
arXiv:1210.6613, proof of thm:gapless, lines 1302–1314. -/
theorem norm_mpv_span_projection_sq_le
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b) (N : ℕ)
    (φ : EuclideanSpace ℂ (Cfg d N))
    (hA : (1 / 2 : ℝ) ≤ ‖mpvState A N‖ ^ 2)
    (hB : (1 / 2 : ℝ) ≤ ‖mpvState B N‖ ^ 2)
    (hAB : ‖inner ℂ (mpvState A N) (mpvState B N)‖ ≤ 1 / 4) :
    ‖(Submodule.span ℂ ({mpvState A N, mpvState B N} :
        Set (EuclideanSpace ℂ (Cfg d N)))).starProjection φ‖ ^ 2 ≤
      4 * (‖inner ℂ (mpvState A N) φ‖ ^ 2 + ‖inner ℂ (mpvState B N) φ‖ ^ 2) :=
  norm_span_pair_projection_sq_le _ _ _ hA hB hAB

/-- The actual finite uncle Hamiltonian has a positive eigenvalue below a
strict Rayleigh bound from its kernel complement. Positivity is derived from
the actual interaction rather than supplied as another hypothesis.

This is the finite spectral argument of arXiv:1210.6613, proof of thm:gapless,
lines 1302–1314; constructing the variational vector remains a separate step. -/
theorem exists_pos_eigenvalue_uncleHamiltonianES_lt_of_rayleigh
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ)
    (v : EuclideanSpace ℂ (Cfg d N))
    (hv : v ∈ (LinearMap.ker (uncleHamiltonianES A B R L N).toLinearMap)ᗮ)
    (ε : ℝ)
    (hRayleigh : (⟪uncleHamiltonianES A B R L N v, v⟫_ℂ).re < ε * ‖v‖ ^ 2) :
    ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧
      Module.End.HasEigenvalue (uncleHamiltonianES A B R L N).toLinearMap (μ : ℂ) :=
  exists_small_pos_eigenvalue_of_rayleigh _ (uncleHamiltonianES_isPositive A B R L N)
    v hv ε hRayleigh

/-- The actual variational spectral step for an arbitrary trial vector.
Subtracting its actual kernel projection preserves energy and removes
exactly the projected squared norm. This derives the kernel-complement
vector rather than requiring orthogonality of the supplied trial.
Source: arXiv:1210.6613, proof of thm:gapless, lines 1302–1314. -/
theorem exists_pos_eigenvalue_uncleHamiltonianES_lt_of_projection_bound
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ) (N : ℕ)
    (v : EuclideanSpace ℂ (Cfg d N)) (ε : ℝ)
    (hRayleigh : (⟪uncleHamiltonianES A B R L N v, v⟫_ℂ).re <
      ε * (‖v‖ ^ 2 -
        ‖(LinearMap.ker (uncleHamiltonianES A B R L N).toLinearMap).starProjection v‖ ^ 2)) :
    ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧
      Module.End.HasEigenvalue (uncleHamiltonianES A B R L N).toLinearMap (μ : ℂ) := by
  let T := (uncleHamiltonianES A B R L N).toLinearMap
  let K := LinearMap.ker T
  let w := v - K.starProjection v
  have hT : T.IsPositive := uncleHamiltonianES_isPositive A B R L N
  have hw : w ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal (K := K) v
  have hkill : T (K.starProjection v) = 0 :=
    LinearMap.mem_ker.mp (K.starProjection_apply_mem v)
  have hTw : T w = T v := by
    change T (v - K.starProjection v) = T v
    rw [map_sub, hkill, sub_zero]
  have hcross : inner ℂ (T v) (K.starProjection v) = 0 := by
    rw [hT.isSymmetric v (K.starProjection v), hkill, inner_zero_right]
  have henergy : (⟪T w, w⟫_ℂ).re = (⟪T v, v⟫_ℂ).re := by
    rw [hTw]
    change (inner ℂ (T v) (v - K.starProjection v)).re = _
    rw [inner_sub_right, hcross, sub_zero]
  have hnorm : ‖w‖ ^ 2 = ‖v‖ ^ 2 - ‖K.starProjection v‖ ^ 2 := by
    have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection v K
    have horth : Kᗮ.starProjection v = w :=
      Submodule.starProjection_orthogonal_val (K := K) v
    rw [horth] at hpyth
    linarith
  apply exists_small_pos_eigenvalue_of_rayleigh T hT w hw ε
  rw [henergy, hnorm]
  exact hRayleigh

end MPSTensor
