/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Uncle.UncleKernelConditions
import TNLean.MPS.Tensor.Overlap
import Mathlib.Analysis.InnerProductSpace.Spectrum
import TNLean.MPS.ParentHamiltonian.Uncle.UncleTrialOverlap

/-!
# The finite variational spectral step for the uncle Hamiltonian

A positive operator with a vector orthogonal to its kernel and Rayleigh
quotient below epsilon has a positive eigenvalue below epsilon.
Applied to the explicit finite uncle Hamiltonian, this is the spectral step
in arXiv:1210.6613, proof of Theorem thm:gapless, lines 1302–1314.
The preceding norm, energy, and ground-overlap estimates must still supply
such a vector; they are not assumed as a gaplessness conclusion here.

## Vanishing projection of the actual two-wall trial onto the periodic sectors

The derived trial overlaps and the asymptotic Gram matrix of the two periodic
vectors force the actual projected squared norm to vanish. This supplies the
projection-removal step for arXiv:1210.6613, proof of Theorem thm:gapless,
lines 1302–1314. The separate canonical Gram theorem discharges the explicit
Gram-limit input; the exact uncle kernel theorem identifies this span with
the full kernel for injective perturbations and sufficiently large lengths.

## The asymptotic finite variational step for the uncle Hamiltonian

A quadratic lower bound for an actual trial's squared norm, a vanishing
actual kernel projection and a linear energy upper bound give arbitrarily
small positive eigenvalues on the chains of length 6N+1. This is the purely
analytic step after the source tensor and genericity estimates; those
estimates remain explicit inputs here.

Source: arXiv:1210.6613, proof of Theorem thm:gapless, lines 1302–1314.
-/

section

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
    rw [inner_smul_left, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (lam i * ·) (inner_self_eq_norm_sq (𝕜 := ℂ) (b.repr v i))
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
        simp only [inner_smul_left, inner_smul_right, norm_mul, starRingEnd_apply, norm_star]
        ring
      _ ≤ ‖α‖ * ‖β‖ * (1 / 4) :=
        mul_le_mul_of_nonneg_left huv (mul_nonneg (norm_nonneg α) (norm_nonneg β))
      _ = _ := by ring
  have hexpand : ‖w‖ ^ 2 = ‖α‖ ^ 2 * ‖u‖ ^ 2 +
      2 * (inner ℂ (α • u) (β • v)).re + ‖β‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [hw', norm_add_sq (𝕜 := ℂ), RCLike.re_eq_complex_re,
      norm_smul, norm_smul, mul_pow, mul_pow]
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
        simpa only [norm_mul, starRingEnd_apply, norm_star] using
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

/-- The two periodic MPS sectors give a controlled ground-space
projection once their Gram matrix is close to the identity. The hypotheses
are finite scalar inequalities, to be supplied by the canonical transfer
limits and the mixed-overlap decay. Source application:
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

/-- The finite uncle Hamiltonian has a positive eigenvalue below a
strict Rayleigh bound from its kernel complement. Positivity is derived from
the interaction rather than supplied as another hypothesis.

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

/-- The variational spectral step for an arbitrary trial vector.
Subtracting its kernel projection preserves energy and removes
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
end

end

section

open scoped InnerProductSpace Topology
open Filter

namespace MPSTensor

/-- The actual source trial has vanishing squared projection onto the two
periodic ground sectors. The actual overlap limits are derived from unital
normalization and mixed damping, rather than supplied as an orthogonality
premise. Source: arXiv:1210.6613, proof of Theorem thm:gapless. -/
theorem uncleTwoWallTrialSource_span_projection_tendsto_zero
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (hGram :
      Tendsto (fun M ↦ ‖mpvState A M‖ ^ 2) atTop (nhds (1 : ℝ)) ∧
        Tendsto (fun M ↦ ‖mpvState B M‖ ^ 2) atTop (nhds (1 : ℝ)) ∧
        Tendsto (fun M ↦ inner ℂ (mpvState A M) (mpvState B M)) atTop (nhds (0 : ℂ)))
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    Tendsto (fun N : ℕ ↦
      ‖(Submodule.span ℂ ({mpvState A (6 * N + 1), mpvState B (6 * N + 1)} :
          Set (EuclideanSpace ℂ (Cfg d (6 * N + 1))))).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N))‖ ^ 2) atTop (nhds (0 : ℝ)) := by
  have hlen : Tendsto (fun N : ℕ ↦ 6 * N + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    exact eventually_atTop.mpr ⟨M, fun N hN ↦ by omega⟩
  have hA := (hGram.1.comp hlen).eventually
    (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hB := (hGram.2.1.comp hlen).eventually
    (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hcrossNorm : Tendsto (fun N : ℕ ↦
      ‖inner ℂ (mpvState A (6 * N + 1)) (mpvState B (6 * N + 1))‖)
      atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_apply, norm_zero] using (hGram.2.2.comp hlen).norm
  have hcross := hcrossNorm.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hleft := inner_mpvState_left_uncleTwoWallTrialSource_tendsto_zero A B R L hUA hBA
  have hright := inner_mpvState_right_uncleTwoWallTrialSource_tendsto_zero A B R L hUB hAB
  have hbound := ((hleft.norm.pow 2).add (hright.norm.pow 2)).const_mul 4
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ sq_nonneg _)
  · filter_upwards [hA, hB, hcross] with N hAN hBN hcrossN
    exact norm_mpv_span_projection_sq_le A B (6 * N + 1) _ hAN.le hBN.le hcrossN.le
  · simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero] using hbound

end MPSTensor

end

section

noncomputable section

open Filter
open scoped InnerProductSpace Topology

namespace MPSTensor

/-- The actual uncle Hamiltonians have eventually a positive eigenvalue
below every positive threshold when the actual trial family has quadratic
squared norm, vanishing kernel projection and linear energy. The kernel
complement vector is derived by subtracting its actual orthogonal projection.
This is the analytic step of arXiv:1210.6613, proof of thm:gapless,
lines 1302–1314; no source tensor estimate is asserted by this lemma alone. -/
theorem eventually_exists_pos_eigenvalue_uncleHamiltonianES_lt_of_trial_bounds
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (v : (N : ℕ) → EuclideanSpace ℂ (Cfg d (6 * N + 1)))
    (c : ℝ) (hc : 0 < c)
    (hNorm : ∀ᶠ N : ℕ in atTop, c * ((N + 1 : ℕ) : ℝ) ^ 2 ≤ ‖v N‖ ^ 2)
    (hProj : Tendsto (fun N : ℕ ↦
      ‖(LinearMap.ker (uncleHamiltonianES A B R L (6 * N + 1)).toLinearMap).starProjection
        (v N)‖ ^ 2) atTop (𝓝 0))
    (hEnergy : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (⟪uncleHamiltonianES A B R L (6 * N + 1) (v N), v N⟫_ℂ).re ≤ C * N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧
        Module.End.HasEigenvalue
          (uncleHamiltonianES A B R L (6 * N + 1)).toLinearMap (μ : ℂ) := by
  obtain ⟨C, hC, hEnergy⟩ := hEnergy
  intro ε hε
  let k : ℝ := ε * c / 2
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (C / k)
  have hMpos : 0 < M := Nat.cast_pos.mp ((div_pos hC hk).trans hM)
  have hProjSmall : ∀ᶠ N : ℕ in atTop,
      ‖(LinearMap.ker (uncleHamiltonianES A B R L (6 * N + 1)).toLinearMap).starProjection
        (v N)‖ ^ 2 < c / 2 :=
    hProj.eventually (eventually_lt_nhds (half_pos hc))
  filter_upwards [hNorm, hEnergy, hProjSmall, eventually_ge_atTop M]
    with N hNormN hEnergyN hProjN hMN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (hMpos.trans_le hMN)
  have hNormN' : c * ((N : ℝ) + 1) ^ 2 ≤ ‖v N‖ ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hNormN
  have hMass : (c / 2) * (N : ℝ) ^ 2 ≤ ‖v N‖ ^ 2 -
      ‖(LinearMap.ker (uncleHamiltonianES A B R L (6 * N + 1)).toLinearMap).starProjection
        (v N)‖ ^ 2 := by
    have hlinear : 0 ≤ c * (N : ℝ) := mul_nonneg hc.le hNpos.le
    have hquadratic : 0 ≤ c * (N : ℝ) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
    nlinarith only [hNormN', hProjN.le, hc, hlinear, hquadratic]
  have hLarge : C < k * (N : ℝ) := by
    have hdiv : C / k < (N : ℝ) := hM.trans_le (Nat.cast_le.mpr hMN)
    simpa only [mul_comm] using (div_lt_iff₀ hk).mp hdiv
  have hRayleigh : C * (N : ℝ) < ε * ((c / 2) * (N : ℝ) ^ 2) := by
    calc
      C * (N : ℝ) < (k * (N : ℝ)) * (N : ℝ) :=
        mul_lt_mul_of_pos_right hLarge hNpos
      _ = _ := by dsimp [k]; ring
  apply exists_pos_eigenvalue_uncleHamiltonianES_lt_of_projection_bound
    A B R L (6 * N + 1) (v N) ε
  exact hEnergyN.trans_lt
    (hRayleigh.trans_le (mul_le_mul_of_nonneg_left hMass hε.le))

end MPSTensor
end

end
