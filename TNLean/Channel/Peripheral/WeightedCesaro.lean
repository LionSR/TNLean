/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Peripheral.CesaroRecurrence
import TNLean.Analysis.WeightedCesaroMean

/-!
# The phase-weighted Cesàro formula for `T_φ` — Wolf Equation (6.15)

For a positive trace-preserving linear map `T` on `M_d(ℂ)` the peripheral
spectral projection `T_φ` of Wolf Equation (6.12) is the limit of the averages
$$
  \frac{1}{N}\sum_{n=1}^{N}\ \sum_{k\,:\,|\lambda_k| = 1} (\bar\lambda_k T)^n ,
$$
the inner sum running over the peripheral spectrum of `T`.

The argument splits the space along the complementary pair of spectral
subspaces of Wolf Equation (6.5).  On the peripheral part, Wolf
Proposition 6.2 makes the peripheral generalized eigenspaces ordinary
eigenspaces, so on the `λ_j`-eigenspace the summand `(\bar\lambda_k T)^n` acts
as the scalar `(\bar\lambda_k\lambda_j)^n`; the ratio has modulus one and
equals `1` exactly when `λ_k = λ_j`, so the averages converge to `1` by the
finite geometric sum.  On the non-peripheral part every eigenvalue has modulus
strictly below one, the powers `T^n` already tend to zero, and multiplying by
unit phases leaves the norms unchanged, so the averages tend to zero as well.

## Main definitions

* `Module.End.weightedCesaroMean`: the average
  `(1/N) ∑_{n=1}^{N} ∑_{μ ∈ s} (conj μ • f)^n`.

## Main statements

* `Module.End.tendsto_weightedCesaroMean_apply_self_of_mem_iSup_eigenspace`:
  the averages fix the span of the eigenspaces indexed by the averaging set.
* `Module.End.tendsto_weightedCesaroMean_apply_zero_of_tendsto_pow_zero`: the
  averages vanish wherever the powers already vanish.
* `IsPositiveMap.tendsto_weightedCesaroMean_peripheralProjection`: **Wolf
  Equation (6.15)** — the averages over the peripheral spectrum converge
  pointwise to `T_φ`.
* `IsPositiveMap.tendsto_endEquiv_weightedCesaroMean_peripheralProjection`:
  the same convergence in the operator norm.
* `IsPositiveMap.tendsto_weightedCesaroMean_toFinset_peripheralProjection`:
  **Wolf Equation (6.15)** with the peripheral spectrum enumerated by its own
  finiteness proof, pointwise.
* `IsPositiveMap.tendsto_endEquiv_weightedCesaroMean_toFinset_peripheralProjection`:
  the same convergence in the operator norm, with the peripheral spectrum
  enumerated by its own finiteness proof.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Equation (6.15);
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
  lines 258--264.
-/

open Filter Topology

namespace Module.End

section Definition

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The **phase-weighted Cesàro mean** of an endomorphism `f` over a finite set
`s` of phases:
`(1/N) ∑_{n=1}^{N} ∑_{μ ∈ s} (conj μ • f)^n`.

Taking `s` to be the peripheral spectrum of `f` gives the averages of Wolf
Equation (6.15); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 258--264. -/
noncomputable def weightedCesaroMean (f : Module.End ℂ V) (s : Finset ℂ) (N : ℕ) :
    Module.End ℂ V :=
  (N : ℂ)⁻¹ • ∑ n ∈ Finset.Icc 1 N, ∑ μ ∈ s, ((starRingEnd ℂ) μ • f) ^ n

@[simp]
theorem weightedCesaroMean_apply (f : Module.End ℂ V) (s : Finset ℂ) (N : ℕ) (x : V) :
    f.weightedCesaroMean s N x =
      (N : ℂ)⁻¹ • ∑ n ∈ Finset.Icc 1 N, ∑ μ ∈ s, (((starRingEnd ℂ) μ • f) ^ n) x := by
  simp [weightedCesaroMean]

/-- On the `μ`-eigenspace the `n`-th power acts as the scalar `μ ^ n`. -/
private theorem pow_apply_of_mem_eigenspace {f : Module.End ℂ V} {μ : ℂ} {x : V}
    (hx : x ∈ f.eigenspace μ) (n : ℕ) : (f ^ n) x = μ ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change f ((f ^ n) x) = _
      rw [ih, map_smul, Module.End.mem_eigenspace_iff.mp hx, smul_smul, pow_succ]

end Definition

section Convergence

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- **The phase-weighted averages fix the peripheral eigenvectors.**  If every
element of `s` has modulus one, then on the span of the eigenspaces indexed by
`s` the averages `(1/N) ∑_{n=1}^{N} ∑_{μ ∈ s} (conj μ • f)^n` converge to the
identity: on the `λ`-eigenspace the summand indexed by `μ` is the scalar
`(conj μ * λ)^n`, and only `μ = λ` contributes in the limit. -/
theorem tendsto_weightedCesaroMean_apply_self_of_mem_iSup_eigenspace
    {f : Module.End ℂ V} {s : Finset ℂ} (hs : ∀ μ ∈ s, ‖μ‖ = 1) {x : V}
    (hx : x ∈ ⨆ μ ∈ s, f.eigenspace μ) :
    Tendsto (fun N : ℕ ↦ f.weightedCesaroMean s N x) atTop (𝓝 x) := by
  classical
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).mp hx
  rw [← hv]
  have hterm : ∀ lam ∈ s,
      Tendsto (fun N : ℕ ↦ f.weightedCesaroMean s N (v lam : V)) atTop (𝓝 (v lam : V)) := by
    intro lam hlam
    have hkey : ∀ N : ℕ, f.weightedCesaroMean s N (v lam : V) =
        ((N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
          ∑ μ ∈ s, ((starRingEnd ℂ) μ * lam) ^ n) • (v lam : V) := by
      intro N
      rw [weightedCesaroMean_apply, mul_smul]
      congr 1
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [smul_pow, LinearMap.smul_apply, pow_apply_of_mem_eigenspace (v lam).2,
        smul_smul, ← mul_pow]
    have hlim := (WeightedCesaro.tendsto_cesaro_phase_sum hs hlam).smul
      (tendsto_const_nhds (x := (v lam : V)) (f := atTop (α := ℕ)))
    rw [one_smul] at hlim
    exact hlim.congr fun N ↦ (hkey N).symm
  simpa only [map_sum] using tendsto_finsetSum _ hterm

/-- **The phase-weighted averages vanish where the powers vanish.**  Unit
phases do not change norms, so if `f ^ n x → 0` then every summand of the
average tends to zero, and so does the average. -/
theorem tendsto_weightedCesaroMean_apply_zero_of_tendsto_pow_zero
    {f : Module.End ℂ V} {s : Finset ℂ} (hs : ∀ μ ∈ s, ‖μ‖ = 1) {x : V}
    (hx : Tendsto (fun n : ℕ ↦ (f ^ n) x) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ f.weightedCesaroMean s N x) atTop (𝓝 0) := by
  classical
  have hterm : ∀ μ ∈ s,
      Tendsto (fun n : ℕ ↦ (((starRingEnd ℂ) μ • f) ^ n) x) atTop (𝓝 0) := by
    intro μ hμ
    have hnorm : ∀ n : ℕ, ‖(((starRingEnd ℂ) μ • f) ^ n) x‖ = ‖(f ^ n) x‖ := by
      intro n
      rw [smul_pow, LinearMap.smul_apply, norm_smul, norm_pow, RCLike.norm_conj, hs μ hμ,
        one_pow, one_mul]
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simpa only [hnorm] using tendsto_zero_iff_norm_tendsto_zero.mp hx
  have hsum : Tendsto (fun n : ℕ ↦ ∑ μ ∈ s, (((starRingEnd ℂ) μ • f) ^ n) x) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum _ hterm
  simpa only [weightedCesaroMean_apply] using WeightedCesaro.tendsto_cesaro_zero hsum

end Convergence

end Module.End

namespace IsPositiveMap

open scoped Matrix.Norms.Frobenius

variable {D : ℕ} [NeZero D] {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}

/-- **Wolf Equation (6.15).**  For a positive trace-preserving map `T` on
`M_d(ℂ)` the peripheral spectral projection `T_φ` is the limit of the
phase-weighted averages over the peripheral spectrum,
`T_φ = lim_N (1/N) ∑_{n=1}^{N} ∑_{k : |λ_k| = 1} (conj λ_k • T)^n`.

Source: Wolf, Equation (6.15); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 258--264. -/
theorem tendsto_weightedCesaroMean_peripheralProjection
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) {s : Finset ℂ}
    (hs : (s : Set ℂ) = peripheralEigenvalues T) (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun N : ℕ ↦ T.weightedCesaroMean s N X) atTop
      (𝓝 (T.peripheralProjection X)) := by
  have hnorm : ∀ μ ∈ s, ‖μ‖ = 1 := fun μ hμ ↦
    (hs ▸ (Finset.mem_coe.mpr hμ) : μ ∈ peripheralEigenvalues T).2
  -- The peripheral part: `T_φ X` lies in the span of the peripheral eigenspaces
  -- (Wolf Proposition 6.2), where the averages act as the identity.
  have hPmem : T.peripheralProjection X ∈ ⨆ μ ∈ s, T.eigenspace μ := by
    have h1 := T.peripheralProjection_apply_mem X
    rw [hPos.peripheralSubspace_eq_iSup_eigenspace hTP, ← hs] at h1
    simpa only [Finset.mem_coe] using h1
  have hper := T.tendsto_weightedCesaroMean_apply_self_of_mem_iSup_eigenspace hnorm hPmem
  -- The non-peripheral part: the powers already vanish there.
  have hb : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ ≤ 1 := fun μ hμ ↦
    (hPos.hasBoundedOrbits_of_tracePreserving hTP).norm_le_one_of_hasEigenvalue hμ
  have hnonp := T.tendsto_weightedCesaroMean_apply_zero_of_tendsto_pow_zero hnorm
    (T.tendsto_pow_apply_zero_of_mem_nonPeripheralSubspace hb
      (T.sub_peripheralProjection_mem X))
  -- Combine along `X = T_φ X + (X - T_φ X)`.
  have hsum := hper.add hnonp
  rw [add_zero] at hsum
  exact hsum.congr fun N ↦ by rw [← map_add, add_sub_cancel]

/-- **Wolf Equation (6.15), operator-norm form.**  The phase-weighted averages
over the peripheral spectrum converge to `T_φ` in the operator norm. -/
theorem tendsto_endEquiv_weightedCesaroMean_peripheralProjection
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) {s : Finset ℂ}
    (hs : (s : Set ℂ) = peripheralEigenvalues T) :
    Tendsto (fun N : ℕ ↦ endEquiv (T.weightedCesaroMean s N)) atTop
      (𝓝 (endEquiv T.peripheralProjection)) :=
  ContinuousLinearMap.tendsto_of_tendsto_apply_of_finiteDimensional fun X ↦
    hPos.tendsto_weightedCesaroMean_peripheralProjection hTP hs X

/-- **Wolf Equation (6.15)** with the peripheral spectrum enumerated by its own
finiteness proof.

**Local fix (distinct phases):** the inner sum of Wolf Equation (6.15) is
printed over `k : |λ_k| = 1` with `k` indexing the Jordan blocks of
Equations (6.4)--(6.5) of the source, where several blocks may share an
eigenvalue.  The summand `(conj λ_k • T)^n` depends only on the eigenvalue
`λ_k`, so a literal block-indexed reading counts each peripheral phase with
its geometric multiplicity, and the identity channel on `M_D(ℂ)` with `D > 1`
would converge to `D ^ 2 • id` instead of `T_φ`.  This theorem reads `k` as
indexing the distinct peripheral eigenvalues, each phase counted once.  See
`docs/paper-gaps/wolf_ch6_eq615_deduplicated_phases.tex`. -/
theorem tendsto_weightedCesaroMean_toFinset_peripheralProjection
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Tendsto (fun N : ℕ ↦
        T.weightedCesaroMean (peripheralEigenvalues_finite T).toFinset N X) atTop
      (𝓝 (T.peripheralProjection X)) :=
  hPos.tendsto_weightedCesaroMean_peripheralProjection hTP
    (Set.Finite.coe_toFinset _) X

/-- **Wolf Equation (6.15), operator-norm form.**  The phase-weighted averages
over the distinct peripheral eigenvalues, each phase counted once, converge to
`T_φ` in the operator norm.

Source: Wolf, Equation (6.15); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 258--264.

**Local fix (distinct phases):** as in
`IsPositiveMap.tendsto_weightedCesaroMean_toFinset_peripheralProjection`, the
averages count each distinct peripheral eigenvalue once; see
`docs/paper-gaps/wolf_ch6_eq615_deduplicated_phases.tex`. -/
theorem tendsto_endEquiv_weightedCesaroMean_toFinset_peripheralProjection
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    Tendsto (fun N : ℕ ↦
        endEquiv (T.weightedCesaroMean (peripheralEigenvalues_finite T).toFinset N)) atTop
      (𝓝 (endEquiv T.peripheralProjection)) :=
  hPos.tendsto_endEquiv_weightedCesaroMean_peripheralProjection hTP
    (Set.Finite.coe_toFinset _)

end IsPositiveMap
