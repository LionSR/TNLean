/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CompactKernelGap
import TNLean.MPS.CanonicalForm.SectorComparison.NormalityChain
import TNLean.MPS.ParentHamiltonian.CompactParentGap
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# Uniform gaps for compact families of normal tensors

A compact continuous family of normal tensors of fixed bond dimension
\(D>0\) has a uniform parent-Hamiltonian gap at interaction range
\(D^4+1\). A sharper common injectivity length \(p\) gives interaction
range \(p+1\). The argument first transfers the open-chain martingale
gap to this fixed interaction range, then applies a strict finite-range
Knabe window and compactness. The quantum Wielandt bound supplies
\(p=D^4\) for every normal tensor, without a normalization hypothesis.

**Scope restriction (single normal block):** arXiv:1010.3732, Appendix A,
lines 2475--2580, allows several normal blocks. This module treats one
normal block; the common injectivity length is proved rather than assumed.
The several-block result is proved separately in `CompactBlockParentGap`.
The distinction and its resolution are recorded in
`docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
-/

open scoped Topology ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A normal tensor of bond dimension \(D>0\) is injective at length
\(D^4\), without assuming a trace-preserving normalization. A nonzero
rescaling and a virtual gauge reduce to the normalized quantum Wielandt
bound, and injectivity is invariant under both operations. Source:
arXiv:0909.5347, Theorem 1; arXiv:1606.00608, line 332. -/
theorem isNBlkInjective_pow_four_of_isNormal [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsNormal A) :
    Kraus.IsNBlkInjective A (D ^ 4) := by
  obtain ⟨B, ζ, ρ, hζ, hGauge, _hMPV, hP, _hρ, _hGS, _hPI, _hChain⟩ :=
    exists_isPrimitiveMPS_gauge_of_isNormal hA
  have hNormalB : Kraus.IsNormal B :=
    isNormal_of_gaugeEquiv ((isNormal_smul_iff hζ A).2 hA) hGauge
  have hInjB : Kraus.IsNBlkInjective B (D ^ 4) :=
    isNBlkInjective_pow_four_of_isNormal_leftCanonical B hP.norm hNormalB
  exact (isNBlkInjective_smul_iff hζ A (D ^ 4)).1
    (isNBlkInjective_of_gaugeEquiv hInjB hGauge.symm)

/-- A tensor injective after \(p\) sites has a positive uniform open-chain
gap at the fixed interaction range \(p+1\), for every sufficiently long
interval. Source: arXiv:2011.12127, Section IV.C, lines 2183--2187;
arXiv:cond-mat/9410110, Section 6. -/
theorem exists_openParentHamiltonianES_uniform_gap_of_isNBlkInjective
    [NeZero D] (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) :
    ∃ W : ℕ, p + 1 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A (p + 1) N v‖ := by
  obtain ⟨B, ζ, ρ, _hζ, _hGauge, _hMPV, hP, hρ, hGS, _hPI, _hChain⟩ :=
    exists_isPrimitiveMPS_gauge_of_isNormal ⟨p, hp, hA⟩
  obtain ⟨l, hlp, hl, hInjB, ε, hε, hsmall, hDefect⟩ :=
    ((Filter.eventually_ge_atTop p).and
      (hP.eventually_openChain_groundProjection_defect_mul_sqrt_lt hρ zero_lt_one)).exists
  have hOpenB : ∀ N : ℕ, l + 1 ≤ N → ∀ v ∈ (groundSpaceES B N)ᗮ,
      (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 * ‖v‖ ≤
        ‖openParentHamiltonianES B (l + 1) N v‖ := by
    have hsqrt : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hεlt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) :=
      (lt_div_iff₀ hsqrt).2 hsmall
    have hC3 : ∀ (K : ℕ) (hK : 0 < K),
        ‖openChainTailGroundProjectionES B K (l + 1) ∘L
          openChainMartingaleDifferenceES B K l hInjB hl.le hK‖ ≤ ε := by
      intro K hK
      rw [openChainTailGroundProjection_comp_martingaleDifference hInjB hl.le hK]
      exact hDefect K
    exact fun N hN => openParentHamiltonianES_norm_gap_of_fixedAmbient_c3
      B hl.le hInjB hN hε hεlt
      (fun n hn => fixedAmbient_martingaleDifference_norm_le_of_openChain
        hl hInjB hε hC3 N n (Finset.mem_range.mp hn))
  have hShortKer : ∀ N, l + 1 ≤ N →
      LinearMap.ker (openParentHamiltonianES A (p + 1) N) = groundSpaceES A N :=
    fun N hN => ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
      hA hp (by omega)
  have hLongKer : ∀ N, l + 1 ≤ N →
      LinearMap.ker (openParentHamiltonianES A (l + 1) N) = groundSpaceES A N :=
    fun N hN => ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
      (isNBlkInjective_of_le hp hA hlp) hl.le hN
  obtain ⟨κ, C, hκ, _hC, hLocal, _hUpper⟩ :=
    exists_pos_parentInteractionES_openParentHamiltonianES_comparison
      A (hShortKer (l + 1) le_rfl)
  let γ : ℝ := (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2
  have hγ : 0 < γ := by
    dsimp only [γ]
    exact sq_pos_of_pos (sub_pos.mpr hsmall)
  have hOpenA : ∀ N : ℕ, l + 1 ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A (l + 1) N v‖ := by
    intro N hN v hv
    have hES : groundSpaceES A N = groundSpaceES B N := by
      simp only [groundSpaceES, hGS N]
    have hvB : v ∈ (groundSpaceES B N)ᗮ := by simpa only [hES] using hv
    have hB := hOpenB N hN v hvB
    rwa [← openParentHamiltonianES_eq_of_groundSpace_eq (hGS (l + 1)) N] at hB
  refine ⟨l + 1, by omega, κ * γ / (l + 1 - (p + 1) + 1 : ℕ),
    div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr (by omega)), ?_⟩
  exact openParentHamiltonianES_gap_of_long_gap A (by omega) (by omega)
    hκ hγ hLocal hShortKer hLongKer hOpenA

/-- Fixed-length injectivity supplies a strict finite-range Knabe window at
range \(p+1\), without assuming a gap estimate. Source: arXiv:2011.12127,
Section IV.C, lines 2183--2187. The finite-range threshold is recorded in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem exists_strict_openParentHamiltonianES_window_of_isNBlkInjective
    [NeZero D] (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) :
    ∃ m : ℕ, p + 1 ≤ m ∧ ∃ γ : ℝ,
      (p : ℝ) ^ 2 < (m : ℝ) * γ ∧
      ∀ v ∈ (groundSpaceES A (m + p))ᗮ,
        γ * ‖v‖ ≤ ‖openParentHamiltonianES A (p + 1) (m + p) v‖ := by
  obtain ⟨W, hW, δ, hδ, hGap⟩ :=
    exists_openParentHamiltonianES_uniform_gap_of_isNBlkInjective A hp hA
  obtain ⟨n, hn⟩ := exists_lt_nsmul hδ ((p : ℝ) ^ 2)
  let m := n + W
  have hm : p + 1 ≤ m := by dsimp only [m]; omega
  have hnum : (p : ℝ) ^ 2 < (m : ℝ) * δ := by
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by dsimp only [m]; omega : n ≤ m)
    calc
      (p : ℝ) ^ 2 < n • δ := hn
      _ = (n : ℝ) * δ := by simp [nsmul_eq_mul]
      _ ≤ (m : ℝ) * δ := mul_le_mul_of_nonneg_right hnm hδ.le
  exact ⟨m, hm, δ, hnum, hGap (m + p) (by dsimp only [m]; omega)⟩

/-- A strict range-\(p+1\) Knabe window persists near one parameter of a
continuous family injective at length \(p\), giving a common periodic gap
and a common volume threshold throughout that neighborhood. Source:
arXiv:1010.3732, Appendix A. -/
theorem eventually_parentHamiltonianES_gap_of_strict_openGap_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] [NeZero D] {p m : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) (hm : p + 1 ≤ m) {x₀ : X}
    {γ : ℝ} (hnum : (p : ℝ) ^ 2 < (m : ℝ) * γ)
    (hgap : ∀ v ∈ (groundSpaceES (A x₀) (m + p))ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES (A x₀) (p + 1) (m + p) v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 x₀, ∀ N : ℕ, 2 * m ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) (p + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) (p + 1) N v‖ := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : (p : ℝ) ^ 2 / (m : ℝ) < γ :=
    (div_lt_iff₀ hmpos).2 (by simpa only [mul_comm] using hnum)
  obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between hthreshold
  have hγpos : 0 < γ :=
    (div_pos (sq_pos_of_pos (Nat.cast_pos.mpr hp)) hmpos).trans hthreshold
  have hnear := eventually_openParentHamiltonianES_gap A hA (by omega : p + 1 ≤ m + p)
    (fun x => isNBlkInjective_of_le hp (hInj x) (by omega : p ≤ p + 1))
    (fun x => isNBlkInjective_of_le hp (hInj x) (by omega : p ≤ m + p))
    hγpos hγ'upper hgap
  have hnum' : (((p + 1 : ℕ) : ℝ) - 1) ^ 2 < (m : ℝ) * γ' := by
    simpa [mul_comm] using (div_lt_iff₀ hmpos).1 hγ'lower
  let δ := ((m : ℝ) * γ' - (((p + 1 : ℕ) : ℝ) - 1) ^ 2) /
    ((m : ℝ) - ((p + 1 : ℕ) : ℝ) + 1)
  refine ⟨δ, ?_, ?_⟩
  · apply div_pos (sub_pos.mpr hnum')
    have hmR : ((p + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · filter_upwards [hnear] with x hx
    apply (parentHamiltonianES_gap_of_openParentHamiltonianES_gap (A x)
      (R := p + 1) (m := m) (by omega) hm hnum' ?_).2
    rw [show m + (p + 1) - 1 = m + p by omega,
      ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        (hInj x) hp (by omega)]
    exact hx

/-- A continuous compact family injective at one common positive length
\(p\) has a range-\(p+1\) periodic parent-Hamiltonian gap uniform in the
parameter and all sufficiently large volumes. No finite-window gap is
assumed. Source: arXiv:1010.3732, Appendix A, single-block case. -/
theorem exists_uniform_parentHamiltonianES_gap_of_compact_isNBlkInjective
    {X : Type*} [TopologicalSpace X] [NeZero D] {p : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) (p + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) (p + 1) N v‖ := by
  apply hS.exists_uniform_pos_nat_bounds
    (fun δ N₀ x => ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) (p + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) (p + 1) N v‖)
  · intro δ δ' N₀ x hle hgap N hN v hv
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap N hN v hv)
  · intro δ N₀ N₁ x hle hgap N hN
    exact hgap N (hle.trans hN)
  · intro x hx
    obtain ⟨m, hm, γ, hnum, hgap⟩ :=
      exists_strict_openParentHamiltonianES_window_of_isNBlkInjective (A x) hp (hInj x)
    obtain ⟨δ, hδ, hnear⟩ :=
      eventually_parentHamiltonianES_gap_of_strict_openGap_of_isNBlkInjective
        A hA hp hInj hm hnum hgap
    exact ⟨δ, hδ, 2 * m, hnear⟩

/-- Injectivity at length \(p\) makes the scalar-to-state map injective
at every periodic length \(N\ge p+1\). Source: arXiv:quant-ph/0608197,
Theorem `uniqueGS`, nonvanishing of the periodic ground vector. -/
theorem periodicMpvLineMap_injective_of_isNBlkInjective
    [NeZero D] (A : MPSTensor d D) {p N : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) (hN : p + 1 ≤ N) :
    Function.Injective (periodicMpvLineMap A N) := by
  have hψ : (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A) ≠ 0 := by
    intro hzero
    have h := congrArg (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)) hzero
    have hmpv : (mpv A : NSiteSpace d N) ≠ 0 :=
      mpv_ne_zero_of_isNBlkInjective hA hp hN
    exact hmpv (by simpa using h)
  intro c c' hcc
  have hsmul : (c - c') •
      (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A) = 0 := by
    simpa [periodicMpvLineMap, sub_smul] using
      congrArg (fun v => v - periodicMpvLineMap A N c') hcc
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hψ)

/-- Above a positive injectivity length \(p\), the periodic parent kernel
is the range of the scalar-to-state map at every volume containing the
interaction. Source: arXiv:2011.12127, Section IV.C, lines 2078--2090. -/
theorem ker_parentHamiltonianES_eq_range_periodicMpvLineMap_of_isNBlkInjective
    [NeZero D] (A : MPSTensor d D) {p R N : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) (hR : p < R) (hRN : R ≤ N) :
    LinearMap.ker (parentHamiltonianES A R N) =
      (periodicMpvLineMap A N).range := by
  rw [← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES,
    parentHamiltonianGroundSpaceES,
    ker_parentHamiltonian_eq_chainGroundSpace A (by omega : 0 < N) hRN,
    chainGroundSpace_eq_mpvSubmodule_normal ⟨p, hp, hA⟩ hA hp
      (by omega : 2 ≤ N) hR hRN (by omega : p + 1 ≤ N)]
  simp only [mpvSubmodule, periodicMpvLineMap]
  rw [Submodule.map_span]
  simp only [Set.image_singleton]
  change (ℂ ∙ ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A))) = _
  exact
    (ContinuousLinearMap.range_smulRight_apply
      (by norm_num : (1 : ℂ →L[ℂ] ℂ) ≠ 0)
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm (mpv A))).symm

/-- For an interaction range larger than a common positive injectivity
length, the periodic ground-line projection is continuous at every fixed
volume containing the interaction. Source: arXiv:1010.3732, Appendix A,
lines 2575--2578, single-block case. -/
theorem continuous_parentHamiltonianES_kernelProjection_family_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] [NeZero D] {p R N : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) (hR : p < R) (hRN : R ≤ N) :
    Continuous fun x =>
      (LinearMap.ker (parentHamiltonianES (A x) R N)).starProjection := by
  have hT := continuous_periodicMpvLineMap_family A hA N
  have hTinj (x : X) : Function.Injective (periodicMpvLineMap (A x) N) :=
    periodicMpvLineMap_injective_of_isNBlkInjective (A x) hp (hInj x) (by omega)
  have hProj := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun x => periodicMpvLineMap (A x) N) hT hTinj
  have heq :
      (fun x => ContinuousLinearMap.injectiveRangeProjector
        (periodicMpvLineMap (A x) N) (hTinj x)) =
      (fun x => (LinearMap.ker (parentHamiltonianES (A x) R N)).starProjection) := by
    funext x
    rw [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection]
    exact congrArg
      (fun K : Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) => K.starProjection)
      (ker_parentHamiltonianES_eq_range_periodicMpvLineMap_of_isNBlkInjective
        (A x) hp (hInj x) hR hRN).symm
  rw [← heq]
  exact hProj

/-- A compact continuous family injective at length \(p\) has a uniform
positive gap at each fixed periodic volume and interaction range
\(p<R\le N\). Source: arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem exists_uniform_parentHamiltonianES_gap_fixed_volume_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] [NeZero D] {p R N : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) {S : Set X} (hS : IsCompact S)
    (hR : p < R) (hRN : R ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) R N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) R N v‖ := by
  have hBlock (x : X) : Kraus.IsNBlkInjective (A x) R :=
    isNBlkInjective_of_le hp (hInj x) hR.le
  have hH := continuous_parentHamiltonianES_family A hA hRN hBlock
  have hK := continuous_parentHamiltonianES_kernelProjection_family_of_isNBlkInjective
    A hA hp hInj hR hRN
  exact ContinuousLinearMap.exists_uniform_norm_gap_of_compact
    (fun x => LinearMap.toContinuousLinearMap (parentHamiltonianES (A x) R N)) hH hK hS

/-- A continuous compact family injective at one common positive length
\(p\) has one positive range-\(p+1\) parent-Hamiltonian gap valid for every
periodic chain with \(N\ge p+1\). No finite-window gap or normalized
gauge is assumed. Source: arXiv:1010.3732, Appendix A, single-block case. -/
theorem exists_uniform_parentHamiltonianES_gap_of_compact_isNBlkInjective_all_lengths
    {X : Type*} [TopologicalSpace X] [NeZero D] {p : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ N : ℕ, p + 1 ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) (p + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) (p + 1) N v‖ := by
  obtain ⟨δ₀, hδ₀, N₀, hlong⟩ :=
    exists_uniform_parentHamiltonianES_gap_of_compact_isNBlkInjective A hA hp hInj hS
  obtain ⟨δ, hδ, hgap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ => p + 1 ≤ N → ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) (p + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) (p + 1) N v‖)
    (fun N γ δ hle h hN x hx v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (h hN x hx v hv))
    (fun N => by
      by_cases hN : p + 1 ≤ N
      · obtain ⟨δ, hδ, hgap⟩ :=
          exists_uniform_parentHamiltonianES_gap_fixed_volume_of_isNBlkInjective
            A hA hp hInj hS (by omega : p < p + 1) hN
        exact ⟨δ, hδ, fun _ => hgap⟩
      · exact ⟨1, one_pos, fun h => (hN h).elim⟩)
    hδ₀ (fun N hN _ x hx => hlong x hx N hN)
  exact ⟨δ, hδ, fun x hx N hN => hgap N hN x hx⟩

/-- A continuous compact family of normal tensors of fixed bond dimension
\(D>0\) has one positive parent-Hamiltonian gap at the common interaction
range \(D^4+1\), valid for every periodic length \(N\ge D^4+1\).
The common injectivity length is supplied by the quantum Wielandt bound;
no common blocking length or finite-window gap is assumed. Source:
arXiv:1010.3732, Appendix A, single-block case; arXiv:0909.5347, Theorem 1. -/
theorem exists_uniform_parentHamiltonianES_gap_of_compact_isNormal_all_lengths
    {X : Type*} [TopologicalSpace X] [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hNormal : ∀ x, Kraus.IsNormal (A x)) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ N : ℕ, D ^ 4 + 1 ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) (D ^ 4 + 1) N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) (D ^ 4 + 1) N v‖ :=
  exists_uniform_parentHamiltonianES_gap_of_compact_isNBlkInjective_all_lengths
    A hA (pow_pos (NeZero.pos D) 4)
    (fun x => isNBlkInjective_pow_four_of_isNormal (A x) (hNormal x)) hS

/-- A compact continuous family injective at length \(p>0\) has a common
positive periodic gap at every fixed range \(R>p\), for all \(N\ge R\).
Source: arXiv:1010.3732, Appendix A, single-block case;
arXiv:0909.5347, lines 828--831. -/
theorem exists_uniform_parentHamiltonianES_gap_of_compact_isNBlkInjective_at_range
    {X : Type*} [TopologicalSpace X] [NeZero D] {p R : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) (hR : p < R)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) R N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) R N v‖ := by
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ R)] using
    exists_uniform_parentHamiltonianES_gap_of_compact_isNBlkInjective_all_lengths
      A hA (by omega : 0 < R - 1)
      (fun x => isNBlkInjective_of_le hp (hInj x) (by omega : p ≤ R - 1)) hS

/-- Every compact continuous family of normal tensors has a positive periodic
gap at every fixed range \(R\ge D^4+1\), uniformly over all \(N\ge R\).
No normalization or common injectivity length is supplied. Source:
arXiv:1010.3732, Appendix A, single-block case;
arXiv:0909.5347, lines 828--831. -/
theorem exists_uniform_parentHamiltonianES_gap_of_compact_isNormal_at_range
    {X : Type*} [TopologicalSpace X] [NeZero D] {R : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hNormal : ∀ x, Kraus.IsNormal (A x)) (hR : D ^ 4 + 1 ≤ R)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ N : ℕ, R ≤ N →
      ∀ v ∈ (LinearMap.ker (parentHamiltonianES (A x) R N))ᗮ,
        δ * ‖v‖ ≤ ‖parentHamiltonianES (A x) R N v‖ :=
  exists_uniform_parentHamiltonianES_gap_of_compact_isNBlkInjective_at_range
    A hA (pow_pos (NeZero.pos D) 4)
    (fun x => isNBlkInjective_pow_four_of_isNormal (A x) (hNormal x)) (by omega) hS

end MPSTensor
