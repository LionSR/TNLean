/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.CompactKernelGap
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
The several-block results in `CompactBlockParentGap`, applied to the
blocked source path in `IsometricDeformation`, remove this restriction;
documented in `docs/paper-gaps/spc11_uniform_gap_injective_scope.tex`.
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
    exists_hasComplementaryFixedPointGap_gauge_of_isNormal hA
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
theorem exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNBlkInjective
    [NeZero D] (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) :
    ∃ W : ℕ, p + 1 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A (p + 1) N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨B, ζ, ρ, _hζ, _hGauge, _hMPV, hP, hρ, hGS, _hPI, _hChain⟩ :=
    exists_hasComplementaryFixedPointGap_gauge_of_isNormal ⟨p, hp, hA⟩
  obtain ⟨l, hlp, hl, hInjB, ε, hε, hsmall, hDefect⟩ :=
    ((Filter.eventually_ge_atTop p).and
      (hP.eventually_openChain_groundProjection_defect_mul_sqrt_lt hρ zero_lt_one)).exists
  have hOpenB : ∀ N : ℕ, ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction B (l + 1) N).hamiltonian) μ →
        μ = 0 ∨ (((1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) ≤ μ := by
    have hsqrt : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hεlt : ε < 1 / Real.sqrt ((l + 1 : ℕ) : ℝ) :=
      (lt_div_iff₀ hsqrt).2 hsmall
    have hC3 : ∀ (K : ℕ) (hK : 0 < K),
        ‖openChainTailGroundProjectionES B K (l + 1) ∘L
          openChainMartingaleDifferenceES B K l hInjB hl.le hK‖ ≤ ε := by
      intro K hK
      rw [openChainTailGroundProjection_comp_martingaleDifference hInjB hl.le hK]
      exact hDefect K
    exact fun N => hamiltonian_parentChainInteraction_gap_of_fixedAmbient_c3 B hε hεlt
      (fun n hn => fixedAmbient_martingaleDifference_norm_le_of_openChain
        hl hInjB hε hC3 N n (Finset.mem_range.mp hn))
  have hShortKer : ∀ N, l + 1 ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (p + 1) N).hamiltonian) =
          groundSpaceES A N :=
    fun N hN => ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
      hA hp (by omega)
  have hLongKer : ∀ N, l + 1 ≤ N →
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A (l + 1) N).hamiltonian) =
          groundSpaceES A N :=
    fun N hN => ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
      (isNBlkInjective_of_le hp hA hlp) hl.le hN
  obtain ⟨κ, C, hκ, _hC, hLocal, _hUpper⟩ :=
    exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison
      A (hShortKer (l + 1) le_rfl)
  let γ : ℝ := (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2
  have hγ : 0 < γ := by
    dsimp only [γ]
    exact sq_pos_of_pos (sub_pos.mpr hsmall)
  refine ⟨l + 1, by omega, κ * γ / (l + 1 - (p + 1) + 1 : ℕ),
    div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr (by omega)), fun N hN ↦ ?_⟩
  refine toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length A _
    (posSemidef_toMatrix'_parentInteraction A (p + 1)) (by omega) hκ hγ hLocal
    (hShortKer N hN) (hLongKer N hN) ?_
  rw [parentChainInteraction_eq_of_groundSpace_eq (hGS (l + 1)) N]
  exact hOpenB N

/-- Fixed-length injectivity supplies a strict finite-range Knabe window at
range \(p+1\), without assuming a gap estimate. Source: arXiv:2011.12127,
Section IV.C, lines 2183--2187. The finite-range threshold is recorded in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`. -/
theorem exists_strict_hamiltonian_parentChainInteraction_window_of_isNBlkInjective
    [NeZero D] (A : MPSTensor d D) {p : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) :
    ∃ m : ℕ, p + 1 ≤ m ∧ ∃ γ : ℝ,
      (p : ℝ) ^ 2 < (m : ℝ) * γ ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A (p + 1) (m + p)).hamiltonian) μ →
          μ = 0 ∨ (γ : ℂ) ≤ μ := by
  obtain ⟨W, hW, δ, hδ, hGap⟩ :=
    exists_hamiltonian_parentChainInteraction_uniform_gap_of_isNBlkInjective A hp hA
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
continuous family injective at length \(p\), giving a common gap of the Hamiltonians of the
parent interaction on the rings
and a common volume threshold throughout that neighborhood. Source:
arXiv:1010.3732, Appendix A. -/
theorem eventually_hamiltonian_parentRingInteraction_gap_of_strict_openGap_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] [NeZero D] {p m : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) (hm : p + 1 ≤ m) {x₀ : X}
    {γ : ℝ} (hnum : (p : ℝ) ^ 2 < (m : ℝ) * γ)
    (hgap : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction (A x₀) (p + 1) (m + p)).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in 𝓝 x₀, ∀ (N : ℕ) (hN : 2 * m ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) (p + 1) N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hthreshold : (p : ℝ) ^ 2 / (m : ℝ) < γ :=
    (div_lt_iff₀ hmpos).2 (by simpa only [mul_comm] using hnum)
  obtain ⟨γ', hγ'lower, hγ'upper⟩ := exists_between hthreshold
  have hγpos : 0 < γ :=
    (div_pos (sq_pos_of_pos (Nat.cast_pos.mpr hp)) hmpos).trans hthreshold
  have hnear := eventually_hamiltonian_parentChainInteraction_gap A hA
    (fun x => isNBlkInjective_of_le hp (hInj x) (by omega : p ≤ p + 1))
    (fun x => isNBlkInjective_of_le hp (hInj x) (by omega : p ≤ m + p))
    hγpos hγ'upper (by
      rw [← ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
        (hInj x₀) hp (by omega)]
      exact (ManyBody.forall_hasEigenvalue_iff_norm
        (posSemidef_hamiltonian_parentChainInteraction (A x₀) (p + 1) _)).mp hgap)
  have hnum' : (((p + 1 : ℕ) : ℝ) - 1) ^ 2 < (m : ℝ) * γ' := by
    simpa [mul_comm] using (div_lt_iff₀ hmpos).1 hγ'lower
  let δ : ℝ := ((m : ℝ) * γ' - (((p + 1 : ℕ) : ℝ) - 1) ^ 2) /
    ((m : ℝ) - ((p + 1 : ℕ) : ℝ) + 1)
  refine ⟨δ, ?_, ?_⟩
  · apply div_pos (sub_pos.mpr hnum')
    have hmR : ((p + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · filter_upwards [hnear] with x hx N hN
    refine (hamiltonian_parentRingInteraction_gap_of_hamiltonian_parentChainInteraction_gap (A x)
      (R := p + 1) (m := m) (by omega) hm hnum' ?_).2 N hN
    refine (ManyBody.forall_hasEigenvalue_iff_norm
      (posSemidef_hamiltonian_parentChainInteraction (A x) (p + 1) _)).mpr ?_
    rw [show m + (p + 1) - 1 = m + p by omega,
      ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
        (hInj x) hp (by omega)]
    exact hx

/-- A continuous compact family injective at one common positive length
\(p\) has a gap of the Hamiltonians of the range-\(p+1\) parent interaction on the rings, uniform
in the parameter and all sufficiently large volumes. No finite-window gap is
assumed. Source: arXiv:1010.3732, Appendix A, single-block case. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNBlkInjective
    {X : Type*} [TopologicalSpace X] [NeZero D] {p : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) (p + 1) N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  refine hS.exists_uniform_pos_nat_bounds (fun δ N₀ x ↦ ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentRingInteraction (A x) (p + 1) N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ)
    (fun hle hgap N _ hN ↦ ManyBody.forall_hasEigenvalue_mono hle (hgap N hN))
    (fun hle hgap N _ hN ↦ hgap N (hle.trans hN)) fun x hx ↦ ?_
  obtain ⟨m, hm, γ, hnum, hgap⟩ :=
    exists_strict_hamiltonian_parentChainInteraction_window_of_isNBlkInjective (A x) hp (hInj x)
  obtain ⟨δ, hδ, hnear⟩ :=
    eventually_hamiltonian_parentRingInteraction_gap_of_strict_openGap_of_isNBlkInjective
      A hA hp hInj hm hnum hgap
  exact ⟨δ, hδ, 2 * m, hnear.mono fun y hy N _ hN ↦ hy N hN⟩

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

/-- Above a positive injectivity length \(p\), the kernel of the Hamiltonian of the parent
interaction on the ring is the range of the scalar-to-state map at every volume containing the
interaction. Source: arXiv:2011.12127, Section IV.C, lines 2078--2090. -/
theorem ker_hamiltonian_parentRingInteraction_eq_range_periodicMpvLineMap_of_isNBlkInjective
    [NeZero D] (A : MPSTensor d D) {p R N : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) (hR : p < R) (hRN : R ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    LinearMap.ker (Matrix.toEuclideanLin (parentRingInteraction A R N).hamiltonian) =
      (periodicMpvLineMap A N).range := by
  have : NeZero N := ⟨by omega⟩
  rw [← parentHamiltonianGroundSpaceES_eq_ker_hamiltonian_parentRingInteraction _ _ _,
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

/-- Above a positive injectivity length \(p\), zero is an eigenvalue of the Hamiltonian of the
parent interaction on every ring containing the interaction: the periodic vector is a nonzero
zero-energy vector. -/
theorem groundSpace_hamiltonian_parentRingInteraction_ne_bot_of_isNBlkInjective
    [NeZero D] (A : MPSTensor d D) {p R N : ℕ} (hp : 0 < p)
    (hA : Kraus.IsNBlkInjective A p) (hR : p < R) (hRN : R ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ManyBody.groundSpace (parentRingInteraction A R N).hamiltonian 0 ≠ ⊥ := by
  have : NeZero N := ⟨by omega⟩
  rw [ManyBody.groundSpace_zero,
    ker_hamiltonian_parentRingInteraction_eq_range_periodicMpvLineMap_of_isNBlkInjective
      A hp hA hR hRN]
  exact range_periodicMpvLineMap_ne_bot
    (periodicMpvLineMap_injective_of_isNBlkInjective A hp hA (by omega))

/-- For an interaction range larger than a common positive injectivity length, the projection
onto the kernel of the Hamiltonian of the parent interaction on the ring is continuous at every
fixed volume containing the interaction. Source: arXiv:1010.3732, Appendix A,
lines 2575--2578, single-block case. -/
theorem continuous_hamiltonian_parentRingInteraction_kernelProjection_family_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] [NeZero D] {p R N : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) (hR : p < R) (hRN : R ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    Continuous fun x => (LinearMap.ker
      (Matrix.toEuclideanLin (parentRingInteraction (A x) R N).hamiltonian)).starProjection := by
  have : NeZero N := ⟨by omega⟩
  have hT := continuous_periodicMpvLineMap_family A hA N
  have hTinj (x : X) : Function.Injective (periodicMpvLineMap (A x) N) :=
    periodicMpvLineMap_injective_of_isNBlkInjective (A x) hp (hInj x) (by omega)
  have hProj := ContinuousLinearMap.continuous_injectiveRangeProjector
    (fun x => periodicMpvLineMap (A x) N) hT hTinj
  have heq :
      (fun x => ContinuousLinearMap.injectiveRangeProjector
        (periodicMpvLineMap (A x) N) (hTinj x)) =
      (fun x => (LinearMap.ker (Matrix.toEuclideanLin
        (parentRingInteraction (A x) R N).hamiltonian)).starProjection) := by
    funext x
    rw [ContinuousLinearMap.injectiveRangeProjector_eq_starProjection]
    exact congrArg
      (fun K : Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) => K.starProjection)
      (ker_hamiltonian_parentRingInteraction_eq_range_periodicMpvLineMap_of_isNBlkInjective
        (A x) hp (hInj x) hR hRN).symm
  rw [← heq]
  exact hProj

/-- A compact continuous family injective at length \(p\) has a uniform positive gap of the
Hamiltonian of the parent interaction on the ring at each fixed periodic volume and interaction
range \(p<R\le N\): every member is gapped above its zero ground energy. Source:
arXiv:1010.3732, Appendix A, lines 2575--2578. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_fixed_volume_of_isNBlkInjective
    {X : Type*} [TopologicalSpace X] [NeZero D] {p R N : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) {S : Set X} (hS : IsCompact S)
    (hR : p < R) (hRN : R ≤ N) :
    haveI : NeZero N := ⟨by omega⟩;
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S,
      ManyBody.IsGapped (parentRingInteraction (A x) R N).hamiltonian 0 δ := by
  have : NeZero N := ⟨by omega⟩
  have hne (x : X) :
      ManyBody.groundSpace (parentRingInteraction (A x) R N).hamiltonian 0 ≠ ⊥ :=
    groundSpace_hamiltonian_parentRingInteraction_ne_bot_of_isNBlkInjective (A x) hp (hInj x)
      hR hRN
  suffices hnorm : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ v ∈ (LinearMap.ker
      (Matrix.toEuclideanLin (parentRingInteraction (A x) R N).hamiltonian))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (parentRingInteraction (A x) R N).hamiltonian v‖ by
    obtain ⟨δ, hδ, hgap⟩ := hnorm
    exact ⟨δ, hδ, fun x hx ↦ (ManyBody.isGapped_zero_iff_norm
      (posSemidef_hamiltonian_parentRingInteraction (A x) _ _)).mpr ⟨hne x, hgap x hx⟩⟩
  have hBlock (x : X) : Kraus.IsNBlkInjective (A x) R :=
    isNBlkInjective_of_le hp (hInj x) hR.le
  let e := (Matrix.toEuclideanCLM : Matrix (Cfg d N) (Cfg d N) ℂ ≃⋆ₐ[ℂ] _)
  have hH : Continuous fun x ↦ e (parentRingInteraction (A x) R N).hamiltonian :=
    e.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_hamiltonian_parentRingInteraction_family A hA hRN hBlock)
  have hK := continuous_hamiltonian_parentRingInteraction_kernelProjection_family_of_isNBlkInjective
    A hA hp hInj hR hRN
  simp only [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at hK ⊢
  exact ContinuousLinearMap.exists_uniform_norm_gap_of_compact
    (fun x ↦ e (parentRingInteraction (A x) R N).hamiltonian) hH hK hS

/-- A continuous compact family injective at one common positive length
\(p\) has one positive gap valid on every ring of \(N\ge p+1\) sites: the Hamiltonian of the
range-\(p+1\) parent interaction is gapped above its zero ground energy. No finite-window gap or
normalized gauge is assumed. Source: arXiv:1010.3732, Appendix A, single-block case. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNBlkInjective_all_lengths
    {X : Type*} [TopologicalSpace X] [NeZero D] {p : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ (N : ℕ) (hN : p + 1 ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped (parentRingInteraction (A x) (p + 1) N).hamiltonian 0 δ := by
  obtain ⟨δ₀, hδ₀, N₀, hlong⟩ :=
    exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNBlkInjective
      A hA hp hInj hS
  obtain ⟨δ, hδ, hgap⟩ := Nat.exists_pos_forall_of_eventually
    (P := fun N δ => ∀ hN : p + 1 ≤ N, ∀ x ∈ S, haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped (parentRingInteraction (A x) (p + 1) N).hamiltonian 0 δ)
    (fun N γ δ hle h hN x hx => (h hN x hx).mono hle)
    (fun N => by
      by_cases hN : p + 1 ≤ N
      · obtain ⟨δ, hδ, hgap⟩ :=
          exists_uniform_hamiltonian_parentRingInteraction_gap_fixed_volume_of_isNBlkInjective
            A hA hp hInj hS (by omega : p < p + 1) hN
        exact ⟨δ, hδ, fun _ => hgap⟩
      · exact ⟨1, one_pos, fun h => (hN h).elim⟩)
    hδ₀ (fun N hN hN' x hx =>
      haveI : NeZero N := ⟨by omega⟩
      ManyBody.isGapped_zero_iff.mpr
        ⟨groundSpace_hamiltonian_parentRingInteraction_ne_bot_of_isNBlkInjective (A x) hp
          (hInj x) (by omega : p < p + 1) hN', hlong x hx N hN⟩)
  exact ⟨δ, hδ, fun x hx N hN => hgap N hN x hx⟩

/-- A continuous compact family of normal tensors of fixed bond dimension
\(D>0\) has one positive gap at the common interaction
range \(D^4+1\), valid on every ring of \(N\ge D^4+1\) sites: the Hamiltonian of the parent
interaction is gapped above its zero ground energy.
The common injectivity length is supplied by the quantum Wielandt bound;
no common blocking length or finite-window gap is assumed. Source:
arXiv:1010.3732, Appendix A, single-block case; arXiv:0909.5347, Theorem 1. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNormal_all_lengths
    {X : Type*} [TopologicalSpace X] [NeZero D]
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hNormal : ∀ x, Kraus.IsNormal (A x)) {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ (N : ℕ) (hN : D ^ 4 + 1 ≤ N),
      haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped (parentRingInteraction (A x) (D ^ 4 + 1) N).hamiltonian 0 δ :=
  exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNBlkInjective_all_lengths
    A hA (pow_pos (NeZero.pos D) 4)
    (fun x => isNBlkInjective_pow_four_of_isNormal (A x) (hNormal x)) hS

/-- A compact continuous family injective at length \(p>0\) has a common
positive gap at every fixed range \(R>p\), on every ring of \(N\ge R\) sites: the Hamiltonian
of the parent interaction is gapped above its zero ground energy.
Source: arXiv:1010.3732, Appendix A, single-block case;
arXiv:0909.5347, lines 828--831. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNBlkInjective_at_range
    {X : Type*} [TopologicalSpace X] [NeZero D] {p R : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A) (hp : 0 < p)
    (hInj : ∀ x, Kraus.IsNBlkInjective (A x) p) (hR : p < R)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ (N : ℕ) (hN : R ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped (parentRingInteraction (A x) R N).hamiltonian 0 δ := by
  obtain ⟨R, rfl⟩ : ∃ q, R = q + 1 := ⟨R - 1, by omega⟩
  exact exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNBlkInjective_all_lengths
    A hA (by omega) (fun x => isNBlkInjective_of_le hp (hInj x) (by omega)) hS

/-- Every compact continuous family of normal tensors has a positive
gap at every fixed range \(R\ge D^4+1\), uniformly over the rings of \(N\ge R\) sites: the
Hamiltonian of the parent interaction is gapped above its zero ground energy.
No normalization or common injectivity length is supplied. Source:
arXiv:1010.3732, Appendix A, single-block case;
arXiv:0909.5347, lines 828--831. -/
theorem exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNormal_at_range
    {X : Type*} [TopologicalSpace X] [NeZero D] {R : ℕ}
    (A : X → MPSTensor d D) (hA : Continuous A)
    (hNormal : ∀ x, Kraus.IsNormal (A x)) (hR : D ^ 4 + 1 ≤ R)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, ∀ (N : ℕ) (hN : R ≤ N), haveI : NeZero N := ⟨by omega⟩;
      ManyBody.IsGapped (parentRingInteraction (A x) R N).hamiltonian 0 δ :=
  exists_uniform_hamiltonian_parentRingInteraction_gap_of_compact_isNBlkInjective_at_range
    A hA (pow_pos (NeZero.pos D) 4)
    (fun x => isNBlkInjective_pow_four_of_isNormal (A x) (hNormal x)) (by omega) hS

end MPSTensor
