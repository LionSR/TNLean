/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.CyclicWindowOpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteIntervalGapComparison
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorOrder
import TNLean.MPS.ParentHamiltonian.PrimitiveGaugeExistence

/-!
# Comparison of parent interactions on open chains

A comparison on one finite interval can be inserted into every nonwrapping
interval of a longer open chain. Summing these comparisons controls the
longer-range open parent Hamiltonian by the shorter-range one. This is the
open-boundary counterpart of the periodic comparison used in the finite-range
gap argument.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

private def suffixStartEquiv {R W N n : ℕ} (hR : 0 < R) (_hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) :
    NonwrappingStart R W ≃
      {i : NonwrappingStart R N // n - W ≤ i.1.val ∧ i.1.val + R ≤ n} where
  toFun q := by
    have hq : q.1.val + R ≤ W := q.2
    refine ⟨⟨⟨n - W + q.1.val, by omega⟩, by
      change n - W + q.1.val + R ≤ N
      omega⟩, by
      change n - W ≤ n - W + q.1.val ∧ n - W + q.1.val + R ≤ n
      omega⟩
  invFun i := by
    have hi : n - W ≤ i.1.1.val ∧ i.1.1.val + R ≤ n := i.2
    refine ⟨⟨i.1.1.val - (n - W), by omega⟩, by
      change i.1.1.val - (n - W) + R ≤ W
      omega⟩
  left_inv q := by
    apply Subtype.ext
    apply Fin.ext
    have hq := q.2
    simp only
    omega
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    have hi := i.2
    simp only
    omega

/-- A nonwrapping suffix interval, viewed in cyclic active-block coordinates,
is the same Hamiltonian on the active interval acting independently of all
spectator coordinates. -/
theorem openSuffixParentHamiltonianES_conj_cyclicActiveBlock
    (A : MPSTensor d D) {R W N n : ℕ} (hR : 0 < R) (hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) :
    let s : Fin N := ⟨n - W, by omega⟩
    let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega : W ≤ N) s
    U.toLinearEquiv.toLinearMap.comp
      ((openSuffixParentHamiltonianES A R W N n).comp
        U.symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (openParentHamiltonianES A R W))).toLinearMap := by
  classical
  dsimp only
  let s : Fin N := ⟨n - W, by omega⟩
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega : W ≤ N) s
  let e := suffixStartEquiv hR hRW hWn hnN
  have hsum : openSuffixParentHamiltonianES A R W N n =
      ∑ i : {i : NonwrappingStart R N // n - W ≤ i.1.val ∧ i.1.val + R ≤ n},
        localTermES A R i.1.1 := by
    rw [openSuffixParentHamiltonianES]
    exact Finset.sum_subtype _ (fun i => by simp) _
  rw [hsum]
  apply LinearMap.ext
  intro x
  simp only [openParentHamiltonianES, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    ContinuousLinearMap.rightFiberwiseMap_sum]
  calc
    (∑ i : {i : NonwrappingStart R N // n - W ≤ i.1.val ∧ i.1.val + R ≤ n},
        U (localTermES A R i.1.1 (U.symm x))) =
      ∑ q : NonwrappingStart R W,
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
          (LinearMap.toContinuousLinearMap (localTermES A R q.1)) x := by
        apply Fintype.sum_equiv e.symm
        intro i
        have hstart : i.1.1 = cyclicForwardSite s (e.symm i).1.val := by
          apply Fin.ext
          have hi := i.2
          simp only [cyclicForwardSite, Fin.val_mk, s]
          rw [Nat.mod_eq_of_lt (by omega : n - W + (e.symm i).1.val < N)]
          change i.1.1.val = n - W + (i.1.1.val - (n - W))
          omega
        rw [hstart]
        exact LinearMap.congr_fun
          (localTermES_conj_cyclicActiveBlockConfigLinearIsometryEquiv A
            (by omega : W ≤ N) s (e.symm i).1 (e.symm i).2) x
    _ = (∑ q : NonwrappingStart R W,
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
          (LinearMap.toContinuousLinearMap (localTermES A R q.1))) x := by
      simp

/-- A comparison between the long parent projection and the short-range
Hamiltonian on one interval holds on every nonwrapping interval of that
length in an open chain. -/
theorem openSuffixParentHamiltonianES_comparison_of_local
    (A : MPSTensor d D) {R W N n : ℕ} (hR : 0 < R) (hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) {κ : ℝ}
    (hLocal : (κ : ℂ) • parentInteractionES A W ≤
      openParentHamiltonianES A R W) :
    (κ : ℂ) • openSuffixParentHamiltonianES A W W N n ≤
      openSuffixParentHamiltonianES A R W N n := by
  let s : Fin N := ⟨n - W, by omega⟩
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega : W ≤ N) s
  have hShort : U.toLinearEquiv.conj (openSuffixParentHamiltonianES A R W N n) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (openParentHamiltonianES A R W))).toLinearMap := by
    simpa only [U, LinearEquiv.conj_apply, LinearMap.comp_assoc] using!
      openSuffixParentHamiltonianES_conj_cyclicActiveBlock A hR hRW hWn hnN
  have hLong : U.toLinearEquiv.conj (openSuffixParentHamiltonianES A W W N n) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (parentInteractionES A W))).toLinearMap := by
    simpa only [U, LinearEquiv.conj_apply, LinearMap.comp_assoc,
      openParentHamiltonianES_self_eq_parentInteractionES A (by omega : 0 < W)] using!
      openSuffixParentHamiltonianES_conj_cyclicActiveBlock A
        (by omega : 0 < W) le_rfl hWn hnN
  refine (U.conj_le_conj_iff _ _).mp ?_
  simpa only [map_smul, hLong, hShort, ContinuousLinearMap.rightFiberwiseMap_smul,
    ContinuousLinearMap.toLinearMap_smul] using
    (ContinuousLinearMap.rightFiberwiseMap_mono (S := Cfg d (N - W))
      (G := LinearMap.toContinuousLinearMap ((κ : ℂ) • parentInteractionES A W))
      (H := LinearMap.toContinuousLinearMap (openParentHamiltonianES A R W)) hLocal)

/-- Summing all complete suffix windows of length \(W\) counts every range-\(W\)
open-chain parent term exactly once. -/
theorem sum_openSuffixParentHamiltonianES_full_window
    (A : MPSTensor d D) {W N : ℕ} (hW : 0 < W) :
    ∑ n ∈ Finset.Icc W N, openSuffixParentHamiltonianES A W W N n =
      openParentHamiltonianES A W N := by
  classical
  have hSuffix (n : ℕ) (hn : n ∈ Finset.Icc W N) :
      openSuffixParentHamiltonianES A W W N n =
        localTermES A W (⟨n - W, by
          have := Finset.mem_Icc.mp hn
          omega⟩ : Fin N) := by
    have hnBounds := Finset.mem_Icc.mp hn
    let i : NonwrappingStart W N := ⟨⟨n - W, by omega⟩, by
      change n - W + W ≤ N
      omega⟩
    have hfilter :
        Finset.univ.filter (fun j : NonwrappingStart W N =>
          n - W ≤ j.1.val ∧ j.1.val + W ≤ n) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hj
        apply Subtype.ext
        apply Fin.ext
        change j.1.val = n - W
        omega
      · intro hji
        subst j
        change n - W ≤ n - W ∧ n - W + W ≤ n
        omega
    rw [openSuffixParentHamiltonianES, hfilter, Finset.sum_singleton]
  rw [openParentHamiltonianES]
  apply Finset.sum_bij (fun n hn =>
    (⟨⟨n - W, by
      have hnBounds := Finset.mem_Icc.mp hn
      omega⟩, by
      have hnBounds := Finset.mem_Icc.mp hn
      change n - W + W ≤ N
      omega⟩ : NonwrappingStart W N))
  · intro n hn
    exact Finset.mem_univ _
  · intro n₁ hn₁ n₂ hn₂ h
    have hval := congrArg (fun i : NonwrappingStart W N => i.1.val) h
    simp only at hval
    have hn₁ := Finset.mem_Icc.mp hn₁
    have hn₂ := Finset.mem_Icc.mp hn₂
    omega
  · intro i _
    refine ⟨i.1.val + W, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      have hi := i.2
      omega
    · apply Subtype.ext
      apply Fin.ext
      simp only
      omega
  · intro n hn
    rw [hSuffix n hn]

/-- A positive comparison on one window bounds the longer-range open-chain
Hamiltonian by the shorter-range one at every volume. Each short-range term
belongs to at most \(W - R + 1\) windows. -/
theorem openParentHamiltonianES_comparison_of_local
    (A : MPSTensor d D) {R W N : ℕ} (hR : 0 < R) (hRW : R ≤ W)
    (_hWN : W ≤ N) {κ : ℝ}
    (hLocal : (κ : ℂ) • parentInteractionES A W ≤
      openParentHamiltonianES A R W) :
    (κ : ℂ) • openParentHamiltonianES A W N ≤
      ((W - R + 1 : ℕ) : ℂ) • openParentHamiltonianES A R N := by
  calc
    (κ : ℂ) • openParentHamiltonianES A W N =
        (κ : ℂ) • ∑ n ∈ Finset.Icc W N,
          openSuffixParentHamiltonianES A W W N n := by
          rw [sum_openSuffixParentHamiltonianES_full_window A (by omega : 0 < W)]
    _ = ∑ n ∈ Finset.Icc W N,
          (κ : ℂ) • openSuffixParentHamiltonianES A W W N n := by
          rw [Finset.smul_sum]
    _ ≤ ∑ n ∈ Finset.Icc W N,
          openSuffixParentHamiltonianES A R W N n := by
          apply Finset.sum_le_sum
          intro n hn
          have hBounds := Finset.mem_Icc.mp hn
          exact openSuffixParentHamiltonianES_comparison_of_local A hR hRW
            hBounds.1 hBounds.2 hLocal
    _ ≤ ((W - R + 1 : ℕ) : ℂ) • openParentHamiltonianES A R N :=
          (openParentHamiltonianES_C1 A hRW).2

/-- A positive comparison on one interval transfers the open-chain gap
from range \(W\) to range \(R\) at a specified chain length, provided
both kernels are the canonical local MPS space. The loss is the window
multiplicity \(W-R+1\). Source: arXiv:cond-mat/9410110, Section 6. -/
theorem openParentHamiltonianES_gap_of_long_gap_at_length
    (A : MPSTensor d D) {R W N : ℕ}
    (hR : 0 < R) (hRW : R ≤ W) (hWN : W ≤ N) {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 < γ)
    (hLocal : (κ : ℂ) • parentInteractionES A W ≤
      openParentHamiltonianES A R W)
    (hShortKer : LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N)
    (hLongKer : LinearMap.ker (openParentHamiltonianES A W N) = groundSpaceES A N)
    (hLong : ∀ v ∈ (groundSpaceES A N)ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A W N v‖) :
    ∀ v ∈ (groundSpaceES A N)ᗮ,
      (κ * γ / (W - R + 1 : ℕ)) * ‖v‖ ≤
        ‖openParentHamiltonianES A R N v‖ := by
  intro v hv
  have hOrder := openParentHamiltonianES_comparison_of_local A
    hR hRW hWN hLocal
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hm : 0 < (W - R + 1 : ℕ) := by omega
  have hm' : ((W - R + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hGapScaled : ∀ u ∈
      (LinearMap.ker ((κ : ℂ) • openParentHamiltonianES A W N))ᗮ,
      (κ * γ) * ‖u‖ ≤
        ‖((κ : ℂ) • openParentHamiltonianES A W N) u‖ := by
    intro u hu
    have hu' : u ∈ (groundSpaceES A N)ᗮ := by
      simpa only [LinearMap.ker_smul _ _ hκ', hLongKer] using hu
    simpa only [LinearMap.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hκ, mul_assoc] using
      mul_le_mul_of_nonneg_left (hLong u hu') hκ.le
  have hKerScaled :
      LinearMap.ker ((κ : ℂ) • openParentHamiltonianES A W N) =
      LinearMap.ker (((W - R + 1 : ℕ) : ℂ) • openParentHamiltonianES A R N) := by
    simp only [LinearMap.ker_smul _ _ hκ', LinearMap.ker_smul _ _ hm',
      hLongKer, hShortKer]
  have hTransfer := LinearMap.IsPositive.norm_gap_of_le_of_ker_eq
    ((openParentHamiltonianES_isPositive A W N).smul_of_nonneg
      (by exact_mod_cast hκ.le))
    (mul_nonneg hκ.le hγ.le) hOrder
    hKerScaled hGapScaled
  have hv' : v ∈
      (LinearMap.ker (((W - R + 1 : ℕ) : ℂ) • openParentHamiltonianES A R N))ᗮ := by
    simpa only [LinearMap.ker_smul _ _ hm', hShortKer] using hv
  have h := hTransfer v hv'
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).mpr
  calc
    (κ * γ) * ‖v‖ ≤ ((W - R + 1 : ℕ) : ℝ) * ‖openParentHamiltonianES A R N v‖ := by
      simpa only [LinearMap.smul_apply, norm_smul, Complex.norm_natCast,
        Real.norm_natCast] using h
    _ = ‖openParentHamiltonianES A R N v‖ * ((W - R + 1 : ℕ) : ℝ) := mul_comm _ _

/-- A positive finite-interval comparison transfers a uniform open-chain
gap from range \(W\) to range \(R\), provided both open kernels are the
canonical local MPS space. The loss is the window multiplicity
\(W-R+1\). Source: arXiv:cond-mat/9410110, Section 6. -/
theorem openParentHamiltonianES_gap_of_long_gap
    (A : MPSTensor d D) {R W : ℕ} (hR : 0 < R) (hRW : R ≤ W) {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 < γ)
    (hLocal : (κ : ℂ) • parentInteractionES A W ≤
      openParentHamiltonianES A R W)
    (hShortKer : ∀ N, W ≤ N →
      LinearMap.ker (openParentHamiltonianES A R N) = groundSpaceES A N)
    (hLongKer : ∀ N, W ≤ N →
      LinearMap.ker (openParentHamiltonianES A W N) = groundSpaceES A N)
    (hLong : ∀ N : ℕ, W ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A W N v‖) :
    ∀ N : ℕ, W ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      (κ * γ / (W - R + 1 : ℕ)) * ‖v‖ ≤
        ‖openParentHamiltonianES A R N v‖ := by
  intro N hWN
  exact openParentHamiltonianES_gap_of_long_gap_at_length A hR hRW hWN
    hκ hγ hLocal (hShortKer N hWN) (hLongKer N hWN) (hLong N hWN)

/-- For a one-site injective tensor, a uniform open-chain gap at a longer
range transfers to the canonical two-site parent Hamiltonian. The interval
comparison is supplied at the long range, and the resulting constant is
independent of the chain length. -/
theorem openParentHamiltonianES_two_gap_of_long_gap
    [NeZero D] (A : MPSTensor d D) (hInj : Kraus.IsInjective A)
    {W : ℕ} (hW : 2 ≤ W) {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 < γ)
    (hLocal : (κ : ℂ) • parentInteractionES A W ≤
      openParentHamiltonianES A 2 W)
    (hLong : ∀ N : ℕ, W ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A W N v‖) :
    ∀ N : ℕ, W ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      (κ * γ / (W - 1 : ℕ)) * ‖v‖ ≤
        ‖openParentHamiltonianES A 2 N v‖ := by
  have hInjOne : Kraus.IsNBlkInjective A 1 :=
    Kraus.isNBlkInjective_one_of_isInjective hInj
  have hShortKer (N : ℕ) (hWN : W ≤ N) :
      LinearMap.ker (openParentHamiltonianES A 2 N) = groundSpaceES A N := by
    simpa only [Nat.reduceAdd] using
      ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        hInjOne (by norm_num : 0 < 1) (by omega : 1 + 1 ≤ N)
  have hInjLong : Kraus.IsNBlkInjective A (W - 1) :=
    isNBlkInjective_of_le (by norm_num : 0 < 1) hInjOne (by omega)
  have hLongKer (N : ℕ) (hWN : W ≤ N) :
      LinearMap.ker (openParentHamiltonianES A W N) = groundSpaceES A N := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ W)] using
      ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
        hInjLong (by omega : 0 < W - 1) (by omega : W - 1 + 1 ≤ N)
  simpa only [show W - 2 + 1 = W - 1 by omega] using
    openParentHamiltonianES_gap_of_long_gap A (by norm_num : 0 < 2) hW
      hκ hγ hLocal hShortKer hLongKer hLong

/-- Equality of the local MPS spaces at one length makes the corresponding
open-chain parent Hamiltonians equal at every volume. -/
theorem openParentHamiltonianES_eq_of_groundSpace_eq
    {A B : MPSTensor d D} {L : ℕ}
    (h : groundSpace A L = groundSpace B L) (N : ℕ) :
    openParentHamiltonianES A L N = openParentHamiltonianES B L N := by
  have hParent : parentInteraction A L = parentInteraction B L :=
    parentInteraction_eq_of_groundSpace_eq h
  unfold openParentHamiltonianES localTermES localTerm
  simp only [hParent]

/-- A one-site injective tensor has a positive open-chain gap at its canonical
two-site parent interaction, uniformly in the interval length once that length
is sufficiently large. The interaction range is fixed at two sites; the
constant and the starting length may depend on the tensor. -/
theorem exists_openParentHamiltonianES_two_uniform_gap_of_isInjective
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A) :
    ∃ W : ℕ, 2 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
        δ * ‖v‖ ≤ ‖openParentHamiltonianES A 2 N v‖ := by
  obtain ⟨B, ζ, ρ, _hζ, _hGauge, _hMPV, hP, hρ, hGS, _hPI, _hChain⟩ :=
    exists_isPrimitiveMPS_gauge_of_isNormal hA.isNormal
  obtain ⟨l, ε, hl, _hInjB, hε, hεlt, hOpenB⟩ :=
    hP.exists_openParentHamiltonianES_gap hρ
  let W := l + 1
  have hW : 2 ≤ W := by dsimp [W]; omega
  have hInjOne : Kraus.IsNBlkInjective A 1 :=
    Kraus.isNBlkInjective_one_of_isInjective hA
  have hker : LinearMap.ker (openParentHamiltonianES A 2 W) =
      groundSpaceES A W := by
    exact ker_openParentHamiltonianES_eq_groundSpaceES_of_isNBlkInjective
      hInjOne (by norm_num : 0 < 1) hW
  obtain ⟨κ, C, hκ, _hC, hLocal, _hUpper⟩ :=
    exists_pos_parentInteractionES_openParentHamiltonianES_comparison A hker
  let γ : ℝ := (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2
  have hsqrt : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hγ : 0 < γ := by
    dsimp [γ]
    have hprod : ε * Real.sqrt ((l + 1 : ℕ) : ℝ) < 1 :=
      (lt_div_iff₀ hsqrt).mp hεlt
    positivity
  have hOpenA : ∀ N : ℕ, W ≤ N → ∀ v ∈ (groundSpaceES A N)ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A W N v‖ := by
    intro N hWN v hv
    have hES : groundSpaceES A N = groundSpaceES B N := by
      simp only [groundSpaceES, hGS N]
    have hvB : v ∈ (groundSpaceES B N)ᗮ := by simpa only [hES] using hv
    have hB := hOpenB N (by simpa only [W] using hWN) v hvB
    rwa [← openParentHamiltonianES_eq_of_groundSpace_eq (hGS W) N] at hB
  let δ : ℝ := κ * γ / (W - 1 : ℕ)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (mul_pos hκ hγ) (Nat.cast_pos.mpr (by omega))
  refine ⟨W, hW, δ, hδ, ?_⟩
  exact openParentHamiltonianES_two_gap_of_long_gap A hA hW hκ hγ hLocal hOpenA

/-- Every one-site injective tensor has a finite nearest-neighbor open window
whose excitation gap satisfies the strict Knabe threshold. -/
theorem exists_strict_openParentHamiltonianES_two_window_of_isInjective
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ γ : ℝ,
      1 < (m : ℝ) * γ ∧
      ∀ v ∈ (groundSpaceES A (m + 1))ᗮ,
        γ * ‖v‖ ≤ ‖openParentHamiltonianES A 2 (m + 1) v‖ := by
  obtain ⟨W, hW, δ, hδ, hGap⟩ :=
    exists_openParentHamiltonianES_two_uniform_gap_of_isInjective A hA
  obtain ⟨n, hn⟩ := exists_lt_nsmul hδ (1 : ℝ)
  let m := n + W
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hnum : 1 < (m : ℝ) * δ := by
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by dsimp [m]; omega : n ≤ m)
    calc
      (1 : ℝ) < n • δ := hn
      _ = (n : ℝ) * δ := by simp [nsmul_eq_mul]
      _ ≤ (m : ℝ) * δ := mul_le_mul_of_nonneg_right hnm hδ.le
  refine ⟨m, hm, δ, hnum, ?_⟩
  intro v hv
  exact hGap (m + 1) (by dsimp [m]; omega) v hv

end MPSTensor
