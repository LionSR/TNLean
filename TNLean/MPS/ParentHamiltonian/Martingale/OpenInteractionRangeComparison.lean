/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.OpenRangeComparison
import TNLean.MPS.ParentHamiltonian.Martingale.OpenInteraction

/-!
# Finite-window comparison for positive open-chain interactions

A positive interaction of range \(R\) need not have the canonical local MPS
kernel. If its open Hamiltonian on \(W\) sites dominates a positive multiple
of the canonical length-\(W\) parent projection, the same comparison holds
on larger open chains, with multiplicity \(W-R+1\). Equality of the global
kernels then transfers a norm gap at each specified volume.

These are finite-window consequences of Nachtergaele,
arXiv:cond-mat/9410110, condition C1 (lines 1030--1041) and Section 6,
used in the proof of Theorem 1.2 (lines 933--947). The comparison itself
requires positivity but no local parent-kernel condition.
-/
open scoped BigOperators ComplexOrder
namespace MPSTensor
variable {d D : ℕ}
/-- The sum of a fixed range-\(R\) interaction over windows contained in the
suffix \([n-W,n)\) of an open chain. Source: Nachtergaele,
arXiv:cond-mat/9410110, condition C1. -/
noncomputable def openSuffixInteractionHamiltonianES {R : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (W N n : ℕ) : EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  ∑ i ∈ Finset.univ.filter (fun i : NonwrappingStart R N =>
    n - W ≤ i.1.val ∧ i.1.val + R ≤ n), periodicLocalInteractionES h i.1

/-- The sum of all complete suffix Hamiltonians is bounded by
\(W-R+1\) times the full open Hamiltonian. Source: Nachtergaele,
arXiv:cond-mat/9410110, condition C1. -/
theorem sum_openSuffixInteractionHamiltonianES_le {R W N : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hh : h.IsPositive) (hRW : R ≤ W) :
    (∑ n ∈ Finset.Icc W N, openSuffixInteractionHamiltonianES h W N n) ≤
      ((W - R + 1 : ℕ) : ℂ) • openInteractionHamiltonianES h N := by
  apply sum_nonwrappingWindowTerms_le hRW
  intro i
  have hzero : periodicLocalInteractionES
      (0 : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) i.1 = 0 := by
    simp [periodicLocalInteractionES]
  simpa only [hzero] using periodicLocalInteractionES_mono
    (LinearMap.nonneg_iff_isPositive.mpr hh) i.1
/-- An extended local interaction acts on the restricted window, with all
outside coordinates fixed. This is the coordinate form of finite-range
extension by the identity in Nachtergaele, arXiv:cond-mat/9410110, equation (3.12). -/
theorem periodicLocalInteractionES_apply {R N : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hR : 0 < R) (hRN : R ≤ N) (i : Fin N)
    (v : EuclideanSpace ℂ (Cfg d N)) (σ : Cfg d N) :
    periodicLocalInteractionES h i v σ =
      h (cyclicRestrictES (Fin.pos i) R i σ v) (extractWindow R i σ) := by
  unfold periodicLocalInteractionES
  rw [dite_eq_left hRN]
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply]
  change ((cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i).symm
    (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - R))
      (LinearMap.toContinuousLinearMap h)
      (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v))) σ = _
  rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply]
  change h (ContinuousLinearMap.rightFiber
    (cyclicActiveBlockConfigLinearIsometryEquiv d R hRN i v)
    ((cyclicActiveBlockConfigEquiv d R hRN i) σ).2) (extractWindow R i σ) = _
  apply congrArg (fun w : EuclideanSpace ℂ (Cfg d R) => h w (extractWindow R i σ))
  ext ω
  change v ((cyclicActiveBlockConfigEquiv d R hRN i).symm
      (ω, ((cyclicActiveBlockConfigEquiv d R hRN i) σ).2)) =
    v (cyclicCfg (Fin.pos i) R i ω σ)
  have hfull (ξ : Cfg d R) : cyclicCfg hR R (⟨0, hR⟩ : Fin R) ω ξ = ω := by
    funext j
    simp [cyclicCfg, Nat.mod_eq_of_lt j.isLt]
  have hj := cyclicCfg_join_cyclicActiveBlock hRN i (⟨0, hR⟩ : Fin R)
    (by simp) ω ((cyclicActiveBlockConfigEquiv d R hRN i) σ).1
      ((cyclicActiveBlockConfigEquiv d R hRN i) σ).2
  simp only [cyclicForwardSite_zero, hfull, Prod.mk.eta,
    Equiv.symm_apply_apply] at hj
  exact congrArg v hj.symm

/-- A local interaction inside an active interval acts independently on each
spectator configuration. Source: Nachtergaele, arXiv:cond-mat/9410110,
equation (3.12). -/
theorem periodicLocalInteractionES_conj_cyclicActiveBlock
    {N W R : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hR : 0 < R) (hWN : W ≤ N) (s : Fin N) (q : Fin W) (hqR : q.val + R ≤ W) :
    (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).toLinearEquiv.toLinearMap.comp
      ((periodicLocalInteractionES h (cyclicForwardSite s q.val)).comp
        (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (periodicLocalInteractionES h q))).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨σ, τ⟩
  simp only [LinearMap.comp_apply]
  change periodicLocalInteractionES h (cyclicForwardSite s q.val)
      ((cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x)
        ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ)) =
    periodicLocalInteractionES h q (ContinuousLinearMap.rightFiber x τ) σ
  rw [periodicLocalInteractionES_apply h hR (by omega),
    periodicLocalInteractionES_apply h hR (by omega)]
  have hrestrict :
      cyclicRestrictES (d := d) (Fin.pos (cyclicForwardSite s q.val)) R
          (cyclicForwardSite s q.val)
          ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ))
          ((cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x) =
        cyclicRestrictES (d := d) (Fin.pos q) R q σ
          (ContinuousLinearMap.rightFiber x τ) := by
    apply PiLp.ext
    intro ω
    change (cyclicActiveBlockConfigLinearIsometryEquiv d W hWN s).symm x
        (cyclicCfg (Fin.pos (cyclicForwardSite s q.val)) R
          (cyclicForwardSite s q.val) ω
          ((cyclicActiveBlockConfigEquiv d W hWN s).symm (σ, τ))) =
      x (cyclicCfg (Fin.pos q) R q ω σ, τ)
    rw [cyclicActiveBlockConfigLinearIsometryEquiv_symm_apply_apply,
      cyclicCfg_join_cyclicActiveBlock hWN s q hqR]
    simp
  rw [hrestrict, extractWindow_join_cyclicActiveBlock hWN s q hqR σ τ]
/-- An embedded suffix Hamiltonian is the open Hamiltonian on its active
interval acting independently on each spectator configuration.
Source: Nachtergaele, arXiv:cond-mat/9410110, condition C1. -/
theorem openSuffixInteractionHamiltonianES_conj_cyclicActiveBlock
    {R W N n : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hR : 0 < R) (hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) :
    let s : Fin N := ⟨n - W, by omega⟩
    let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega : W ≤ N) s
    U.toLinearEquiv.toLinearMap.comp
      ((openSuffixInteractionHamiltonianES h W N n).comp
        U.symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (openInteractionHamiltonianES h W))).toLinearMap := by
  classical
  dsimp only
  let s : Fin N := ⟨n - W, by omega⟩
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega : W ≤ N) s
  let e := nonwrappingSuffixStartEquiv hR hRW hWn hnN
  have hsum : openSuffixInteractionHamiltonianES h W N n =
      ∑ i : {i : NonwrappingStart R N // n - W ≤ i.1.val ∧ i.1.val + R ≤ n},
        periodicLocalInteractionES h i.1.1 := by
    rw [openSuffixInteractionHamiltonianES]
    exact Finset.sum_subtype _ (fun i => by simp) _
  rw [hsum]
  apply LinearMap.ext
  intro x
  simp only [openInteractionHamiltonianES, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    ContinuousLinearMap.rightFiberwiseMap_sum]
  calc
    (∑ i : {i : NonwrappingStart R N // n - W ≤ i.1.val ∧ i.1.val + R ≤ n},
        U (periodicLocalInteractionES h i.1.1 (U.symm x))) =
      ∑ q : NonwrappingStart R W,
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
          (LinearMap.toContinuousLinearMap (periodicLocalInteractionES h q.1)) x := by
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
          (periodicLocalInteractionES_conj_cyclicActiveBlock h hR
            (by omega : W ≤ N) s (e.symm i).1 (e.symm i).2) x
    _ = (∑ q : NonwrappingStart R W,
        ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
          (LinearMap.toContinuousLinearMap (periodicLocalInteractionES h q.1))) x := by
      simp

/-- A comparison on a finite interval remains valid after embedding that
interval in an open chain. No positivity or local kernel condition is needed
for this transport of order. Source: Nachtergaele,
arXiv:cond-mat/9410110, Section 6. -/
theorem openSuffixInteractionHamiltonianES_comparison_of_local
    (A : MPSTensor d D) {R W N n : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R)) (hR : 0 < R) (hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) {κ : ℝ}
    (hLocal : (κ : ℂ) • parentInteractionES A W ≤
      openInteractionHamiltonianES h W) :
    (κ : ℂ) • openSuffixParentHamiltonianES A W W N n ≤
      openSuffixInteractionHamiltonianES h W N n := by
  let s : Fin N := ⟨n - W, by omega⟩
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega : W ≤ N) s
  have hShort : U.toLinearEquiv.conj (openSuffixInteractionHamiltonianES h W N n) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (openInteractionHamiltonianES h W))).toLinearMap := by
    simpa only [U, LinearEquiv.conj_apply, LinearMap.comp_assoc] using!
      openSuffixInteractionHamiltonianES_conj_cyclicActiveBlock h hR hRW hWn hnN
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
      (H := LinearMap.toContinuousLinearMap (openInteractionHamiltonianES h W)) hLocal)

/-- A positive interaction dominating the length-\(W\) parent projection on
\(W\) sites dominates the corresponding open parent Hamiltonian on every
larger chain, up to the window multiplicity \(W-R+1\).
Source: Nachtergaele, arXiv:cond-mat/9410110, condition C1 and Section 6. -/
theorem openInteractionHamiltonianES_comparison_of_local
    (A : MPSTensor d D) {R W N : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hh : h.IsPositive) (hR : 0 < R) (hRW : R ≤ W)
    (_hWN : W ≤ N) {κ : ℝ}
    (hLocal : (κ : ℂ) • parentInteractionES A W ≤
      openInteractionHamiltonianES h W) :
    (κ : ℂ) • openParentHamiltonianES A W N ≤
      ((W - R + 1 : ℕ) : ℂ) • openInteractionHamiltonianES h N := by
  calc
    (κ : ℂ) • openParentHamiltonianES A W N =
        (κ : ℂ) • ∑ n ∈ Finset.Icc W N,
          openSuffixParentHamiltonianES A W W N n := by
          rw [sum_openSuffixParentHamiltonianES_full_window A (by omega : 0 < W)]
    _ = ∑ n ∈ Finset.Icc W N,
          (κ : ℂ) • openSuffixParentHamiltonianES A W W N n := by
          rw [Finset.smul_sum]
    _ ≤ ∑ n ∈ Finset.Icc W N,
          openSuffixInteractionHamiltonianES h W N n := by
          apply Finset.sum_le_sum
          intro n hn
          have hBounds := Finset.mem_Icc.mp hn
          exact openSuffixInteractionHamiltonianES_comparison_of_local A h hR hRW
            hBounds.1 hBounds.2 hLocal
    _ ≤ ((W - R + 1 : ℕ) : ℂ) • openInteractionHamiltonianES h N :=
          sum_openSuffixInteractionHamiltonianES_le h hh hRW

private theorem norm_gap_of_scaled_comparison {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {P Q : E →ₗ[ℂ] E} (hP : P.IsPositive) {κ γ m : ℝ}
    (hκ : 0 < κ) (hγ : 0 < γ) (hm : 0 < m)
    (hOrder : (κ : ℂ) • P ≤ (m : ℂ) • Q)
    (hKer : LinearMap.ker P = LinearMap.ker Q)
    (hGap : ∀ v ∈ (LinearMap.ker P)ᗮ, γ * ‖v‖ ≤ ‖P v‖) :
    ∀ v ∈ (LinearMap.ker Q)ᗮ, (κ * γ / m) * ‖v‖ ≤ ‖Q v‖ := by
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hGapScaled : ∀ u ∈ (LinearMap.ker ((κ : ℂ) • P))ᗮ,
      (κ * γ) * ‖u‖ ≤ ‖((κ : ℂ) • P) u‖ := by
    intro u hu
    have hu' : u ∈ (LinearMap.ker P)ᗮ := by
      simpa only [LinearMap.ker_smul _ _ hκ'] using hu
    simpa only [LinearMap.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hκ, mul_assoc] using
      mul_le_mul_of_nonneg_left (hGap u hu') hκ.le
  have hKerScaled : LinearMap.ker ((κ : ℂ) • P) =
      LinearMap.ker ((m : ℂ) • Q) := by
    simp only [LinearMap.ker_smul _ _ hκ', LinearMap.ker_smul _ _ hm', hKer]
  have hTransfer := LinearMap.IsPositive.norm_gap_of_le_of_ker_eq
    (E := E) (hP.smul_of_nonneg (by exact_mod_cast hκ.le))
    (mul_nonneg hκ.le hγ.le) hOrder hKerScaled hGapScaled
  intro v hv
  have hv' : v ∈ (LinearMap.ker ((m : ℂ) • Q))ᗮ := by
    simpa only [LinearMap.ker_smul _ _ hm'] using hv
  have h := hTransfer v hv'
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hm).mpr
  calc
    (κ * γ) * ‖v‖ ≤ m * ‖Q v‖ := by
      simpa only [LinearMap.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hm] using h
    _ = ‖Q v‖ * m := mul_comm _ _

/-- A finite-window comparison transfers a norm gap at a specified volume
when the two global kernels are the same MPS boundary-condition space.
The transferred gap is \(\kappa\gamma/(W-R+1)\). There is no hypothesis on
the kernel of the original local interaction. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem openInteractionHamiltonianES_gap_of_long_gap_at_length
    (A : MPSTensor d D) {R W N : ℕ}
    (h : EuclideanSpace ℂ (Cfg d R) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d R))
    (hh : h.IsPositive)
    (hR : 0 < R) (hRW : R ≤ W) (hWN : W ≤ N) {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 < γ)
    (hLocal : (κ : ℂ) • parentInteractionES A W ≤
      openInteractionHamiltonianES h W)
    (hShortKer : LinearMap.ker (openInteractionHamiltonianES h N) = groundSpaceES A N)
    (hLongKer : LinearMap.ker (openParentHamiltonianES A W N) = groundSpaceES A N)
    (hLong : ∀ v ∈ (groundSpaceES A N)ᗮ,
      γ * ‖v‖ ≤ ‖openParentHamiltonianES A W N v‖) :
    ∀ v ∈ (groundSpaceES A N)ᗮ,
      (κ * γ / (W - R + 1 : ℕ)) * ‖v‖ ≤
        ‖openInteractionHamiltonianES h N v‖ := by
  have hOrder := openInteractionHamiltonianES_comparison_of_local A h hh
    hR hRW hWN hLocal
  have hTransfer := norm_gap_of_scaled_comparison
    (E := EuclideanSpace ℂ (Cfg d N))
    (openParentHamiltonianES_isPositive A W N) hκ hγ
    (by positivity : 0 < ((W - R + 1 : ℕ) : ℝ)) hOrder
    (hLongKer.trans hShortKer.symm)
    (fun v hv => hLong v (by rwa [hLongKer] at hv))
  simpa only [hShortKer] using hTransfer

end MPSTensor
