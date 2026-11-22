/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.CyclicWindowOpenHamiltonian
import TNLean.MPS.ParentHamiltonian.ParentInteraction.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.ParentInteraction.EmbeddedC2
import TNLean.MPS.ParentHamiltonian.ParentInteraction.FiniteIntervalGapComparison
import QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.PrimitiveGaugeExistence
import QICLean.Spectral.Gap.PositiveComparisonGap
import QICLean.Algebra.Combinatorics.FinSum

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

/-- A nonwrapping suffix interval, viewed in cyclic active-block coordinates,
is the same Hamiltonian on the active interval acting independently of all
spectator coordinates. -/
theorem hamiltonian_restrict_parentChainInteraction_conj_cyclicActiveBlock
    (A : MPSTensor d D) {R W N n : ℕ} (hR : 0 < R) (hRW : R ≤ W)
    (hWn : W ≤ n) (hnN : n ≤ N) :
    let s : Fin N := ⟨n - W, by omega⟩
    let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega : W ≤ N) s
    U.toLinearEquiv.toLinearMap.comp
      ((Matrix.toEuclideanLin
          ((parentChainInteraction A R N).restrict fun i ↦ n - W ≤ i.val ∧ i.val + R ≤
              n).hamiltonian).comp
        U.symm.toLinearEquiv.toLinearMap) =
      (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap
            (Matrix.toEuclideanLin (parentChainInteraction A R W).hamiltonian))).toLinearMap := by
  classical
  dsimp only
  let s : Fin N := ⟨n - W, by omega⟩
  let U := cyclicActiveBlockConfigLinearIsometryEquiv d W (by omega : W ≤ N) s
  apply LinearMap.ext
  intro x
  rw [ManyBody.Interaction.hamiltonian_restrict,
    ManyBody.Interaction.partialHamiltonian]
  simp only [ManyBody.Interaction.hamiltonian, LinearMap.comp_apply,
    LinearMap.sum_apply, map_sum, ContinuousLinearMap.rightFiberwiseMap_sum,
    ContinuousLinearMap.toLinearMap_sum]
  symm
  refine Finset.sum_bij
    (fun (q : Fin (W + 1 - R)) _ ↦ (⟨n - W + q.val, by omega⟩ : Fin (N + 1 - R)))
    (fun q _ ↦ ?_) (fun q₁ _ q₂ _ h ↦ ?_) (fun i hi ↦ ?_) (fun q _ ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  · rw [Finset.mem_filter] at hi
    exact ⟨⟨i.val - (n - W), by omega⟩, Finset.mem_univ _, Fin.ext (by simp only; omega)⟩
  · have hq : (⟨q.val, by omega⟩ : Fin W).val + R ≤ W := by
      change q.val + R ≤ W
      omega
    have hstart : (⟨n - W + q.val, by omega⟩ : Fin N) = cyclicForwardSite s q.val := by
      apply Fin.ext
      simp only [cyclicForwardSite, Fin.val_mk, s]
      rw [Nat.mod_eq_of_lt (by omega)]
    have hW : NeZero W := ⟨by omega⟩
    have hN : NeZero N := ⟨by omega⟩
    change (ContinuousLinearMap.rightFiberwiseMap (S := Cfg d (N - W))
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
          ((parentChainInteraction A R W).term ⟨q.val, by omega⟩)))) x =
      U (Matrix.toEuclideanLin ((parentChainInteraction A R N).term ⟨n - W + q.val, by omega⟩)
        (U.symm x))
    rw [ManyBody.Interaction.chainTranslates_term_eq_translationInvariant_term _ (by omega),
      ManyBody.Interaction.chainTranslates_term_eq_translationInvariant_term _ (by omega)]
    simp only [hstart]
    exact (LinearMap.congr_fun
      (toEuclideanLin_translationInvariant_term_conj_cyclicActiveBlock
        (LinearMap.toMatrix' (parentInteraction A R)) (by omega : W ≤ N) s
        ⟨q.val, by omega⟩ hq) x).symm

/-- Summing all complete suffix windows of length \(W\) counts every range-\(W\)
open-chain parent term exactly once. -/
theorem sum_hamiltonian_restrict_parentChainInteraction_full_window
    (A : MPSTensor d D) (W N : ℕ) :
    ∑ n ∈ Finset.Icc W N, Matrix.toEuclideanLin
        ((parentChainInteraction A W N).restrict fun i ↦ n - W ≤ i.val ∧ i.val + W ≤
            n).hamiltonian =
      Matrix.toEuclideanLin (parentChainInteraction A W N).hamiltonian := by
  rw [ManyBody.Interaction.hamiltonian, map_sum]
  refine Finset.sum_bij (fun n hn ↦ (⟨n - W, by
      have := Finset.mem_Icc.mp hn
      omega⟩ : Fin (N + 1 - W))) (fun n hn ↦ Finset.mem_univ _) (fun n₁ hn₁ n₂ hn₂ h ↦ ?_)
    (fun i _ ↦ ⟨i.val + W, ?_, ?_⟩) (fun n hn ↦ ?_)
  · have hval := congrArg Fin.val h
    simp only at hval
    have hn₁ := Finset.mem_Icc.mp hn₁
    have hn₂ := Finset.mem_Icc.mp hn₂
    omega
  · simp only [Finset.mem_Icc]
    omega
  · exact Fin.ext (by simp)
  · have hn := Finset.mem_Icc.mp hn
    rw [hamiltonian_restrict_parentChainInteraction_eq_term A hn.1 hn.2]

/-! ### The comparison for the Hamiltonians of the interactions

The comparison and the gap transfer for a local matrix `h` and the Hamiltonians of its open-chain
translates (`ManyBody.Interaction.chainTranslates`) and of the parent interaction on the open
chain (`parentChainInteraction`), in the matrix order. -/

section Interaction

open scoped MatrixOrder
open ManyBody.Interaction (chainTranslates hamiltonian_chainTranslates_eq_sum_range)

/-- **Comparison from one window.** If the open Hamiltonian of a positive semidefinite range-`R`
matrix `h` on `W` sites dominates a multiple of the local parent projection on `W` sites, then on
every open chain the Hamiltonian of the translates of `h`, times the window multiplicity
\(W-R+1\), dominates the same multiple of the open-chain parent Hamiltonian of range `W`.
Nachtergaele, arXiv:cond-mat/9410110, condition C1 and Section 6. -/
theorem hamiltonian_chainTranslates_comparison_of_local (A : MPSTensor d D) {R W N : ℕ}
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef) (hRW : R ≤ W) {κ : ℝ}
    (hLocal : (κ : ℂ) • LinearMap.toMatrix' (parentInteraction A W) ≤
      (chainTranslates R W h).hamiltonian) :
    (κ : ℂ) • (parentChainInteraction A W N).hamiltonian ≤
      ((W - R + 1 : ℕ) : ℂ) • (chainTranslates R N h).hamiltonian := by
  let g : ℕ → Matrix (Cfg d N) (Cfg d N) ℂ := fun i ↦
    if hi : i + R ≤ N then ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow i hi) h
    else 0
  have hg : ∀ i, 0 ≤ g i := fun i ↦ by
    by_cases hi : i + R ≤ N
    · simp only [g, dite_eq_left hi]
      exact Matrix.nonneg_iff_posSemidef.mpr (ManyBody.posSemidef_placeAlong _ hh)
    · simp only [g, dite_eq_right hi, le_refl]
  have hwindow (n : ℕ) (hn : n + W ≤ N) :
      (κ : ℂ) • ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow n hn)
          (LinearMap.toMatrix' (parentInteraction A W)) ≤
        ∑ j ∈ Finset.range (W + 1 - R), g (n + j) := by
    rw [← ManyBody.placeAlong_smul]
    refine (ManyBody.placeAlong_le_placeAlong _ hLocal).trans_eq ?_
    rw [hamiltonian_chainTranslates_eq_sum_range, ManyBody.placeAlong_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j + R ≤ W := by have := Finset.mem_range.mp hj; omega
    simp only [g, dite_eq_left hj', dite_eq_left (show n + j + R ≤ N by omega),
      ManyBody.placeAlong_placeAlong, ManyBody.chainWindow_trans_chainWindow]
  rw [hamiltonian_chainTranslates_eq_sum_range, hamiltonian_chainTranslates_eq_sum_range,
    Finset.smul_sum, show W - R + 1 = W + 1 - R by omega, Nat.cast_smul_eq_nsmul]
  calc ∑ n ∈ Finset.range (N + 1 - W), (κ : ℂ) • (if hn : n + W ≤ N then
          ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow n hn)
            (LinearMap.toMatrix' (parentInteraction A W)) else 0)
      ≤ ∑ n ∈ Finset.range (N + 1 - W), ∑ j ∈ Finset.range (W + 1 - R), g (n + j) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        rw [dite_eq_left (show n + W ≤ N by have := Finset.mem_range.mp hn; omega)]
        exact hwindow n _
    _ ≤ (W + 1 - R) • ∑ i ∈ Finset.range (N + 1 - R), g i :=
        Finset.sum_range_sum_range_add_le g hg fun n hn j hj ↦ by omega

/-- **Gap transfer at a specified volume.** Under the comparison of
`hamiltonian_chainTranslates_comparison_of_local`, if the open Hamiltonian of `h` and the
open-chain parent Hamiltonian of range `W` on `N` sites have the same kernel, the MPS
boundary-condition space, a gap \(γ\) above the kernel of the latter (every eigenvalue is `0`
or at least \(γ\)) gives the gap \(κγ/(W-R+1)\) above the kernel of the former. There is no
hypothesis on the kernel of the local matrix `h` itself. Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.2 and Section 6. -/
theorem toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length
    (A : MPSTensor d D) {R W N : ℕ} (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hh : h.PosSemidef)
    (hRW : R ≤ W) {κ γ : ℝ} (hκ : 0 < κ) (hγ : 0 < γ)
    (hLocal : (κ : ℂ) • LinearMap.toMatrix' (parentInteraction A W) ≤
      (chainTranslates R W h).hamiltonian)
    (hShortKer : LinearMap.ker (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) =
      groundSpaceES A N)
    (hLongKer : LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A W N).hamiltonian) =
      groundSpaceES A N)
    (hLong : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (parentChainInteraction A W N).hamiltonian) μ →
        μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (chainTranslates R N h).hamiltonian) μ →
        μ = 0 ∨ ((κ * γ / (W - R + 1 : ℕ) : ℝ) : ℂ) ≤ μ := by
  have hOrder := hamiltonian_chainTranslates_comparison_of_local A h hh hRW (N := N) hLocal
  rw [← Matrix.toEuclideanLin_le_toEuclideanLin_iff, map_smul, map_smul] at hOrder
  refine (ManyBody.forall_hasEigenvalue_iff_norm
    (ManyBody.Interaction.posSemidef_hamiltonian_chainTranslates hh N)).mpr ?_
  exact LinearMap.IsPositive.norm_gap_of_scaled_comparison
    (E := EuclideanSpace ℂ (Cfg d N))
    (Matrix.isPositive_toEuclideanLin_iff.mpr (posSemidef_hamiltonian_parentChainInteraction A W N))
    hκ hγ (by positivity : 0 < ((W - R + 1 : ℕ) : ℝ)) (by exact_mod_cast hOrder)
    (hLongKer.trans hShortKer.symm)
    ((ManyBody.forall_hasEigenvalue_iff_norm
      (posSemidef_hamiltonian_parentChainInteraction A W N)).mp hLong)

/-- Equality of the local MPS spaces at one length makes the parent interactions on the open
chain equal at every volume. -/
theorem parentChainInteraction_eq_of_groundSpace_eq
    {A B : MPSTensor d D} {L : ℕ}
    (h : groundSpace A L = groundSpace B L) (N : ℕ) :
    parentChainInteraction A L N = parentChainInteraction B L N := by
  unfold parentChainInteraction
  rw [parentInteraction_eq_of_groundSpace_eq h]

/-- A one-site injective tensor has a positive open-chain gap at its canonical two-site parent
interaction, uniformly in the interval length once that length is sufficiently large: every
eigenvalue of the open-chain Hamiltonian is `0` or at least the gap. The interaction range is
fixed at two sites; the constant and the starting length may depend on the tensor. -/
theorem exists_hamiltonian_parentChainInteraction_two_uniform_gap_of_isInjective
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A) :
    ∃ W : ℕ, 2 ≤ W ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, W ≤ N → ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A 2 N).hamiltonian) μ →
          μ = 0 ∨ (δ : ℂ) ≤ μ := by
  obtain ⟨B, ζ, ρ, _hζ, _hGauge, _hMPV, hP, hρ, hGS, _hPI, _hChain⟩ :=
    exists_hasComplementaryFixedPointGap_gauge_of_isNormal hA.isNormal
  obtain ⟨l, ε, hl, _hInjB, hε, hεlt, hOpenB⟩ :=
    hP.exists_hamiltonian_parentChainInteraction_gap hρ
  have hInjOne : Kraus.IsNBlkInjective A 1 :=
    Kraus.isNBlkInjective_one_of_isInjective hA
  have hShortKer (N : ℕ) (hN : 2 ≤ N) :
      LinearMap.ker (Matrix.toEuclideanLin (parentChainInteraction A 2 N).hamiltonian) =
        groundSpaceES A N :=
    ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
      hInjOne (by norm_num : 0 < 1) hN
  obtain ⟨κ, C, hκ, _hC, hLocal, _hUpper⟩ :=
    exists_pos_toMatrix'_parentInteraction_hamiltonian_parentChainInteraction_comparison A
      (hShortKer (l + 1) (by omega))
  have hsqrt : 0 < Real.sqrt ((l + 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hγ : 0 < (1 - ε * Real.sqrt ((l + 1 : ℕ) : ℝ)) ^ 2 := by
    have hprod : ε * Real.sqrt ((l + 1 : ℕ) : ℝ) < 1 :=
      (lt_div_iff₀ hsqrt).mp hεlt
    positivity
  refine ⟨l + 1, by omega, _, div_pos (mul_pos hκ hγ)
    (Nat.cast_pos.mpr (Nat.succ_pos (l + 1 - 2))), fun N hN ↦ ?_⟩
  refine toEuclideanLin_hamiltonian_chainTranslates_gap_of_long_gap_at_length A
    (LinearMap.toMatrix' (parentInteraction A 2)) (posSemidef_toMatrix'_parentInteraction A 2)
    (by omega) hκ hγ hLocal (hShortKer N (by omega))
    (ker_hamiltonian_parentChainInteraction_eq_groundSpaceES_of_isNBlkInjective
      (isNBlkInjective_of_le (by norm_num : 0 < 1) hInjOne (by omega)) (by omega) hN) ?_
  rw [parentChainInteraction_eq_of_groundSpace_eq (hGS (l + 1)) N]
  exact hOpenB N hN

/-- Every one-site injective tensor has a finite nearest-neighbor open window whose gap above
the kernel satisfies the strict Knabe threshold. -/
theorem exists_strict_hamiltonian_parentChainInteraction_two_window_of_isInjective
    [NeZero D] (A : MPSTensor d D) (hA : Kraus.IsInjective A) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ γ : ℝ,
      1 < (m : ℝ) * γ ∧
      ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (parentChainInteraction A 2 (m + 1)).hamiltonian) μ →
          μ = 0 ∨ (γ : ℂ) ≤ μ := by
  obtain ⟨W, hW, δ, hδ, hGap⟩ :=
    exists_hamiltonian_parentChainInteraction_two_uniform_gap_of_isInjective A hA
  obtain ⟨n, hn⟩ := exists_lt_nsmul hδ (1 : ℝ)
  let m := n + W
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hnum : 1 < (m : ℝ) * δ := by
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by dsimp [m]; omega : n ≤ m)
    calc
      (1 : ℝ) < n • δ := hn
      _ = (n : ℝ) * δ := by simp [nsmul_eq_mul]
      _ ≤ (m : ℝ) * δ := mul_le_mul_of_nonneg_right hnm hδ.le
  exact ⟨m, hm, δ, hnum, hGap (m + 1) (by dsimp [m]; omega)⟩

end Interaction

end MPSTensor
