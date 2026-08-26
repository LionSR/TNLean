/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ChainGroundSpace
import TNLean.MPS.ParentHamiltonian.CyclicTranslation
import TNLean.MPS.ParentHamiltonian.BoundaryClosing
import TNLean.MPS.ParentHamiltonian.BoundaryClosingAuxiliary
import TNLean.MPS.ParentHamiltonian.ExtendRight
import TNLean.MPS.ParentHamiltonian.Nonvanishing
import TNLean.MPS.ParentHamiltonian.RestrictTransport

/-!
# Periodic-boundary reductions for injective MPS

The injective periodic ground-space identification and the two boundary-window
compatibility families used in the block-injective closure argument.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Uniqueness theorems -/

/-- On a periodic chain, the injective parent-Hamiltonian ground space
coincides with \(ℂ V^{(N)}(A)\) when the window size satisfies \(L ≥ 2\).

For injective tensors, the open-chain intersection argument requires only
a window of at least `2` sites. -/
theorem chainGroundSpace_eq_mpvSubmodule {A : MPSTensor d D} [NeZero D]
    (hA : Kraus.IsInjective A) {L N : ℕ} (hN : 2 ≤ N) (hL : 1 < L) (hLN : L ≤ N) :
    chainGroundSpace A L N = mpvSubmodule A N := by
  have hN0 : 0 < N := by omega
  have : NeZero d := Kraus.neZero_d_of_isInjective hA
  apply le_antisymm
  · -- ⊆ direction: chainGroundSpace ≤ mpvSubmodule
    intro ψ hψ
    rw [chainGroundSpace, dite_eq_left ⟨hN0, hLN⟩] at hψ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
    -- Step 1: ψ ∈ groundSpace A N (via non-wrapping windows)
    have hψGS : ψ ∈ groundSpace A N := by
      apply contiguous_mem_groundSpace hA hL hLN
      intro s hs τ
      rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ hN0 hLN
        (show (⟨s, by omega⟩ : Fin N).val + L ≤ N from hs)]
      exact hψ ⟨s, by omega⟩ τ
    -- Step 2: ψ = groundSpaceMap A N X for some X
    rw [groundSpace, LinearMap.mem_range] at hψGS
    obtain ⟨X, hX⟩ := hψGS
    -- Step 3: X commutes with all A j (periodic boundary condition)
    have hComm : ∀ j : Fin d, X * A j = A j * X := by
      apply boundary_matrix_commutes hA hN hL hLN
      intro i τ
      rw [show groundSpaceMap A N X = ψ from hX]
      exact hψ i τ
    -- Step 4: X is scalar (center argument)
    have hCenter : X ∈ Set.center (Matrix (Fin D) (Fin D) ℂ) := by
      rw [Semigroup.mem_center_iff]
      intro M
      have hext : LinearMap.mulLeft ℂ X = LinearMap.mulRight ℂ X := by
        apply LinearMap.ext_on_range (v := A) (hv := hA.span_eq_top)
        intro j
        simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
        exact hComm j
      have := LinearMap.congr_fun hext M
      simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply] at this
      exact this.symm
    rw [Matrix.center_eq_range] at hCenter
    obtain ⟨c, hc⟩ := hCenter
    have hX_eq : X = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
      rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    -- Step 5: ψ = c • mpv A
    rw [mpvSubmodule]
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [← hX]
    ext σ
    simp only [groundSpaceMap_apply, Pi.smul_apply, smul_eq_mul, mpv, coeff]
    rw [hX_eq, Algebra.mul_smul_comm, mul_one, Matrix.trace_smul, smul_eq_mul]
  · -- ⊇ direction: mpvSubmodule ≤ chainGroundSpace
    intro ψ hψ
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hψ
    obtain ⟨c, rfl⟩ := hψ
    exact Submodule.smul_mem _ c (mpv_mem_chainGroundSpace A L N hN0 hLN)

/-- Reduced cyclic constraints give the two cyclic-window compatibility families
at the boundary for an open-chain boundary matrix.

After the cyclic-to-open-chain step writes a periodic-chain vector as
\(\psi=\Gamma_N(X)\), the two reduced cyclic windows used in the
periodic-boundary closure-property step expose the boundary matrix \(X\) on the
two sides of the same length \(N-(L₀+1)\) complement word. This theorem gives
the local algebraic output needed for the remaining periodic-boundary coordinate comparison
(arXiv:2011.12127, Section IV.C, lines 2078--2079). -/
theorem chainGroundSpace_wrapped_boundary_compatibilities_of_isNBlkInjective
    {A : MPSTensor d D} [NeZero D] {L₀ L N : ℕ}
    (hInj : Kraus.IsNBlkInjective A L₀) (hL₀ : 0 < L₀)
    (hN : 2 ≤ N) (hL : L₀ < L) (hLN : L ≤ N)
    {ψ : NSiteSpace d N} {X : Matrix (Fin D) (Fin D) ℂ}
    (hψ : ψ ∈ chainGroundSpace A L N) (hψX : ψ = groundSpaceMap A N X) :
    ∃ Ywrap Ymirror : (Fin N → Fin d) → Matrix (Fin D) (Fin D) ℂ,
      (∀ (j : Fin d) (τ : Fin N → Fin d),
        Kraus.evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
          τ ⟨k.val + L₀, by omega⟩)) * A j * X = Ywrap τ * A j) ∧
      (∀ (j : Fin d) (τ : Fin N → Fin d),
        X * A j * Kraus.evalWord A (List.ofFn (fun k : Fin (N - (L₀ + 1)) =>
          τ ⟨k.val + 1, by omega⟩)) = A j * Ymirror τ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hN0 : 0 < M + 1 := by omega
  have hL₀N : L₀ + 1 ≤ M + 1 := by omega
  have hM : L₀ ≤ M := by omega
  have hψmap : groundSpaceMap A (M + 1) X ∈ chainGroundSpace A L (M + 1) := by
    simpa [hψX] using hψ
  have hψred : groundSpaceMap A (M + 1) X ∈ chainGroundSpace A (L₀ + 1) (M + 1) :=
    chainGroundSpace_le_chainGroundSpace_of_le (A := A) hN0
      (by omega : L₀ + 1 ≤ L) hLN hψmap
  rw [chainGroundSpace, dite_eq_left ⟨hN0, hL₀N⟩] at hψred
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψred
  have hGSAt : ∀ (i : Fin (M + 1)) (τ : Fin (M + 1) → Fin d),
      ∃ Y : Matrix (Fin D) (Fin D) ℂ,
        ∀ σ_w : Fin (L₀ + 1) → Fin d,
          Matrix.trace (Kraus.evalWord A (List.ofFn
            (cyclicCfg hN0 (L₀ + 1) i σ_w τ)) * X) =
          Matrix.trace (Kraus.evalWord A (List.ofFn σ_w) * Y) := by
    intro i τ
    have hmem := hψred i τ
    rw [groundSpace, LinearMap.mem_range] at hmem
    obtain ⟨Y, hY⟩ := hmem
    refine ⟨Y, fun σ_w => ?_⟩
    have : cyclicRestrictₗ hN0 (L₀ + 1) i τ
        (groundSpaceMap A (M + 1) X) σ_w = groundSpaceMap A (L₀ + 1) Y σ_w := by
      rw [← hY]
    simp only [cyclicRestrictₗ_apply, groundSpaceMap_apply] at this
    exact this
  choose YAt hYAt using hGSAt
  let wrapPos : Fin (M + 1) := ⟨M, by omega⟩
  let mirrorPos : Fin (M + 1) := ⟨M + 1 - L₀, by omega⟩
  have hWrap := wrapping_window_compatibility_of_isNBlkInjective
    (A := A) hInj hL₀ hM (YAt wrapPos) (fun τ σ_w => hYAt wrapPos τ σ_w)
  have hMirror := wrapping_window_mirror_compatibility_of_isNBlkInjective
    (A := A) hInj hL₀ hM (YAt mirrorPos) (fun τ σ_w => hYAt mirrorPos τ σ_w)
  exact ⟨YAt wrapPos, YAt mirrorPos, hWrap, hMirror⟩


end MPSTensor
