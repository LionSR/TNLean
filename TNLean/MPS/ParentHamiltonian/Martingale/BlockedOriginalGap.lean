/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PositiveGapTransfer
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace
import TNLean.MPS.ParentHamiltonian.Martingale.BlockedGap
import TNLean.MPS.ParentHamiltonian.Martingale.BlockedOriginalComparison
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# Spectral gap in original-site units after blocking

This file transfers the proved range-two gap of a blocked primitive MPS tensor
to the canonical range-\(2p\) parent Hamiltonian of the original tensor on
periodic chains whose lengths are multiples of \(p\).

The finite cyclic sparse-sum comparison is a TNLean reconstruction. The cited
Nachtergaele source uses a rescaled sequence of compatible open intervals; it
does not state the finite periodic comparison below.

## Main result

* `MPSTensor.IsPrimitiveMPS.exists_parentHamiltonianES_gap_eighth_mul`
  gives the original-site interaction range \(2p\) and gap \(1/8\) on lengths
  \(Np\), for \(N \geq 4\).

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:2011.12127, Section IV.C.
* B. Nachtergaele, arXiv:cond-mat/9410110, equations (3.12)--(3.16) and the
  rescaled-volume argument in Theorem 2.1(ii).
-/

open scoped ComplexOrder InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

private theorem parentHamiltonianES_blockTensor_conj_ker_eq
    [NeZero D] (A : MPSTensor d D) (p : ℕ) (hp : 0 < p)
    (hInj : IsNBlkInjective A p) {N : ℕ} (hN : 4 ≤ N) :
    LinearMap.ker
        ((blockedConfigLinearIsometryEquiv d N p).toLinearEquiv.toLinearMap.comp
          ((parentHamiltonianES (blockTensor A p) 2 N).comp
            (blockedConfigLinearIsometryEquiv d N p).symm.toLinearEquiv.toLinearMap)) =
      LinearMap.ker (parentHamiltonianES A (2 * p) (N * p)) := by
  let U := blockedConfigLinearIsometryEquiv d N p
  have hB : IsInjective (blockTensor A p) :=
    (isNBlkInjective_iff_blockTensor_isInjective A p).mp hInj
  have hNpos : 0 < N := by omega
  have hNp : 0 < N * p := Nat.mul_pos hNpos hp
  have hBchain := chainGroundSpace_eq_mpvSubmodule hB (by omega) (by omega)
    (by omega : 2 ≤ N)
  have hAchain := chainGroundSpace_eq_mpvSubmodule_normal
    (⟨p, hp, hInj⟩ : IsNormal A) hInj hp (by nlinarith) (by nlinarith)
      (by nlinarith : 2 * p ≤ N * p) (by nlinarith)
  let eB := WithLp.linearEquiv 2 ℂ (NSiteSpace (blockPhysDim d p) N)
  let eA := WithLp.linearEquiv 2 ℂ (NSiteSpace d (N * p))
  have hmpv : U (eB.symm (mpv (blockTensor A p))) = eA.symm (mpv A) := by
    ext σ
    change mpv (blockTensor A p) ((blockedConfigEquiv d N p).symm σ) = mpv A σ
    rw [mpv_eq_groundSpaceMap_one, mpv_eq_groundSpaceMap_one]
    exact groundSpaceMap_blockTensor_blockedConfigEquiv A p N 1 σ
  ext v
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
  have hUzero : U ((parentHamiltonianES (blockTensor A p) 2 N) (U.symm v)) = 0 ↔
      parentHamiltonianES (blockTensor A p) 2 N (U.symm v) = 0 := by
    exact U.injective.eq_iff' (map_zero U)
  change U (parentHamiltonianES (blockTensor A p) 2 N (U.symm v)) = 0 ↔ _
  rw [hUzero]
  rw [← mem_parentHamiltonianGroundSpaceES_iff]
  change U.symm v ∈ parentHamiltonianGroundSpaceES (blockTensor A p) 2 N ↔
    v ∈ LinearMap.ker (parentHamiltonianES A (2 * p) (N * p))
  rw [← parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES]
  rw [parentHamiltonianGroundSpaceES_eq_chainGroundSpaceES _ hNpos (by omega : 2 ≤ N)]
  rw [parentHamiltonianGroundSpaceES_eq_chainGroundSpaceES _ hNp
    (by nlinarith : 2 * p ≤ N * p)]
  simp only [chainGroundSpaceES, hBchain, hAchain, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    refine ⟨c • (mpv A : NSiteSpace d (N * p)), ?_, ?_⟩
    · rw [mpvSubmodule, Submodule.mem_span_singleton]
      exact ⟨c, rfl⟩
    · calc
        eA.symm (c • (mpv A : NSiteSpace d (N * p))) =
            c • eA.symm (mpv A) := by simp
        _ = c • U (eB.symm (mpv (blockTensor A p))) := by rw [hmpv]
        _ = U (eB.symm (c • (mpv (blockTensor A p) :
            NSiteSpace (blockPhysDim d p) N))) := by simp
        _ = v := by
          change U ((WithLp.linearEquiv 2 ℂ (NSiteSpace (blockPhysDim d p) N)).symm
            (c • (mpv (blockTensor A p) : NSiteSpace (blockPhysDim d p) N))) = v
          exact congrArg U hwv |>.trans (U.apply_symm_apply v)
  · rintro ⟨w, hw, hwv⟩
    rw [mpvSubmodule, Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    refine ⟨c • (mpv (blockTensor A p) : NSiteSpace (blockPhysDim d p) N), ?_, ?_⟩
    · rw [mpvSubmodule, Submodule.mem_span_singleton]
      exact ⟨c, rfl⟩
    · apply U.injective
      rw [U.apply_symm_apply, ← hwv]
      change U (eB.symm (c • (mpv (blockTensor A p) :
        NSiteSpace (blockPhysDim d p) N))) = eA.symm (c • (mpv A : NSiteSpace d (N * p)))
      simp only [map_smul]
      rw [hmpv]

/-- A primitive tensor has an original-site range-\(2p\) parent Hamiltonian
with gap \(1/8\) on every periodic chain of length \(Np\), \(N \geq 4\).

**Scope restriction (divisible periodic lengths):** the conclusion is only for
chain lengths divisible by the selected block length. The remainder-length
extension is not proved here. See
`docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem IsPrimitiveMPS.exists_parentHamiltonianES_gap_eighth_mul
    [NeZero d] [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : Matrix.PosDef ρ) :
    ∃ p : ℕ, 0 < p ∧ IsNBlkInjective A p ∧
      ∀ (N : ℕ) (_hN : 4 ≤ N) (v : EuclideanSpace ℂ (Cfg d (N * p))),
        v ∈ (parentHamiltonianGroundSpaceES A (2 * p) (N * p))ᗮ →
          (1 / 8 : ℝ) * ‖v‖ ≤ ‖parentHamiltonianES A (2 * p) (N * p) v‖ := by
  obtain ⟨p, hp, hInj, hGap⟩ := hP.exists_blockTensor_parentHamiltonianES_gap_eighth hρ
  refine ⟨p, hp, hInj, ?_⟩
  intro N hN v hv
  let U := blockedConfigLinearIsometryEquiv d N p
  let P := U.toLinearEquiv.toLinearMap.comp
    ((parentHamiltonianES (blockTensor A p) 2 N).comp U.symm.toLinearEquiv.toLinearMap)
  let Q := parentHamiltonianES A (2 * p) (N * p)
  have hPpos : P.IsPositive := by
    constructor
    · intro x y
      simp only [P, LinearMap.comp_apply]
      calc
        ⟪U (parentHamiltonianES (blockTensor A p) 2 N (U.symm x)), y⟫_ℂ =
            ⟪parentHamiltonianES (blockTensor A p) 2 N (U.symm x), U.symm y⟫_ℂ := by
          rw [← U.inner_map_map, U.apply_symm_apply]
        _ = ⟪U.symm x, parentHamiltonianES (blockTensor A p) 2 N (U.symm y)⟫_ℂ :=
          (parentHamiltonianES_isPositive (blockTensor A p) 2 N).isSymmetric _ _
        _ = ⟪x, U (parentHamiltonianES (blockTensor A p) 2 N (U.symm y))⟫_ℂ := by
          rw [← U.inner_map_map, U.apply_symm_apply]
    · intro x
      simp only [P, LinearMap.comp_apply]
      have hinner := U.inner_map_map
        (parentHamiltonianES (blockTensor A p) 2 N (U.symm x)) (U.symm x)
      rw [U.apply_symm_apply] at hinner
      change 0 ≤ (⟪U (parentHamiltonianES (blockTensor A p) 2 N (U.symm x)), x⟫_ℂ).re
      rw [hinner]
      exact (parentHamiltonianES_isPositive (blockTensor A p) 2 N).re_inner_nonneg_left _
  have hPQ : P ≤ Q := blockTensor_parentHamiltonianES_conj_le A p hp (by omega)
  have hker : LinearMap.ker P = LinearMap.ker Q :=
    parentHamiltonianES_blockTensor_conj_ker_eq A p hp hInj hN
  have hGapP : ∀ w ∈ (LinearMap.ker P)ᗮ, (1 / 8 : ℝ) * ‖w‖ ≤ ‖P w‖ := by
    intro w hw
    let z := U.symm w
    have hz : z ∈
        (parentHamiltonianGroundSpaceES (blockTensor A p) 2 N)ᗮ := by
      rw [parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES]
      intro x hx
      have hUx : U x ∈ LinearMap.ker P := by
        rw [LinearMap.mem_ker]
        change U (parentHamiltonianES (blockTensor A p) 2 N (U.symm (U x))) = 0
        rw [U.symm_apply_apply, hx, map_zero]
      have horth := hw (U x) hUx
      change ⟪x, U.symm w⟫_ℂ = 0
      have hinner := U.inner_map_map x (U.symm w)
      rw [U.apply_symm_apply] at hinner
      exact hinner.symm.trans horth
    simpa [P, z] using hGap N hN z hz
  have hvker : v ∈ (LinearMap.ker Q)ᗮ := by
    simpa [Q, parentHamiltonianGroundSpaceES_eq_ker_parentHamiltonianES] using hv
  exact hPpos.norm_gap_of_le_of_ker_eq (by norm_num) hPQ hker hGapP v hvker

end MPSTensor
