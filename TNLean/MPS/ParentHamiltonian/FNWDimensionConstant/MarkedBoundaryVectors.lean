/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram

/-!
# Boundary vectors multiplied on spectator sites

Multiplying a full boundary vector by a function of the spectator configuration
preserves membership in the corresponding interval ground-space range.
-/

namespace MPSTensor

/-- A multiplier on the prefix spectator sites is absorbed into the boundary
matrix of the tail interval. -/
theorem marked_groundSpaceMap_mem_tailBoundaryRange
    {d D : ℕ} (A : MPSTensor d D) (K L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (u : Cfg d K → ℂ) :
    WithLp.toLp 2 (fun σ : Cfg d (K + L) ↦
      u (σ ∘ Fin.castAdd L) * groundSpaceMap A (K + L) X σ) ∈
        (tailBoundaryMapES A K L).range := by
  refine ⟨(boundaryFamilyEquiv (D := D) (Cfg d K)).symm
    (fun τ ↦ u τ • (X * Kraus.evalWord A (List.ofFn τ))), ?_⟩
  apply PiLp.ext
  intro σ
  change tailBoundaryMap A K L
    (boundaryFamilyEquiv (D := D) (Cfg d K)
      ((boundaryFamilyEquiv (D := D) (Cfg d K)).symm _)) σ = _
  rw [LinearEquiv.apply_symm_apply, tailBoundaryMap_apply,
    Matrix.mul_smul, Matrix.trace_smul]
  change u (σ ∘ Fin.castAdd L) *
    tailBoundaryMap A K L (fun τ ↦ X * Kraus.evalWord A (List.ofFn τ)) σ = _
  rw [tailBoundaryMap_factorization]

/-- A multiplier on the suffix spectator sites is absorbed into the boundary
matrix of the left interval. -/
theorem marked_groundSpaceMap_mem_leftBoundaryRange
    {d D : ℕ} (A : MPSTensor d D) (K L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (u : Cfg d L → ℂ) :
    WithLp.toLp 2 (fun σ : Cfg d (K + L) ↦
      u (σ ∘ Fin.natAdd K) * groundSpaceMap A (K + L) X σ) ∈
        (leftBoundaryMapES A K L).range := by
  refine ⟨(boundaryFamilyEquiv (D := D) (Cfg d L)).symm
    (fun τ ↦ u τ • (Kraus.evalWord A (List.ofFn τ) * X)), ?_⟩
  apply PiLp.ext
  intro σ
  change leftBoundaryMap A K L
    (boundaryFamilyEquiv (D := D) (Cfg d L)
      ((boundaryFamilyEquiv (D := D) (Cfg d L)).symm _)) σ = _
  rw [LinearEquiv.apply_symm_apply, leftBoundaryMap_apply,
    Matrix.mul_smul, Matrix.trace_smul]
  change u (σ ∘ Fin.natAdd K) *
    leftBoundaryMap A K L (fun τ ↦ Kraus.evalWord A (List.ofFn τ) * X) σ = _
  rw [leftBoundaryMap_factorization]

end MPSTensor
