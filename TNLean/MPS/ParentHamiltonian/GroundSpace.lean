import TNLean.MPS.Defs
import TNLean.MPS.Overlap.Basic

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Pi

/-!
# Ground space for parent Hamiltonians

For a tensor `A` and block length `L`, the local ground space `G_L(A)` is the
image of the linear map
`X ↦ (σ ↦ trace (evalWord A (List.ofFn σ) * X))`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The local Hilbert space on `N` sites, represented as coefficient functions on
configurations `σ : Fin N → Fin d`. -/
abbrev NSiteSpace (d N : ℕ) := Cfg d N → ℂ

/-- The linear map whose image is the local MPS ground space. -/
noncomputable def groundSpaceMap (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] NSiteSpace d L :=
  LinearMap.pi fun σ : Fin L → Fin d =>
    (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ (evalWord A (List.ofFn σ)))

@[simp] lemma groundSpaceMap_apply (A : MPSTensor d D) (L : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (σ : Fin L → Fin d) :
    groundSpaceMap A L X σ = Matrix.trace (evalWord A (List.ofFn σ) * X) := by
  simp [groundSpaceMap, Matrix.traceLinearMap_apply]

/-- Ground space on `L` consecutive sites: image of
`X ↦ (σ ↦ trace (evalWord A (List.ofFn σ) * X))`. -/
noncomputable def groundSpace (A : MPSTensor d D) (L : ℕ) :
    Submodule ℂ (NSiteSpace d L) :=
  (groundSpaceMap A L).range

lemma groundSpace_finrank_le (A : MPSTensor d D) (L : ℕ) :
    Module.finrank ℂ (groundSpace A L) ≤ D ^ 2 := by
  have hRange : Module.finrank ℂ (groundSpace A L) ≤
      Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) := by
    simpa [groundSpace] using LinearMap.finrank_range_le (groundSpaceMap A L)
  have hMatrix : Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) = D ^ 2 := by
    calc
      Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ)
          = (Fintype.card (Fin D) * Fintype.card (Fin D)) * Module.finrank ℂ ℂ := by
              simpa using (Module.finrank_matrix ℂ ℂ (Fin D) (Fin D))
      _ = D * D := by simp
      _ = D ^ 2 := by simp [pow_two]
  exact hRange.trans (by simpa [hMatrix])

/-- The ambient local space has dimension `d^L`. -/
lemma nSiteSpace_finrank (d L : ℕ) :
    Module.finrank ℂ (NSiteSpace d L) = d ^ L := by
  calc
    Module.finrank ℂ (NSiteSpace d L)
        = Fintype.card (Cfg d L) := by
            simpa [NSiteSpace] using (Module.finrank_fintype_fun_eq_card ℂ (η := Cfg d L))
    _ = d ^ L := by simp

/-- If `d^L > D^2`, then `G_L(A)` is a proper subspace. -/
lemma groundSpace_ne_top (A : MPSTensor d D) (L : ℕ) (hDim : d ^ L > D ^ 2) :
    groundSpace A L ≠ ⊤ := by
  intro hTop
  have hLe' : Module.finrank ℂ (groundSpace A L) ≤ D ^ 2 := groundSpace_finrank_le A L
  rw [hTop] at hLe'
  have hLe : d ^ L ≤ D ^ 2 := by
    simpa [nSiteSpace_finrank] using hLe'
  have hNotLe : ¬ d ^ L ≤ D ^ 2 := Nat.not_le.mpr hDim
  exact hNotLe hLe

end MPSTensor
