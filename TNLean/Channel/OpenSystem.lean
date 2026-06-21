/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import TNLean.Channel.RadonNikodym

/-!
# Unitary open-system representation

This file proves the unitary form of Wolf's open-system representation theorem
from the isometric Stinespring form.  The linear-algebra step is the following
rectangular Gram theorem: two maps with the same Gram matrix differ by a
unitary on the codomain.  Its proof extends the induced isometry between the
ranges to the ambient finite-dimensional Hilbert space.

## Main results

* `Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq` — rectangular matrices
  with equal Gram matrices differ by left multiplication by a unitary matrix.
* `Matrix.firstEnvEmbedding` — the embedding of the system into the first
  coordinate of an environment.
* `IsChannel.exists_stinespring_open_system_unitary` — Wolf Theorem 2.5 in
  unitary open-system form.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.5]
  [Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
open Matrix Finset BigOperators

variable {D : ℕ}

namespace Matrix

/-- If two rectangular matrices have the same Gram matrix, then they differ by
left multiplication by a unitary matrix on the codomain. -/
theorem exists_unitary_mul_eq_of_conjTranspose_mul_eq
    {m n : Type*} [Fintype m] [DecidableEq m] [Finite n]
    (B A : Matrix m n ℂ)
    (hGram : Bᴴ * B = Aᴴ * A) :
    ∃ U : Matrix.unitaryGroup m ℂ, B = (U : Matrix m m ℂ) * A := by
  classical
  letI : Fintype n := Fintype.ofFinite n
  letI : InnerProductSpace ℂ (EuclideanSpace ℂ m) :=
    PiLp.innerProductSpace (fun _ : m => ℂ)
  letI : FiniteDimensional ℂ (EuclideanSpace ℂ m) :=
    (EuclideanSpace.basisFun m ℂ).toBasis.finiteDimensional_of_finite
  let fB : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m :=
    Matrix.toEuclideanLin B
  let fA : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m :=
    Matrix.toEuclideanLin A
  have hinner : ∀ v w : EuclideanSpace ℂ n,
      ⟪fB v, fB w⟫_ℂ = ⟪fA v, fA w⟫_ℂ := by
    intro v w
    rw [← LinearMap.adjoint_inner_right fB v (fB w),
        ← LinearMap.adjoint_inner_right fA v (fA w)]
    congr 1
    change fB.adjoint (fB w) = fA.adjoint (fA w)
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint B,
        ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
    change (Bᴴ.toEuclideanLin.comp B.toEuclideanLin) w =
      (Aᴴ.toEuclideanLin.comp A.toEuclideanLin) w
    rw [← toLpLin_mul_same, ← toLpLin_mul_same, hGram]
  have hker : LinearMap.ker fA ≤ LinearMap.ker fB := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h0 := hinner v v
    simp only [hv, inner_zero_left] at h0
    exact inner_self_eq_zero.mp h0
  let L_lm : LinearMap.range fA →ₗ[ℂ] EuclideanSpace ℂ m :=
    ((LinearMap.ker fA).liftQ fB hker).comp
      fA.quotKerEquivRange.symm.toLinearMap
  have hL_apply : ∀ v, L_lm ⟨fA v, LinearMap.mem_range_self fA v⟩ = fB v := by
    intro v
    change ((LinearMap.ker fA).liftQ fB hker)
        (fA.quotKerEquivRange.symm ⟨fA v, LinearMap.mem_range_self fA v⟩) =
      fB v
    rw [fA.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ _
  have hL_inner : ∀ x y : LinearMap.range fA,
      ⟪L_lm x, L_lm y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨v, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    rw [hL_apply, hL_apply, hinner, Submodule.coe_inner]
  let L_iso : LinearMap.range fA →ₗᵢ[ℂ] EuclideanSpace ℂ m :=
    LinearMap.isometryOfInner L_lm hL_inner
  let U := L_iso.extend
  have hU_eq : ∀ v, U (fA v) = fB v := by
    intro v
    have : U (fA v) = L_iso ⟨fA v, LinearMap.mem_range_self fA v⟩ :=
      LinearIsometry.extend_apply L_iso ⟨fA v, LinearMap.mem_range_self fA v⟩
    rw [this]
    simpa [L_iso] using hL_apply v
  let U_mat : Matrix m m ℂ :=
    Matrix.toEuclideanLin.symm U.toLinearMap
  have h_U_lin : Matrix.toEuclideanLin U_mat = U.toLinearMap :=
    LinearEquiv.apply_symm_apply Matrix.toEuclideanLin U.toLinearMap
  have hU_unitary : U_matᴴ * U_mat = 1 := by
    apply Matrix.toEuclideanLin.injective
    ext1 v
    have hadj : U.toLinearMap.adjoint (U.toLinearMap v) = v :=
      ext_inner_right ℂ fun y => by
        rw [LinearMap.adjoint_inner_left]
        exact LinearIsometry.inner_map_map U v y
    rw [toLpLin_mul_same, LinearMap.comp_apply,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, h_U_lin, hadj]
    simp only [toLpLin_one, LinearMap.id_apply]
  have hU_mat_eq : U_mat * A = B := by
    apply Matrix.toEuclideanLin.injective
    ext1 v
    rw [toLpLin_mul_same, LinearMap.comp_apply, h_U_lin]
    exact hU_eq v
  refine ⟨⟨U_mat, Matrix.mem_unitaryGroup_iff'.2 hU_unitary⟩, ?_⟩
  exact hU_mat_eq.symm

/-- The embedding `x ↦ x ⊗ e₀` into the first coordinate of an environment. -/
noncomputable def firstEnvEmbedding (D r : ℕ) (hr : 0 < r) :
    Matrix (Fin D × Fin r) (Fin D) ℂ :=
  fun ik j =>
    if ik.2 = ⟨0, hr⟩ then (1 : Matrix (Fin D) (Fin D) ℂ) ik.1 j else 0

@[simp]
theorem firstEnvEmbedding_apply_zero (D r : ℕ) (hr : 0 < r)
    (i j : Fin D) :
    firstEnvEmbedding D r hr (i, ⟨0, hr⟩) j =
      (1 : Matrix (Fin D) (Fin D) ℂ) i j := by
  simp [firstEnvEmbedding]

@[simp]
theorem firstEnvEmbedding_apply_ne (D r : ℕ) (hr : 0 < r)
    (i j : Fin D) {k : Fin r} (hk : k ≠ ⟨0, hr⟩) :
    firstEnvEmbedding D r hr (i, k) j = 0 := by
  simp [firstEnvEmbedding, hk]

/-- The first-coordinate environment embedding is an isometry. -/
theorem firstEnvEmbedding_conjTranspose_mul_self (D r : ℕ) (hr : 0 < r) :
    (firstEnvEmbedding D r hr)ᴴ * firstEnvEmbedding D r hr = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  by_cases hij : i = j
  · simp [firstEnvEmbedding, Matrix.one_apply, hij]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [firstEnvEmbedding, Matrix.one_apply, hij, hji]

end Matrix

namespace IsChannel

private theorem stinespring_environment_pos [NeZero D]
    {r : ℕ} {V : Matrix (Fin D × Fin r) (Fin D) ℂ}
    (hV : Vᴴ * V = 1) :
    0 < r := by
  by_contra hr
  have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
  let j : Fin D := ⟨0, NeZero.pos D⟩
  have hdiag := congr_fun (congr_fun hV j) j
  subst r
  simp [Matrix.mul_apply] at hdiag

/-- **Wolf Theorem 2.5 (unitary open-system representation).**

For a nonzero finite-dimensional system, every quantum channel has a
system-plus-environment unitary realization.  The matrix
`Matrix.firstEnvEmbedding D r hr` inserts the system into the first
environment coordinate, so the middle factor is `ρ ⊗ |0⟩⟨0|` in matrix form. -/
theorem exists_stinespring_open_system_unitary [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsChannel T) :
    ∃ (r : ℕ) (hr : 0 < r) (U : Matrix.unitaryGroup (Fin D × Fin r) ℂ),
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ,
        T ρ =
          ((U : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) *
            (Matrix.firstEnvEmbedding D r hr * ρ *
              (Matrix.firstEnvEmbedding D r hr)ᴴ) *
            (U : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)ᴴ).traceRight := by
  obtain ⟨r, V, hV, htrace⟩ := hT.exists_stinespring_open_system_traceRight
  have hr : 0 < r := stinespring_environment_pos (D := D) (V := V) hV
  let W : Matrix (Fin D × Fin r) (Fin D) ℂ := Matrix.firstEnvEmbedding D r hr
  have hW : Wᴴ * W = 1 :=
    Matrix.firstEnvEmbedding_conjTranspose_mul_self D r hr
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (B := V) (A := W) (by rw [hV, hW])
  refine ⟨r, hr, U, ?_⟩
  intro ρ
  rw [htrace ρ, hU]
  simp [W, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end IsChannel
