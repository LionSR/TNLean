/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!
# Phase extraction from a product-tensor identity

This file isolates the algebraic proportionality step in arXiv:1708.00029,
Appendix A, lines 1072--1080.  Once the preceding \(F_u,\Omega_u\) contraction
has produced the uniform product-tensor identity, the result below extracts the
sectorwise scalars whose product is the global phase.
-/

open scoped BigOperators TensorProduct

namespace TNLean.Algebra

namespace PiTensorProductPhase

/-- Coordinate functional normalized to take the matrix `M` to one at entry `(a,b)`. -/
noncomputable def normalizedMatrixEntryDual {r c : Type*} (M : Matrix r c ℂ)
    (a : r) (b : c) : Module.Dual ℂ (Matrix r c ℂ) :=
  (M a b)⁻¹ • Matrix.entryLinearMap ℂ ℂ a b

@[simp]
lemma normalizedMatrixEntryDual_apply_self {r c : Type*} {M : Matrix r c ℂ}
    {a : r} {b : c} (hM : M a b ≠ 0) :
    normalizedMatrixEntryDual M a b M = 1 := by
  simp [normalizedMatrixEntryDual, hM]

/-- arXiv:1708.00029, Appendix A, lines 1072--1080: a product-tensor identity
with a nonzero reference tensor implies sectorwise proportionality, and the
sector scalars multiply to the global scalar.

**Scope restriction (arXiv:1708.00029, Appendix A, lines 1068--1080):** this
theorem starts from the uniform identity
\(\bigotimes_v A_v(\sigma_v)=z\cdot\bigotimes_v B_v(\sigma_v)\).  The paper
first obtains a cyclically shifted product identity between sector labels; the
reduction from that identity to the uniform form used here is recorded in
`docs/paper-gaps/1708_periodic_overlap_route_alignment.tex`.

The reference entries are the formal analogue of choosing one nonzero matrix
entry in each right-invertible sector block after the \(F_u,\Omega_u\)
contraction has produced the displayed product-tensor identity. -/
theorem exists_kappa_of_piTensorProduct_eq_smul
    {d m : ℕ}
    {row col : Fin m → Type*}
    (A B : (v : Fin m) → Fin d → Matrix (row v) (col v) ℂ)
    (z : ℂ) (hz : z ≠ 0)
    (ref : Fin m → Fin d) (r : (v : Fin m) → row v) (c : (v : Fin m) → col v)
    (hB_ref : ∀ v : Fin m, B v (ref v) (r v) (c v) ≠ 0)
    (hresult :
      ∀ σ : Fin m → Fin d,
        (⨂ₜ[ℂ] v : Fin m, A v (σ v)) =
          z • (⨂ₜ[ℂ] v : Fin m, B v (σ v))) :
    ∃ κ : Fin m → ℂ,
      (∏ v : Fin m, κ v = z) ∧
      ∀ (v : Fin m) (i : Fin d), A v i = κ v • B v i := by
  classical
  let ell : (v : Fin m) → Module.Dual ℂ (Matrix (row v) (col v) ℂ) :=
    fun v => normalizedMatrixEntryDual (B v (ref v)) (r v) (c v)
  let κ : Fin m → ℂ := fun v => ell v (A v (ref v))
  have hκ_prod : ∏ v : Fin m, κ v = z := by
    have h :=
      congrArg
        (fun T => PiTensorProduct.dualDistrib (⨂ₜ[ℂ] v : Fin m, ell v) T)
        (hresult ref)
    simpa [ell, κ, hB_ref] using h
  refine ⟨κ, hκ_prod, ?_⟩
  intro v i
  ext a b
  let entry : Module.Dual ℂ (Matrix (row v) (col v) ℂ) :=
    Matrix.entryLinearMap ℂ ℂ a b
  let ell' : (w : Fin m) → Module.Dual ℂ (Matrix (row w) (col w) ℂ) :=
    Function.update ell v entry
  have hcoord :
      (∏ w : Fin m, ell' w (A w (Function.update ref v i w))) =
        z * ∏ w : Fin m, ell' w (B w (Function.update ref v i w)) := by
    have h :=
      congrArg
        (fun T => PiTensorProduct.dualDistrib (⨂ₜ[ℂ] w : Fin m, ell' w) T)
        (hresult (Function.update ref v i))
    simpa using h
  have hprodA :
      (∏ w : Fin m, ell' w (A w (Function.update ref v i w))) =
        A v i a b * ∏ w ∈ Finset.univ \ {v}, κ w := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ v)]
    congr 1
    · simp [ell', entry]
    · apply Finset.prod_congr rfl
      intro w hw
      have hw_ne : w ≠ v := by
        simpa using (Finset.mem_sdiff.mp hw).2
      simp [ell', κ, Function.update_of_ne hw_ne]
  have hprodB :
      (∏ w : Fin m, ell' w (B w (Function.update ref v i w))) =
        B v i a b := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ v)]
    have hcomp :
        (∏ x ∈ Finset.univ \ {v}, ell' x (B x (Function.update ref v i x))) = 1 := by
      apply Finset.prod_eq_one
      intro w hw
      have hw_ne : w ≠ v := by
        simpa using (Finset.mem_sdiff.mp hw).2
      simp [ell', ell, Function.update_of_ne hw_ne, hB_ref w]
    have hfirst : ell' v (B v (Function.update ref v i v)) = B v i a b := by
      simp [ell', entry]
    rw [hfirst, hcomp, mul_one]
  let P : ℂ := ∏ w ∈ Finset.univ \ {v}, κ w
  have hκ_split : κ v * P = z := by
    change κ v * (∏ w ∈ Finset.univ \ {v}, κ w) = z
    rw [Finset.sdiff_singleton_eq_erase,
      Finset.mul_prod_erase Finset.univ κ (Finset.mem_univ v)]
    exact hκ_prod
  have hP_ne : P ≠ 0 := by
    intro hP
    exact hz (by rw [← hκ_split, hP, mul_zero])
  apply mul_right_cancel₀ hP_ne
  calc
    A v i a b * P = z * B v i a b := by
      simpa [P, hprodA, hprodB] using hcoord
    _ = (κ v * B v i a b) * P := by
      rw [← hκ_split]
      ring
    _ = ((κ v • B v i) a b) * P := by
      simp [Matrix.smul_apply]

/-- arXiv:1708.00029, Appendix A, lines 1072--1080: after the preceding
translation step has made the scalar \(z\) independent of the sector label,
choosing a common root \(\xi\) with \(\xi^m=z\) normalizes the sector scalars
to have product one.

This is the product-one form used to pass from a uniform product-tensor
proportionality to sector scalars satisfying \(\prod_v \kappa_v=1\) and
\(A_v^i=(\kappa_v\xi)B_v^i\).

**Scope restriction (arXiv:1708.00029, Appendix A, lines 1068--1080):** this
theorem starts from the uniform product-tensor identity, as in
`exists_kappa_of_piTensorProduct_eq_smul`; the contraction producing that
identity from the \(F_u,\Omega_u\) maps is recorded separately in
`docs/paper-gaps/1708_periodic_overlap_route_alignment.tex`. -/
theorem exists_kappa_product_one_of_piTensorProduct_eq_root_smul
    {d m : ℕ} [NeZero m]
    {row col : Fin m → Type*}
    (A B : (v : Fin m) → Fin d → Matrix (row v) (col v) ℂ)
    (z ξ : ℂ) (hz : z ≠ 0) (hξ_pow : ξ ^ m = z)
    (ref : Fin m → Fin d) (r : (v : Fin m) → row v) (c : (v : Fin m) → col v)
    (hB_ref : ∀ v : Fin m, B v (ref v) (r v) (c v) ≠ 0)
    (hresult :
      ∀ σ : Fin m → Fin d,
        (⨂ₜ[ℂ] v : Fin m, A v (σ v)) =
          z • (⨂ₜ[ℂ] v : Fin m, B v (σ v))) :
    ∃ κ : Fin m → ℂ,
      (∏ v : Fin m, κ v = 1) ∧
      ∀ (v : Fin m) (i : Fin d), A v i = (κ v * ξ) • B v i := by
  classical
  obtain ⟨κ₀, hκ₀_prod, hκ₀⟩ :=
    exists_kappa_of_piTensorProduct_eq_smul
      A B z hz ref r c hB_ref hresult
  have hξ_ne : ξ ≠ 0 := by
    intro hξ_zero
    have hpow_zero : ξ ^ m = 0 := by
      rw [hξ_zero]
      exact zero_pow (NeZero.ne m)
    exact hz (by rw [← hξ_pow, hpow_zero])
  let κ : Fin m → ℂ := fun v => κ₀ v / ξ
  refine ⟨κ, ?_, ?_⟩
  · calc
      ∏ v : Fin m, κ v =
          (∏ v : Fin m, κ₀ v) / (∏ _v : Fin m, ξ) := by
        simp [κ, Finset.prod_div_distrib]
      _ = z / ξ ^ m := by
        simp [hκ₀_prod]
      _ = 1 := by
        rw [hξ_pow, div_self hz]
  · intro v i
    calc
      A v i = κ₀ v • B v i := hκ₀ v i
      _ = (κ v * ξ) • B v i := by
        have hκ_mul : κ v * ξ = κ₀ v := by
          simp [κ, hξ_ne]
        rw [hκ_mul]

end PiTensorProductPhase

end TNLean.Algebra
