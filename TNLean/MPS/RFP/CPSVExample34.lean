/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# CPSV16 Example 3.4: correlation independence without an RFP

This file formalizes the tensor displayed in arXiv:1606.00608, Example 3.4
(`Ex:ZCL`, lines 450--465). Its positive-length MPV is
$|0,\ldots,0\rangle+|+,\ldots,+\rangle$. The state has physical correlation
independence because all of its diagonal word operators induce commuting
entrywise multipliers. Its transfer map is not idempotent, so it has no
physical blocking isometry and is not a renormalization fixed point.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor

/-- The scalar $1/\sqrt 2$, viewed as a complex number. -/
noncomputable def cpsvExample34InvSqrtTwo : ℂ :=
  (↑(1 / Real.sqrt 2) : ℂ)

/-- The exact tensor from CPSV16, Example 3.4:
$A^0=\operatorname{diag}(1,1/\sqrt2)$ and
$A^1=\operatorname{diag}(0,1/\sqrt2)$. -/
noncomputable def cpsvExample34Tensor : MPSTensor 2 2
  | 0 => !![(1 : ℂ), 0; 0, cpsvExample34InvSqrtTwo]
  | 1 => !![(0 : ℂ), 0; 0, cpsvExample34InvSqrtTwo]

@[simp] theorem cpsvExample34Tensor_zero :
    cpsvExample34Tensor 0 =
      !![(1 : ℂ), 0; 0, cpsvExample34InvSqrtTwo] := rfl

@[simp] theorem cpsvExample34Tensor_one :
    cpsvExample34Tensor 1 =
      !![(0 : ℂ), 0; 0, cpsvExample34InvSqrtTwo] := rfl

private noncomputable def cpsvExample34WordDiag (w : List (Fin 2)) : Fin 2 → ℂ
  | 0 => if w.Forall (· = 0) then 1 else 0
  | 1 => cpsvExample34InvSqrtTwo ^ w.length

private theorem cpsvExample34_evalWord (w : List (Fin 2)) :
    evalWord cpsvExample34Tensor w = Matrix.diagonal (cpsvExample34WordDiag w) := by
  induction w with
  | nil =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [cpsvExample34WordDiag, Matrix.diagonal_apply]
  | cons i w ih =>
      rw [evalWord_cons, ih]
      fin_cases i <;>
        ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [cpsvExample34Tensor, cpsvExample34WordDiag, Matrix.mul_apply,
          Fin.sum_univ_two, pow_succ']

/-- The exact positive-length amplitude formula in CPSV16, Example 3.4.
For a nonempty configuration $\sigma$, the first summand is the amplitude of
$|0,\ldots,0\rangle$ and the second is the amplitude of
$|+,\ldots,+\rangle$. -/
theorem cpsvExample34_mpv {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin 2) :
    mpv cpsvExample34Tensor σ =
      (if ∀ k, σ k = 0 then 1 else 0) + cpsvExample34InvSqrtTwo ^ N := by
  rw [mpv, coeff, cpsvExample34_evalWord]
  simp only [Matrix.trace, Matrix.diagonal_apply_eq, Fin.sum_univ_two,
    cpsvExample34WordDiag, List.length_ofFn]
  congr 2
  simp only [List.forall_iff_forall_mem, List.mem_ofFn]
  constructor
  · intro h k
    exact h (σ k) ⟨k, rfl⟩
  · rintro h x ⟨k, rfl⟩
    exact h k

private def IsEntrywiseMultiplier
    (F : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ c : Matrix (Fin 2) (Fin 2) ℂ, ∀ X a b, F X a b = c a b * X a b

private theorem isEntrywiseMultiplier_commute
    {F G : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ}
    (hF : IsEntrywiseMultiplier F) (hG : IsEntrywiseMultiplier G) :
    Commute F G := by
  obtain ⟨c, hc⟩ := hF
  obtain ⟨e, he⟩ := hG
  apply LinearMap.ext
  intro X
  ext a b
  simp only [Module.End.mul_apply, hc, he]
  ring

private theorem cpsvExample34_physicalObservableTransfer_isEntrywiseMultiplier
    (L : ℕ) (O : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ) :
    IsEntrywiseMultiplier (physicalObservableTransfer cpsvExample34Tensor L O) := by
  let c : Matrix (Fin 2) (Fin 2) ℂ := fun a b =>
    ∑ σ : Fin L → Fin 2, ∑ τ : Fin L → Fin 2,
      O τ σ * cpsvExample34WordDiag (List.ofFn σ) a *
        star (cpsvExample34WordDiag (List.ofFn τ) b)
  refine ⟨c, ?_⟩
  intro X a b
  simp only [physicalObservableTransfer, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  simp_rw [cpsvExample34_evalWord]
  simp only [Matrix.conjTranspose_diagonal, Matrix.mul_apply, Matrix.diagonal_apply,
    Finset.sum_ite_irrel, Finset.ite_sum, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  simp [c, mul_assoc, Finset.sum_mul]

private theorem cpsvExample34_transferMap_isEntrywiseMultiplier :
    IsEntrywiseMultiplier (transferMap cpsvExample34Tensor) := by
  let O : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ := 1
  have hPhys := cpsvExample34_physicalObservableTransfer_isEntrywiseMultiplier 1 O
  rw [show physicalObservableTransfer cpsvExample34Tensor 1 O =
      transferMap cpsvExample34Tensor by
    apply LinearMap.ext
    intro X
    simp [physicalObservableTransfer, transferMap_apply, O, evalWord]] at hPhys
  exact hPhys

private theorem cpsvExample34_transfer_commutes_physicalObservableTransfer
    (L : ℕ) (O : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ) :
    Commute (transferMap cpsvExample34Tensor)
      (physicalObservableTransfer cpsvExample34Tensor L O) :=
  isEntrywiseMultiplier_commute cpsvExample34_transferMap_isEntrywiseMultiplier
    (cpsvExample34_physicalObservableTransfer_isEntrywiseMultiplier L O)

/-- The literal physical correlation-independence claim of CPSV16,
Example 3.4. The result uses `IsPhysicalCID`, not the stronger BNT local
orthogonality, ZCL, or RFP predicates. -/
theorem cpsvExample34_isPhysicalCID :
    IsPhysicalCID cpsvExample34Tensor := by
  intro L₁ L₂ O₁ O₂ n₁ n₂ m₁ m₂ _ _ hsum
  let E := transferMap cpsvExample34Tensor
  let F₁ := physicalObservableTransfer cpsvExample34Tensor L₁ O₁
  let F₂ := physicalObservableTransfer cpsvExample34Tensor L₂ O₂
  have hComm₁ : Commute E F₁ :=
    cpsvExample34_transfer_commutes_physicalObservableTransfer L₁ O₁
  simp only [physicalTwoPointExpectation, ← Module.End.mul_eq_comp]
  congr 1
  calc
    F₂ * E ^ n₂ * (F₁ * E ^ n₁) = F₂ * F₁ * (E ^ n₂ * E ^ n₁) :=
      (hComm₁.pow_left n₂).mul_mul_mul_comm F₂ (E ^ n₁)
    _ = F₂ * F₁ * E ^ (n₂ + n₁) := by rw [← pow_add]
    _ = F₂ * F₁ * E ^ (m₂ + m₁) := by rw [Nat.add_comm n₂ n₁, Nat.add_comm m₂ m₁, hsum]
    _ = F₂ * F₁ * (E ^ m₂ * E ^ m₁) := by rw [← pow_add]
    _ = F₂ * E ^ m₂ * (F₁ * E ^ m₁) :=
      ((hComm₁.pow_left m₂).mul_mul_mul_comm F₂ (E ^ m₁)).symm

private theorem cpsvExample34_invSqrtTwo_sq :
    cpsvExample34InvSqrtTwo ^ 2 = (1 / 2 : ℂ) := by
  norm_num [cpsvExample34InvSqrtTwo, div_pow, Real.sq_sqrt]

private theorem cpsvExample34_invSqrtTwo_ne_half :
    cpsvExample34InvSqrtTwo ≠ (1 / 2 : ℂ) := by
  intro h
  have hsquare := cpsvExample34_invSqrtTwo_sq
  rw [h] at hsquare
  norm_num at hsquare

private def offDiagonalUnit : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 0, 0]

private theorem cpsvExample34_transferMap_offDiagonalUnit :
    transferMap cpsvExample34Tensor offDiagonalUnit =
      cpsvExample34InvSqrtTwo • offDiagonalUnit := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [transferMap_apply, cpsvExample34Tensor, offDiagonalUnit,
      Matrix.mul_apply, Fin.sum_univ_two, cpsvExample34InvSqrtTwo]

/-- The transfer map of the tensor in CPSV16, Example 3.4 is not idempotent.
The off-diagonal matrix unit has transfer eigenvalue $1/\sqrt2$, whose square
is $1/2$, so the second transfer application differs from the first. -/
theorem cpsvExample34_not_isTransferIdempotent :
    ¬ IsTransferIdempotent cpsvExample34Tensor := by
  intro hIdem
  have h := congr_fun (congr_arg DFunLike.coe hIdem) offDiagonalUnit
  simp only [LinearMap.comp_apply, cpsvExample34_transferMap_offDiagonalUnit,
    map_smul] at h
  have h01 := congrFun (congrFun h 0) 1
  simp [offDiagonalUnit, cpsvExample34_invSqrtTwo_sq] at h01
  exact cpsvExample34_invSqrtTwo_ne_half h01.symm

/-- The exact tensor in CPSV16, Example 3.4 has no physical blocking isometry,
so it fails the source equation `AA=A` and is not a pure-state RFP. -/
theorem cpsvExample34_not_hasPhysicalBlockingIsometry :
    ¬ HasPhysicalBlockingIsometry cpsvExample34Tensor := by
  rwa [← isTransferIdempotent_iff_hasPhysicalBlockingIsometry]

/-- The product-state overlap after blocking $n$ spins is
$\langle 0^{\otimes n}|+^{\otimes n}\rangle=2^{-n/2}$, written as
$(1/\sqrt2)^n$. -/
theorem cpsvExample34_blocked_overlap (n : ℕ) :
    ∑ σ : Fin n → Fin 2,
      (if ∀ k, σ k = 0 then (1 : ℂ) else 0) * cpsvExample34InvSqrtTwo ^ n =
        cpsvExample34InvSqrtTwo ^ n := by
  classical
  rw [Finset.sum_ite_irrel]
  simp

end MPSTensor
