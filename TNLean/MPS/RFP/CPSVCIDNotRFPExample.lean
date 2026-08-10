/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.RFP.ZeroCorrelationLength
import TNLean.MPS.Tactic.Basic

/-!
# CPSV16 Example 3.4: correlation independence without an RFP

This file formalizes the tensor displayed in arXiv:1606.00608, Example 3.4
(`Ex:ZCL`, lines 450--465). Its positive-length MPV is
$|0,\ldots,0\rangle+|+,\ldots,+\rangle$. The state has physical correlation
independence because all of its diagonal word operators induce commuting
entrywise multipliers. Its transfer map is not idempotent, so it has no
physical blocking isometry and is not a renormalization fixed point.
-/

open scoped Matrix BigOperators

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

/-- The bond-dimension-one $|0\rangle$ component obtained from the first
virtual diagonal entry of `cpsvExample34Tensor`. -/
noncomputable def cpsvExample34ZeroTensor : MPSTensor 2 1 :=
  fun i _ _ => cpsvExample34Tensor i 0 0

/-- The bond-dimension-one $|+\rangle$ component obtained from the second
virtual diagonal entry of `cpsvExample34Tensor`. -/
noncomputable def cpsvExample34PlusTensor : MPSTensor 2 1 :=
  fun i _ _ => cpsvExample34Tensor i 1 1

private noncomputable def cpsvExample34WordDiag (w : List (Fin 2)) : Fin 2 → ℂ
  | 0 => if w.Forall (· = 0) then 1 else 0
  | 1 => cpsvExample34InvSqrtTwo ^ w.length

private theorem cpsvExample34_evalWord (w : List (Fin 2)) :
    evalWord cpsvExample34Tensor w = Matrix.diagonal (cpsvExample34WordDiag w) := by
  induction w with
  | nil =>
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [cpsvExample34WordDiag]
  | cons i w ih =>
      rw [evalWord_cons, ih]
      fin_cases i <;>
        ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [cpsvExample34Tensor, cpsvExample34WordDiag, Matrix.mul_apply,
          Fin.sum_univ_two, pow_succ']

private theorem cpsvExample34_forall_ofFn_zero_iff {N : ℕ} (σ : Fin N → Fin 2) :
    (List.ofFn σ).Forall (· = 0) ↔ ∀ k, σ k = 0 := by
  rw [List.forall_iff_forall_mem, List.forall_mem_iff_get]
  have hlen : (List.ofFn σ).length = N := List.length_ofFn
  constructor
  · intro h k
    have hk : k.val < (List.ofFn σ).length := hlen.symm ▸ k.isLt
    simpa using h ⟨k.val, hk⟩
  · intro h k
    have hk : k.val < N := by omega
    simpa using h ⟨k.val, hk⟩

private theorem cpsvExample34_component_evalWord (a : Fin 2) (w : List (Fin 2)) :
    evalWord (fun i : Fin 2 => fun _ _ : Fin 1 => cpsvExample34Tensor i a a) w =
      fun _ _ : Fin 1 => cpsvExample34WordDiag w a := by
  induction w with
  | nil =>
      ext x y
      fin_cases x
      fin_cases y
      fin_cases a <;> simp [cpsvExample34WordDiag]
  | cons i w ih =>
      rw [evalWord_cons, ih]
      ext x y
      fin_cases x
      fin_cases y
      fin_cases a <;> fin_cases i <;>
        simp [cpsvExample34Tensor, cpsvExample34WordDiag, Matrix.mul_apply, pow_succ']

private theorem cpsvExample34ZeroTensor_mpv {N : ℕ} (σ : Fin N → Fin 2) :
    mpv cpsvExample34ZeroTensor σ = if ∀ k, σ k = 0 then 1 else 0 := by
  rw [mpv, coeff]
  change Matrix.trace (evalWord (fun i _ _ => cpsvExample34Tensor i 0 0) (List.ofFn σ)) = _
  rw [cpsvExample34_component_evalWord]
  simp [Matrix.trace, cpsvExample34WordDiag, cpsvExample34_forall_ofFn_zero_iff]

private theorem cpsvExample34PlusTensor_mpv {N : ℕ} (σ : Fin N → Fin 2) :
    mpv cpsvExample34PlusTensor σ = cpsvExample34InvSqrtTwo ^ N := by
  rw [mpv, coeff]
  change Matrix.trace (evalWord (fun i _ _ => cpsvExample34Tensor i 1 1) (List.ofFn σ)) = _
  rw [cpsvExample34_component_evalWord]
  simp [Matrix.trace, cpsvExample34WordDiag]

/-- The exact positive-length amplitude formula in CPSV16, Example 3.4.
For a nonempty configuration $\sigma$, the first summand is the amplitude of
$|0,\ldots,0\rangle$ and the second is the amplitude of
$|+,\ldots,+\rangle$. -/
theorem cpsvExample34_mpv {N : ℕ} (_hN : 0 < N) (σ : Fin N → Fin 2) :
    mpv cpsvExample34Tensor σ =
      (if ∀ k, σ k = 0 then 1 else 0) + cpsvExample34InvSqrtTwo ^ N := by
  rw [mpv, coeff, cpsvExample34_evalWord]
  simp [Matrix.trace, cpsvExample34WordDiag, cpsvExample34_forall_ofFn_zero_iff]

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

private theorem diagonal_sandwich_apply (u v : Fin 2 → ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    (Matrix.diagonal u * (X * (Matrix.diagonal v)ᴴ)) a b =
      u a * X a b * star (v b) := by
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

private theorem diagonal_sandwich_apply_left (u v : Fin 2 → ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    (Matrix.diagonal u * X * (Matrix.diagonal v)ᴴ) a b =
      u a * X a b * star (v b) := by
  rw [Matrix.mul_assoc]
  exact diagonal_sandwich_apply u v X a b

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
  simp_rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [cpsvExample34_evalWord, diagonal_sandwich_apply]
  dsimp only [c]
  simpa only [Fintype.sum_prod_type, mul_comm, mul_left_comm, mul_assoc] using
    (Fintype.sum_mul_mul_eq_mul_sum_mul (X a b)
      (fun p : (Fin L → Fin 2) × (Fin L → Fin 2) =>
        O p.2 p.1 * cpsvExample34WordDiag (List.ofFn p.1) a)
      (fun p => star (cpsvExample34WordDiag (List.ofFn p.2) b)))

private theorem cpsvExample34_letter_diagonal (i : Fin 2) :
    cpsvExample34Tensor i =
      Matrix.diagonal (cpsvExample34WordDiag [i]) := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [cpsvExample34Tensor, cpsvExample34WordDiag]

private theorem cpsvExample34_transferMap_isEntrywiseMultiplier :
    IsEntrywiseMultiplier (transferMap cpsvExample34Tensor) := by
  let c : Matrix (Fin 2) (Fin 2) ℂ := fun a b =>
    ∑ i : Fin 2, cpsvExample34WordDiag [i] a *
      star (cpsvExample34WordDiag [i] b)
  refine ⟨c, ?_⟩
  intro X a b
  transfer_simp
  change (∑ i : Fin 2, (cpsvExample34Tensor i * X *
    (cpsvExample34Tensor i)ᴴ) a b) = c a b * X a b
  simp_rw [cpsvExample34_letter_diagonal, diagonal_sandwich_apply_left]
  dsimp only [c]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (Fintype.sum_mul_mul_eq_mul_sum_mul (X a b)
      (fun i : Fin 2 => cpsvExample34WordDiag [i] a)
      (fun i => star (cpsvExample34WordDiag [i] b)))

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
    _ = F₂ * F₁ * E ^ (m₂ + m₁) := by
      rw [Nat.add_comm n₂ n₁, Nat.add_comm m₂ m₁, hsum]
    _ = F₂ * F₁ * (E ^ m₂ * E ^ m₁) := by rw [← pow_add]
    _ = F₂ * E ^ m₂ * (F₁ * E ^ m₁) :=
      ((hComm₁.pow_left m₂).mul_mul_mul_comm F₂ (E ^ m₁)).symm

private theorem cpsvExample34_invSqrtTwo_sq :
    cpsvExample34InvSqrtTwo ^ 2 = (1 / 2 : ℂ) := by
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hreal : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt (by norm_num)]
  rw [cpsvExample34InvSqrtTwo, ← Complex.ofReal_pow]
  exact (congrArg (fun x : ℝ => (x : ℂ)) hreal).trans (by norm_num)

private theorem cpsvExample34_invSqrtTwo_ne_half :
    cpsvExample34InvSqrtTwo ≠ (1 / 2 : ℂ) := by
  intro h
  have hsquare := cpsvExample34_invSqrtTwo_sq
  rw [h] at hsquare
  norm_num at hsquare

private theorem star_cpsvExample34InvSqrtTwo :
    star cpsvExample34InvSqrtTwo = cpsvExample34InvSqrtTwo := by
  simp [cpsvExample34InvSqrtTwo]

private def offDiagonalUnit : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 0, 0]

private theorem cpsvExample34_transferMap_offDiagonalUnit :
    transferMap cpsvExample34Tensor offDiagonalUnit =
      cpsvExample34InvSqrtTwo • offDiagonalUnit := by
  ext a b
  transfer_simp
  change (∑ i : Fin 2, (cpsvExample34Tensor i * offDiagonalUnit *
    (cpsvExample34Tensor i)ᴴ) a b) =
      (cpsvExample34InvSqrtTwo • offDiagonalUnit) a b
  simp_rw [cpsvExample34_letter_diagonal, diagonal_sandwich_apply_left]
  fin_cases a <;> fin_cases b <;>
    simp [cpsvExample34WordDiag, offDiagonalUnit, star_cpsvExample34InvSqrtTwo]

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
  have hscalar : cpsvExample34InvSqrtTwo * cpsvExample34InvSqrtTwo =
      cpsvExample34InvSqrtTwo := by
    simpa [offDiagonalUnit] using h01
  rw [← pow_two, cpsvExample34_invSqrtTwo_sq] at hscalar
  exact cpsvExample34_invSqrtTwo_ne_half hscalar.symm

/-- The exact tensor in CPSV16, Example 3.4 has no physical blocking isometry,
so it fails the source equation `AA=A` and is not a pure-state RFP. -/
theorem cpsvExample34_not_hasPhysicalBlockingIsometry :
    ¬ HasPhysicalBlockingIsometry cpsvExample34Tensor := by
  intro hBlocking
  exact cpsvExample34_not_isTransferIdempotent
    ((isTransferIdempotent_iff_hasPhysicalBlockingIsometry _).mpr hBlocking)

private theorem cpsvExample34_blocked_overlap_sum (n : ℕ) :
    ∑ σ : Fin n → Fin 2,
      (if ∀ k, σ k = 0 then (1 : ℂ) else 0) * cpsvExample34InvSqrtTwo ^ n =
        cpsvExample34InvSqrtTwo ^ n := by
  classical
  let zeroConfig : Fin n → Fin 2 := fun _ => 0
  rw [Fintype.sum_eq_single zeroConfig]
  · simp [zeroConfig]
  · intro σ hσ
    have hnot : ¬ ∀ k, σ k = 0 := by
      intro hzero
      apply hσ
      funext k
      exact hzero k
    simp [hnot]

/-- The formal overlap between the two product-state components of the tensor
in CPSV16, Example 3.4 is
$\langle 0^{\otimes n}|+^{\otimes n}\rangle=(1/\sqrt2)^n$. -/
theorem cpsvExample34_blocked_overlap (n : ℕ) :
    mpvOverlap cpsvExample34ZeroTensor cpsvExample34PlusTensor n =
      cpsvExample34InvSqrtTwo ^ n := by
  rw [mpvOverlap]
  simp_rw [cpsvExample34ZeroTensor_mpv, cpsvExample34PlusTensor_mpv,
    star_pow, star_cpsvExample34InvSqrtTwo]
  exact cpsvExample34_blocked_overlap_sum n

end MPSTensor
