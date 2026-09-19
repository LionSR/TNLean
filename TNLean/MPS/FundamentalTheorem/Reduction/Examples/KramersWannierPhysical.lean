/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.KramersWannier
import TNLean.MPS.Core.CyclicTrace

/-!
# The periodic Kramers–Wannier kernel and spin flip

The raw periodic operator of `kwTensor` has entries
`(-1)^(∑ j, a j * (b j + b (j + 1)))` at positive length, with the first
physical index denoting the output. The trace is not normalized by the bond
dimension. At length zero its value is two, not the empty phase product one.

Complementing the input leaves the kernel unchanged. Consequently the operator
absorbs global spin flip, annihilates spin-flip-odd vectors, and is not invertible
on the full periodic spin space.

The kernel convention is the unnormalized version of the primal-to-dual map in
Aasen–Mong–Fendley, arXiv:1601.07185, with the dual output at site `j + 1/2`
identified with output site `j`. The local tensor is the one recorded in
`Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §1.1.
-/

noncomputable section

open scoped Matrix BigOperators

namespace KWExample

open MPSTensor

/-- The local entries of the existing duality tensor. The row is fixed by the
input physical bit, and the remaining factor is a binary phase. -/
theorem kwTensor_apply (a b u v : Fin 2) :
    kwTensor a b u v =
      if u = b then (-1 : ℂ) ^ (a.val * (b.val + v.val)) else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases u <;> fin_cases v <;>
    norm_num [kwTensor, kwIntTensor, complexOfInt]

/-- Contracting the positive-length periodic tensor gives the product of the
nearest-neighbor phases, with cyclic successor `j + 1`. -/
theorem kwTensor_mpo_eq_prod {L : ℕ} [NeZero L] (a b : Fin L → Fin 2) :
    kwTensor.mpo L a b =
      ∏ j : Fin L, (-1 : ℂ) ^ ((a j).val * ((b j).val + (b (j + 1)).val)) := by
  classical
  change Matrix.trace (MPOTensor.evalWord kwTensor (List.ofFn a) (List.ofFn b)) = _
  rw [← MPOTensor.evalWord_toMPSTensor_pairConfig,
    MPSTensor.trace_evalWord_eq_sum_cyclic]
  have hlocal (j : Fin L) (g : Fin L → Fin 2) :
      kwTensor.toMPSTensor (finProdFinEquiv (a j, b j)) (g j) (g (j + 1)) =
        if g j = b j then
          (-1 : ℂ) ^ ((a j).val * ((b j).val + (g (j + 1)).val)) else 0 := by
    generalize a j = x, b j = y
    fin_cases x <;> fin_cases y <;> exact kwTensor_apply _ _ _ _
  simp_rw [hlocal]
  rw [Finset.sum_eq_single b]
  · simp
  · intro g _ hgb
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hgb
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  · simp

/-- The positive-length periodic Kramers–Wannier kernel as a single phase.
The sum and the arithmetic inside its exponent are in the natural numbers. -/
theorem kwTensor_mpo_eq_pow_sum {L : ℕ} [NeZero L] (a b : Fin L → Fin 2) :
    kwTensor.mpo L a b =
      (-1 : ℂ) ^ (∑ j : Fin L, (a j).val * ((b j).val + (b (j + 1)).val)) := by
  rw [kwTensor_mpo_eq_prod, Finset.prod_pow_eq_pow_sum]

/-- The empty periodic contraction is the trace of the virtual identity of
size two. It is not the empty product of the positive-length phase formula. -/
theorem kwTensor_mpo_zero (a b : Fin 0 → Fin 2) : kwTensor.mpo 0 a b = 2 := by
  norm_num [MPOTensor.mpo, MPOTensor.mpoMatrixEntry, MPOTensor.evalWord,
    Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Complement every physical bit. On `Fin 2`, `Fin.rev` exchanges zero and one. -/
def flipConfig {L : ℕ} (b : Fin L → Fin 2) : Fin L → Fin 2 := fun j => (b j).rev

/-- Global complementation is an involution, including at length zero. -/
@[simp] theorem flipConfig_flipConfig {L : ℕ} (b : Fin L → Fin 2) :
    flipConfig (flipConfig b) = b := by
  funext j
  exact Fin.rev_rev (b j)

/-- The matrix of global spin flip, sending the basis vector at `b` to the
basis vector at its complement. -/
def spinFlip (L : ℕ) : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ :=
  fun a b => if a = flipConfig b then 1 else 0

/-- Complementing the input configuration leaves the periodic kernel unchanged. -/
theorem kwTensor_mpo_flip_input {L : ℕ} [NeZero L] (a b : Fin L → Fin 2) :
    kwTensor.mpo L a (flipConfig b) = kwTensor.mpo L a b := by
  rw [kwTensor_mpo_eq_prod, kwTensor_mpo_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  change (-1 : ℂ) ^ ((a j).val * ((b j).rev.val + (b (j + 1)).rev.val)) = _
  generalize a j = x, b j = y, b (j + 1) = z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num

/-- Complementing the output configuration leaves the periodic kernel unchanged. -/
theorem kwTensor_mpo_flip_output {L : ℕ} [NeZero L] (a b : Fin L → Fin 2) :
    kwTensor.mpo L (flipConfig a) b = kwTensor.mpo L a b := by
  have hphase (x y z : Fin 2) :
      (-1 : ℂ) ^ (x.rev.val * (y.val + z.val)) =
        ((-1 : ℂ) ^ y.val * (-1 : ℂ) ^ z.val) *
          (-1 : ℂ) ^ (x.val * (y.val + z.val)) := by
    fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num
  rw [kwTensor_mpo_eq_prod, kwTensor_mpo_eq_prod]
  simp only [flipConfig, hphase, Finset.prod_mul_distrib]
  have hshift : (∏ j : Fin L, (-1 : ℂ) ^ (b (j + 1)).val) =
      ∏ j : Fin L, (-1 : ℂ) ^ (b j).val :=
    Fintype.prod_equiv (Equiv.addRight (1 : Fin L)) _ _ (fun _ => rfl)
  rw [hshift, ← Finset.prod_mul_distrib]
  have hsq (j : Fin L) : (-1 : ℂ) ^ (b j).val * (-1 : ℂ) ^ (b j).val = 1 := by
    generalize b j = x
    fin_cases x <;> norm_num
  simp only [hsq, Finset.prod_const_one, one_mul]

/-- The raw periodic operator absorbs global spin flip on its input. -/
theorem kwTensor_mpo_mul_spinFlip {L : ℕ} [NeZero L] :
    kwTensor.mpo L * spinFlip L = kwTensor.mpo L := by
  classical
  ext a b
  simp only [Matrix.mul_apply, spinFlip, mul_ite, mul_one, mul_zero]
  simpa using kwTensor_mpo_flip_input a b

/-- The raw periodic operator absorbs global spin flip on its output. -/
theorem spinFlip_mul_kwTensor_mpo {L : ℕ} [NeZero L] :
    spinFlip L * kwTensor.mpo L = kwTensor.mpo L := by
  classical
  have hiff (a c : Fin L → Fin 2) : a = flipConfig c ↔ c = flipConfig a := by
    constructor <;> intro h
    · rw [h, flipConfig_flipConfig]
    · rw [h, flipConfig_flipConfig]
  ext a b
  simp only [Matrix.mul_apply, spinFlip, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (flipConfig a)]
  · simpa only [flipConfig_flipConfig, ite_true] using kwTensor_mpo_flip_output a b
  · intro c _ hc
    simp only [show a ≠ flipConfig c from fun h => hc ((hiff a c).mp h), ite_false]
  · simp

/-- Every spin-flip-odd vector is annihilated. This proves inclusion in the
kernel, not an equality of subspaces or a rank formula. -/
theorem kwTensor_mpo_mulVec_eq_zero_of_odd {L : ℕ} [NeZero L]
    (v : (Fin L → Fin 2) → ℂ) (hv : spinFlip L *ᵥ v = -v) :
    kwTensor.mpo L *ᵥ v = 0 := by
  have h : -(kwTensor.mpo L *ᵥ v) = kwTensor.mpo L *ᵥ v := by
    calc
      -(kwTensor.mpo L *ᵥ v) = kwTensor.mpo L *ᵥ (spinFlip L *ᵥ v) := by
        rw [hv, Matrix.mulVec_neg]
      _ = (kwTensor.mpo L * spinFlip L) *ᵥ v := Matrix.mulVec_mulVec v _ _
      _ = kwTensor.mpo L *ᵥ v := by rw [kwTensor_mpo_mul_spinFlip]
  ext a
  have ha := congrFun h a
  change -(kwTensor.mpo L *ᵥ v) a = (kwTensor.mpo L *ᵥ v) a at ha
  change (kwTensor.mpo L *ᵥ v) a = 0
  linear_combination -ha / 2

/-- The periodic Kramers–Wannier matrix is not a unit at any positive length.
The constant-zero and constant-one inputs have identical columns but are distinct. -/
theorem kwTensor_mpo_not_isUnit {L : ℕ} [NeZero L] :
    ¬ IsUnit (kwTensor.mpo L) := by
  classical
  intro hunit
  have hcol : kwTensor.mpo L *ᵥ Pi.single (fun _ : Fin L => (0 : Fin 2)) 1 =
      kwTensor.mpo L *ᵥ Pi.single (flipConfig (fun _ : Fin L => (0 : Fin 2))) 1 := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    funext a
    exact (kwTensor_mpo_flip_input a _).symm
  have heq := Matrix.mulVec_injective_of_isUnit hunit hcol
  have hne : (fun _ : Fin L => (0 : Fin 2)) ≠
      flipConfig (fun _ : Fin L => (0 : Fin 2)) := by
    intro h
    have h0 := congrFun h ⟨0, NeZero.pos L⟩
    norm_num [flipConfig] at h0
  have h0 := congrFun heq (fun _ : Fin L => (0 : Fin 2))
  simp [hne] at h0

end KWExample
