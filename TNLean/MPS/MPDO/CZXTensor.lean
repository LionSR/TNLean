/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXGaussCircuitTuple
import TNLean.MPS.MPU.Basic

/-!
# The exact FBC25 CZX matrix product unitary

The shared bond-two tensor is the once-blocked, Z-decorated tensor of
arXiv:2502.20257, `eq:MPU_CZX` (lines 4503–4547). The weight in `eq:CZ`
and `eq:deltas` (lines 3795–3851) is the unnormalized Hadamard weight
`W = √2 H`. Thus this is not the block of the normalized tensor printed in
arXiv:1703.09188, lines 1906–1943: if that tensor is P, the present tensor is
`(Z ⊗ Z) blockTwo (√2 • P)`. The output Z gates are part of the 2025 diagram.

We use exactly the two-bit ordering of `CZX.siteBits`. No GHZ, fusion,
defect, injectivity or classification assertion is made here.
-/

noncomputable section

open scoped BigOperators

namespace MPOTensor.CZX

/-- The corrected and output-Z-decorated one-qubit constituent of FBC25
`eq:MPU_CZX`; its Hadamard weight is unnormalized (`eq:CZ`, `eq:deltas`). -/
def decoratedSiteTensor : MPOTensor 2 2 :=
  fun u d l r ↦ if u = 1 - (d : ZMod 2) ∧ l = u then
    (-1 : ℂ) ^ (u.val + l.val * r.val) else 0

/-- The single shared CZX tensor, FBC25 `eq:MPU_CZX`, lines 4503–4547.
Uses the existing two-site physical blocking, in the ordering `2a+b`.
Unlike the tensor printed in arXiv:1703.09188, lines 1906–1943, the
constituent uses `√2 H` and an output Z gate. -/
def tensor : MPOTensor 4 2 := blockTwo decoratedSiteTensor

/-- General physical blocking gives the same tensor after the maintained
length-two index equivalence. -/
theorem tensor_eq_blockTensor : tensor = fun i j ↦
    blockTensor decoratedSiteTensor 2 (twoSiteBlockEquiv 2 i) (twoSiteBlockEquiv 2 j) :=
  blockTwo_eq_blockTensor_reindex decoratedSiteTensor

/-- Both matter bits complemented, in the established site encoding. -/
def complementSite : Equiv.Perm (Fin 4) :=
  siteBits.trans ((Equiv.prodCongr (Equiv.subLeft (1 : ZMod 2))
    (Equiv.subLeft (1 : ZMod 2))).trans siteBits.symm)

/-- Complement every matter bit in the periodic configuration. -/
def complement (N : ℕ) : Equiv.Perm (Fin N → Fin 4) :=
  Equiv.piCongrRight fun _ ↦ complementSite

/-- The local integer exponent `a+b+ab+br` in FBC25 `eq:MPU_CZX`.
Bit values are natural numbers, so no parity representative is implicit. -/
def edgeExponent (i : Fin 4) (r : Fin 2) : ℕ :=
  (siteBits i).1.val + (siteBits i).2.val +
    (siteBits i).1.val * (siteBits i).2.val + (siteBits i).2.val * r.val

/-- The displayed bond-two coordinates of FBC25 `eq:MPU_CZX`. -/
theorem tensor_apply (i j : Fin 4) (l r : Fin 2) :
    tensor i j l r =
      if i = complementSite j ∧ l = (show Fin 2 from (siteBits i).1) then
        (-1 : ℂ) ^ edgeExponent i r else 0 := by
  have hc : ∀ j : Fin 4, complementSite j = j.rev := by decide
  have hb : ∀ i : Fin 4, (siteBits i).1 =
      (show ZMod 2 from Fin.divNat (m := 2) (n := 2) i) := by decide
  have he : ∀ (i : Fin 4) (r : Fin 2), edgeExponent i r =
      (Fin.divNat (m := 2) (n := 2) i).val +
      (Fin.modNat (m := 2) (n := 2) i).val +
      (Fin.divNat (m := 2) (n := 2) i).val *
      (Fin.modNat (m := 2) (n := 2) i).val +
      (Fin.modNat (m := 2) (n := 2) i).val * r.val := by decide
  rw [hc, hb, he]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
    norm_num [tensor, blockTwo, decoratedSiteTensor, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.divNat, Fin.modNat, Fin.rev]

/-- FBC25 `eq:MPU_CZX` written with the six individual binary coordinates.
The three conditions are the three Kronecker deltas in the diagram. -/
theorem tensor_apply_bits (a b c d l r : ZMod 2) :
    tensor (siteBits.symm (a, b)) (siteBits.symm (c, d)) l r =
      if a = 1 - c ∧ b = 1 - d ∧ l = a then
        (-1 : ℂ) ^ (a.val + b.val + a.val * b.val + b.val * r.val) else 0 := by
  erw [tensor_apply]
  have hc : (siteBits.symm (a, b) = complementSite (siteBits.symm (c, d)) ∧
      l = (show Fin 2 from (siteBits (siteBits.symm (a, b))).1)) ↔
      (a = 1 - c ∧ b = 1 - d ∧ l = a) := by
    generalize_decide a, b, c, d, l
  have he : edgeExponent (siteBits.symm (a, b)) r =
      a.val + b.val + a.val * b.val + b.val * r.val := by
    unfold edgeExponent
    rw [Equiv.apply_symm_apply]
    rfl
  exact ite_congr (propext hc) (fun _ ↦ congrArg (fun n ↦ (-1 : ℂ) ^ n) he) (fun _ ↦ rfl)

/-- The exponent summed around a periodic chain, with cyclic successor `j+1`. -/
def cyclicExponent {N : ℕ} [NeZero N] (s : Fin N → Fin 4) : ℕ :=
  ∑ j, edgeExponent (s j) (siteBits (s (j + 1))).1

/-- Exact all-positive-length cyclic contraction of FBC25 `eq:MPU_CZX`.
The output configuration supplies the displayed exponent. -/
theorem mpo_tensor_apply {N : ℕ} [NeZero N] (s t : Fin N → Fin 4) :
    mpo tensor N s t = if s = complement N t then
      (-1 : ℂ) ^ cyclicExponent s else 0 := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  have h := MPSTensor.trace_evalWord_eq_sum_cyclic tensor.toMPSTensor
    (fun n ↦ finProdFinEquiv (s n, t n))
  rw [MPSTensor.evalWord_ofFn_eq_prod] at h
  have h' : (List.ofFn fun i ↦ tensor (s i) (t i)).prod.trace =
      ∑ g : Fin N → Fin 2, ∏ v : Fin N,
        tensor (s v) (t v) (g v) (g (v + 1)) := by
    simpa only [toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat] using h
  rw [h']
  let g0 : Fin N → Fin 2 := fun n ↦ (siteBits (s n)).1
  rw [Fintype.sum_eq_single g0]
  · by_cases hst : s = complement N t
    · have hp : ∀ n, s n = complementSite (t n) := fun n ↦ congrFun hst n
      rw [ite_eq_left hst]
      calc
        _ = ∏ n, (-1 : ℂ) ^ edgeExponent (s n) (g0 (n + 1)) := by
          apply Finset.prod_congr rfl
          intro n _
          rw [tensor_apply, ite_eq_left ⟨hp n, rfl⟩]
        _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
    · rw [ite_eq_right hst]
      have hn : ∃ n, s n ≠ complementSite (t n) := Function.ne_iff.mp hst
      obtain ⟨n, hn⟩ := hn
      apply Finset.prod_eq_zero (Finset.mem_univ n)
      simp [tensor_apply, hn]
  · intro g hg
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    simp [tensor_apply, show g n ≠ (siteBits (s n)).1 from hn]

/-- Monomial form with the phase attached to the input column. It is evaluated
on the complemented input, so no extraneous length-dependent phase occurs. -/
theorem mpo_tensor {N : ℕ} [NeZero N] :
    mpo tensor N = Matrix.monomial (complement N)
      (fun t ↦ (-1 : ℂ) ^ cyclicExponent (complement N t)) := by
  ext s t
  rw [mpo_tensor_apply, Matrix.monomial_apply]
  split_ifs with h
  · rw [h]
  · rfl

/-- The FBC25 CZX operator is unitary at every positive blocked length,
including one (stronger than the `IsMPU` length requirement). -/
theorem mpo_tensor_mem_unitaryGroup {N : ℕ} [NeZero N] :
    mpo tensor N ∈ Matrix.unitaryGroup (Fin N → Fin 4) ℂ := by
  rw [mpo_tensor]
  refine Matrix.monomial_mem_unitaryGroup _ _ fun t ↦ ?_
  rw [star_pow, star_neg, star_one, ← mul_pow]
  simp

/-- The exact shared FBC25 tensor is an MPU. -/
theorem tensor_isMPU : IsMPU tensor := by
  intro N hN
  let : NeZero N := ⟨by omega⟩
  exact mpo_tensor_mem_unitaryGroup

end MPOTensor.CZX
