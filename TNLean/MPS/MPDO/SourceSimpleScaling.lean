/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTTransport
import TNLean.MPS.MPDO.SourceSimpleTensor

/-!
# Positive rescaling of source-simple MPO tensors

This module records the exact effect of a scalar rescaling on closed MPOs and
physical blocking. It then proves that the normalization-free source simplicity
predicate is invariant under multiplication by a strictly positive real scalar.

An arbitrary nonzero complex scalar does not preserve the MPDO condition: at
chain length `N`, the closed operator is multiplied by `c ^ N`, not by
`‖c‖ ^ (2 * N)`. The positive-real hypothesis is therefore essential.

## Main results

* `MPOTensor.mpo_smul`: scaling every tensor letter by `c` scales the length-`N`
  closed MPO by `c ^ N`.
* `MPOTensor.blockTensor_smul`: length-`L` blocking turns a scalar `c` into
  `c ^ L`.
* `MPOTensor.isMPDO_smul_ofReal_iff`: MPDO is invariant under strictly positive
  real rescaling.
* `MPOTensor.isSourceSimple_smul_ofReal_iff`: source simplicity is invariant
  under strictly positive real rescaling, with the same normal-basis blocks.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Scaling every MPO tensor letter by `c` scales a word by `c` to its length. -/
theorem evalWord_smul (c : ℂ) (M : MPOTensor d D) (is js : List (Fin d))
    (hlen : js.length = is.length) :
    evalWord (c • M) is js = c ^ is.length • evalWord M is js := by
  induction is generalizing js with
  | nil =>
      simp only [List.length_nil, List.length_eq_zero_iff] at hlen
      subst js
      simp
  | cons i is ih =>
      cases js with
      | nil => simp at hlen
      | cons j js =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [evalWord_cons, Pi.smul_apply, ih js hlen, Matrix.mul_smul,
            Matrix.smul_mul, smul_smul]
          simp [pow_succ', mul_comm]

/-- Exact scalar law for closed MPOs: `mpo (c • M) N = c ^ N • mpo M N`. -/
theorem mpo_smul (c : ℂ) (M : MPOTensor d D) (N : ℕ) :
    mpo (c • M) N = c ^ N • mpo M N := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, Matrix.smul_apply]
  rw [evalWord_smul c M (List.ofFn σ) (List.ofFn τ) (by simp), Matrix.trace_smul]
  simp

/-- Exact scalar law for physical blocking: an `L`-site block carries `c ^ L`. -/
theorem blockTensor_smul (c : ℂ) (M : MPOTensor d D) (L : ℕ) :
    blockTensor (c • M) L = c ^ L • blockTensor M L := by
  funext i j
  simp only [blockTensor_apply, Pi.smul_apply]
  rw [evalWord_smul c M (MPSTensor.wordOfBlock d L i)
    (MPSTensor.wordOfBlock d L j) (by simp), MPSTensor.length_wordOfBlock]

/-- Nonnegative real rescaling preserves the MPDO property, including the zero scalar. -/
theorem IsMPDO.smul_ofReal {M : MPOTensor d D} (hM : IsMPDO M) {r : ℝ}
    (hr : 0 ≤ r) :
    IsMPDO ((r : ℂ) • M) := by
  intro N hN
  rw [mpo_smul]
  exact (hM N hN).smul (by positivity : (0 : ℂ) ≤ (r : ℂ) ^ N)

/-- MPDO is invariant under multiplication by a strictly positive real scalar. -/
theorem isMPDO_smul_ofReal_iff (M : MPOTensor d D) {r : ℝ} (hr : 0 < r) :
    IsMPDO ((r : ℂ) • M) ↔ IsMPDO M := by
  constructor
  · intro hscaled
    have hinv : IsMPDO (((r⁻¹ : ℝ) : ℂ) • ((r : ℂ) • M)) :=
      hscaled.smul_ofReal (le_of_lt (inv_pos.mpr hr))
    have hri : (((r⁻¹ : ℝ) : ℂ) * (r : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul]
      simp [ne_of_gt hr]
    simpa only [smul_smul, hri, one_smul] using hinv
  · exact fun hM ↦ hM.smul_ofReal (le_of_lt hr)

end MPOTensor

namespace MPSTensor

variable {d D : ℕ}

/-- Scaling the represented tensor preserves a CPSV basis of normal tensors.

The basis blocks, their normality, and their eventual linear independence are
unchanged. Only the length-`N` spanning coefficients are multiplied by `c ^ N`.
-/
theorem IsCPSVBasisOfNormalTensors.smul_left
    {g : ℕ} {A : MPSTensor d D}
    {blocks : (j : Fin g) → Σ D' : ℕ, MPSTensor d D'}
    (hBNT : IsCPSVBasisOfNormalTensors A blocks) (c : ℂ) :
    IsCPSVBasisOfNormalTensors (c • A) blocks := by
  refine ⟨hBNT.blocks_normal, ?_, hBNT.eventually_li⟩
  intro N hN
  obtain ⟨a, ha⟩ := hBNT.spans_mpv N hN
  refine ⟨fun j ↦ c ^ N * a j, fun σ ↦ ?_⟩
  change mpv (fun i ↦ c • A i) σ = _
  rw [mpv_smul, ha]
  simp only [Finset.mul_sum, mul_assoc]

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- Strictly positive real rescaling preserves source simplicity.

The blocking length and normal-basis blocks are unchanged. The represented
blocked tensor is multiplied by `(r ^ L : ℝ)`, so its length-`N` spanning
coefficients are multiplied by `(r : ℂ) ^ (L * N)`.
-/
theorem IsSourceSimple.smul_ofReal {M : MPOTensor d D} (hM : IsSourceSimple M)
    {r : ℝ} (hr : 0 < r) :
    IsSourceSimple ((r : ℂ) • M) := by
  obtain ⟨hMPDO, hne, L, hL, g, blocks, hBNT, hnil⟩ := hM
  refine ⟨hMPDO.smul_ofReal (le_of_lt hr), ?_, L, hL, g, blocks, ?_, hnil⟩
  · intro N hN
    rw [mpo_smul]
    exact smul_ne_zero (pow_ne_zero N (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))) (hne N hN)
  · rw [blockTensor_smul]
    change MPSTensor.IsCPSVBasisOfNormalTensors
      (((r : ℂ) ^ L) • (blockTensor M L).toMPSTensor) blocks
    exact hBNT.smul_left ((r : ℂ) ^ L)

/-- Source simplicity is invariant under multiplication by a strictly positive real scalar. -/
theorem isSourceSimple_smul_ofReal_iff (M : MPOTensor d D) {r : ℝ} (hr : 0 < r) :
    IsSourceSimple ((r : ℂ) • M) ↔ IsSourceSimple M := by
  constructor
  · intro hscaled
    have hinv : IsSourceSimple (((r⁻¹ : ℝ) : ℂ) • ((r : ℂ) • M)) :=
      hscaled.smul_ofReal (inv_pos.mpr hr)
    have hri : (((r⁻¹ : ℝ) : ℂ) * (r : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul]
      simp [ne_of_gt hr]
    simpa only [smul_smul, hri, one_smul] using hinv
  · exact fun hM ↦ hM.smul_ofReal hr

end MPOTensor
