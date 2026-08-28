/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Simple

/-!
# Positive rescaling of simple MPO tensors

This module records the exact effect of a scalar rescaling on closed MPOs and
physical blocking. It then proves that simplicity is invariant under
multiplication by a strictly positive real scalar.

An arbitrary nonzero complex scalar does not preserve the MPDO condition: at
chain length `N`, the closed operator is multiplied by `c ^ N`, not by
`‖c‖ ^ (2 * N)`. The positive-real hypothesis is therefore essential.

## Main results

* `MPOTensor.mpo_smul`: scaling every tensor letter by `c` scales the length-`N`
  closed MPO by `c ^ N`.
* `MPOTensor.blockTensor_smul`: length-`L` blocking turns a scalar `c` into
  `c ^ L`.
* `MPOTensor.normalizedMPO_smul`: the normalized density operator is unchanged
  by any nonzero complex rescaling of the tensor.
* `MPOTensor.isMPDO_smul_ofReal_iff`: MPDO is invariant under strictly positive
  real rescaling.
* `MPOTensor.isSimple_smul_ofReal_iff`: simplicity is invariant under strictly
  positive real rescaling, with the same representatives.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.7, lines 815--822
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Scaling every MPO tensor letter by `c` scales a word by `c` to its length.

Project-derived from the closed-word definition underlying the MPDO formula in
arXiv:1606.00608, lines 623--630. -/
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

/-- Exact scalar law for closed MPOs: `mpo (c • M) N = c ^ N • mpo M N`.

Project-derived from the periodic MPDO formula in arXiv:1606.00608,
lines 623--630. -/
theorem mpo_smul (c : ℂ) (M : MPOTensor d D) (N : ℕ) :
    mpo (c • M) N = c ^ N • mpo M N := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, Matrix.smul_apply]
  rw [evalWord_smul c M (List.ofFn σ) (List.ofFn τ) (by simp), Matrix.trace_smul]
  simp

/-- Exact scalar law for physical blocking: an `L`-site block carries `c ^ L`.

Project-derived from the positive physical blocking at arXiv:1606.00608,
line 815, using the project's explicit block-word encoding. -/
theorem blockTensor_smul (c : ℂ) (M : MPOTensor d D) (L : ℕ) :
    blockTensor (c • M) L = c ^ L • blockTensor M L := by
  funext i j
  simp only [blockTensor_apply, Pi.smul_apply]
  rw [evalWord_smul c M (MPSTensor.wordOfBlock d L i)
    (MPSTensor.wordOfBlock d L j) (by simp), MPSTensor.length_wordOfBlock]

/-- Rescaling the tensor by a nonzero complex scalar leaves every normalized
density operator unchanged.  At chain length `N` the closed operator and its
trace are both multiplied by `c ^ N`, and the two factors cancel in the
normalization; when the trace vanishes, both sides are zero by the
inverse-of-zero convention, so no nonzero-trace hypothesis is needed.

Project-derived from the normalization convention of arXiv:1606.00608,
line 792, and the exact closed-MPO scaling law above. -/
theorem normalizedMPO_smul {c : ℂ} (hc : c ≠ 0) (M : MPOTensor d D) (N : ℕ) :
    normalizedMPO (c • M) N = normalizedMPO M N := by
  have hcN : c ^ N ≠ 0 := pow_ne_zero N hc
  rw [normalizedMPO, normalizedMPO, mpo_smul, Matrix.trace_smul, smul_smul,
    smul_eq_mul]
  congr 1
  field_simp

/-- Nonnegative real rescaling preserves the MPDO property, including the zero scalar.

Project-derived from the MPDO positivity condition in arXiv:1606.00608,
lines 623--630, and the exact closed-MPO scaling law above. -/
theorem IsMPDO.smul_ofReal {M : MPOTensor d D} (hM : IsMPDO M) {r : ℝ}
    (hr : 0 ≤ r) :
    IsMPDO ((r : ℂ) • M) := by
  intro N hN
  rw [mpo_smul]
  exact (hM N hN).smul (by positivity : (0 : ℂ) ≤ (r : ℂ) ^ N)

/-- MPDO is invariant under multiplication by a strictly positive real scalar.

Project-derived from the MPDO positivity condition in arXiv:1606.00608,
lines 623--630, by applying nonnegative rescaling in both directions. -/
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

namespace MPOTensor

variable {d D : ℕ}

/-- Strictly positive real rescaling preserves simplicity.

The blocking length, normal representatives, and copy multiplicities are unchanged.
The represented blocked tensor is multiplied by `(r : ℂ) ^ L`, so every copy weight
is multiplied by that same nonzero scalar.

Project-derived from simplicity in arXiv:1606.00608, Definition 4.7,
lines 815--822. -/
theorem IsSimple.smul_ofReal {M : MPOTensor d D} (hM : IsSimple M)
    {r : ℝ} (hr : 0 < r) :
    IsSimple ((r : ℂ) • M) := by
  obtain ⟨hMPDO, L, hL, P, hPres, hNonNil⟩ := hM
  have hScale : ((r : ℂ) ^ L) ≠ 0 :=
    pow_ne_zero L (Complex.ofReal_ne_zero.mpr hr.ne')
  refine ⟨hMPDO.smul_ofReal (le_of_lt hr), L, hL,
    P.scaleWeights ((r : ℂ) ^ L) hScale, ?_, ?_⟩
  · rw [blockTensor_smul]
    exact hPres.smul_left ((r : ℂ) ^ L) hScale
  · intro j
    exact hNonNil j

/-- Simplicity is invariant under multiplication by a strictly positive real scalar.

Project-derived from simplicity in arXiv:1606.00608, Definition 4.7,
lines 815--822, by applying positive rescaling in both directions. -/
theorem isSimple_smul_ofReal_iff (M : MPOTensor d D) {r : ℝ} (hr : 0 < r) :
    IsSimple ((r : ℂ) • M) ↔ IsSimple M := by
  constructor
  · intro hscaled
    have hinv : IsSimple (((r⁻¹ : ℝ) : ℂ) • ((r : ℂ) • M)) :=
      hscaled.smul_ofReal (inv_pos.mpr hr)
    have hri : (((r⁻¹ : ℝ) : ℂ) * (r : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul]
      simp [ne_of_gt hr]
    simpa only [smul_smul, hri, one_smul] using hinv
  · exact fun hM ↦ hM.smul_ofReal hr

end MPOTensor
