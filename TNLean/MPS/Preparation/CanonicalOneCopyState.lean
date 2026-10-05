/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CanonicalFixedPoint
import TNLean.MPS.Preparation.OneCopyPairState
import TNLean.MPS.Preparation.SectorCopyCoordinates

/-!
# The corrected one-copy state of a canonical tensor

For the actual normal blocks of a BNT canonical tensor, choose the unique normalized
faithful transfer fixed points and place their pairs on one retained copy of each block.
At length `N = qM`, use the corrected coefficients
`β'_j = (∑_k μ_{j,k}^{qM}) (c_j / μ_{j,κ_j}^q)^M`, where
`c_j = (∑_k |μ_{j,k}|^{2q})^{1/2}`. The resulting normalized state has the GHZ form of
arXiv:2307.01696, eq. (19). Its image under the polar factor of the actual blocked canonical
tensor has the same normalized overlap as the corrected copy-isometry construction.

**False source (coefficients):** eq. (S7) uses `β_j` instead of `β'_j`. This fails even with
one copy per block and complex phases. The corrected multiplicity-one coefficient is
`|μ_j|^N`. See `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex` and
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix QuantumCircuit

namespace MPSTensor.IsBNTCanonicalForm

variable {d : ℕ} {P : SectorDecomposition d}

/-- The normalized one-copy fixed-point state at `N = qM`, with the actual canonical block
fixed points and corrected weights. This is the corrected instance of arXiv:2307.01696,
eqs. (19) and (S7), described in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`. -/
noncomputable def oneCopyFixedPointState (h : IsBNTCanonicalForm P)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) (q M : ℕ) :
    (Fin M → Fin P.totalDim × Fin P.totalDim) → ℂ :=
  nonNormalFixedPointState (ghzAmplitude (oneCopyWeight P.copyWeights κ q M))
    (h.basisFixedPointPair κ)

/-- In bond coordinates the actual canonical one-copy state is obtained by applying the
pair isometry to a GHZ state, as in arXiv:2307.01696, the paragraph after eq. (19), with
the corrected coefficients of `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`. -/
theorem oneCopyFixedPointState_eq_tensorPower_mulVec_ghzState (h : IsBNTCanonicalForm P)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) (q M : ℕ)
    (p : Fin M → Fin P.totalDim × Fin P.totalDim) :
    h.oneCopyFixedPointState κ q M ((bondRegrouping M P.totalDim).symm p) =
      (Matrix.tensorPower M (pairIsometry (h.basisFixedPointPair κ)) *ᵥ
        ghzState (ghzAmplitude (oneCopyWeight P.copyWeights κ q M))) p :=
  nonNormalFixedPointState_eq_tensorPower_mulVec_ghzState _ _ p

/-- The corrected canonical one-copy state is normalized at every positive blocked length
with a nonzero coefficient vector. The pairs and their unit norms are derived from the
canonical tensor, not supplied as hypotheses (arXiv:2307.01696, eqs. (19) and (S8)). -/
theorem oneCopyFixedPointState_norm_sq (h : IsBNTCanonicalForm P)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) {q M : ℕ} (hM : M ≠ 0)
    (hβ : P.coeff (q * M) ≠ 0) :
    ∑ c : Fin M → Fin P.totalDim × Fin P.totalDim,
      star (h.oneCopyFixedPointState κ q M c) * h.oneCopyFixedPointState κ q M c = 1 := by
  have hcoeff : bntWeight P.copyWeights (M * q) = P.coeff (q * M) := by
    funext j
    simp only [SectorDecomposition.bntWeight_copyWeights, Nat.mul_comm]
  have hβ' : bntWeight P.copyWeights (M * q) ≠ 0 := hcoeff.symm ▸ hβ
  exact nonNormalFixedPointState_norm_sq hM (oneCopyWeight_ne_zero κ hβ')
    (h.inner_basisFixedPointPair κ)

/-- Before normalization, the corrected one-copy state and the copy-isometry construction
have exactly the same physical vector for the actual canonical tensor and its faithful
block fixed points. This is the corrected identity replacing arXiv:2307.01696, eq. (S7);
see `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`. -/
theorem nonNormalApproxVector_oneCopyFixedPoint (h : IsBNTCanonicalForm P)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) {q : ℕ} (hq : q ≠ 0) (M : ℕ) :
    nonNormalApproxVector P.toTensor q M (oneCopyWeight P.copyWeights κ q M)
        (h.basisFixedPointPair κ) =
      copyApproxVector P.toTensor q M (P.coeff (q * M))
        (copyIsometry P.copyCoord P.copyWeights q) h.basisFixedPoint := by
  rw [P.toTensor_eq_repeatedBlockSum]
  change nonNormalApproxVector _ _ _ _
    (fun j => embedPair (P.copyCoord j (κ j)) (fixedPointPair (h.basisFixedPoint j))) = _
  rw [nonNormalApproxVector_repeatedBlockSum_oneCopy P.copyCoord_injective
    P.copyCoord_disjoint P.copyWeights hq]
  congr 1
  funext j
  have hc : (copyNorm P.copyWeights q j : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (copyNorm_pos (P.copyWeights.weight_fun_ne_zero j) q).ne'
  have hμ : P.copyWeights j (κ j) ^ q ≠ 0 :=
    pow_ne_zero q (P.copyWeights.weight_ne_zero j (κ j))
  rw [oneCopyWeight, SectorDecomposition.bntWeight_copyWeights, Nat.mul_comm M q]
  rw [mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm (copyNorm P.copyWeights q j : ℂ),
    div_self (mul_ne_zero hμ hc), one_pow, mul_one]

/-- The physical image of the actual canonical one-copy pairs, with corrected weights,
has the same normalized overlap with the target as the corrected copy-isometry state.
The tensor is `P.toTensor` itself, the fixed points are determined by its basis blocks,
and the coefficient length is exactly `qM`.

This instantiates the correction to arXiv:2307.01696, eq. (S7), proved in
`docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`. -/
theorem nonNormalApproxOverlap_oneCopyFixedPoint (h : IsBNTCanonicalForm P)
    (κ : (j : Fin P.basisCount) → Fin (P.copies j)) {q : ℕ} (hq : q ≠ 0) (M : ℕ) :
    nonNormalApproxOverlap P.toTensor q M
        (ghzAmplitude (oneCopyWeight P.copyWeights κ q M)) (h.basisFixedPointPair κ) =
      copyApproxOverlap P.toTensor q M (ghzAmplitude (P.coeff (q * M)))
        (copyIsometry P.copyCoord P.copyWeights q) h.basisFixedPoint := by
  rw [P.toTensor_eq_repeatedBlockSum]
  change nonNormalApproxOverlap _ _ _ _
    (fun j => embedPair (P.copyCoord j (κ j)) (fixedPointPair (h.basisFixedPoint j))) = _
  simpa only [SectorDecomposition.bntWeight_copyWeights, Nat.mul_comm] using
    nonNormalApproxOverlap_repeatedBlockSum_oneCopy P.copyCoord_injective
      P.copyCoord_disjoint P.copyWeights hq κ h.basisFixedPoint M

end MPSTensor.IsBNTCanonicalForm
