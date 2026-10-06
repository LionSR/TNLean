/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RectangularIntervalBlocks
import QICLean.Analysis.GeometricDecay

/-!
# Rectangular interval rates from local window minorization

Fixed-width Choi minorization on the actual varying bond spaces produces compatible
reference densities and a dimension-uniform interval estimate. The references are derived
from the full-cycle channel and may be singular.

**Scope restriction (local minorization):** the interval estimate takes fixed-width
Choi minorization as quantitative input. Qualitative finite correlation alone does
not supply a uniform positive minorization strength; see
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS".
* Wolf, *Quantum Channels & Operations*, Theorem 8.17 and Eq. (8.86).
-/

open Matrix MPSTensor MPSPreparation Fin.NatCast
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace VaryingBondChain

variable {d D N : ℕ} [NeZero N]

/-- Local rectangular Choi minorization derives actual bond references and a uniform
block estimate. The Choi denominator is the actual input dimension of each window.
No interval mixing rate or compatible reference family is supplied as an assumption. -/
theorem exists_rectangular_block_mixing_of_window_domination (A : VaryingBondChain d D N)
    (hD : ∀ i, 0 < A.bondDim i)
    (hA : ∀ i, IsKrausCPTP (Matrix.rectangularKrausMap (A.tensor i)))
    (s : ℕ) (hs : 0 < s) (η : ℝ) (hη : η ≤ 1)
    (hwindow : ∀ a (_ha : a + s ≤ N),
      ∃ τ : Matrix (Fin (bondDimAt A a)) (Fin (bondDimAt A a)) ℂ,
        τ.PosSemidef ∧ τ.trace = 1 ∧
        ChoiRectangular.choiMatrix
          (Matrix.channelInterval (siteTransferAt A) a (a + s) (Nat.le_add_right a s)) ≥
            ((η : ℂ) / bondDimAt A (a + s)) •
              (τ ⊗ₖ (1 : Matrix (Fin (bondDimAt A (a + s)))
                (Fin (bondDimAt A (a + s))) ℂ))) :
    ∃ σ : ∀ i : Fin N, Matrix (Fin (A.bondDim i)) (Fin (A.bondDim i)) ℂ,
      (∀ i, (σ i).PosSemidef ∧ (σ i).trace = 1) ∧
      ∀ {M : ℕ} (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N) (j : Fin M) (_hj : 0 < ℓ j),
        ‖Matrix.linearMapMatrix (Matrix.rectangularKrausMap (rectangularBlockTensor A hN j) -
          Matrix.tracePrepareMap (α := Fin (rightBond A ℓ j))
            (β := Fin (blockBondDim A ℓ j 0))
            (σ (blockOffset ℓ j.val : Fin N)))‖ ≤
          2 * D * (1 - η) ^ (ℓ j / s) := by
  classical
  obtain ⟨ρ, hρ, _hcyc, htransport⟩ := exists_compatible_actual_densities A hD hA
  let σ (i : Fin N) := Matrix.equivReindexMap (finCongr (bondDimAt_val A i))
    (ρ i.val i.isLt.le)
  have hσ (i : Fin N) : (σ i).PosSemidef ∧ (σ i).trace = 1 := by
    have hC := Matrix.equivReindexMap_isKrausCPTP (finCongr (bondDimAt_val A i))
    exact ⟨hC.map_posSemidef (hρ i.val i.isLt.le).1,
      (hC.trace_map _).trans (hρ i.val i.isLt.le).2⟩
  have hσcut (a : ℕ) (ha : a < N) : σ (a : Fin N) = ρ a ha.le := by
    ext x y
    have hi : (a : Fin N) = ⟨a, ha⟩ := Fin.ext (Nat.mod_eq_of_lt ha)
    exact Matrix.entry_eq_of_heq (fun i => σ i) hi
      (x' := Fin.cast (congrArg A.bondDim hi) x)
      (y' := Fin.cast (congrArg A.bondDim hi) y)
      ((Fin.heq_ext_iff (congrArg A.bondDim hi)).2 rfl)
      ((Fin.heq_ext_iff (congrArg A.bondDim hi)).2 rfl)
  refine ⟨σ, hσ, fun {M} ℓ hN j hj => ?_⟩
  have hbound : blockOffset ℓ j.val + ℓ j ≤ N := by
    have h := blockOffset_mono ℓ j.isLt
    rw [blockOffset_of_le ℓ le_rfl, hN, blockOffset_succ ℓ j] at h
    exact h
  have hstart : blockOffset ℓ j.val < N := by omega
  have hm := Matrix.norm_linearMapMatrix_channelInterval_sub_transport_le_of_window_domination
    (siteTransferAt A) N s hs η hη (fun i _ => hD (i : Fin N))
    (fun i _ => siteTransferAt_isKrausCPTP A hA i) hwindow
    (blockOffset ℓ j.val) (blockOffset ℓ j.val + ℓ j) (Nat.le_add_right _ _) hbound
    (ρ _ hbound) (hρ _ hbound).1 (hρ _ hbound).2
  rw [htransport, ← hσcut _ hstart, Nat.add_sub_cancel_left] at hm
  have hcast := Matrix.norm_linearMapMatrix_sub_tracePrepareMap_finCast
    rfl (blockBondDim_length A hN j) (rectangularBlockTensor A hN j)
    (σ (blockOffset ℓ j.val : Fin N))
  have hnorm :
      ‖Matrix.linearMapMatrix (Matrix.channelInterval (siteTransferAt A)
          (blockOffset ℓ j.val) (blockOffset ℓ j.val + ℓ j) (Nat.le_add_right _ _) -
        Matrix.tracePrepareMap (α := Fin (bondDimAt A (blockOffset ℓ j.val + ℓ j)))
          (β := Fin (bondDimAt A (blockOffset ℓ j.val)))
          (σ (blockOffset ℓ j.val : Fin N)))‖ =
      ‖Matrix.linearMapMatrix (Matrix.rectangularKrausMap (rectangularBlockTensor A hN j) -
        Matrix.tracePrepareMap (α := Fin (rightBond A ℓ j))
            (β := Fin (blockBondDim A ℓ j 0))
          (σ (blockOffset ℓ j.val : Fin N)))‖ := by
    simp only [Fin.cast_refl] at hcast
    rw [rectangularKrausMap_blockTensor_cast_eq_channelInterval] at hcast
    exact hcast
  rw [← hnorm]
  refine hm.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (bondDimAt_le A _)) (by norm_num))
    (pow_nonneg (sub_nonneg.mpr hη) _)

end VaryingBondChain
