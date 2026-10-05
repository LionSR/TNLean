/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousApproximationError
import TNLean.MPS.Preparation.RemainderBlocks

/-!
# Pair-approximation rate from actual ordered mixing

Ordered transfer products within `K exp(-r ℓ)` of one faithful normalized reference
produce a normalized pair error at most `Cp K N exp(-r q)` on remainder-absorbing blocks.
The constant `Cp` depends only on the bond dimension and reference state, before the
physical dimension, chain, ring length and blocking scale are chosen.

This is an additional quantitative sufficient condition for arXiv:2307.01696's
inhomogeneous preparation scheme, not a consequence of its qualitative convergence
assumption. A nonzero periodic target is required.

## References

* [arXiv:2307.01696](https://arxiv.org/abs/2307.01696),
  the inhomogeneous short-range correlated MPS discussion.
  The uniform ordered-mixing estimate is an additional quantitative hypothesis.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSPreparation

/-- **Actual ordered mixing implies the pair rate.** Every positive nonwrapping contiguous
block has transfer error at most `K exp(-r ℓ)`. The remainder-absorbing partition has
normalized pair error at most `Cp K N exp(-r q)` for each `1 ≤ q ≤ N`.

This extracts the quantitative hypothesis used by the physical preparation results, with
`Cp` independent of the chain and ring length. Source: arXiv:2307.01696, paragraph
"Inhomogeneous short-range correlated MPS", under the additional ordered-mixing condition. -/
theorem exists_isPairApproximable_of_ordered_mixing {D : ℕ}
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (d N : ℕ) [NeZero N] (A : MPSChainTensor d D N)
      (K r : ℝ), 0 < K → 0 < r → chainState A ≠ 0 →
      (∀ {M : ℕ} (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
        ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
            Kraus.transferMap (A (blockSite hN j i))).prod) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
            K * Real.exp (-(r * ℓ j))) →
      ∀ q : ℕ, 0 < q → q ≤ N →
        ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
          (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
          IsPairApproximable (ofChain A) hN
            (Cp * K * ((N : ℝ) ^ 1 * Real.exp (-(r * q)))) := by
  classical
  obtain ⟨Cp, hCp, hp⟩ := exists_one_sub_norm_inner_chainPosState_le hσ htr
  refine ⟨Cp, hCp, fun d N _ A K r hK hr hne hmix q hq hqN => ?_⟩
  let ℓ := remainderBlockLengths q N
  have hsum := sum_remainderBlockLengths hq hqN
  have hM := Nat.div_pos hqN hq
  let : NeZero (N / q) := ⟨hM.ne'⟩
  have hℓq : ∀ j, q ≤ ℓ j := le_remainderBlockLengths q N
  have hℓ2q : ∀ j, ℓ j ≤ 2 * q := fun j => (remainderBlockLengths_lt_two_mul hq j).le
  refine ⟨N / q, hM, ℓ, hsum, hℓq, hℓ2q, ?_⟩
  have hpos : chainPosState (zeroPad (ofChain A)) hsum ≠ 0 := by
    rw [zeroPad_ofChain]
    intro hz
    have hn := norm_chainState_eq A hsum
    rw [hz, norm_zero] at hn
    exact hne (norm_eq_zero.mp hn)
  have hpair : padPairs (ofChain A) ℓ (fun _ => fixedPointPair σ) =
      fun _ : Fin (N / q) => fixedPointPair σ := by
    funext j p
    simp [padPairs, padPair, Matrix.zeroPad, rightBond, leftBond, ofChain]
    rfl
  refine ⟨hpos, fun _ => fixedPointPair σ, (fun _ => ?_), ?_⟩
  · change ∑ p : Fin D × Fin D, star (fixedPointPair σ p) * fixedPointPair σ p = 1
    rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
  rw [hpair, zeroPad_ofChain]
  let δ := K * Real.exp (-(r * q))
  have hblock : ∀ j, ‖transferMatrix (Kraus.transferMap (chainBlockTensor A hsum j)) -
      transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ := by
    intro j
    rw [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
    refine (hmix ℓ hsum j (hq.trans_le (hℓq j))).trans ?_
    dsimp [δ]
    gcongr
    exact hℓq j
  have hwhole : ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
      transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ := by
    have hsingle : ∑ _ : Fin 1, N = N := by simp
    have hi : ∀ i : Fin N, blockSite hsingle 0 i = i := by
      intro i
      apply Fin.ext
      simp [blockSite, blockOffset]
    have h := hmix (fun _ : Fin 1 => N) hsingle 0
      (Nat.pos_of_ne_zero (NeZero.ne N))
    simp only [hi] at h
    rw [MPSChainTensor.transferMap_blockTensor]
    refine h.trans ?_
    dsimp [δ]
    gcongr
  have herr := hp A ℓ hsum (show 0 ≤ δ by positivity) hblock hwhole
  refine herr.trans ?_
  dsimp [δ]
  simp only [pow_one]
  calc Cp * (((N / q : ℕ) : ℝ) * (K * Real.exp (-(r * q)))) =
      Cp * K * (((N / q : ℕ) : ℝ) * Real.exp (-(r * q))) := by ring
    _ ≤ Cp * K * (N * Real.exp (-(r * q))) := by gcongr; exact Nat.div_le_self N q

end MPSPreparation
