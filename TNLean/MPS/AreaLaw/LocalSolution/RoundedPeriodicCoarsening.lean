/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.RoundedPeriodicGeometry
import TNLean.MPS.AreaLaw.LocalSolution.PeriodicCoarsening

/-!
# Sharp periodic pair estimates at arbitrary physical length

For every projection radius `ℓ>0`, the original physical chain is grouped into
`max 1 (M/(2ℓ))` contiguous blocks. The last block contains the remainder. Every
edge receives at most `4ℓ` terms, so the centred pair norm is at most `8ℓJ` and
the pair residual at most `4ℓε`. These bounds are independent of physical chain
length. The total Hamiltonian and the physical Hilbert space are unchanged.

The physical distance is cyclic. No divisibility assumption or open-chain
replacement is made.

Source: Hastings, arXiv:cond-mat/0508554v3, lines 609–639 and 676–695.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- A rounded periodic edge receives at most four locality radii of physical terms.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem card_roundedPeriodicEdge_fibre_le {M N ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N)
    (hhi : M < (N + 1) * (2 * ℓ)) (j : Fin N) :
    (Finset.univ.filter (fun i : Fin M ↦ roundedPeriodicEdge (ℓ := ℓ) hN i = j)).card ≤
      4 * ℓ := by
  by_cases hj : (j : ℕ) = 0
  · let A := (N - 1) * (2 * ℓ)
    have hNw : N * (2 * ℓ) = A + 2 * ℓ := by
      have : N - 1 + 1 = N := by omega
      dsimp [A]
      nlinarith
    have hM : M < A + 4 * ℓ := by nlinarith
    have hband (i : Fin M) (he : roundedPeriodicEdge (ℓ := ℓ) hN i = j) :
        (i : ℕ) < ℓ ∨ A + ℓ ≤ (i : ℕ) := by
      unfold roundedPeriodicEdge at he
      split_ifs at he with hq
      · have hval : ((i : ℕ) + ℓ) / (2 * ℓ) = 0 := (congrArg Fin.val he).trans hj
        have hlt := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * ℓ)).mp
          (show ((i : ℕ) + ℓ) / (2 * ℓ) < 1 by omega)
        left
        nlinarith
      · have hlow := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * ℓ)).mp
          (show N ≤ ((i : ℕ) + ℓ) / (2 * ℓ) by omega)
        right
        omega
    let f : Fin M → ℕ := fun i ↦ if (i : ℕ) < ℓ then (i : ℕ) else (i : ℕ) - A
    have hf : Set.MapsTo f
        (↑(Finset.univ.filter (fun i : Fin M ↦ roundedPeriodicEdge (ℓ := ℓ) hN i = j)))
        (↑(Finset.range (4 * ℓ))) := by
      intro i hi
      have hb := hband i (Finset.mem_filter.mp hi).2
      have hiM := i.isLt
      simp only [Finset.mem_coe, Finset.mem_range]
      dsimp [f]
      split_ifs <;> omega
    have hinj : Set.InjOn f
        (↑(Finset.univ.filter (fun i : Fin M ↦ roundedPeriodicEdge (ℓ := ℓ) hN i = j))) := by
      intro i hi k hk hik
      have hbi := hband i (Finset.mem_filter.mp hi).2
      have hbk := hband k (Finset.mem_filter.mp hk).2
      apply Fin.ext
      dsimp [f] at hik
      split_ifs at hik <;> omega
    simpa using Finset.card_le_card_of_injOn f hf hinj
  · let lo := (j : ℕ) * (2 * ℓ) - ℓ
    have hband (i : Fin M) (he : roundedPeriodicEdge (ℓ := ℓ) hN i = j) :
        lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + 4 * ℓ := by
      obtain ⟨hlo, hhi⟩ := roundedPeriodicEdge_internal_centre hℓ hN i (by omega) he
      have hjlo : ℓ ≤ (j : ℕ) * (2 * ℓ) := by
        have : 1 ≤ (j : ℕ) := by omega
        nlinarith
      dsimp [lo]
      omega
    have hf : Set.MapsTo (fun i : Fin M ↦ (i : ℕ) - lo)
        (↑(Finset.univ.filter (fun i : Fin M ↦ roundedPeriodicEdge (ℓ := ℓ) hN i = j)))
        (↑(Finset.range (4 * ℓ))) := by
      intro i hi
      have hb := hband i (Finset.mem_filter.mp hi).2
      simp only [Finset.mem_coe, Finset.mem_range]
      omega
    have hinj : Set.InjOn (fun i : Fin M ↦ (i : ℕ) - lo)
        (↑(Finset.univ.filter (fun i : Fin M ↦ roundedPeriodicEdge (ℓ := ℓ) hN i = j))) := by
      intro i hi k hk hik
      have hbi := hband i (Finset.mem_filter.mp hi).2
      have hbk := hband k (Finset.mem_filter.mp hk).2
      apply Fin.ext
      dsimp at hik
      omega
    simpa using Finset.card_le_card_of_injOn (fun i : Fin M ↦ (i : ℕ) - lo) hf hinj

/-- Actual local terms grouped along the rounded periodic chain.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
def roundedPeriodicOperator {M d : ℕ} (ℓ : ℕ)
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ) :=
  edgePartition (roundedPeriodicEdge (ℓ := ℓ) (roundedPeriodicBlockCount_pos M ℓ)) a

/-- Rounding and grouping preserve the full operator sum.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem sum_roundedPeriodicOperator {M d : ℕ} (ℓ : ℕ)
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ) :
    ∑ j, roundedPeriodicOperator ℓ a j = ∑ i, a i := sum_edgePartition _ _

/-- Actual cyclic locality gives the internal pair supports, including short chains.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem roundedPeriodicOperator_mem_supportedOperators {M ℓ d : ℕ} (hℓ : 0 < ℓ)
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    (ha : ∀ i, a i ∈ supportedOperators d {v | roundedPeriodicDistance i v ≤ ℓ})
    (j : Fin (roundedPeriodicBlockCount M ℓ)) (hj : 0 < (j : ℕ)) :
    roundedPeriodicOperator ℓ a j ∈ supportedOperators d
      {v | roundedPeriodicBlock (roundedPeriodicBlockCount M ℓ) ℓ v + 1 = (j : ℕ) ∨
        roundedPeriodicBlock (roundedPeriodicBlockCount M ℓ) ℓ v = (j : ℕ)} := by
  apply edgePartition_mem_supportedOperators
  intro i hi
  exact supportedOperators_mono
    (fun v hv ↦ roundedPeriodicEdge_support_of_cover hℓ (roundedPeriodicBlockCount_pos M ℓ)
      (roundedPeriodicBlockCount_cover M ℓ) i v hj hi hv) (ha i)

/-- Grouping preserves Hermiticity.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem isHermitian_roundedPeriodicOperator {M ℓ d : ℕ}
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    (ha : ∀ i, (a i).IsHermitian) (j : Fin (roundedPeriodicBlockCount M ℓ)) :
    (roundedPeriodicOperator ℓ a j).IsHermitian := isHermitian_edgePartition _ a ha j

/-- Each actual pair residual uses at most `4ℓ` local residuals.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem residual_roundedPeriodicOperator_le {M ℓ d : ℕ} (hℓ : 0 < ℓ)
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    (ψ : EuclideanSpace ℂ (Fin M → Fin d)) {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ i, ‖toEuclideanLin
      (a i - ((⟪ψ, toEuclideanLin (a i) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤ ε)
    (j : Fin (roundedPeriodicBlockCount M ℓ)) :
    ‖toEuclideanLin (roundedPeriodicOperator ℓ a j -
      ((⟪ψ, toEuclideanLin (roundedPeriodicOperator ℓ a j) ψ⟫_ℂ).re : ℂ) • 1) ψ‖ ≤
      (4 * ℓ : ℕ) * ε := by
  rw [roundedPeriodicOperator, centered_edgePartition]
  simp only [edgePartition, map_sum, LinearMap.sum_apply]
  exact norm_edgePartition_le_of_fibre_card _ _ hε ha j
    (card_roundedPeriodicEdge_fibre_le hℓ (roundedPeriodicBlockCount_pos M ℓ)
      (roundedPeriodicBlockCount_upper hℓ) j)

/-- The actual centred pair norm is at most `8ℓJ`, independently of physical chain length.
Hastings, arXiv:cond-mat/0508554v3, Section II, lines 609–730. -/
theorem centeredNorm_roundedPeriodicOperator_le {M ℓ d : ℕ} (hℓ : 0 < ℓ)
    (a : Fin M → Matrix (Fin M → Fin d) (Fin M → Fin d) ℂ)
    {ψ : EuclideanSpace ℂ (Fin M → Fin d)} (hψ : ‖ψ‖ = 1)
    {J : ℝ} (hJ : 0 ≤ J) (ha : ∀ i, ‖a i‖ ≤ J)
    (j : Fin (roundedPeriodicBlockCount M ℓ)) :
    ‖roundedPeriodicOperator ℓ a j -
      ((⟪ψ, toEuclideanLin (roundedPeriodicOperator ℓ a j) ψ⟫_ℂ).re : ℂ) • 1‖ ≤
      8 * (ℓ : ℝ) * J := by
  refine (norm_sub_smul_one_le_two_mul
    (abs_re_inner_toEuclideanLin_le (roundedPeriodicOperator ℓ a j) hψ)).trans ?_
  have hn := norm_edgePartition_le_of_fibre_card _ a hJ ha j
    (card_roundedPeriodicEdge_fibre_le hℓ (roundedPeriodicBlockCount_pos M ℓ)
      (roundedPeriodicBlockCount_upper hℓ) j)
  change ‖roundedPeriodicOperator ℓ a j‖ ≤ _ at hn
  push_cast at hn
  nlinarith

end TNLean.MPS.AreaLaw.LocalSolution
