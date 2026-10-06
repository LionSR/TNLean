/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RectangularWindowMixing
import TNLean.MPS.Preparation.RectangularPreparation

/-!
# Physical preparation from rectangular local windows

A uniform fixed-width Choi minorization on the actual rectangular bond spaces derives
the references and exponential interval estimate required for physical preparation.
The original MPS is unchanged, and the circuit conclusion uses ring adjacency.

**Scope restriction (local minorization):** this is a quantitative sufficient condition
for the inhomogeneous paragraph of arXiv:2307.01696v2. Qualitative convergence alone does
not provide its uniform strength or accuracy rate; see
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS".
* Wolf, *Quantum Channels & Operations*, Theorem 8.17 and Eq. (8.86).
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain Fin.NatCast
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace MPSPreparation

/-- Uniform local Choi minorization on actual varying bond spaces gives eventual physical
logarithmic-depth preparation of the original ring states. The references and global
interval rate are derived internally. Singular minorizers and dimension-one bonds are
allowed. The cutoff and depth constant are selected before the accuracy and ring length. -/
theorem exists_isPreparedInDepth_le_log_eventually_of_rectangular_window_domination
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, VaryingBondChain d D N)
    (s : ℕ) (hs : 0 < s) {η : ℝ} (hη : 0 < η)
    (hD : ∀ (N : ℕ) [NeZero N] (i : Fin N), 0 < (A N).bondDim i)
    (hA : ∀ (N : ℕ) [NeZero N] (i : Fin N),
      IsKrausCPTP (Matrix.rectangularKrausMap ((A N).tensor i)))
    (hwindow : ∀ (N : ℕ) [NeZero N] (a : ℕ) (_ha : a + s ≤ N),
      ∃ τ : Matrix (Fin (bondDimAt (A N) a)) (Fin (bondDimAt (A N) a)) ℂ,
        τ.PosSemidef ∧ τ.trace = 1 ∧
        ChoiRectangular.choiMatrix (Matrix.channelInterval (siteTransferAt (A N))
          a (a + s) (Nat.le_add_right a s)) ≥
            ((η : ℂ) / bondDimAt (A N) (a + s)) •
              (τ ⊗ₖ (1 : Matrix (Fin (bondDimAt (A N) (a + s)))
                (Fin (bondDimAt (A N) (a + s))) ℂ))) :
    ∃ N₀ : ℕ, s ≤ N₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun x => ψ x) ∧
        1 - ‖⟪ψ, (‖state (A N)‖ : ℂ)⁻¹ • state (A N)⟫_ℂ‖ ≤ ε := by
  classical
  have hDpos : 0 < D := by
    let : NeZero s := ⟨Nat.ne_of_gt hs⟩
    exact (hD s 0).trans_le ((A s).bondDim_le 0)
  have hη1 : η ≤ 1 := by
    let : NeZero s := ⟨Nat.ne_of_gt hs⟩
    obtain ⟨τ, _hτ, hτtr, hchoi⟩ := hwindow s 0 (by omega)
    let : NeZero (bondDimAt (A s) (0 + s)) :=
      ⟨Nat.ne_of_gt (hD s ((0 + s : ℕ) : Fin s))⟩
    have hT := Matrix.channelInterval_isKrausCPTP (siteTransferAt (A s))
      (Nat.le_add_right 0 s) (fun i _ _ => siteTransferAt_isKrausCPTP (A s) (hA s) i)
    exact Matrix.le_one_of_choi_domination _ hT.trace_map τ hτtr η hchoi
  have hαhalf : 1 / 2 ≤ 1 - η / 2 := by linarith
  have hα0 : 0 < 1 - η / 2 := by linarith
  have hα1 : 1 - η / 2 < 1 := by linarith
  let r := -Real.log (1 - η / 2) / s
  have hr : 0 < r := div_pos (neg_pos.mpr (Real.log_neg hα0 hα1)) (Nat.cast_pos.mpr hs)
  have hweak : ∀ (N : ℕ) [NeZero N] (a : ℕ) (_ha : a + s ≤ N),
      ∃ τ : Matrix (Fin (bondDimAt (A N) a)) (Fin (bondDimAt (A N) a)) ℂ,
        τ.PosSemidef ∧ τ.trace = 1 ∧
        ChoiRectangular.choiMatrix (Matrix.channelInterval (siteTransferAt (A N))
          a (a + s) (Nat.le_add_right a s)) ≥
            (((η / 2 : ℝ) : ℂ) / bondDimAt (A N) (a + s)) •
              (τ ⊗ₖ (1 : Matrix (Fin (bondDimAt (A N) (a + s)))
                (Fin (bondDimAt (A N) (a + s))) ℂ)) := by
    intro N _ a ha
    obtain ⟨τ, hτ, hτtr, hchoi⟩ := hwindow N a ha
    refine ⟨τ, hτ, hτtr, le_trans ?_ hchoi⟩
    apply Matrix.le_iff.mpr
    rw [← sub_smul]
    apply (hτ.kronecker Matrix.PosSemidef.one).smul
    have heq : (η : ℂ) / bondDimAt (A N) (a + s) -
        ((η / 2 : ℝ) : ℂ) / bondDimAt (A N) (a + s) =
      ((η / (2 * bondDimAt (A N) (a + s)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq]
    exact Complex.zero_le_real.mpr (by positivity)
  choose σ hσ hmix using fun (N : ℕ) (hN : 0 < N) => by
    let : NeZero N := ⟨Nat.ne_of_gt hN⟩
    exact exists_rectangular_block_mixing_of_window_domination (A N) (hD N) (hA N)
      s hs (η / 2) (by linarith) (hweak N)
  let σ' (N : ℕ) (i : Fin N) := σ N (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt) i
  have hσpos (N : ℕ) [NeZero N] (i : Fin N) : (σ' N i).PosSemidef :=
    (hσ N (Nat.pos_of_ne_zero (NeZero.ne N)) i).1
  have hσtr (N : ℕ) [NeZero N] (i : Fin N) : (σ' N i).trace = 1 :=
    (hσ N (Nat.pos_of_ne_zero (NeZero.ne N)) i).2
  obtain ⟨N₀, C, hC⟩ := exists_isPreparedInDepth_le_log_eventually_of_rectangular_mixing
    d D hd A σ' hσpos hσtr (4 * D) r (by positivity) hr (by
      intro N _ M ℓ hN j hj
      have h := hmix N (Nat.pos_of_ne_zero (NeZero.ne N)) ℓ hN j hj
      have hp := Real.pow_nat_div_le_two_mul_exp s (ℓ j) hs (1 - η / 2) hαhalf hα1
      have hb := h.trans (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2 : ℝ) * D))
      convert hb using 1 <;> dsimp [σ', r] <;> first | rfl | ring)
  refine ⟨max s N₀, le_max_left _ _, C, fun ε hε hε1 N _ hN => ?_⟩
  exact hC ε hε hε1 N ((le_max_right s N₀).trans hN)

end MPSPreparation
