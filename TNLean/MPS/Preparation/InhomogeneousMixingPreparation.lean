/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.InhomogeneousApproximationError
import TNLean.MPS.Preparation.InhomogeneousUniformRate

/-!
# Physical logarithmic-depth preparation from ordered mixing

Uniform exponential mixing of the actual ordered transfer products towards one faithful
trace-one state implies a uniform normalized pair-approximation rate, and hence physical
preparation in depth `O(log(N/ε))`. The constants are independent of the ring and partition.
The assumption concerns nonwrapping contiguous intervals in the chosen linear ordering,
not separate eigenvalue bounds on sites.

The targets are required to be nonzero because the source compares normalized quantum
states. This condition retains the finite short rings for which a decay estimate by itself
may not exclude a zero periodic vector. The existing exact short-ring preparation handles
scales longer than the ring.

This is a quantitative sufficient condition for arXiv:2307.01696, paragraph "Inhomogeneous
short-range correlated MPS". The paper's qualitative finite-correlation definition alone
does not supply the ordered mixing hypothesis.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace MPSPreparation

/-- Actual ordered transfer mixing gives normalized physical preparation in logarithmic
accuracy-dependent depth. Fix `K,r > 0` and one faithful normalized reference state before
the ring length is chosen. Every positive nonwrapping contiguous block has transfer-matrix error at
most `K exp(-r ℓ)`, in the `L²` operator norm. Then the normalized nonzero chain states can
be approximated to error `ε` in depth `C log(N/ε)`.

The finite-dimensional norm conversions and overlap estimates have constants depending only
on the fixed bond dimension and reference state. The pair-approximation rate is proved from
the tensors, rather than supplied as a hypothesis. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_of_ordered_mixing
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosDef) (htr : σ.trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hne : ∀ (N : ℕ) [NeZero N], chainState (A N) ≠ 0)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M), 0 < ℓ j →
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤
          K * Real.exp (-(r * ℓ j))) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N],
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cp, hCp, hp⟩ := exists_one_sub_norm_inner_chainPosState_le hσ htr
  let B (N : ℕ) : VaryingBondChain d D N :=
    { bondDim := fun _ => D
      bondDim_le := fun _ => le_rfl
      tensor := A N }
  have hpad (N : ℕ) : zeroPad (B N) = A N := by
    funext j i a b
    simp [B, VaryingBondChain.zeroPad, Matrix.zeroPad]
  have hstate (N : ℕ) [NeZero N] : state (B N) = chainState (A N) := by
    rw [state_eq_chainState, hpad]
  have hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsPairApproximable (B N) hN (Cp * K * ((N : ℝ) ^ 1 * Real.exp (-(r * q)))) := by
    intro N _ q hq hqN
    obtain ⟨m, hm⟩ : ∃ m, N / q = m + 1 :=
      ⟨N / q - 1, (Nat.succ_pred_eq_of_pos (Nat.div_pos hqN hq)).symm⟩
    let ℓ : Fin (m + 1) → ℕ := fun j => if j = Fin.last m then q + N % q else q
    have hsum : ∑ j, ℓ j = N := by
      rw [Fin.sum_univ_castSucc]
      simp only [ℓ, Fin.castSucc_ne_last, ite_false, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ite_true]
      have h := Nat.div_add_mod N q
      rw [hm] at h
      linarith
    have hℓq : ∀ j, q ≤ ℓ j := fun j => by dsimp [ℓ]; split_ifs <;> omega
    have hℓ2q : ∀ j, ℓ j ≤ 2 * q := fun j => by
      have h := Nat.mod_lt N hq
      dsimp [ℓ]; split_ifs <;> omega
    refine ⟨m + 1, Nat.succ_pos _, ℓ, hsum, hℓq, hℓ2q, ?_⟩
    have hpos : chainPosState (zeroPad (B N)) hsum ≠ 0 := by
      rw [hpad]
      intro hz
      have hn := norm_chainState_eq (A N) hsum
      rw [hz, norm_zero] at hn
      exact hne N (norm_eq_zero.mp hn)
    have hpair : padPairs (B N) ℓ (fun _ => fixedPointPair σ) =
        fun _ : Fin (m + 1) => fixedPointPair σ := by
      funext j p
      simp [padPairs, padPair, Matrix.zeroPad, rightBond, leftBond, B]
      rfl
    refine ⟨hpos, fun _ => fixedPointPair σ, (fun _ => ?_), ?_⟩
    · change ∑ p : Fin D × Fin D, star (fixedPointPair σ p) * fixedPointPair σ p = 1
      rw [fixedPointPair_norm_sq hσ.posSemidef, htr]
    rw [hpair, hpad]
    let δ := K * Real.exp (-(r * q))
    have hblock : ∀ j, ‖transferMatrix (Kraus.transferMap (chainBlockTensor (A N) hsum j)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ := by
      intro j
      rw [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
      refine (hmix N ℓ hsum j (hq.trans_le (hℓq j))).trans ?_
      dsimp [δ]
      gcongr
      exact hℓq j
    have hwhole : ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (A N))) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ ≤ δ := by
      have hsingle : ∑ _ : Fin 1, N = N := by simp
      have hi : ∀ i : Fin N, blockSite hsingle 0 i = i := by
        intro i
        apply Fin.ext
        simp [blockSite, blockOffset]
      have h := hmix N (fun _ : Fin 1 => N) hsingle 0
        (Nat.pos_of_ne_zero (NeZero.ne N))
      simp only [hi] at h
      rw [MPSChainTensor.transferMap_blockTensor]
      refine h.trans ?_
      dsimp [δ]
      gcongr
    have hMN : m + 1 ≤ N := by
      calc m + 1 = ∑ _ : Fin (m + 1), 1 := by simp
        _ ≤ ∑ j, ℓ j := Finset.sum_le_sum fun j _ => hq.trans_le (hℓq j)
        _ = N := hsum
    have herr := hp (A N) ℓ hsum (show 0 ≤ δ by positivity) hblock hwhole
    refine herr.trans ?_
    dsimp [δ]
    simp only [pow_one, Nat.cast_add, Nat.cast_one]
    calc Cp * ((m + 1) * (K * Real.exp (-(r * q)))) =
        Cp * K * ((m + 1) * Real.exp (-(r * q))) := by ring
      _ ≤ Cp * K * (N * Real.exp (-(r * q))) := by gcongr; exact_mod_cast hMN
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate
    d D hd B (Cp * K) r 1 (mul_pos hCp hK) hr hrate
  refine ⟨C, fun ε hε hε1 N _ => ?_⟩
  simpa only [hstate] using hC ε hε hε1 N

end MPSPreparation
