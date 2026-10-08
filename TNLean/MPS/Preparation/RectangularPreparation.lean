/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.VaryingReferencePreparation
import TNLean.MPS.Preparation.RectangularTransferEstimate
import TNLean.MPS.Preparation.RectangularBlocks

/-!
# Quantitative preparation on actual varying bond spaces

Uniform exponential convergence of the actual rectangular interval transfers to density
resets gives normalized pair approximation and eventual physical logarithmic-depth
preparation. The norm is the Hilbert--Schmidt induced operator norm, expressed in matrix-unit
bases. References may be singular and vary with both the site and the ring.

The quantitative mixing bound is an additional sufficient hypothesis. The qualitative
finite-correlation condition in arXiv:2307.01696v2 does not supply this accuracy rate.
The circuits act on rings; no nearest-neighbor open-line conclusion is asserted.

## References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS", and
  Supplemental Material, eqs. (S39) and (S42).
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MPSPreparation

/-- Actual rectangular interval mixing gives physical logarithmic-depth preparation of
varying-bond rings. Every reference has trace one, so each actual bond is nonzero, while
`VaryingBondChain.bondDim_le` bounds it by `D`. The cutoff and depth constant precede both
accuracy and ring length. Whole-ring mixing supplies eventual nonvanishing; short rings
are not assumed nonzero. This is a quantitative sufficient condition for the inhomogeneous
paragraph of arXiv:2307.01696v2, not a rate deduced from qualitative convergence. -/
theorem exists_isPreparedInDepth_le_log_eventually_of_rectangular_mixing
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, VaryingBondChain d D N)
    (σ : ∀ N, (i : Fin N) → Matrix (Fin ((A N).bondDim i)) (Fin ((A N).bondDim i)) ℂ)
    (hσ : ∀ (N : ℕ) [NeZero N] (i : Fin N), (σ N i).PosSemidef)
    (htr : ∀ (N : ℕ) [NeZero N] (i : Fin N), (σ N i).trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M) (_hj : 0 < ℓ j),
      ‖Matrix.linearMapMatrix (Matrix.rectangularKrausMap (rectangularBlockTensor (A N) hN j) -
        Matrix.tracePrepareMap (α := Fin (rightBond (A N) ℓ j))
          (β := Fin (blockBondDim (A N) ℓ j 0))
          (σ N ⟨blockOffset ℓ j.val % N,
            Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩))‖ ≤
        K * Real.exp (-(r * ℓ j))) :
    ∃ N₀ : ℕ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖state (A N)‖ : ℂ)⁻¹ • state (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cpad, hCpad, hpad⟩ := exists_norm_transferMatrix_zeroPad_sub_cornerReferenceMap_le D
  let K' := Cpad * K
  have hK' : 0 < K' := mul_pos hCpad hK
  let ρ (N : ℕ) (i : Fin N) : Matrix (Fin D) (Fin D) ℂ := Matrix.zeroPad D (σ N i)
  have hρ (N : ℕ) [NeZero N] (i : Fin N) : (ρ N i).PosSemidef := by
    change (Matrix.zeroPad D (σ N i)).PosSemidef
    rw [zeroPad_eq_embeddedBlockState ((A N).bondDim_le i), embeddedBlockState]
    exact (hσ N i).mul_mul_conjTranspose_same _
  have hρtr (N : ℕ) [NeZero N] (i : Fin N) : (ρ N i).trace = 1 := by
    change (Matrix.zeroPad D (σ N i)).trace = 1
    rw [zeroPad_eq_embeddedBlockState ((A N).bondDim_le i),
      trace_embeddedBlockState (Fin.castLE_injective _), htr N i]
  have hρsupp (N : ℕ) [NeZero N] (i : Fin N) :
      cornerProjection D ((A N).bondDim i) * ρ N i = ρ N i := by
    ext a b
    simp only [cornerProjection, Matrix.diagonal_mul, ρ, Matrix.zeroPad]
    split_ifs <;> simp
  have hpmix (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M) (hj : 0 < ℓ j) :
      ‖transferMatrix (Kraus.transferMap (chainBlockTensor (zeroPad (A N)) hN j)) -
        transferMatrix (cornerReferenceMap
          (ρ N ⟨blockOffset ℓ j.val % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩)
          (rightBond (A N) ℓ j))‖ ≤ K' * Real.exp (-(r * ℓ j)) := by
    have hp := hpad ((A N).bondDim_le _) (rightBond_le (A N) ℓ j)
      (rectangularBlockTensor (A N) hN j)
      (σ N ⟨blockOffset ℓ j.val % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩)
    have ht : transferMatrix (Kraus.transferMap
        (fun s => Matrix.zeroPad D (rectangularBlockTensor (A N) hN j s))) =
        transferMatrix (Kraus.transferMap (chainBlockTensor (zeroPad (A N)) hN j)) := by
      congr 2
      exact funext (zeroPad_rectangularBlockTensor (A N) hN j hj)
    erw [ht] at hp
    calc _ ≤ Cpad * ‖Matrix.linearMapMatrix
          (Matrix.rectangularKrausMap (rectangularBlockTensor (A N) hN j) -
            Matrix.tracePrepareMap (α := Fin (rightBond (A N) ℓ j))
              (β := Fin (blockBondDim (A N) ℓ j 0))
              (σ N ⟨blockOffset ℓ j.val % N,
                Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩))‖ := hp
      _ ≤ Cpad * (K * Real.exp (-(r * ℓ j))) :=
        mul_le_mul_of_nonneg_left (hmix N ℓ hN j hj) hCpad.le
      _ = K' * Real.exp (-(r * ℓ j)) := by dsimp [K']; ring
  have hwhole (N : ℕ) [NeZero N] :
      ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (zeroPad (A N)))) -
        transferMatrix (cornerReferenceMap (ρ N 0) ((A N).bondDim 0))‖ ≤
          K' * Real.exp (-(r * N)) := by
    have hsingle : ∑ _ : Fin 1, N = N := by simp
    have hi := blockSite_singleton hsingle
    simpa [chainBlockTensor, hi, rightBond, leftBond, blockOffset] using
      hpmix N (fun _ : Fin 1 => N) hsingle 0 (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_chainState_sq_sub_one_le_corner_reference D
  let L := Kn * K' + 1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((Real.log L - Real.log (1 / 2 : ℝ)) / r)
  have hne (N : ℕ) [NeZero N] (hcut : N₀ ≤ N) : chainState (zeroPad (A N)) ≠ 0 := by
    have hsmall : L * Real.exp (-(r * N)) ≤ 1 / 2 :=
      mul_exp_neg_mul_le_of_div_log_le hL hr (by norm_num)
        (hN₀.trans (Nat.cast_le.mpr hcut))
    have hb : |‖chainState (zeroPad (A N))‖ ^ 2 - 1| ≤ 1 / 2 := by
      calc |‖chainState (zeroPad (A N))‖ ^ 2 - 1|
          ≤ Kn * ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (zeroPad (A N)))) -
            transferMatrix (cornerReferenceMap (ρ N 0) ((A N).bondDim 0))‖ :=
              hnorm _ _ _ (hρtr N 0) (hρsupp N 0)
        _ ≤ Kn * (K' * Real.exp (-(r * N))) := mul_le_mul_of_nonneg_left (hwhole N) hKn
        _ ≤ L * Real.exp (-(r * N)) := by
            dsimp only [L]
            nlinarith [Real.exp_pos (-(r * N))]
        _ ≤ 1 / 2 := hsmall
    intro hz
    norm_num [hz] at hb
  obtain ⟨Cp, hCp, hp⟩ := exists_one_sub_norm_inner_chainPosState_le_varying_reference D
  have hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N → N₀ ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsPairApproximable (A N) hN
          (Cp * Real.sqrt K' * ((N : ℝ) ^ 1 * Real.exp (-((r / 2) * q)))) := by
    intro N _ q hq hqN hcut
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
    have hpos : chainPosState (zeroPad (A N)) hsum ≠ 0 := by
      intro hz
      have hn := norm_chainState_eq (zeroPad (A N)) hsum
      rw [hz, norm_zero] at hn
      exact hne N hcut (norm_eq_zero.mp hn)
    let i₀ : Fin (m + 1) → Fin N := fun j =>
      ⟨blockOffset ℓ j.val % N, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne N))⟩
    let ω : ∀ j, Fin (rightBond (A N) ℓ j) × Fin (rightBond (A N) ℓ j) → ℂ :=
      fun j => fixedPointPair (σ N (i₀ (finRotate (m + 1) j)))
    have hpair : padPairs (A N) ℓ ω =
        fun j => fixedPointPair (ρ N (i₀ (finRotate (m + 1) j))) := by
      funext j
      exact padPair_fixedPointPair ((A N).bondDim_le _) (hσ N _)
    refine ⟨hpos, ω, (fun j => ?_), ?_⟩
    · exact (fixedPointPair_norm_sq (hσ N _)).trans (htr N _)
    rw [hpair]
    let δ := K' * Real.exp (-(r * q))
    have hblock : ∀ j,
        ‖transferMatrix (Kraus.transferMap (chainBlockTensor (zeroPad (A N)) hsum j)) -
        transferMatrix (cornerReferenceMap (ρ N (i₀ j)) (rightBond (A N) ℓ j))‖ ≤ δ := by
      intro j
      refine (hpmix N ℓ hsum j (hq.trans_le (hℓq j))).trans ?_
      dsimp [δ]
      gcongr
      exact hℓq j
    have hwhole' :
        ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (zeroPad (A N)))) -
        transferMatrix (cornerReferenceMap (ρ N 0) ((A N).bondDim 0))‖ ≤ δ := by
      refine (hwhole N).trans ?_
      dsimp [δ]
      gcongr
    have hMN : m + 1 ≤ N := by
      calc m + 1 = ∑ _ : Fin (m + 1), 1 := by simp
        _ ≤ ∑ j, ℓ j := Finset.sum_le_sum fun j _ => hq.trans_le (hℓq j)
        _ = N := hsum
    have herr := hp (zeroPad (A N)) ℓ hsum (fun j => ρ N (i₀ j)) (ρ N 0)
      (leftBond (A N) ℓ) ((A N).bondDim 0) (fun j => hρ N _) (fun j => hρtr N _)
      (fun j => hρsupp N _) (hρtr N 0) (hρsupp N 0)
      (show 0 ≤ δ by positivity) hblock hwhole'
    have hsqrt : Real.sqrt δ = Real.sqrt K' * Real.exp (-((r / 2) * q)) := by
      dsimp [δ]
      rw [Real.sqrt_mul hK'.le]
      congr 1
      apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsqrt] at herr
    refine herr.trans ?_
    simp only [pow_one, Nat.cast_add, Nat.cast_one]
    calc Cp * ((m + 1) * (Real.sqrt K' * Real.exp (-((r / 2) * q)))) =
        Cp * Real.sqrt K' * ((m + 1) * Real.exp (-((r / 2) * q))) := by ring
      _ ≤ Cp * Real.sqrt K' * (N * Real.exp (-((r / 2) * q))) := by
          gcongr; exact_mod_cast hMN
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate_from
    d D hd A (Cp * Real.sqrt K') (r / 2) 1 (mul_pos hCp (Real.sqrt_pos.mpr hK'))
      (by positivity) N₀ hrate
  exact ⟨N₀, C, hC⟩

end MPSPreparation
