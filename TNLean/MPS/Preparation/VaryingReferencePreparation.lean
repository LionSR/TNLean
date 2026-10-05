/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.VaryingReferenceOverlap
import TNLean.MPS.Preparation.InhomogeneousUniformRate

/-!
# Physical preparation with varying positive semidefinite references

Quantitative ordered mixing on a fixed square bond space gives normalized pair approximation
and eventual physical logarithmic-depth preparation. References may vary with the ring and
site and may be singular. The square-root Hölder estimate loses a factor two in the decay
exponent, while keeping all constants uniform before the ring and its reference family.

**Scope restriction (ordered mixing):** the exponential product estimates are additional
sufficient hypotheses for arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated
MPS". Rectangular bonds and deriving a rate from qualitative convergence remain outside this
statement. See `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
* arXiv:2103.13367, Supplemental Material, eq. (26) and proof of Theorem MPS_classification.
-/

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace MPSPreparation

/-- The normalization constant is uniform over every density-matrix reference, including
singular ones. Only the fixed bond dimension enters it. -/
theorem exists_abs_norm_chainState_sq_sub_one_le_uniform_reference (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d N : ℕ} (A : MPSChainTensor d D N)
      (σ : Matrix (Fin D) (Fin D) ℂ), σ.PosSemidef → σ.trace = 1 →
      |‖chainState A‖ ^ 2 - 1| ≤ K *
        ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
          transferMatrix (Kraus.transferMap (fixedPointTensor σ))‖ := by
  let trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  refine ⟨‖trL‖, norm_nonneg _, fun {d N} A σ hσ htr => ?_⟩
  have := Matrix.neZero_of_trace_eq_one htr
  have htrace : Matrix.trace (transferMatrix (Kraus.transferMap (fixedPointTensor σ))) = 1 := by
    simpa only [pow_one] using
      (trace_transferMatrix_transferMap_pow_eq_mpvOverlap (fixedPointTensor σ) 1).trans
        (mpvOverlap_fixedPointTensor_self hσ htr 1)
  have heq : ((‖chainState A‖ ^ 2 - 1 : ℝ) : ℂ) =
      trL (transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor σ))) := by
    change _ = Matrix.trace _
    rw [Matrix.trace_sub, htrace, Complex.ofReal_sub, Complex.ofReal_one,
      ofReal_norm_chainState_sq]
  have h := trL.le_opNorm (transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
    transferMatrix (Kraus.transferMap (fixedPointTensor σ)))
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Uniform normalized pair error from varying density-matrix reset references. The pair
leaving a block uses the following block's reference, and the whole-ring transfer estimate
controls normalization separately. -/
theorem exists_one_sub_norm_inner_chainPosState_le_varying_reference (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d N M : ℕ} [NeZero M]
      (A : MPSChainTensor d D N) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N)
      (σ : Fin M → Matrix (Fin D) (Fin D) ℂ) (τ : Matrix (Fin D) (Fin D) ℂ),
      (∀ j, (σ j).PosSemidef) → (∀ j, (σ j).trace = 1) →
      τ.PosSemidef → τ.trace = 1 → ∀ {δ : ℝ}, 0 ≤ δ →
      (∀ j, ‖transferMatrix (Kraus.transferMap (chainBlockTensor A hN j)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor (σ j)))‖ ≤ δ) →
      ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor τ))‖ ≤ δ →
      1 - ‖⟪pairFamilyVector (fun j => fixedPointPair (σ (finRotate M j))),
        (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ‖ ≤
          C * (M * Real.sqrt δ) := by
  obtain ⟨Co, hCo, hover⟩ := exists_norm_trace_prod_polarPos_sub_one_le_varying_reference D
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_chainState_sq_sub_one_le_uniform_reference D
  let C := Co + Kn
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C * Real.exp C + 1, by positivity,
    fun {d N M} _ A ℓ hN σ τ hσ htr hτ hτtr δ hδ hA hwhole => ?_⟩
  let Ω := pairFamilyVector (fun j => fixedPointPair (σ (finRotate M j)))
  let v := chainPosState A hN
  have hΩ : ‖Ω‖ = 1 := norm_pairFamilyVector fun j => by
    rw [fixedPointPair_norm_sq (hσ _), htr]
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have htriv : 1 - ‖⟪Ω, (‖v‖ : ℂ)⁻¹ • v⟫_ℂ‖ ≤ 1 := by
    linarith only [norm_nonneg ⟪Ω, (‖v‖ : ℂ)⁻¹ • v⟫_ℂ]
  rcases le_or_gt (M * Real.sqrt δ) 1 with hy | hy
  · have hs : Real.sqrt δ ≤ 1 := by nlinarith [Real.sqrt_nonneg δ]
    have hδs : δ ≤ Real.sqrt δ := by nlinarith [Real.sq_sqrt hδ, Real.sqrt_nonneg δ]
    have ho : ‖⟪Ω, v⟫_ℂ - 1‖ ≤ Co * (M * Real.sqrt δ) *
        Real.exp (Co * (M * Real.sqrt δ)) := by
      have hi : ⟪Ω, v⟫_ℂ = Matrix.trace (List.ofFn fun j => transferMatrix
          (Kraus.mixedMapLM (polarPosTensor (chainBlockTensor A hN j))
            (fixedPointTensor (σ j)))).prod := by
        rw [← sum_mpvFamily_mul_star_mpvFamily, PiLp.inner_apply]
        simp only [RCLike.inner_apply, mpvFamily_fixedPointTensor]
        rfl
      rw [hi]
      exact hover _ _ σ hσ htr hδ hA
    have hn : |‖v‖ ^ 2 - 1| ≤ Kn * Real.sqrt δ := by
      rw [← norm_chainState_eq A hN]
      exact (hnorm A τ hτ hτtr).trans
        (mul_le_mul_of_nonneg_left (hwhole.trans hδs) hKn)
    have ha : |1 - ‖⟪Ω, v⟫_ℂ‖| ≤ Co * (M * Real.sqrt δ) *
        Real.exp (Co * (M * Real.sqrt δ)) := by
      calc |1 - ‖⟪Ω, v⟫_ℂ‖| = |‖(1 : ℂ)‖ - ‖⟪Ω, v⟫_ℂ‖| := by rw [norm_one]
        _ ≤ ‖⟪Ω, v⟫_ℂ - 1‖ := by rw [norm_sub_rev]; exact abs_norm_sub_norm_le _ _
        _ ≤ _ := ho
    have herr := one_sub_norm_inner_smul_inv_norm_le hΩ.le ha hn
    have hCoC : Co ≤ C := by dsimp [C]; linarith
    have hexp : 1 ≤ Real.exp C := Real.one_le_exp hC.le
    have ho' : Co * (M * Real.sqrt δ) * Real.exp (Co * (M * Real.sqrt δ)) ≤
        Co * (M * Real.sqrt δ) * Real.exp C := by
      gcongr
      exact (mul_le_of_le_one_right hCo.le hy).trans hCoC
    have hn' : Kn * Real.sqrt δ ≤ Kn * (M * Real.sqrt δ) * Real.exp C := by
      calc Kn * Real.sqrt δ ≤ Kn * (M * Real.sqrt δ) := by
            gcongr; exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hM
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hexp
    dsimp only [C]
    nlinarith
  · have hbound : 1 ≤ (C * Real.exp C + 1) * (M * Real.sqrt δ) := by
      nlinarith [mul_nonneg hC.le (Real.exp_pos C).le]
    exact htriv.trans hbound

/-- Uniform exponential ordered mixing towards site-dependent density reset maps gives
physical logarithmic-depth preparation of the original family at all sufficiently large
lengths. References need only be positive semidefinite and trace one; the uniform Hölder
bound replaces the input exponent `r` by `r/2`. The cutoff and depth constant are selected
before the ring length and accuracy, and no short-ring nonzero assumption is imposed. -/
theorem exists_isPreparedInDepth_inhomogeneous_le_log_eventually_of_varying_reference
    (d D : ℕ) (hd : 0 < d) (A : ∀ N, MPSChainTensor d D N)
    (σ : ∀ N, Fin N → Matrix (Fin D) (Fin D) ℂ)
    (hσ : ∀ (N : ℕ) [NeZero N] (j : Fin N), (σ N j).PosSemidef)
    (htr : ∀ (N : ℕ) [NeZero N] (j : Fin N), (σ N j).trace = 1)
    (K r : ℝ) (hK : 0 < K) (hr : 0 < r)
    (hmix : ∀ (N : ℕ) [NeZero N] {M : ℕ} (ℓ : Fin M → ℕ)
      (hN : ∑ j, ℓ j = N) (j : Fin M) (hj : 0 < ℓ j),
      ‖transferMatrix ((List.ofFn fun i : Fin (ℓ j) =>
          Kraus.transferMap (A N (blockSite hN j i))).prod) -
        transferMatrix (Kraus.transferMap (fixedPointTensor
          (σ N (blockSite hN j ⟨0, hj⟩))))‖ ≤ K * Real.exp (-(r * ℓ j))) :
    ∃ N₀ : ℕ, ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ C * Real.log (N / ε) ∧
        IsPreparedInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_chainState_sq_sub_one_le_uniform_reference D
  let L := Kn * K + 1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((Real.log L - Real.log (1 / 2 : ℝ)) / r)
  have hne (N : ℕ) [NeZero N] (hcut : N₀ ≤ N) : chainState (A N) ≠ 0 := by
    have hthreshold : Real.log L - Real.log (1 / 2 : ℝ) ≤ r * N := by
      have hle := hN₀.trans (Nat.cast_le.mpr hcut)
      simpa only [mul_comm] using (div_le_iff₀ hr).mp hle
    have hsmall : L * Real.exp (-(r * N)) ≤ 1 / 2 := by
      have h := mul_mul_exp_neg_le_of_log_le hL zero_lt_one
        (by norm_num : 0 < (1 / 2 : ℝ))
        (by simpa only [Real.log_one, add_zero] using hthreshold)
      simpa only [one_mul] using h
    have hsingle : ∑ _ : Fin 1, N = N := by simp
    have hi : ∀ i : Fin N, blockSite hsingle 0 i = i := by
      intro i
      apply Fin.ext
      simp [blockSite, blockOffset]
    have ht := hmix N (fun _ : Fin 1 => N) hsingle 0
      (Nat.pos_of_ne_zero (NeZero.ne N))
    simp only [hi] at ht
    rw [← MPSChainTensor.transferMap_blockTensor] at ht
    have hb : |‖chainState (A N)‖ ^ 2 - 1| ≤ 1 / 2 := by
      calc |‖chainState (A N)‖ ^ 2 - 1|
          ≤ Kn * ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (A N))) -
            transferMatrix (Kraus.transferMap (fixedPointTensor (σ N 0)))‖ :=
              hnorm _ _ (hσ N 0) (htr N 0)
        _ ≤ Kn * (K * Real.exp (-(r * N))) := mul_le_mul_of_nonneg_left ht hKn
        _ ≤ L * Real.exp (-(r * N)) := by
            dsimp only [L]
            nlinarith [Real.exp_pos (-(r * N))]
        _ ≤ 1 / 2 := hsmall
    intro hz
    norm_num [hz] at hb
  obtain ⟨Cp, hCp, hp⟩ := exists_one_sub_norm_inner_chainPosState_le_varying_reference D
  let B (N : ℕ) : VaryingBondChain d D N :=
    { bondDim := fun _ => D
      bondDim_le := fun _ => le_rfl
      tensor := A N }
  have hpad (N : ℕ) : zeroPad (B N) = A N := by
    funext j i a b
    simp [B, VaryingBondChain.zeroPad, Matrix.zeroPad]
  have hstate (N : ℕ) [NeZero N] : state (B N) = chainState (A N) := by
    rw [state_eq_chainState, hpad]
  have hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N → N₀ ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsPairApproximable (B N) hN
          (Cp * Real.sqrt K * ((N : ℝ) ^ 1 * Real.exp (-((r / 2) * q)))) := by
    intro N _ q hq hqN hN₀
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
      exact hne N hN₀ (norm_eq_zero.mp hn)
    let ρ : Fin (m + 1) → Matrix (Fin D) (Fin D) ℂ := fun j =>
      σ N (blockSite hsum j ⟨0, hq.trans_le (hℓq j)⟩)
    have hpair : padPairs (B N) ℓ (fun j => fixedPointPair (ρ (finRotate (m + 1) j))) =
        fun j : Fin (m + 1) => fixedPointPair (ρ (finRotate (m + 1) j)) := by
      funext j p
      simp [padPairs, padPair, Matrix.zeroPad, rightBond, leftBond, B]
      rfl
    refine ⟨hpos, fun j => fixedPointPair (ρ (finRotate (m + 1) j)), (fun j => ?_), ?_⟩
    · change ∑ p : Fin D × Fin D,
        star (fixedPointPair (ρ (finRotate (m + 1) j)) p) *
          fixedPointPair (ρ (finRotate (m + 1) j)) p = 1
      rw [fixedPointPair_norm_sq (hσ N _), htr N]
    rw [hpair, hpad]
    let δ := K * Real.exp (-(r * q))
    have hblock : ∀ j, ‖transferMatrix (Kraus.transferMap (chainBlockTensor (A N) hsum j)) -
        transferMatrix (Kraus.transferMap (fixedPointTensor (ρ j)))‖ ≤ δ := by
      intro j
      rw [chainBlockTensor, MPSChainTensor.transferMap_blockTensor]
      refine (hmix N ℓ hsum j (hq.trans_le (hℓq j))).trans ?_
      dsimp [δ]
      gcongr
      exact hℓq j
    have hwhole : ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (A N))) -
        transferMatrix (Kraus.transferMap (fixedPointTensor (σ N 0)))‖ ≤ δ := by
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
    have herr := hp (A N) ℓ hsum ρ (σ N 0) (fun j => hσ N _) (fun j => htr N _)
      (hσ N 0) (htr N 0) (show 0 ≤ δ by positivity) hblock hwhole
    have hsqrt : Real.sqrt δ = Real.sqrt K * Real.exp (-((r / 2) * q)) := by
      dsimp [δ]
      rw [Real.sqrt_mul hK.le]
      congr 1
      apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsqrt] at herr
    refine herr.trans ?_
    simp only [pow_one, Nat.cast_add, Nat.cast_one]
    calc Cp * ((m + 1) * (Real.sqrt K * Real.exp (-((r / 2) * q)))) =
        Cp * Real.sqrt K * ((m + 1) * Real.exp (-((r / 2) * q))) := by ring
      _ ≤ Cp * Real.sqrt K * (N * Real.exp (-((r / 2) * q))) := by
          gcongr; exact_mod_cast hMN
  obtain ⟨C, hC⟩ := exists_isPreparedInDepth_inhomogeneous_le_log_of_uniform_rate_from
    d D hd B (Cp * Real.sqrt K) (r / 2) 1 (mul_pos hCp (Real.sqrt_pos.mpr hK))
      (by positivity) N₀ hrate
  refine ⟨N₀, C, fun ε hε hε1 N _ hN₀ => ?_⟩
  simpa only [hstate] using hC ε hε hε1 N hN₀

end MPSPreparation
