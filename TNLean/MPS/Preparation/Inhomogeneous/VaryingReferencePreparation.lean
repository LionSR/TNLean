/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.Inhomogeneous.CornerReferenceOverlap
import TNLean.MPS.Preparation.Inhomogeneous.InhomogeneousSequence
import TNLean.MPS.Preparation.Circuit.RemainderBlocks
import TNLean.MPS.Preparation.Inhomogeneous.RectangularBlocks
import TNLean.MPS.Preparation.Inhomogeneous.RectangularIntervalBlocks

/-!
# Physical preparation with varying positive semidefinite references

Quantitative ordered mixing gives normalized pair approximation for corner-supported
references, including actual varying bond spaces after padding. The final theorem of this
module specializes to a fixed square bond space. References may vary with the ring and
site and may be singular. The square-root Hölder estimate loses a factor two in the decay
exponent, while keeping all constants uniform before the ring and its reference family.

**Scope restriction (ordered mixing):** the exponential product estimates are additional
sufficient hypotheses for arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated
MPS". Deriving a rate from qualitative convergence remains outside this statement.
The actual rectangular-bond extension is in `RectangularPreparation`.
See `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

It also contains the following results.

* `MPSPreparation.exists_isPreparedInDepth_le_log_eventually_of_rectangular_mixing`,
  `MPSPreparation.exists_isPreparedInDepth_le_log_eventually_of_rectangular_window_domination`:
  quantitative preparation on actual varying bond spaces.

## References

* arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated MPS".
* arXiv:2103.13367, Supplemental Material, eq. (26) and proof of Theorem MPS_classification.
-/

section VaryingReferencePreparation

open Matrix MPSTensor QuantumCircuit VaryingBondChain
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker
  Matrix.Norms.L2Operator

namespace MPSPreparation

/-- The normalization constant is uniform over every density-matrix reference, including
singular ones. Only the fixed bond dimension enters it. -/
theorem exists_abs_norm_chainState_sq_sub_one_le_corner_reference (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {d N : ℕ} (A : MPSChainTensor d D N)
      (σ : Matrix (Fin D) (Fin D) ℂ) (b : ℕ), σ.trace = 1 →
      cornerProjection D b * σ = σ →
      |‖chainState A‖ ^ 2 - 1| ≤ K *
        ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
          transferMatrix (cornerReferenceMap σ b)‖ := by
  let trL := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin D × Fin D) ℂ ℂ)
  refine ⟨‖trL‖, norm_nonneg _, fun {d N} A σ b htr hsupp => ?_⟩
  have := Matrix.neZero_of_trace_eq_one htr
  have htrace : Matrix.trace (transferMatrix (cornerReferenceMap σ b)) = 1 := by
    rw [trace_transferMatrix_cornerReferenceMap, hsupp, htr]
  have heq : ((‖chainState A‖ ^ 2 - 1 : ℝ) : ℂ) =
      trL (transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
        transferMatrix (cornerReferenceMap σ b)) := by
    change _ = Matrix.trace _
    rw [Matrix.trace_sub, htrace, Complex.ofReal_sub, Complex.ofReal_one,
      ofReal_norm_chainState_sq]
  have h := trL.le_opNorm (transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
    transferMatrix (cornerReferenceMap σ b))
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- Uniform normalized pair error from varying density-matrix reset references. The pair
leaving a block uses the following block's reference, and the whole-ring transfer estimate
controls normalization separately. -/
theorem exists_one_sub_norm_inner_chainPosState_le_varying_reference (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d N M : ℕ} [NeZero M]
      (A : MPSChainTensor d D N) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N)
      (σ : Fin M → Matrix (Fin D) (Fin D) ℂ) (τ : Matrix (Fin D) (Fin D) ℂ)
      (b : Fin M → ℕ) (c : ℕ),
      (∀ j, (σ j).PosSemidef) → (∀ j, (σ j).trace = 1) →
      (∀ j, cornerProjection D (b j) * σ j = σ j) →
      τ.trace = 1 → cornerProjection D c * τ = τ → ∀ {δ : ℝ}, 0 ≤ δ →
      (∀ j, ‖transferMatrix (Kraus.transferMap (chainBlockTensor A hN j)) -
        transferMatrix (cornerReferenceMap (σ j) (b (finRotate M j)))‖ ≤ δ) →
      ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor A)) -
        transferMatrix (cornerReferenceMap τ c)‖ ≤ δ →
      1 - ‖⟪pairFamilyVector (fun j => fixedPointPair (σ (finRotate M j))),
        (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ‖ ≤
          C * (M * Real.sqrt δ) := by
  obtain ⟨Co, hCo, hover⟩ := exists_norm_trace_prod_polarPos_sub_one_le_corner_reference D
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_chainState_sq_sub_one_le_corner_reference D
  let C := Co + Kn
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C * Real.exp C + 1, by positivity,
    fun {d N M} _ A ℓ hN σ τ b c hσ htr hsupp hτtr hτsupp δ hδ hA hwhole => ?_⟩
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
      exact hover _ _ σ b hσ htr hsupp hδ hA
    have hn : |‖v‖ ^ 2 - 1| ≤ Kn * Real.sqrt δ := by
      rw [← norm_chainState_eq A hN]
      exact (hnorm A τ c hτtr hτsupp).trans
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
        IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Kn, hKn, hnorm⟩ := exists_abs_norm_chainState_sq_sub_one_le_corner_reference D
  let L := Kn * K + 1
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge ((Real.log L - Real.log (1 / 2 : ℝ)) / r)
  have hne (N : ℕ) [NeZero N] (hcut : N₀ ≤ N) : chainState (A N) ≠ 0 := by
    have hsmall : L * Real.exp (-(r * N)) ≤ 1 / 2 :=
      mul_exp_neg_mul_le_of_div_log_le hL hr (by norm_num)
        (hN₀.trans (Nat.cast_le.mpr hcut))
    have hsingle : ∑ _ : Fin 1, N = N := by simp
    have hi := blockSite_singleton hsingle
    have ht := hmix N (fun _ : Fin 1 => N) hsingle 0
      (Nat.pos_of_ne_zero (NeZero.ne N))
    simp only [hi] at ht
    rw [← MPSChainTensor.transferMap_blockTensor] at ht
    have hb : |‖chainState (A N)‖ ^ 2 - 1| ≤ 1 / 2 := by
      calc |‖chainState (A N)‖ ^ 2 - 1|
          ≤ Kn * ‖transferMatrix (Kraus.transferMap (MPSChainTensor.blockTensor (A N))) -
            transferMatrix (Kraus.transferMap (fixedPointTensor (σ N 0)))‖ :=
              by simpa only [cornerReferenceMap_full (hσ N 0)] using
                hnorm (A N) (σ N 0) D (htr N 0) (by simp)
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
    obtain ⟨m, ℓ, hm, hsum, hℓq, hℓ2q⟩ := exists_remainderBlocks hq hqN
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
      have hi := blockSite_singleton hsingle
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
    have herr := hp (A N) ℓ hsum ρ (σ N 0) (fun _ => D) D
      (fun j => hσ N _) (fun j => htr N _) (fun j => by simp) (htr N 0) (by simp)
      (show 0 ≤ δ by positivity)
      (fun j => by
        simpa only [cornerReferenceMap_full (show (ρ j).PosSemidef from hσ N _)] using hblock j)
      (by simpa only [cornerReferenceMap_full (hσ N 0)] using hwhole)
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

end VaryingReferencePreparation

section RectangularPreparation

/-!
## Quantitative preparation on actual varying bond spaces

Uniform exponential convergence of the actual rectangular interval transfers to density
resets gives normalized pair approximation and eventual physical logarithmic-depth
preparation. The norm is the Hilbert--Schmidt induced operator norm, expressed in matrix-unit
bases. References may be singular and vary with both the site and the ring.

The quantitative mixing bound is an additional sufficient hypothesis. The qualitative
finite-correlation condition in arXiv:2307.01696v2 does not supply this accuracy rate.
The circuits act on rings; no nearest-neighbor open-line conclusion is asserted.

### References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS", and
  Supplemental Material, eqs. (S39) and (S42).

### Physical preparation from rectangular local windows

A uniform fixed-width Choi minorization on the actual rectangular bond spaces derives
the references and exponential interval estimate required for physical preparation.
The original MPS is unchanged, and the circuit conclusion uses ring adjacency.

**Scope restriction (local minorization):** this is a quantitative sufficient condition
for the inhomogeneous paragraph of arXiv:2307.01696v2. Qualitative convergence alone does
not provide its uniform strength or accuracy rate; see
`docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

#### References

* arXiv:2307.01696v2, paragraph "Inhomogeneous short-range correlated MPS".
* Wolf, *Quantum Channels & Operations*, Theorem 8.17 and Eq. (8.86).
-/

section

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
        IsPreparedInDepth (Geometry.ring N) T (fun s => ψ s) ∧
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
    obtain ⟨m, ℓ, hm, hsum, hℓq, hℓ2q⟩ := exists_remainderBlocks hq hqN
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

end

section

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
        IsPreparedInDepth (Geometry.ring N) T (fun x => ψ x) ∧
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

end

end RectangularPreparation
