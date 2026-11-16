/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixIsometryKronecker
import TNLean.MPS.Preparation.InhomogeneousLongRange
import TNLean.MPS.Preparation.InhomogeneousExactPreparation
import TNLean.MPS.Preparation.InjectivityCutoff
import TNLean.MPS.Preparation.OverlappingMeasurementPreparation

/-!
# Uniform accuracy scales for coherent inhomogeneous pair approximations

The explicit class used here consists of positive-part states approximable by coherent sums
of locally orthonormal pair products. Local orthogonality bounds the number of labels by
D²,
so constants can be uniform even when that number varies with the length and partition.
A uniform bound
`K N^k exp(-r q)` yields blocking and preparation depth `O(1 + log(N/ε))`.

**Scope restriction (specified class and uniform rate):** these are quantitative hypotheses,
not consequences of the last sentence of arXiv:2307.01696, "Long-range MPS using measurements".
The theorem constructs the scale from the uniform rate; it does not infer that rate from
qualitative convergence. See `docs/paper-gaps/mswc24_inhomogeneous_long_range.tex`.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace

namespace MPSPreparation

/-- A nonzero chain has a coherent-pair approximation with `b` labels and error at most `δ`
on a specified partition when its normalized positive-part state has that approximation.
The pairs at each window are orthonormal, and the amplitudes have squared moduli summing to
one. This is an explicit conditional class for the inhomogeneous remark after eq. (19) of
arXiv:2307.01696, not a definition supplied separately by that remark. -/
def IsCoherentPairApproximable {d D N M : ℕ} (b : ℕ) (A : MPSChainTensor d D N)
    {ℓ : Fin M → ℕ} (hN : ∑ j, ℓ j = N) (δ : ℝ) : Prop :=
  chainState A ≠ 0 ∧ ∃ (ω : Fin b → Fin M → Fin D × Fin D → ℂ),
    (∀ k j j', ∑ p, star (ω j k p) * ω j' k p = if j = j' then 1 else 0) ∧
    ∃ α : Fin b → ℂ, (∑ j, star (α j) * α j = 1) ∧
      1 - ‖⟪∑ j, α j • pairFamilyVector (ω j),
        (‖chainPosState A hN‖ : ℂ)⁻¹ • chainPosState A hN⟫_ℂ‖ ≤ δ

/-- Local orthogonality bounds the label count by the dimension of one pair window.
The partition must be nonempty; no lower bound on individual amplitudes is needed. -/
theorem IsCoherentPairApproximable.label_le {d D N M b : ℕ} [NeZero M]
    {A : MPSChainTensor d D N} {ℓ : Fin M → ℕ} {hN : ∑ j, ℓ j = N} {δ : ℝ}
    (h : IsCoherentPairApproximable b A hN δ) : b ≤ D * D := by
  classical
  obtain ⟨_, ω, hω, _⟩ := h
  let X : Matrix (Fin D × Fin D) (Fin b) ℂ := fun p j => ω j 0 p
  have hX : X.IsIsometry := by
    change Xᴴ * X = 1
    ext i j
    change (∑ p, star (ω i 0 p) * ω j 0 p) = if i = j then 1 else 0
    exact hω 0 i j
  simpa only [Fintype.card_prod, Fintype.card_fin] using Matrix.IsIsometry.card_le X hX

/-- The explicit coherent-pair approximation condition transfers to a unit physical output,
with the same error, in depth linear in the largest block length. -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_of_isCoherentPairApproximable
    (d D b : ℕ) (hd : 2 ≤ d) (hD : 0 < D) :
    ∃ C L₀ : ℕ, ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
      (hN : ∑ k, ℓ k = N) (A : MPSChainTensor d D N) (L : ℕ) (δ : ℝ),
      (∀ k, L₀ ≤ ℓ k) → (∀ k, ℓ k ≤ L) → IsCoherentPairApproximable b A hN δ →
      ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧
        IsPreparedWithMeasurementsAndCircuitInDepth (C * L) (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ‖ ≤ δ := by
  obtain ⟨C, L₀, hC⟩ :=
    exists_isPreparedWithMeasurementsAndCircuitInDepth_inhomogeneousLongRange d D b hd hD
  refine ⟨C, L₀, fun {M} _ ℓ N _ hN A L δ hℓ hL ⟨_, ω, hω, α, hα, herr⟩ => ?_⟩
  obtain ⟨X, _, _, hX⟩ := hC ℓ hN A L hℓ hL
  obtain ⟨hprep, hunit, hinner⟩ := hX ω hω α hα
  exact ⟨_, hunit, hprep, by rwa [hinner]⟩

/-- Preparation constants can be chosen independently of the coherent label count.
Local orthogonality supplies the finite bound on that count. -/
theorem exists_coherentPairPreparation_uniform_labels
    (d D : ℕ) (hd : 2 ≤ d) (hD : 0 < D) :
    ∃ C L₀ : ℕ, ∀ (b : ℕ) {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N]
      (hN : ∑ k, ℓ k = N) (A : MPSChainTensor d D N) (L : ℕ) (δ : ℝ),
      (∀ k, L₀ ≤ ℓ k) → (∀ k, ℓ k ≤ L) → IsCoherentPairApproximable b A hN δ →
      ∃ ψ : MPVSpace d N, ‖ψ‖ = 1 ∧
        IsPreparedWithMeasurementsAndCircuitInDepth (C * L) (fun t => ψ t) ∧
        1 - ‖⟪ψ, (‖chainState A‖ : ℂ)⁻¹ • chainState A⟫_ℂ‖ ≤ δ := by
  classical
  have hex (i : Fin (D * D + 1)) :=
    exists_isPreparedWithMeasurementsAndCircuitInDepth_of_isCoherentPairApproximable d D i hd hD
  choose C L₀ hC using hex
  refine ⟨∑ i, C i, ∑ i, L₀ i, ?_⟩
  intro b M _ ℓ N _ hN A L δ hℓ hL happ
  let i : Fin (D * D + 1) := ⟨b, Nat.lt_succ_iff.mpr happ.label_le⟩
  have hCi : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (C j)) (Finset.mem_univ i)
  have hLi : L₀ i ≤ ∑ j, L₀ j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (L₀ j)) (Finset.mem_univ i)
  obtain ⟨ψ, hψ, hprep, herr⟩ := hC i ℓ hN A L δ (fun k => hLi.trans (hℓ k)) hL happ
  obtain ⟨T₁, T₂, φ, U, hT, hmeas, hcir, heq⟩ := hprep
  exact ⟨ψ, hψ, ⟨T₁, T₂, φ, U, hT.trans (Nat.mul_le_mul_right L hCi), hmeas, hcir, heq⟩, herr⟩

/-- A uniform polynomial-exponential coherent-pair approximation rate gives one
accuracy-dependent logarithmic preparation bound for the whole inhomogeneous family.
The label count may vary with the length and partition. Local orthogonality bounds it by
D², so all constants are independent of that choice.
The additive one also covers a one-site ring at accuracy one. All constants are independent
of the ring length and accuracy. Source: the conditional interpretation of arXiv:2307.01696,
eq. (19) and its concluding inhomogeneous remark. -/
theorem exists_inhomogeneousLongRange_depth_le_log_of_uniform_rate_varying_labels
    (d D : ℕ) (hd : 2 ≤ d) (hD : 0 < D) (A : ∀ N, MPSChainTensor d D N)
    (K r : ℝ) (k : ℕ) (hK : 0 < K) (hr : 0 < r)
    (hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        ∃ b : ℕ, IsCoherentPairApproximable b (A N) hN (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧
        (T : ℝ) ≤ C * (1 + Real.log (N / ε)) ∧
        IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  classical
  obtain ⟨Cb, L₀, hCb⟩ :=
    exists_coherentPairPreparation_uniform_labels d D hd hD
  obtain ⟨Ce, hCe⟩ := exists_isPreparedInDepth_normalizedChainState d D (by omega)
  let a : ℝ := max (k : ℝ) 1 / r
  let B : ℝ := max (Real.log K) 0 / r + L₀ + 1
  let c : ℝ := a + B + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 1 ≤ B := by
    have : 0 ≤ max (Real.log K) 0 / r + L₀ := by positivity
    dsimp [B]
    linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨(2 * Cb + Ce) * c, by positivity, fun N _ ε hε hε1 => ?_⟩
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log ((N : ℝ) / ε) :=
    Real.log_nonneg ((one_le_div hε).2 (hε1.trans hN1))
  let Q := a * Real.log ((N : ℝ) / ε) + B
  let q := ⌈Q⌉₊
  have hQq : Q ≤ q := Nat.le_ceil Q
  have hqQ : (q : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by dsimp [Q]; positivity)
  have hq0 : 0 < q := by
    have : 1 ≤ Q := by dsimp [Q]; nlinarith
    exact_mod_cast (show (0 : ℝ) < q by linarith)
  have hqc : (q : ℝ) ≤ c * (1 + Real.log ((N : ℝ) / ε)) := by
    have : Q + 1 ≤ c * (1 + Real.log ((N : ℝ) / ε)) := by
      have := mul_nonneg (show 0 ≤ B + 1 by linarith) hlog
      dsimp [Q, c]
      nlinarith
    exact hqQ.le.trans this
  have hA : chainState (A N) ≠ 0 := by
    obtain ⟨M, _, ℓ, hsum, _, _, _, h⟩ := hrate N N hN0 le_rfl
    exact h.1
  have hunit : ‖(‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hA)]
  by_cases hqN : q ≤ N
  · obtain ⟨M, hM, ℓ, hsum, hℓq, hℓ2q, b, happ⟩ := hrate N q hq0 hqN
    let : NeZero M := ⟨hM.ne'⟩
    have hLq : L₀ ≤ q := by
      have hBL : (L₀ : ℝ) ≤ B := by
        have : 0 ≤ max (Real.log K) 0 / r := by positivity
        dsimp [B]
        linarith
      have : (L₀ : ℝ) ≤ q := by dsimp [Q] at hQq; nlinarith
      exact_mod_cast this
    obtain ⟨ψ, hψ, hprep, herr⟩ := hCb b ℓ hsum (A N) (2 * q) _
      (fun j => hLq.trans (hℓq j)) hℓ2q happ
    refine ⟨ψ, Cb * (2 * q), hψ, ?_, hprep, herr.trans ?_⟩
    · push_cast
      have hCb0 : (0 : ℝ) ≤ Cb := Nat.cast_nonneg _
      calc (Cb : ℝ) * (2 * q) = (2 * Cb) * q := by ring
        _ ≤ (2 * Cb) * (c * (1 + Real.log ((N : ℝ) / ε))) :=
          mul_le_mul_of_nonneg_left hqc (by positivity)
        _ ≤ (2 * Cb + Ce) * c * (1 + Real.log ((N : ℝ) / ε)) := by
          have : 0 ≤ (Ce : ℝ) * c * (1 + Real.log ((N : ℝ) / ε)) := by positivity
          nlinarith
    · exact mul_pow_mul_exp_neg_le_of_le hK hr hN1 hε hε1
        (le_refl a) (by dsimp [B]; have := Nat.cast_nonneg (α := ℝ) L₀; linarith) hQq
  · obtain ⟨T, hT, hprep⟩ := hCe N (A N) hA
    refine ⟨_, T, hunit, ?_, ?_, ?_⟩
    · have hT' : (T : ℝ) ≤ Ce * N := by exact_mod_cast hT
      have hNq : (N : ℝ) < q := by exact_mod_cast (not_le.mp hqN)
      have hCe0 : (0 : ℝ) ≤ Ce := Nat.cast_nonneg _
      calc (T : ℝ) ≤ Ce * N := hT'
        _ ≤ Ce * q := mul_le_mul_of_nonneg_left hNq.le hCe0
        _ ≤ Ce * (c * (1 + Real.log ((N : ℝ) / ε))) :=
          mul_le_mul_of_nonneg_left hqc hCe0
        _ ≤ (2 * Cb + Ce) * c * (1 + Real.log ((N : ℝ) / ε)) := by
          have : 0 ≤ (2 * Cb : ℝ) * c * (1 + Real.log ((N : ℝ) / ε)) := by positivity
          nlinarith
    · exact isPreparedWithMeasurementsAndCircuitInDepth_of_isPreparedInDepth hprep
        (by
          intro hz
          have hz' : (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N) = 0 := by
            ext s
            exact congrFun hz s
          simp [hz'] at hunit)
    · rw [inner_self_eq_norm_sq_to_K, hunit]
      simpa using hε.le

/-- The fixed-label specialization of the uniform rate theorem. -/
theorem exists_inhomogeneousLongRange_depth_le_log_of_uniform_rate
    (d D b : ℕ) (hd : 2 ≤ d) (hD : 0 < D) (A : ∀ N, MPSChainTensor d D N)
    (K r : ℝ) (k : ℕ) (hK : 0 < K) (hr : 0 < r)
    (hrate : ∀ (N : ℕ) [NeZero N] (q : ℕ), 0 < q → q ≤ N →
      ∃ (M : ℕ) (_ : 0 < M) (ℓ : Fin M → ℕ) (hN : ∑ j, ℓ j = N),
        (∀ j, q ≤ ℓ j) ∧ (∀ j, ℓ j ≤ 2 * q) ∧
        IsCoherentPairApproximable b (A N) hN (K * ((N : ℝ) ^ k * Real.exp (-(r * q))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧
        (T : ℝ) ≤ C * (1 + Real.log (N / ε)) ∧
        IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, (‖chainState (A N)‖ : ℂ)⁻¹ • chainState (A N)⟫_ℂ‖ ≤ ε := by
  apply exists_inhomogeneousLongRange_depth_le_log_of_uniform_rate_varying_labels
    d D hd hD A K r k hK hr
  intro N _ q hq hqN
  obtain ⟨M, hM, ℓ, hN, hlo, hhi, happ⟩ := hrate N q hq hqN
  exact ⟨M, hM, ℓ, hN, hlo, hhi, b, happ⟩

end MPSPreparation
