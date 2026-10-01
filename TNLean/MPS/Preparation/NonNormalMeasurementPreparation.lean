/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.DepthLogBound
import TNLean.MPS.Preparation.MeasurementPreparation
import TNLean.MPS.Preparation.RepeatedBlockError

/-!
# Tensors that are not normal, prepared with measurements in depth `O(log(N/ε))`

arXiv:2307.01696, paragraph "Long-range MPS using measurements", prepares every
translation-invariant MPS, "short- or long-range correlated", with measurements: the GHZ-type
state `|χ_{N/q}⟩` is created in constant depth with measurements, the isometries
`W : |j⟩ ↦ |ω_j⟩` and the isometries of the blocked tensor follow as circuits, and with the
block length `q ∝ log(N/ε)` "If instead measurements are only used for the preparation of
`|χ_{N/q}⟩`, the depth is `O(log(N/ε))`."

This file proves this for a direct sum `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` of normal
blocks (eq. (S2)), with the corrected approximating state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` of `TNLean.MPS.Preparation.RepeatedBlockSum`:

* it is prepared with measurements and a circuit in depth `O(q)`
  (`MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_copyApproxVector`), as the
  state `∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩` of the blocks (`MPSPreparation.copyApproxVector_eq_sum`);
* with its error bound (`MPSTensor.exists_approximationError_le_mul_repeatedBlockSum`), a unit
  vector with error at most `ε` is prepared with measurements in depth `O(log(N/ε))`
  (`MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_repeatedBlockSum`).

**Scope restriction (orthogonal blocks):** both results take, at the block length `q`, the
orthogonality `B_jᴴ B_{j'} = 0` of the `q`-site states of distinct blocks, which the source does
not assume. Documented in `docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Scope restriction (block length dividing the chain length):** the depth bound
`O(log(N/ε))` is proved for block lengths `q` dividing `N`, the `N/q` equal blocks of eq. (10);
the source lets the last block be larger. The error bound for orthogonal blocks with
multiplicities is proved for equal blocks only. Documented in
`docs/paper-gaps/mswc24_measurement_preparation_scope.tex`.

**Local fix (corrected fixed-point state):** the state prepared is the corrected state of
`TNLean.MPS.Preparation.RepeatedBlockSum`, not the state of eq. (S7), which fails for blocks of
multiplicity `m_j ≥ 2`. Documented in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

## Main declarations

* `MPSPreparation.copyApproxVector_eq_sum` — the corrected approximating state is
  `∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩`.
* `MPSPreparation.sum_norm_sq_copyApproxVector` — it is a unit vector.
* `MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_copyApproxVector` — depth
  `O(q)` with measurements.
* `MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_repeatedBlockSum` —
  error `ε` in depth `O(log(N/ε))` with measurements.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, paragraph "Long-range MPS using measurements", eq. (19), and Supplemental
  Material, eqs. (S2)–(S7) and Lemma 1'(ii).
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSPreparation

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}
  {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- **The corrected approximating state as a sum over the blocks.** For blocks with nonzero
weights whose `q`-site blocked tensors are injective and have orthogonal physical matrices,
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`, read on the chain of `M q` sites, is
`∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩_{R_k L_{k+1}}` with `ω_j` the pair of the fixed point `σ_j`.

arXiv:2307.01696, eq. (10) for each block and Supplemental Material, eq. (S7), corrected as in
`TNLean.MPS.Preparation.RepeatedBlockSum`. -/
theorem copyApproxVector_eq_sum (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : CopyWeights b m} {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1) {q : ℕ} (hq : q ≠ 0)
    (hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q))
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) (M : ℕ) [NeZero M] (α : Fin b → ℂ)
    (hN : ∑ _ : Fin M, q = M * q) (s : Cfg d (M * q)) :
    copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ
        ((blockedConfigEquiv d M q).symm s) =
      ∑ j, α j * blockIsometryState (Aj j) (fixedPointPair (σ j)) hN s := by
  rw [copyApproxVector_repeatedBlockSum hι hdisj hq horth σ M α]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrArg (fun v : MPVSpace d (M * q) => v s)
    (approximatingMPVState_eq_blockIsometryState (Aj j) (hB j) (hσ j) (htr j) M hN)
  simp only [(inner_approximatingMPVState_mpvState (Aj j) (hB j) (hσ j) (htr j) M).1,
    approximatingMPVStateRaw_apply] at h
  rw [h]

/-- **The corrected approximating state is a unit vector** for unit amplitudes `α`, blocks with
injective blocked tensors and orthogonal physical matrices: the approximating states of the
blocks are orthonormal. -/
theorem sum_norm_sq_copyApproxVector (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    {μ : CopyWeights b m} {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1) {q : ℕ} (hq : q ≠ 0)
    (hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q))
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) (M : ℕ) [NeZero M] {α : Fin b → ℂ}
    (hα : ∑ j, star (α j) * α j = 1) :
    ∑ τ, ‖copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ τ‖ ^ 2 = 1 := by
  have : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  set s : (j : Fin b) → (Fin M → Fin (blockPhysDim d q)) → ℂ :=
    fun j τ => mpv (approximatingTensor (blockTensor (Aj j) q) (σ j)) τ
  have hss : ∀ j j', ∑ τ, star (s j τ) * s j' τ = if j = j' then 1 else 0 := fun j j' => by
    split_ifs with h
    · subst h; exact mpv_approximatingTensor_norm_sq (hB j) (hσ j) (htr j)
    · have := mpvOverlap_eq_zero (X := approximatingTensor (blockTensor (Aj j') q) (σ j'))
        (Y := approximatingTensor (blockTensor (Aj j) q) (σ j))
        (conjTranspose_physicalMatrix_approximatingTensor_mul (horth j j' h) _ _)
        (NeZero.ne M)
      rw [mpvOverlap] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
  have h := ofReal_sum_norm_sq fun τ =>
    copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ τ
  simp only [copyApproxVector_repeatedBlockSum hι hdisj hq horth σ M α] at h
  rw [sum_star_sum_mul_sum_of_orthogonal _ _ (fun _ => 1) s s hss] at h
  simp only [mul_one, hα] at h
  exact_mod_cast h

/-- **The corrected approximating state in depth `O(q)` with measurements.** There are `C` and
`L₀`, depending only on `d`, the number of blocks `b` and their bond dimensions `D_j`, such that
for every direct sum `Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` with nonzero weights, all
`σ_j ≥ 0` with `Tr σ_j = 1`, every block length `q ≥ L₀` at which every blocked tensor of the
blocks is injective and the physical matrices of distinct blocks are orthogonal, every number of
blocks `M ≥ 1` and all unit amplitudes `α`, the corrected approximating state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` on `N = M q` sites is prepared with measurements and a circuit in
depth at most `C q`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements" ("First create `|χ_{N/q}⟩`, which
can be done in constant depth with measurements ... Subsequently, apply in parallel the
isometries `W`"), followed by the isometries of the blocked tensor, in the scope of the module
docstring. -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_copyApproxVector (d b : ℕ)
    (Dj : Fin b → ℕ) :
    ∃ C L₀ : ℕ, ∀ {D : ℕ} {m : Fin b → ℕ} (Aj : (j : Fin b) → MPSTensor d (Dj j))
      (ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D), (∀ j k, Function.Injective (ι j k)) →
      (∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a') →
      ∀ (μ : CopyWeights b m) (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ),
      (∀ j, (σ j).PosSemidef) → (∀ j, (σ j).trace = 1) →
      ∀ q, L₀ ≤ q → (∀ j, Kraus.IsInjective (blockTensor (Aj j) q)) →
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      ∀ (M : ℕ) [NeZero (M * q)] (α : Fin b → ℂ), ∑ j, star (α j) * α j = 1 →
        IsPreparedWithMeasurementsAndCircuitInDepth (C * q) fun s =>
          copyApproxVector (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ
            ((blockedConfigEquiv d M q).symm s) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- No physical states: the hypotheses are contradictory.
    refine ⟨0, 1, fun Aj ι _ _ μ σ _ _ q hq _ _ M _ α hα => ?_⟩
    exfalso
    exact (Fin.elim0 ((Classical.arbitrary (Cfg 0 (M * q))) ⟨0, Nat.pos_of_ne_zero
      (NeZero.ne (M * q))⟩))
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨C, L₀, hC⟩ := exists_isPreparedWithMeasurementsAndCircuitInDepth_sum_blockIsometryState
    (d := d) b Dj
  refine ⟨C, max L₀ 1, fun Aj ι hι hdisj μ σ hσ htr q hq hB horth M _ α hα => ?_⟩
  have hq0 : q ≠ 0 := by have := le_max_right L₀ 1; omega
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hNq : ∑ _ : Fin M, q = M * q := by simp
  have key := hC Aj (fun j => fixedPointPair (σ j))
    (fun j => by rw [fixedPointPair_norm_sq (hσ j), htr j]) α hα (fun _ => q) hNq q
    (fun _ => le_of_max_le_left hq) (fun _ => le_rfl) (fun j _ => hB j) (fun j j' _ h => horth j j' h)
  convert key using 2 with s
  exact copyApproxVector_eq_sum hι hdisj hσ htr hq0 hB horth M α hNq s

/-! ### Error `ε` in depth `O(log(N/ε))` -/

/-- **A common gap for normal blocks.** For finitely many normal left-canonical blocks there is
`0 < t < 1` bounding the moduli of the eigenvalues other than `1` of all their transfer maps
(arXiv:2307.01696, eq. (5) and the remark after it, for each block). -/
theorem exists_forall_eigenvalue_norm_le [NeZero b] (hN : ∀ j, Kraus.IsNormal (Aj j))
    (hA : ∀ j, IsLeftCanonical (Aj j)) (hD : ∀ j, NeZero (Dj j)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖(t : ℂ)‖ := by
  have hgap : ∀ j, ∃ δ > 0, ∀ μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ 1 - δ := fun j =>
    uniform_eigenvalue_gap_of_finite_lt_one
      (Module.End.finite_hasEigenvalue (Kraus.transferMap (Aj j))) fun μ' hμ hne =>
        lt_of_le_of_ne ((Kraus.isChannel_mapLM (Aj j) (hA j)).eigenvalue_norm_le_one μ' hμ)
          fun h => hne ((isNormalTensor_of_isNormal_leftCanonical (Aj j) (hN j)
            (hA j)).primitive_transfer.unique_peripheral μ' hμ h)
  choose δ hδ hgap using hgap
  set δ₀ := Finset.univ.inf' Finset.univ_nonempty δ
  have hδ₀ : 0 < δ₀ := (Finset.lt_inf'_iff _).2 fun j _ => hδ j
  set t := max (1 - δ₀) (1 / 2)
  have ht0 : 0 < t := lt_max_of_lt_right (by norm_num)
  refine ⟨t, ht0, max_lt (by linarith) (by norm_num), fun j μ' hμ hne => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  have : δ₀ ≤ δ j := Finset.inf'_le _ (Finset.mem_univ j)
  exact (hgap j μ' hμ hne).trans ((by linarith : 1 - δ j ≤ 1 - δ₀).trans (le_max_left _ _))

/-- **Tensors that are not normal, with measurements, in depth `O(log(N/ε))`.** Let
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (arXiv:2307.01696, Supplemental Material,
eq. (S2)) with nonzero weights, every block `A_j` normal in the gauge of eq. (5):
`∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1`. There are `a > 0`,
`b' ≥ 1` and `c`, depending only on `A`, with the following property. For `N ≥ 2`, `0 < ε ≤ 1`,
and a block length `q` dividing `N` with `a log(N/ε) + b' ≤ q ≤ 2 (a log(N/ε) + b')`, at which
the `q`-site states of distinct blocks are orthogonal, and with the weights
`βⱼ = ∑ₖ μ_{j,k}^N` not all zero, some unit vector `|ψ⟩` with `1 - |⟨ψ|φ_N⟩| ≤ ε` is prepared
with measurements and a circuit in depth at most `c log(N/ε)`.

arXiv:2307.01696, paragraph "Long-range MPS using measurements": "If instead measurements are
only used for the preparation of `|χ_{N/q}⟩`, the depth is `O(log(N/ε))`", for the corrected
approximating state and in the scope of the module docstring (orthogonal blocks, block length
dividing `N`). The vector `|ψ⟩` is the corrected approximating state
`V^{⊗N/q} ∑ⱼ αⱼ L_j^{⊗N/q} |Ω_j⟩`, prepared in depth `O(q)`
(`exists_isPreparedWithMeasurementsAndCircuitInDepth_copyApproxVector`), with the error bound of
Lemma 1'(ii) (`MPSTensor.exists_approximationError_le_mul_repeatedBlockSum`). -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_repeatedBlockSum [NeZero b]
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j) :
    ∃ a b' c : ℝ, 0 < a ∧ 1 ≤ b' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (N q : ℕ) [NeZero N], 2 ≤ N → q ∣ N → a * Real.log (N / ε) + b' ≤ q →
        (q : ℝ) ≤ 2 * (a * Real.log (N / ε) + b') →
        (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
          physicalMatrix (blockTensor (Aj j') q) = 0) →
        bntWeight μ N ≠ 0 →
        ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (N / ε) ∧
          IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ s) ∧
          1 - ‖⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) N⟫_ℂ‖ ≤ ε := by
  classical
  have hDj : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  obtain ⟨t, ht0, ht1, hlam⟩ := exists_forall_eigenvalue_norm_le hN hA hDj
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  obtain ⟨K, hK, herr⟩ := exists_approximationError_le_mul_repeatedBlockSum (μ := μ) hι hdisj hN
    hA hσ htr hfix (lam₂ := (t : ℂ)) hlam (γ := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨Cp, L₀, hCp⟩ := exists_isPreparedWithMeasurementsAndCircuitInDepth_copyApproxVector d b Dj
  choose Linj hLpos hLinj using hN
  set Lm : ℕ := ∑ j, Linj j
  set r := -(1 / 4 * Real.log t) with hr
  have hr0 : 0 < r := by
    have := Real.log_neg ht0 ht1
    rw [hr]; linarith
  have hexp : ∀ q : ℕ, Real.exp (-(1 / 4) * q / correlationLength (t : ℂ)) =
      Real.exp (-(r * q)) := fun q => by
    congr 1
    rw [mul_div_right_comm, neg_div_correlationLength, hnorm, hr]
    ring
  set a := 1 / r with ha
  have ha0 : 0 < a := by positivity
  set b' : ℝ := a * max (Real.log K) 0 + L₀ + Lm + 1 with hb'
  have hmax : 0 ≤ a * max (Real.log K) 0 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb1 : 1 ≤ b' := by
    have : (0 : ℝ) ≤ L₀ + Lm := by positivity
    linarith
  refine ⟨a, b', Cp * (2 * a + 2 * b' / Real.log 2), ha0, hb1,
    fun ε hε hε1 N q _ hN2 hqN hq hq2 horth hβ => ?_⟩
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hlog : Real.log 2 ≤ Real.log (N / ε) :=
    Real.log_le_log two_pos (hN2'.trans (le_div_self (by positivity) hε hε1))
  have hlog0 : 0 ≤ Real.log (N / ε) := hl2.le.trans hlog
  have hbq : b' ≤ q := by
    have : 0 ≤ a * Real.log (N / ε) := by positivity
    linarith
  have hLq : L₀ ≤ q := by
    have : (L₀ : ℝ) ≤ q := by have : (0 : ℝ) ≤ Lm := by positivity
                              linarith
    exact_mod_cast this
  have hLmq : ∀ j, Linj j ≤ q := fun j => by
    have h1 : Linj j ≤ Lm := Finset.single_le_sum (f := Linj) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    have h2 : (Lm : ℝ) ≤ q := by have : (0 : ℝ) ≤ L₀ := by positivity
                                 linarith
    have : Lm ≤ q := by exact_mod_cast h2
    omega
  have hq1 : (1 : ℝ) ≤ q := hb1.trans hbq
  obtain ⟨M, hM⟩ := hqN
  rw [mul_comm] at hM
  subst hM
  have : NeZero M := ⟨fun h => NeZero.ne (M * q) (by rw [h, zero_mul])⟩
  have hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q) := fun j =>
    (isNBlkInjective_iff_blockTensor_isInjective (Aj j) q).1
      (isNBlkInjective_of_le (hLpos j) (hLinj j) (hLmq j))
  have hq0 : q ≠ 0 := by
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this.ne'
  set α := ghzAmplitude (bntWeight μ (M * q))
  have hα : ∑ j, star (α j) * α j = 1 := ghzAmplitude_norm_sq hβ
  have hprep := hCp Aj ι hι hdisj μ σ (fun j => (hσ j).posSemidef) htr q hLq hB horth M α hα
  set v : Cfg d (M * q) → ℂ := fun s => copyApproxVector (repeatedBlockSum Aj ι μ) q M α
    (copyIsometry ι μ q) σ ((blockedConfigEquiv d M q).symm s) with hv
  set ψ : MPVSpace d (M * q) := (EuclideanSpace.equiv (ι := Cfg d (M * q)) (𝕜 := ℂ)).symm v
  have hψ : (fun s => ψ s) = v := funext fun s => by
    simp [ψ, EuclideanSpace.equiv, PiLp.toLp_apply]
  have hsq := sum_norm_sq_copyApproxVector hι hdisj (μ := μ) (fun j => (hσ j).posSemidef) htr
    hq0 hB horth M hα
  have hψn : ‖ψ‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : ∑ s, ‖ψ s‖ ^ 2 = 1 := by
      rw [← hsq, ← (blockedConfigEquiv d M q).sum_comp]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [show ψ (blockedConfigEquiv d M q τ) = v (blockedConfigEquiv d M q τ) from
        congrFun hψ _, hv]
      simp only [Equiv.symm_apply_apply]
    rw [this, Real.sqrt_one]
  have hinner : ⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) (M * q)⟫_ℂ =
      copyApproxOverlap (repeatedBlockSum Aj ι μ) q M α (copyIsometry ι μ q) σ := by
    rw [copyApproxOverlap, hsq, Real.sqrt_one, Complex.ofReal_one, inv_one, PiLp.inner_apply,
      ← (blockedConfigEquiv d M q).sum_comp]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [RCLike.inner_apply, one_mul, show ψ (blockedConfigEquiv d M q τ) =
      v (blockedConfigEquiv d M q τ) from congrFun hψ _, hv]
    simp only [Equiv.symm_apply_apply]
    rw [mul_comm]
    rfl
  refine ⟨ψ, Cp * q, hψn, ?_, by rw [hψ]; exact hprep, ?_⟩
  · have hbl : b' ≤ b' / Real.log 2 * Real.log (M * q / ε) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlog) (zero_le_one.trans hb1)
    push_cast at hq2 hbl ⊢
    calc (Cp : ℝ) * q ≤ Cp * (2 * (a * Real.log (M * q / ε) + b')) :=
          mul_le_mul_of_nonneg_left hq2 (Nat.cast_nonneg _)
      _ ≤ Cp * ((2 * a + 2 * b' / Real.log 2) * Real.log (M * q / ε)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have e : (2 * a + 2 * b' / Real.log 2) * Real.log (M * q / ε) =
              2 * (a * Real.log (M * q / ε)) + 2 * (b' / Real.log 2 * Real.log (M * q / ε)) := by
            ring
          rw [e]
          linarith
      _ = _ := by ring
  · rw [hinner]
    refine (herr q M horth hβ).trans ?_
    rw [hexp]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
    have hlogN : Real.log ((M * q : ℕ) / ε) = Real.log M + Real.log q - Real.log ε := by
      push_cast
      rw [Real.log_div (by positivity) hε.ne', Real.log_mul (by positivity) (by positivity)]
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
    have hrq : Real.log K + Real.log M - Real.log ε ≤ r * q := by
      have h1 : r * (a * Real.log ((M * q : ℕ) / ε) + b') ≤ r * q :=
        mul_le_mul_of_nonneg_left hq hr0.le
      have h2 : r * (a * Real.log ((M * q : ℕ) / ε) + b') =
          Real.log ((M * q : ℕ) / ε) + max (Real.log K) 0 + r * (L₀ + Lm + 1) := by
        simp only [hb', ha]; field_simp; ring
      have : 0 ≤ r * (L₀ + Lm + 1) := by positivity
      rw [hlogN] at h2
      linarith [le_max_left (Real.log K) 0]
    exact mul_mul_exp_neg_le_of_log_le hK (by positivity) hε hrq

end MPSPreparation
