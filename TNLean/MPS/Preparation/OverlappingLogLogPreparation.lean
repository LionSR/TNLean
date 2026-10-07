/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingMeasurementPreparation
import TNLean.MPS.Preparation.SupportedLogLogPreparation
import TNLean.Spectral.MixedEigenvalueGap

/-!
# Non-normal canonical states in double-logarithmic measurement depth

Combine the amplitude-uniform overlapping-sector approximation with a coherent supported
polar tree. A single circuit preserves arbitrary complex sector superpositions, including
lengths with vanishing individual amplitudes. Every nonzero periodic state at `N ≥ 2` is
covered, using an exact whole-ring tree when the logarithmic accuracy scale exceeds `N`.

The input is an explicitly supplied canonical decomposition. This file does not assert
canonicalization or periodicity transport for an arbitrary original tensor.

## Inherited local corrections

**Local fix (unweighted support and common mixed rate):** the polar factors used for the
approximation belong to the unweighted direct sum of the
normal blocks. They are not the polar factors of the weighted repeated tensor: the source's
block-positive-part formula does not hold for overlapping or repeated blocks. The common
exponential rate bounds both the individual transfer maps and all mixed maps. These are the
existing corrections recorded in `docs/paper-gaps/mswc24_measurement_preparation_scope.tex` and
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`; this theorem composes those corrected
estimates.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements", "Long-range MPS using measurements",
  and Supplemental Material, eqs. (S2)--(S4) and proof of Theorem 1.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators ComplexOrder InnerProductSpace

namespace MPSPreparation

/-- All-length double-logarithmic preparation for a periodic vector expressed in a finite
canonical family. The coefficients may be arbitrary complex functions of length, and may
vanish separately. The mixed-transfer assumption is explicit; no finite-block orthogonality
is needed. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpv_eq_sum
    {d D b : ℕ} (A : MPSTensor d D) {Dj : Fin b → ℕ}
    {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    (hmix : ∀ j j', j ≠ j' → ∀ μ, Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ →
      ‖μ‖ < 1) (β : ℕ → Fin b → ℂ)
    (hφ : ∀ (N : ℕ) [NeZero N] (x : Fin N → Fin d), mpv A x = ∑ j, β N j * mpv (Aj j) x) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N → mpvState A N ≠ 0 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧
        (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
        IsPreparedWithMeasurementRoundsInDepth T (fun x => ψ x) ∧
        1 - ‖⟪ψ, normalizedMPVState A N⟫_ℂ‖ ≤ ε := by
  classical
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · refine ⟨0, fun ε hε _ N _ _ h0 => ⟨_, 0, norm_normalizedMPVState h0, by simp, ?_, ?_⟩⟩
    · apply isPreparedWithMeasurementRoundsInDepth_of_isPreparedWithMeasurementsInDepth
      refine isPreparedWithMeasurementsInDepth_of_isPreparedInDepth
        (isPreparedInDepth_zero_of_le_one (by omega) _) fun h => ?_
      have h1 := norm_normalizedMPVState h0
      rw [show normalizedMPVState A N = 0 from by ext x; exact congrFun h x] at h1
      simp at h1
    · rw [inner_self_eq_norm_sq_to_K, norm_normalizedMPVState h0]
      norm_num [hε.le]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · refine ⟨0, fun ε _ _ N _ _ h0 => absurd ?_ h0⟩
    ext x
    rw [mpvState_apply, hφ N x]
    simp
  have : NeZero b := ⟨hb.ne'⟩
  have hd : 0 < d := by omega
  have hDj : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  -- The direct sum of the blocks with unit weights, on the bond dimension `D' = ∑ⱼ Dⱼ`.
  set D' := ∑ j, Dj j
  set ι' : (j : Fin b) → Fin (Dj j) → Fin D' := flatCoord Dj
  have hι' : ∀ j, Function.Injective (ι' j) := fun j => flatCoord_injective j
  have hdisj' : ∀ j j', j ≠ j' → ∀ a a', ι' j a ≠ ι' j' a' := fun j j' h a a' =>
    flatCoord_ne h a a'
  set AJ := MPSTensor.blockSum Aj ι' fun _ => 1
  set ω : Fin b → Fin D' × Fin D' → ℂ := fun j => embedPair (ι' j) (fixedPointPair (σ j))
  have hω : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0 := fun j j' => by
    split_ifs with h
    · subst h
      rw [inner_embedPair_self (hι' j), fixedPointPair_norm_sq (hσ j).posSemidef, htr j]
    · exact inner_embedPair_eq_zero_of_disjoint (hdisj' j j' h) _ _
  have hωS : ∀ j {M : ℕ} (c : Fin M → Fin D' × Fin D'), pairProductState (ω j) c ≠ 0 →
      ∀ k, c k ∈ blockPairs ι' := fun j M c hc k =>
    mem_blockPairs_of_pairProductState_embedPair_ne_zero j _ hc k
  -- A common rate.
  obtain ⟨t, ht0, ht1, hlam, hmixle⟩ :=
    exists_forall_eigenvalue_norm_le_of_mixed hN hA hDj hmix
  have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  -- The constants.
  obtain ⟨L₀, hL₀⟩ := exists_isInjectiveOn_blockTensor_blockSum hι' hdisj' hN hA hσ htr hfix
    (lam₂ := (t : ℂ)) (by rw [hnorm]; exact ht1) hlam hmixle
  obtain ⟨K, hK, herr⟩ := exists_one_sub_norm_inner_sum_blockIsometryState_le hι' hdisj' hN hA hσ
    htr hfix hlam hmixle (γ := 1 / 4) (by norm_num) (by norm_num)
  set r := -(1 / 4 * Real.log t) with hr
  have hr0 : 0 < r := by
    have := Real.log_neg ht0 ht1
    rw [hr]; linarith
  have hexp : ∀ q : ℕ, Real.exp (-(1 / 4) * q / correlationLength (t : ℂ)) =
      Real.exp (-(r * q)) := fun q => by
    congr 1
    rw [mul_div_right_comm, neg_div_correlationLength, hnorm, hr]
    ring
  apply exists_log_log_preparation_of_supported_block_approximation hd2 AJ (blockPairs ι') L₀
    hL₀ ω hω hωS (fun N => normalizedMPVState A N) (fun N => mpvState A N ≠ 0)
    (fun _ h0 => norm_normalizedMPVState h0) K r hK hr0
  · intro N _ h0
    have hβ : β N ≠ 0 := by
      intro hβ0
      apply h0
      ext x
      rw [mpvState_apply, hφ N x, PiLp.zero_apply]
      simp [hβ0]
    refine ⟨ghzAmplitude (β N), ghzAmplitude_norm_sq hβ, fun M _ ℓ hsum q hLq hℓq => ?_⟩
    have hinjℓ : ∀ k, IsInjectiveOn (blockTensor AJ (ℓ k)) (blockPairs ι' : Set _) :=
      fun k => hL₀ _ (hLq.trans (hℓq k))
    refine ⟨norm_sum_smul_blockIsometryState hι' hdisj' (fun j => (hσ j).posSemidef)
      htr (ghzAmplitude_norm_sq hβ) hsum hinjℓ, ?_⟩
    rw [← hexp]
    exact herr (β N) hβ M ℓ hsum q hℓq hinjℓ (mpvState A N)
      (fun x => by simpa only [mpvState_apply] using hφ N x)
  · intro N _ h0 hLN hsum
    obtain ⟨ω₁, hω₁, hω₁S, heq⟩ := exists_blockIsometryState_eq_smul hι' hdisj' hsum
      (hL₀ N hLN) (β N) (mpvState A N)
      (fun x => by simpa only [mpvState_apply] using hφ N x) h0
    exact ⟨ω₁, hω₁, hω₁S, heq⟩


/-- The canonical repeated-block form of eq. (S2), with arbitrary complex copy weights,
has an all-length double-logarithmic measurement preparation. Aggregate sector amplitudes
may vanish at individual lengths; only the total periodic vector must be nonzero. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_repeatedBlockSum_le_log_log
    {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ < 1) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N →
      mpvState (repeatedBlockSum Aj ι μ) N ≠ 0 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
        IsPreparedWithMeasurementRoundsInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) N⟫_ℂ‖ ≤ ε := by
  exact exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpv_eq_sum
    (repeatedBlockSum Aj ι μ) hN hA hσ htr hfix hmix (bntWeight μ)
    (fun N _ x => mpv_repeatedBlockSum hι hdisj μ (NeZero.ne N) x)

/-- The canonical repeated-block capstone stated directly for inequivalent normal blocks.
No separate mixed spectral hypothesis is needed. This covers all admissible lengths and
accuracies, finite-block overlaps, arbitrary complex phases, repetitions, and vanishing
individual sector amplitudes. Classical communication, measurement and onsite corrections
are free; nearest-neighbor unitary layers are counted, and no branch is postselected. -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_repeatedBlockSum_le_log_log_of_inequivalent
    {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    (hneq : ∀ j j', j ≠ j' → ∀ h : Dj j = Dj j',
      ¬ GaugePhaseEquiv (h ▸ Aj j) (Aj j')) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (N : ℕ) [NeZero N], 2 ≤ N →
      mpvState (repeatedBlockSum Aj ι μ) N ≠ 0 →
      ∃ (ψ : MPVSpace d N) (T : ℕ), ‖ψ‖ = 1 ∧ (T : ℝ) ≤ c * Real.log (Real.log (N / ε) + 1) ∧
        IsPreparedWithMeasurementRoundsInDepth T (fun s => ψ s) ∧
        1 - ‖⟪ψ, normalizedMPVState (repeatedBlockSum Aj ι μ) N⟫_ℂ‖ ≤ ε := by
  have hDj : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  exact exists_isPreparedWithMeasurementRoundsInDepth_repeatedBlockSum_le_log_log
    hι hdisj μ hN hA hσ htr hfix (fun j j' hj μ' hμ' =>
      mixedMap_eigenvalue_norm_lt_one_of_normal_inequivalent (Aj j) (Aj j')
        (hN j) (hN j') (hA j) (hA j') (hneq j j' hj) hμ')

end MPSPreparation
