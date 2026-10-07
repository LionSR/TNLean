/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.PeriodicPhysicalString
import TNLean.Spectral.MPVOverlapDecayRect

/-!
# Full-ring symmetry overlaps of periodic MPS

The source's `RL` is a complex overlap on a periodic ring whose entire length
is acted on by the twist. It is not the stationary-boundary block-twist
functional. The finite normalized expectation is an operator-trace ratio.
A virtual intertwiner makes that ratio exactly the length power of its phase
at every nonzero periodic length. Canonical spectral purity supplies eventual
nonvanishing. A twisted spectral radius below one gives limit zero.

Source: arXiv:0802.0447, displays `MPS`, `fixed`, `EU`, and `RL`, lines
131–160, 168–173, and 381–388. The complex limit in the last passage requires
the phase qualification made explicit below; the modulus has limit zero or one.

**Local fix (full-ring phase):** The complex limit in arXiv:0802.0447,
`RL`, lines 381–388, need not exist when the virtual symmetry has a nontrivial
peripheral phase. The exact finite expectation is `μ^L` at nonzero lengths;
its modulus and phase-adjusted value have the stated limits. The boundary
closure and phase qualifications are recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447,
  Lemma 1 and the periodic overlap in display `RL`.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace InnerProductSpace
open Filter

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The actual normalized full-ring expectation is the ratio of the twisted
and ordinary transfer-power operator traces. At a zero periodic vector both
sides use the existing zero-normalization convention.
Source: arXiv:0802.0447, `MPS`, `EU`, and `RL`. -/
theorem mpvExpectation_finKronecker_const_eq_trace_div
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ) (L : ℕ) :
    mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u) =
      LinearMap.trace ℂ Mat (twistedTransferIter A u L) /
        LinearMap.trace ℂ Mat (Kraus.transferMap A ^ L) := by
  rw [mpvExpectation_eq_div, inner_mpvState_toEuclideanLin,
    physicalObservableTransfer_finKronecker_const, inner_mpvState_self_eq_trace]

/-- Closing the virtual boundary takes the trace of the exact phased transfer
similarity. This identity is finite and needs neither purity nor normalization.
Source: arXiv:0802.0447, Lemma 1 and `RL`. -/
theorem trace_twistedTransferIter_eq_phase_mul_trace_transfer_pow
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Mat) (μ : ℂ) (hV : V * Vᴴ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) (L : ℕ) :
    LinearMap.trace ℂ Mat (twistedTransferIter A u L) =
      μ ^ L * LinearMap.trace ℂ Mat (Kraus.transferMap A ^ L) := by
  let F : Module.End ℂ Mat := LinearMap.mulLeft ℂ V
  let G : Module.End ℂ Mat := LinearMap.mulLeft ℂ Vᴴ
  have hGF : G * F = 1 := by
    apply LinearMap.ext
    intro X
    simp only [F, G, Module.End.mul_apply, LinearMap.mulLeft_apply,
      ← Matrix.mul_assoc, mul_eq_one_comm.mp hV, Matrix.one_mul,
      Module.End.one_apply]
  have hpow : twistedTransferIter A u L =
      μ ^ L • (F * Kraus.transferMap A ^ L * G) := by
    apply LinearMap.ext
    intro X
    exact twistedTransferIter_eq_phase_mul_transfer_pow A u V μ hV hInter X L
  rw [hpow, map_smul, smul_eq_mul, LinearMap.trace_mul_cycle, hGF, one_mul]

/-- At each nonzero periodic length, the full-ring normalized expectation is
exactly the intertwiner phase to that length. No thermodynamic limit is used.
Source: arXiv:0802.0447, Lemma 1 and `RL`. -/
theorem mpvExpectation_finKronecker_const_eq_phase_pow
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Mat) (μ : ℂ) (hV : V * Vᴴ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ))
    (L : ℕ) (hL : mpvState A L ≠ 0) :
    mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u) = μ ^ L := by
  have hden : LinearMap.trace ℂ Mat (Kraus.transferMap A ^ L) ≠ 0 := by
    rw [← inner_mpvState_self_eq_trace A L]
    exact inner_self_ne_zero.mpr hL
  rw [mpvExpectation_finKronecker_const_eq_trace_div,
    trace_twistedTransferIter_eq_phase_mul_trace_transfer_pow A u V μ hV hInter,
    mul_div_cancel_right₀ _ hden]

section PureCanonical

variable [NeZero D] (A : MPSTensor d D)
  (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
  (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
  (hNorm : Kraus.transferMap A 1 = 1)
  (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
    X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
    ev = 1 ∧ ∃ c : ℂ, X = c • 1)

include Λ hΛpos hΛtr hΛfix hNorm hPure

/-- Strictly contracting twisted spectrum makes the normalized full-ring
overlap tend to zero. Its denominator tends to one by canonical purity.
Source: arXiv:0802.0447, Lemma 1 and `RL`. -/
theorem pureCanonical_mpvExpectation_fullRing_tendsto_zero
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hSpect : spectralRadius ℂ
      (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) < 1) :
    Tendsto (fun L : ℕ =>
      mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u))
      atTop (nhds (0 : ℂ)) := by
  have hmix : spectralRadius ℂ (Module.End.toContinuousLinearMap Mat
      (Kraus.mixedMapLM A (twistedMixedCompanion A u))) < 1 := by
    simpa only [← twistedTransferMap_eq_mixedTransfer] using hSpect
  have hnum : Tendsto
      (fun L : ℕ => LinearMap.trace ℂ Mat (twistedTransferIter A u L))
      atTop (nhds (0 : ℂ)) := by
    simpa only [twistedTransferIter, twistedTransferMap_eq_mixedTransfer,
      trace_mixedMapLM_pow_eq_mpvOverlap] using
      mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one
        A (twistedMixedCompanion A u) hmix
  have hden := pureCanonical_mpvState_inner_self_tendsto_one
    A Λ hΛpos hΛtr hΛfix hNorm hPure
  have hlim := hnum.div hden (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [zero_div] at hlim
  apply hlim.congr'
  filter_upwards [] with L
  rw [mpvExpectation_eq_div, inner_mpvState_toEuclideanLin,
    physicalObservableTransfer_finKronecker_const]
  rfl

/-- Canonical purity makes the exact finite-length phase formula hold on an
eventual tail, without assuming that short periodic vectors are nonzero.
Source: arXiv:0802.0447, canonical purity, Lemma 1, and `RL`. -/
theorem pureCanonical_mpvExpectation_fullRing_eventually_eq_phase_pow
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ) (hV : V * Vᴴ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    ∀ᶠ L : ℕ in atTop,
      mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u) = μ ^ L := by
  filter_upwards [pureCanonical_eventually_mpvState_ne_zero
    A Λ hΛpos hΛtr hΛfix hNorm hPure] with L hL
  exact mpvExpectation_finKronecker_const_eq_phase_pow A u V μ hV hInter L hL

/-- In the symmetry branch the full-ring modulus tends to one, independently
of the peripheral phase. Source: arXiv:0802.0447, Lemma 1 and `RL`. -/
theorem pureCanonical_mpvExpectation_fullRing_norm_tendsto_one
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    Tendsto (fun L : ℕ =>
      ‖mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u)‖)
      atTop (nhds (1 : ℝ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [pureCanonical_mpvExpectation_fullRing_eventually_eq_phase_pow
    A Λ hΛpos hΛtr hΛfix hNorm hPure u V μ hV hInter] with L hL
  simp [hL, norm_pow, hμ]

/-- Removing the peripheral phase gives limit one, and is eventually exactly
one. Source: arXiv:0802.0447, Lemma 1 and `RL`. -/
theorem pureCanonical_mpvExpectation_fullRing_phase_adjusted_tendsto_one
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    Tendsto (fun L : ℕ => (μ ^ L)⁻¹ *
      mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u))
      atTop (nhds (1 : ℂ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [pureCanonical_mpvExpectation_fullRing_eventually_eq_phase_pow
    A Λ hΛpos hΛtr hΛfix hNorm hPure u V μ hV hInter] with L hL
  simp [hL, pow_ne_zero L (Complex.ne_zero_of_norm_eq_one hμ)]

/-- A nontrivial peripheral phase prevents any complex full-ring limit. The
conclusion concerns actual normalized periodic expectations, not a fixed-support
thermodynamic observable. Source: arXiv:0802.0447, `RL`, with its phase retained. -/
theorem pureCanonical_mpvExpectation_fullRing_not_tendsto
    (u : Matrix (Fin d) (Fin d) ℂ) (V : Mat) (μ : ℂ)
    (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1) (hμne : μ ≠ 1)
    (hInter : ∀ i, ∑ j, u i j • A j = μ • (V * A i * Vᴴ)) :
    ¬ ∃ z : ℂ, Tendsto (fun L : ℕ =>
      mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u)) atTop (nhds z) := by
  rintro ⟨z, hz⟩
  have hpow : Tendsto (fun L : ℕ => μ ^ L) atTop (nhds z) :=
    hz.congr' (pureCanonical_mpvExpectation_fullRing_eventually_eq_phase_pow
      A Λ hΛpos hΛtr hΛfix hNorm hPure u V μ hV hInter)
  have hznorm : ‖z‖ = 1 := tendsto_nhds_unique hpow.norm
    (by simpa only [norm_pow, hμ, one_pow] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)))
  have hshift : Tendsto (fun L : ℕ => μ ^ (L + 1)) atTop (nhds z) :=
    hpow.comp (Filter.tendsto_add_atTop_nat 1)
  have hmul : Tendsto (fun L : ℕ => μ ^ (L + 1)) atTop (nhds (z * μ)) := by
    simpa only [pow_succ] using hpow.mul_const μ
  have hzμ : z * μ = z * 1 := by
    simpa only [mul_one] using tendsto_nhds_unique hmul hshift
  exact hμne (mul_left_cancel₀ (Complex.ne_zero_of_norm_eq_one hznorm) hzμ)

/-- The full-ring overlap has limiting modulus one exactly in the unit-radius
branch, and otherwise its complex value tends to zero. This is the fixed-unitary
spectral dichotomy relevant to `RL`; no Hamiltonian-gap implication is asserted.
Source: arXiv:0802.0447, Lemma 1 and `RL`. -/
theorem pureCanonical_mpvExpectation_fullRing_dichotomy
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u * uᴴ = 1) :
    (spectralRadius ℂ
        (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) = 1 ∧
      Tendsto (fun L : ℕ =>
        ‖mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u)‖)
        atTop (nhds (1 : ℝ))) ∨
    (spectralRadius ℂ
        (Module.End.toContinuousLinearMap Mat (twistedTransferMap A u)) < 1 ∧
      Tendsto (fun L : ℕ =>
        mpvExpectation A L (Matrix.finKronecker fun _ : Fin L => u))
        atTop (nhds (0 : ℂ))) := by
  obtain ⟨hIrr, _⟩ := pureCanonical_isIrreducibleMap_and_isPrimitive
    A Λ hΛpos hΛfix hNorm hPure
  have hle := twistedTransfer_spectralRadius_le_one_of_irreducible A hIrr u hu hNorm
  rcases eq_or_lt_of_le hle with hEq | hLt
  · obtain ⟨V, μ, hV, hμ, hInter⟩ :=
      (twistedTransfer_spectralRadius_eq_one_iff_intertwiner A hIrr u hu hNorm).mp hEq
    exact Or.inl ⟨hEq, pureCanonical_mpvExpectation_fullRing_norm_tendsto_one
      A Λ hΛpos hΛtr hΛfix hNorm hPure u V μ hV hμ hInter⟩
  · exact Or.inr ⟨hLt, pureCanonical_mpvExpectation_fullRing_tendsto_zero
      A Λ hΛpos hΛtr hΛfix hNorm hPure u hLt⟩

end PureCanonical
end MPSTensor
