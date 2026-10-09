/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.ReplicaTransport.EntropyGain
import QICLean.Analysis.Transport.ErrorFourier
import TNLean.PEPS.AreaLaw.Scan.RegionalMoveEntropy

/-!
# Entropy integrals in the actual old transported state

For each history, all conditional-choice symbols are integrated against its
one old leaf state. The coherent integral and the Fourier integral retain
their actual definitions; classical history and choice weights are not
substituted for either measure. Continuity gives integrability through the
coherent-average trace identity and the existing transported trace estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, displays `transport:states` and `transport:entropy-gain`,
lines 390–412, at `openai/math@adc7f124`.
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix MeasureTheory

noncomputable section

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Positive coherent density preserves a pointwise inequality of continuous
symbols. No comparison of the density matrices is asserted. -/
theorem realCoherentIntegral_mono (k : ℕ) (a : Ω)
    {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hρ : ρ.PosSemidef)
    {f g : (Ω → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, f θ ≤ g θ) :
    realCoherentIntegral k a ρ f ≤ realCoherentIntegral k a ρ g := by
  unfold realCoherentIntegral
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply integral_mono (integrable_realCoherentIntegral_integrand k a ρ hf)
    (integrable_realCoherentIntegral_integrand k a ρ hg)
  intro U
  apply mul_le_mul_of_nonneg_right (hfg _) ?_
  rw [coherentProj, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  exact (Complex.nonneg_iff.mp (hρ.dotProduct_mulVec_nonneg _)).1

/-- Finite continuous sums pass through the same coherent integral. -/
theorem realCoherentIntegral_sum (k : ℕ) (a : Ω)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → (Ω → ℂ) → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    realCoherentIntegral k a ρ (fun θ => ∑ i ∈ s, f i θ) =
      ∑ i ∈ s, realCoherentIntegral k a ρ (f i) := by
  unfold realCoherentIntegral
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i hi => integrable_realCoherentIntegral_integrand k a ρ (hf i hi),
    Finset.mul_sum]

/-- Scalar multiplication passes through the same coherent integral. -/
theorem realCoherentIntegral_const_mul (k : ℕ) (a : Ω)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (c : ℝ) (f : (Ω → ℂ) → ℝ) :
    realCoherentIntegral k a ρ (fun θ => c * f θ) = c * realCoherentIntegral k a ρ f := by
  unfold realCoherentIntegral
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

namespace ReplicaTransport.TransportData

variable {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
variable {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)]
variable (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]

/-- The Fourier and coherent integral at the terminal old leaf of one history.
The old state is independent of the conditional choice in the symbol. -/
def oldFourierCoherentIntegral (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    (f : (SiteConfig n → ℂ) → ℝ) : ℝ :=
  ∫ u, Matrix.Transport.fourierWeight u *
    realCoherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) f

/-- Continuous symbols are Fourier integrable in the actual old state. -/
theorem integrable_oldFourierCoherentIntegral (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    Integrable fun u => Matrix.Transport.fourierWeight u *
      realCoherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) f := by
  refine (D.integrable_fourierWeight_mul_trace_state t k pre p ⟨h, none⟩
    (coherentAverage k (base n) f)).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [trace_mul_coherentAverage k (base n) hf]

/-- Pointwise symbol inequalities survive both integrals in the same old state. -/
theorem oldFourierCoherentIntegral_mono (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {f g : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, f θ ≤ g θ) :
    D.oldFourierCoherentIntegral n t k pre p h f ≤
      D.oldFourierCoherentIntegral n t k pre p h g := by
  apply integral_mono (D.integrable_oldFourierCoherentIntegral n t k pre p h hf)
    (D.integrable_oldFourierCoherentIntegral n t k pre p h hg)
  intro u
  exact mul_le_mul_of_nonneg_left
    (realCoherentIntegral_mono k (base n) (D.posSemidef_state hD ht hcomm pre p _ u)
      hf hg hfg) (Real.sinhRatioDensity_pos (by norm_num) u).le

/-- A nonnegative continuous symbol has nonnegative integral in the old state. -/
theorem oldFourierCoherentIntegral_nonneg (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) (hf0 : ∀ θ, 0 ≤ f θ) :
    0 ≤ D.oldFourierCoherentIntegral n t k pre p h f := by
  have hmono := D.oldFourierCoherentIntegral_mono n hD ht hcomm pre p h
    continuous_const hf hf0
  simpa only [oldFourierCoherentIntegral, realCoherentIntegral, zero_mul,
    integral_zero, mul_zero] using hmono

/-- Finite sums of continuous symbols retain one common old state. -/
theorem oldFourierCoherentIntegral_sum (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {ι : Type*} (s : Finset ι) (f : ι → (SiteConfig n → ℂ) → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    D.oldFourierCoherentIntegral n t k pre p h (fun θ => ∑ i ∈ s, f i θ) =
      ∑ i ∈ s, D.oldFourierCoherentIntegral n t k pre p h (f i) := by
  unfold oldFourierCoherentIntegral
  simp_rw [realCoherentIntegral_sum k (base n) _ s f hf, Finset.mul_sum]
  exact integral_finsetSum _ fun i hi =>
    D.integrable_oldFourierCoherentIntegral n t k pre p h (hf i hi)

/-- Scalar multiplication retains one common old state. -/
theorem oldFourierCoherentIntegral_const_mul (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    (c : ℝ) (f : (SiteConfig n → ℂ) → ℝ) :
    D.oldFourierCoherentIntegral n t k pre p h (fun θ => c * f θ) =
      c * D.oldFourierCoherentIntegral n t k pre p h f := by
  unfold oldFourierCoherentIntegral
  simp_rw [realCoherentIntegral_const_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

/-- For a nonzero symmetric pre-vector and an interior interpolation parameter,
the old-state Fourier-coherent integral has mass one half. -/
theorem oldFourierCoherentIntegral_one (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hsym : pre ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre ≠ 0)
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (h : H) :
    D.oldFourierCoherentIntegral n t k pre p h (fun _ => 1) = 1 / 2 := by
  have hmass (u : ℝ) :
      realCoherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) (fun _ => 1) = 1 :=
    realCoherentIntegral_one (base n) (D.trace_state hD ht hcomm hpre hp _ u)
      (D.symProj_mul_state hD ht hcomm hsym p _ u)
  simp only [oldFourierCoherentIntegral, hmass, mul_one]
  exact Matrix.Transport.integral_fourierWeight

variable [∀ h, Fintype (C h)]

/-- The conditional-choice entropy symbol, with one common old partition
per history and band. It contains no choice-dependent transported state. -/
def choiceEntropySymbol (h : H) (θ : SiteConfig n → ℂ) : ℝ :=
  ∑ g, ∑ c, (D.choiceTree h).weight c *
    moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ)

/-- The actual finite choice entropy symbol is continuous. -/
theorem continuous_choiceEntropySymbol (h : H) : Continuous (D.choiceEntropySymbol n h) := by
  unfold choiceEntropySymbol
  exact continuous_finsetSum _ fun g _ => continuous_finsetSum _ fun c _ =>
    continuous_const.mul (continuous_moveEta (D.old h g) (D.move h c g))

/-- Admissible old partitions and valid moves make the choice symbol nonnegative. -/
theorem choiceEntropySymbol_nonneg (hD : D.IsAdmissible) (h : H)
    (θ : SiteConfig n → ℂ) : 0 ≤ D.choiceEntropySymbol n h θ := by
  apply Finset.sum_nonneg
  intro g _
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (hD.choiceWeight_pos h c).le
    (moveEta_nonneg n _ (hD.old_isPartition h g) _ (hD.move_isValid h c g) _)

variable [Fintype H]

/-- The existing entropy gain is the history average of the actual old-state
integrals. The history weight has no terminal factor `1 - p`. -/
theorem entropyGain_eq_sum_oldFourierCoherentIntegral (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    D.entropyGain n t k pre p =
      ∑ h, D.histTree.weight h *
        D.oldFourierCoherentIntegral n t k pre p h (D.choiceEntropySymbol n h) := by
  unfold entropyGain
  apply Finset.sum_congr rfl
  intro h _
  have hcont (g : Fin K) : Continuous fun θ : SiteConfig n → ℂ =>
      ∑ c, (D.choiceTree h).weight c *
        moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) :=
    continuous_finsetSum _ fun c _ =>
      continuous_const.mul (continuous_moveEta (D.old h g) (D.move h c g))
  simp only [choiceEntropySymbol]
  rw [D.oldFourierCoherentIntegral_sum n t k pre p h Finset.univ _ (fun g _ => hcont g)]
  simp only [Finset.mul_sum, oldFourierCoherentIntegral]

end ReplicaTransport.TransportData
end TensorPower
