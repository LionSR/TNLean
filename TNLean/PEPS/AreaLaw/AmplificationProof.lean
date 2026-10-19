/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AmplificationCutClearance
import TNLean.PEPS.AreaLaw.AmplificationProofSteps
import TNLean.PEPS.AreaLaw.Amplification.ConstraintWordLists
import TNLean.PEPS.AreaLaw.Amplification.ConstraintWordTruncation
import TNLean.PEPS.AreaLaw.Amplification.LatticeChannelSpatialOmission
import TNLean.PEPS.AreaLaw.Amplification.LatticeExcitedDecay
import TNLean.PEPS.AreaLaw.Amplification.LatticeAncillaSites
import TNLean.PEPS.AreaLaw.Amplification.SupportedPolarCorrection
import TNLean.PEPS.AreaLaw.Amplification.RadiusBound
import TNLean.PEPS.AreaLaw.Amplification.EntropyComparison
import TNLean.PEPS.AreaLaw.Geometry.TemplateRows

/-!
# Proposition 10.2: amplification

This module proves Proposition 10.2 of the two-dimensional area-law manuscript
(`prop:amplification`) for every gapped finite-domain Hamiltonian: under the collar
hypotheses, at every large scale there is a radius `r ≤ C_M n^((1-ε)/α)` such that every
part of the target `X = A ∩ T` has mutual information at most `C_M n^(-M)` with every
physical set avoiding the graph neighborhood `N_{2r}(S₀)`, and the neighborhood lies in the
cut when the target is far from the cut endpoints.

The proof follows the source. At the scale `n`, the typical projections of `X`, `Y` and `S₀`
give the restoring operator `R₀` and the column operator `B₀` on the physical system and two
ancillary copies `s', e'` of `X`, with `‖R₀‖, ‖B₀‖ ≤ M₀ = e^{(𝓘+3w)/2}`. The clocks run for
the time `t_*` and the radius `r` of `eq:amplification-time-choice`. On one clock
realization, the excited-state decay bounds the excited component of `R₀ φ`, the omission
estimate of the local-products lemma, applied through the column identity `R₀ φ = B₀ (Ω ⊗ ξ)`,
bounds the omitted events, and the truncation estimate bounds the radius truncation. Markov's
inequality and a union bound select a realization on which all three are at most `n^{-K}`.
The polar correction of `L' R₀` then gives a unitary acting on `s'` and `N_{2r}(S₀)` that
moves `φ` to within `9 n^{-K/2}` of the restored vector `η`. On the sites enlarged by the two
copies, `φ` carries the original reduction of the target on `e'`, and `η` has no mutual
information between `e'` and any physical set. Continuity of mutual information then gives
the output bound, with `K = 4(M + 2)`.

## Main statements

* `TNLean.PEPS.AreaLaw.amplificationBound`: Proposition 10.2.
* `TNLean.PEPS.AreaLaw.amplificationBound_of_locality`: Proposition 10.2 with the constant
  `amplificationConstant` and the threshold `amplificationThreshold`, explicit in
  `q, R, J, Δ, C₀, M` and the filter-locality constants `C₃, c₃` of the positive constraints.
* `TNLean.PEPS.AreaLaw.uniformAreaLaw_of_collar_twoFamilies`: the uniform area law from
  Propositions 9.6 and 11.2 alone, taken as hypotheses. Both are proved, and
  `uniformAreaLaw` is the unconditional Theorem 1.1.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 261–296 (statement)
  and 298–576 (proof); Lemma 10.1 (`lem:amplification-local-products`), lines 42–72, and
  `eq:amplification-excited-decay`, lines 237–253.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix MeasureTheory SpectralFilter QuantumCircuit
open scoped Kronecker NNReal ComplexOrder MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- The square root of `(n^K)⁻¹` is `n^(-K/2)`. -/
private theorem sqrt_inv_pow_eq_rpow (n K : ℕ) :
    √(((n : ℝ) ^ K)⁻¹) = (n : ℝ) ^ (-(K : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg (Nat.cast_nonneg n),
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  ring_nf

/-- The square root of `n^(-2K)` is `(n^K)⁻¹`. -/
private theorem sqrt_rpow_neg_two_mul' (n K : ℕ) :
    √((n : ℝ) ^ (-(2 * K : ℝ))) = ((n : ℝ) ^ K)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n),
    show (2 * K : ℝ) = ((2 * K : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul',
    ← inv_pow, Real.sqrt_sq (by positivity)]

/-- A unit blank vector on a nonempty finite set. -/
private theorem norm_toLp_single_eq_one {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ‖WithLp.toLp 2 (fun x : α => if x = a then (1 : ℂ) else 0)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The final scale estimate: `4ε + √(14ε + 9ε²) ≤ 9 √ε` for `0 ≤ ε ≤ 1`. -/
private theorem unitary_error_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (3 * ε + ε) + √(2 * (3 * ε + ε) + 6 * ε + 9 * ε ^ 2) ≤ 9 * √ε := by
  have hs : ε ≤ √ε := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq : √(2 * (3 * ε + ε) + 6 * ε + 9 * ε ^ 2) ≤ 5 * √ε := by
    rw [show (5 : ℝ) * √ε = √(25 * ε) by
      rw [Real.sqrt_mul (by norm_num), show √(25 : ℝ) = 5 by
        rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

/-- The spectral gap `g_a = Δ / c_*` of the positive-constraint Hamiltonian `∑ᵢ kᵢ` at the
power `p = 10⁶`, with `c_* = positiveNormalization p (Δ / 2) J = max 1 (J (‖f_{p,Δ/2}‖₁ + 1))`.
It is linear in `Δ` through the numerator and decays like `1 / J` once `J (‖f‖₁ + 1) ≥ 1`; the
filter norm `‖f_{p,Δ/2}‖₁` carries the remaining `Δ` dependence. Source:
`eq:amplification-excited-decay`, `09-amplification.tex`, lines 237–253. -/
noncomputable def amplificationGap (J Δ : ℝ) : ℝ :=
  Δ / positiveNormalization Exponents.amplificationPower (Δ / 2) J

/-- The common decay rate `c = min(c_t, γ)` of the truncation and omission estimates, with
`c_t = c₃ / 2` and `γ = latticeOmissionExponent c₃ p` at `p = 10⁶`. Here `c₃` is the
filter-locality rate of the positive constraints, which depends on `J` and `Δ` (through the
localization velocity `localizationVelocity R v_R (μ_R J)` and the filter width `Δ / 2`).
Source: `09-amplification.tex`, lines 42–72 and 466–476. -/
noncomputable def amplificationDecayRate (c₃ : ℝ) : ℝ :=
  min (c₃ / 2) (latticeOmissionExponent c₃ Exponents.amplificationPower)

/-- The common prefactor `C_g = C_t + A_o` of the truncation and omission estimates, with
`C_t = constraintWordTruncationPrefactor μ_R C₃ = 2 μ_R √C₃`, `μ_R = 2^{2R(R+1)}`, and
`A_o = latticeOmissionPrefactor R C₃ c₃ p` at `p = 10⁶`. Source: `09-amplification.tex`,
lines 42–72 and 466–476. -/
noncomputable def amplificationPrefactor (R : ℕ) (C₃ c₃ : ℝ) : ℝ :=
  constraintWordTruncationPrefactor ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) C₃ +
    latticeOmissionPrefactor R C₃ c₃ Exponents.amplificationPower

/-- The constant `C₂` of Proposition 10.2 at the integer `M`, for the filter-locality constants
`C₃, c₃` of the positive constraints:
`C₂ = max(C_rad, 8 √9 (1 + C₀ log q))`, where `K = 4 (M + 2)`, `α = p / (p + 1)` with
`p = 10⁶`, `ε = 10⁻⁵`, `g_a = amplificationGap J Δ`, `c = amplificationDecayRate c₃`,
`v_o = latticeOmissionRate R C₃ c₃ p`, `C' = amplificationRadiusConstant g_a v_o c
= (g_a / 2 + 2 v_o + 12) / c` and `C_rad = amplificationRadiusCoefficient g_a C' C₀ α ε K`.
The first term bounds the radius (`eq:amplification-radius`); through the factor `6 / g_a` of
the clock time it behaves like `g_a^{-1/α}` as `g_a → 0`, so it carries the `J / Δ` dependence
of the gap, together with the `J`- and `Δ`-dependence of `v_o` and `c` through `C₃, c₃`. The
second term bounds the output information (`eq:amplification-output`) and is independent of
`J` and `Δ`. Source: `09-amplification.tex`, lines 453–499 and 541–569. -/
noncomputable def amplificationConstant (q R : ℕ) (J Δ C₀ C₃ c₃ : ℝ) (M : ℕ) : ℝ :=
  max (amplificationRadiusCoefficient (amplificationGap J Δ)
      (amplificationRadiusConstant (amplificationGap J Δ)
        (latticeOmissionRate R C₃ c₃ Exponents.amplificationPower) (amplificationDecayRate c₃))
      C₀ (kernelExponent Exponents.amplificationPower) (Exponents.amplificationEpsilon : ℝ)
      (4 * (M + 2)))
    (8 * √9 * (1 + C₀ * Real.log q))

/-- The threshold `N₂ = max(N_g, N_t)` of the radius and output bounds of Proposition 10.2 at
the integer `M`, for the filter-locality constants `C₃, c₃`: `N_g = goodRealizationThreshold
C_g C₀ c α` selects a good clock realization, with `C_g = amplificationPrefactor R C₃ c₃` and
`c = amplificationDecayRate c₃`, and `N_t = typicalProjectionThreshold q R J Δ C₀ K`,
`K = 4 (M + 2)`, makes the three typical projections fail with probability at most `n^{-2K}`.
The threshold `N_t` depends on `J / Δ` through the rate `typicalFailureRate`, which carries
the factor `(1 + J / Δ)^{-1/2}`; `N_g` depends on `J` and `Δ` only through `C₃, c₃`. The cut
clearance of Proposition 10.2 needs in addition `n ≥ Exponents.collarRadiusThreshold C₂ 1`.
Source: `09-amplification.tex`, lines 304–322 and 453–499. -/
noncomputable def amplificationThreshold (q R : ℕ) (J Δ C₀ C₃ c₃ : ℝ) (M : ℕ) : ℕ :=
  max (goodRealizationThreshold (amplificationPrefactor R C₃ c₃) C₀ (amplificationDecayRate c₃)
      (kernelExponent Exponents.amplificationPower))
    (typicalProjectionThreshold q R J Δ C₀ (4 * (M + 2)))

/-- The constant of Proposition 10.2 is nonnegative. -/
theorem amplificationConstant_nonneg (q R : ℕ) (J Δ : ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (C₃ c₃ : ℝ)
    (M : ℕ) : 0 ≤ amplificationConstant q R J Δ C₀ C₃ c₃ M :=
  le_max_of_le_right (by have := Real.log_natCast_nonneg q; positivity)

/-- **Proposition 10.2 with named constants** (`prop:amplification`, `09-amplification.tex`
lines 261–296, proof at lines 298–576), for the Hamiltonian parameters `q, R, J`, a gap
`Δ > 0`, `C₀ > 0` and an integer `M`. Let `C₃ ≥ 0`, `c₃ > 0` be the constants of the
filter-locality tail of the positive constraints, in the form of
`latticePositiveConstraints_of_locality`. Then the conclusion of `AmplificationBound` holds
with the constant `C₂ = amplificationConstant q R J Δ C₀ C₃ c₃ M` and the threshold
`max N₂ (Exponents.collarRadiusThreshold C₂ 1)`, `N₂ = amplificationThreshold q R J Δ C₀ C₃ c₃
M`. At the named constants `C₃ = latticePositiveConstraintConst R J Δ p` and
`c₃ = latticePositiveConstraintRate R J Δ p`, `p = 10⁶`, this is
`amplificationBound_explicit`. -/
theorem amplificationBound_of_locality {q R : ℕ} {J Δ C₀ C₃ c₃ : ℝ} (hΔ : 0 < Δ)
    (hC₀ : 0 < C₀) (hC₃ : 0 ≤ C₃) (hc₃ : 0 < c₃)
    (htail : ∀ {n : Type} [Fintype n] [DecidableEq n]
      {H : Matrix n n ℂ} {Ω : EuclideanSpace ℂ n} {h : Matrix n n ℂ},
      H.IsHermitian → ‖Ω‖ = 1 → h.IsHermitian → ‖h‖ ≤ J →
      ∀ (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ), (∀ X, ‖L X‖ ≤ ‖X‖) → L 1 = 1 →
      (∀ X, X.IsHermitian → (L X).IsHermitian) →
      L (CFC.abs (L (centeredFilter Exponents.amplificationPower (Δ / 2) H Ω h))) =
        CFC.abs (L (centeredFilter Exponents.amplificationPower (Δ / 2) H Ω h)) →
      ∀ {l : ℝ}, 0 ≤ l →
      (∀ t : ℝ, ‖Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t) -
          L (Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t))‖ ≤
        ‖h‖ * min 2 (localizationPrefactor R 2 2 * Real.exp (localizationVelocity R
          (1 + 2 * R * (R + 1)) (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J) * |t| -
            1 / 2 * l))) →
      ‖positiveConstraint (positiveNormalization Exponents.amplificationPower (Δ / 2) J)
          (centeredFilter Exponents.amplificationPower (Δ / 2) H Ω h) -
          L (positiveConstraint (positiveNormalization Exponents.amplificationPower (Δ / 2) J)
            (centeredFilter Exponents.amplificationPower (Δ / 2) H Ω h))‖ ≤
        C₃ * Real.exp (-(c₃ * l ^ kernelExponent Exponents.amplificationPower)))
    (M : ℕ) :
    ∀ n : ℕ, 2 ≤ n → max (amplificationThreshold q R J Δ C₀ C₃ c₃ M)
        (Exponents.collarRadiusThreshold (amplificationConstant q R J Δ C₀ C₃ c₃ M) 1) ≤ n →
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
        ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (T : Finset (ℤ × ℤ)),
            ((A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
              C₀ * (n : ℝ) ^ 2 →
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
            ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
              C₀ * n →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                (A.filter fun x ↦ x.val ∈ T)
                (A.filter fun x ↦ x.val ∈ ambientDilation T
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
              C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) →
            ∃ r : ℕ, (r : ℝ) ≤ amplificationConstant q R J Δ C₀ C₃ c₃ M *
                (n : ℝ) ^ (Exponents.radiusExponent : ℝ) ∧
              (∀ X ⊆ A.filter (fun x ↦ x.val ∈ T), ∀ Jset : Finset (Site Λ),
                Disjoint Jset (graphNeighborhood Λ (2 * r)
                  (A.filter fun x ↦ x.val ∈ ambientDilation T
                    ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)) →
                FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X Jset ≤
                  amplificationConstant q R J Δ C₀ C₃ c₃ M * ((n : ℝ) ^ M)⁻¹) ∧
              ((∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
                  (⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ : ℝ) +
                      (n : ℝ) ^ (Exponents.beta : ℝ) <
                    (Scan.ambientSupDistance t z : ℝ)) →
                graphNeighborhood Λ (2 * r)
                    (A.filter fun x ↦ x.val ∈ ambientDilation T
                      ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) ⊆ A) := by
  intro n hn2 hnN Λ h E₀ Ω hgs A T hcard hXcut hYcut hScut hI
  have hC₂0 := amplificationConstant_nonneg q R J Δ hC₀.le C₃ c₃ M
  have hcol := fun r hr ↦ graphNeighborhood_collar_subset_of_threshold_le _
    ((le_max_right _ _).trans hnN) r hr Λ A T
  replace hnN : amplificationThreshold q R J Δ C₀ C₃ c₃ M ≤ n := (le_max_left _ _).trans hnN
  by_cases hdeg : q = 0 ∨ J < 0
  · -- With no local states, or with a negative interaction bound, a gapped ground state
    -- exists only on the empty domain, where the target is empty.
    have h0 : ((0 : ℕ) : ℝ) ≤ amplificationConstant q R J Δ C₀ C₃ c₃ M *
        (n : ℝ) ^ (Exponents.radiusExponent : ℝ) := by
      rw [Nat.cast_zero]
      exact mul_nonneg hC₂0 (by positivity)
    refine ⟨0, h0, ?_, hcol 0 h0⟩
    intro X' _ Jset _
    obtain ⟨hΩ, -, -⟩ := Matrix.isGappedGroundState_iff.mp hgs
    have hempty : IsEmpty (Site Λ) := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨v⟩ := hne
      rcases hdeg with hq0 | hJneg
      · subst hq0
        have : IsEmpty (Configuration Λ 0) := ⟨fun c => (c v).elim0⟩
        have hz : Ω = 0 := by
          ext c
          exact (IsEmpty.false c).elim
        rw [hz, norm_zero] at hΩ
        exact zero_ne_one hΩ
      · have hadm : IsAdmissibleSupport Λ R {v} := ⟨Finset.singleton_nonempty v,
          fun x hx y hy => by
            rw [Finset.mem_singleton] at hx hy
            subst hx hy
            exact ⟨SimpleGraph.Walk.nil, Nat.zero_le _⟩⟩
        linarith [h.norm_le ⟨{v}, hadm⟩, norm_nonneg (h.term ⟨{v}, hadm⟩)]
    rw [Finset.eq_empty_of_isEmpty X']
    calc _ = (0 : ℝ) := by
          simp [FiniteProduct.mutualInformation, FiniteProduct.entropy_empty _ Ω hΩ]
      _ ≤ _ := mul_nonneg hC₂0 (by positivity)
  push Not at hdeg
  obtain ⟨hq0, hJ⟩ := hdeg
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have : NeZero q := ⟨hq0⟩
  have hq : 1 ≤ q := hqpos
  -- The fixed exponent `α = p / (p + 1)` and the integer `K = 4 (M + 2)`.
  set pw := Exponents.amplificationPower with hpwdef
  have hpw : 1 ≤ pw := by norm_num [hpwdef, Exponents.amplificationPower]
  set α := kernelExponent pw with hαdef
  have hα : 0 < α := kernelExponent_pos hpw
  set K := 4 * (M + 2) with hKdef
  have hK1 : 1 ≤ K := by omega
  -- Constants of the local-products lemma, the gap and the scales.
  have hμ : (0 : ℝ) ≤ ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  set Ct := constraintWordTruncationPrefactor ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) C₃
    with hCtdef
  have hCt : 0 ≤ Ct := constraintWordTruncationPrefactor_nonneg hμ C₃
  set ct := c₃ / 2 with hctdef
  have hct : 0 < ct := half_pos hc₃
  set Ao := latticeOmissionPrefactor R C₃ c₃ pw with hAodef
  have hAo : 0 ≤ Ao := channelOmissionPrefactor_nonneg hμ C₃ 2 c₃ _
  set vo := latticeOmissionRate R C₃ c₃ pw with hvodef
  have hvo : 0 < vo := channelOmissionRate_pos hμ C₃ 2 c₃ _
  set γ := latticeOmissionExponent c₃ pw with hγdef
  have hγ : 0 < γ := channelOmissionExponent_pos hc₃ _
  set cs := positiveNormalization pw (Δ / 2) J with hcsdef
  have hcs : 0 < cs := positiveNormalization_pos pw _ J
  set g := Δ / cs with hgdef
  have hg : 0 < g := div_pos hΔ hcs
  set c := min ct γ with hcdef
  have hc : 0 < c := lt_min hct hγ
  set Cg := Ct + Ao with hCgdef
  have hCg : 0 ≤ Cg := add_nonneg hCt hAo
  set C' := amplificationRadiusConstant g vo c with hC'def
  have hC' : 0 ≤ C' := by rw [hC'def, amplificationRadiusConstant]; positivity
  set C₂ := C₀ * Real.log q with hC₂def
  have hC₂ : 0 ≤ C₂ := mul_nonneg hC₀.le (Real.log_nonneg (by exact_mod_cast hq))
  have hNg : goodRealizationThreshold Cg C₀ c α ≤ n := (le_max_left _ _).trans hnN
  have hNt : typicalProjectionThreshold q R J Δ C₀ K ≤ n := (le_max_right _ _).trans hnN
  have hC₂eq : amplificationConstant q R J Δ C₀ C₃ c₃ M =
      max (amplificationRadiusCoefficient g C' C₀ α (Exponents.amplificationEpsilon : ℝ) K)
        (8 * √9 * (1 + C₂)) := rfl
  rw [hC₂eq]
  obtain ⟨hΩ, -, -⟩ := Matrix.isGappedGroundState_iff.mp hgs
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  -- The regions of Proposition 10.2.
  set L := ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ with hLdef
  set X := A.filter fun x ↦ x.val ∈ T with hXdef
  set S₀ := A.filter fun x ↦ x.val ∈ ambientDilation T L with hS₀def
  set Y := S₀ \ X with hYdef
  have hXS : X ⊆ S₀ := by
    intro x hx
    simp only [hXdef, hS₀def, Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, mem_ambientDilation_iff.mpr ⟨x.val, hx.2, ?_, ?_, ?_, ?_⟩⟩ <;> omega
  have hXY : Disjoint X Y := Finset.disjoint_sdiff
  have hXYS : X ∪ Y = S₀ := Finset.union_sdiff_of_subset hXS
  -- The scales `w = n^{3/5}`, `t_*` and `r`.
  set w : ℝ := (n : ℝ) ^ ((3 : ℝ) / 5) with hwdef
  have hw0 : 0 ≤ w := Real.rpow_nonneg hn0.le _
  set I := FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X (X ∪ Y)ᶜ with hIdef
  have hII : I ≤ C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
    rw [hIdef, hXYS]
    exact hI
  have hI0 : 0 ≤ I := FiniteProduct.mutualInformation_nonneg _ Ω hΩ _ _
    (disjoint_compl_right.mono_left Finset.subset_union_left)
  set t : ℝ := amplificationTime g I w K n with htdef
  have hKlog : 0 ≤ (K : ℝ) * Real.log n :=
    mul_nonneg (Nat.cast_nonneg K) (Real.log_nonneg (by exact_mod_cast hn1))
  have ht0 : 0 ≤ t :=
    mul_nonneg (div_nonneg (by norm_num) hg.le) (add_nonneg (add_nonneg hI0 hw0) hKlog)
  set r := amplificationRadius C' α t K n with hrdef
  set M₀ := Real.exp ((I + 3 * w) / 2) with hM₀def
  have hM₀ : 1 ≤ M₀ := Real.one_le_exp (by positivity)
  have hr : (r : ℝ) ≤ max (amplificationRadiusCoefficient g C' C₀ α
      (Exponents.amplificationEpsilon : ℝ) K) (8 * √9 * (1 + C₂)) *
        (n : ℝ) ^ (Exponents.radiusExponent : ℝ) := by
    have hr := amplificationRadius_le_coefficient_mul_rpow hg hC' hC₀.le hα
      (by norm_num [Exponents.amplificationEpsilon]) (by norm_num [Exponents.amplificationEpsilon])
      K n hn1 I hI0 hII
    have hexp : ((Exponents.radiusExponent : ℚ) : ℝ) =
        (1 - (Exponents.amplificationEpsilon : ℝ)) / α := by
      simp only [Exponents.radiusExponent, Exponents.alpha, hαdef, kernelExponent, hpwdef]
      push_cast
      ring
    rw [hexp]
    exact hr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  refine ⟨r, hr, ?_, hcol r hr⟩
  intro X' hX' Jset hJset
  -- The typical projections and the restoring operator, with the ancillas as spectators.
  have hfail := typicalProjectors_three_cuts_of_threshold_le hq R hJ hΔ hC₀.le K n hNt Λ h E₀ Ω
    hgs X Y (X ∪ Y) hXcut hYcut
    (by rw [hXYS]; exact hScut)
  let x₀ : RegionalConfiguration q X := fun _ => 0
  let blank : RegionalConfiguration q X → ℂ := fun x => if x = x₀ then 1 else 0
  have hblank : ‖WithLp.toLp 2 blank‖ = 1 := norm_toLp_single_eq_one x₀
  let U := restoringEigenbasis Ω X
  obtain ⟨hU, hU'⟩ := restoringEigenbasis_unitary Ω X
  let 𝒲 := restoringTransport Ω X Y hXY
  let p := (reducedState_isHermitian Λ q Ω X).eigenvalues
  let E := Entropy.typicalSet p (regionalEntropy Λ q Ω X) w
  let Tq := typicalProjection Λ q Ω Y w
  let Q := restoringCutProjection Ω X Y hXY w
  let ψ := restoringVector Ω X Y hXY
  let Rp := 𝒲 * Entropy.restoringGlobal E p blank blank Q Tq * 𝒲ᴴ
  let Bp := 𝒲 * Entropy.restoringColumnGlobal E p blank blank Q Tq * 𝒲ᴴ
  let φ := 𝒲 *ᵥ (Entropy.restoringCopy blank blank ψ).ofLp
  let η := 𝒲 *ᵥ (Entropy.restoringRestored p ψ).ofLp
  let ξb : RegionalConfiguration q X × RegionalConfiguration q X → ℂ :=
    fun c => blank c.1 * (U *ᵥ blank) c.2
  obtain ⟨hφ1, hη1, hRn, hBn, hcol, hgr, hadj⟩ := restoringTransport_estimates Ω hΩ X Y hXY w
    ((n : ℝ) ^ (-(2 * K : ℝ))) (hfail X (by simp)).2.2.2 (hfail Y (by simp)).2.2.2
    (hfail (X ∪ Y) (by simp)).2.2.2 blank blank blank hblank hblank hblank
  have hφ1 : ‖WithLp.toLp 2 φ‖ = 1 := hφ1
  have hη1 : ‖WithLp.toLp 2 η‖ = 1 := hη1
  have hRn : ‖Rp‖ ≤ M₀ := hRn
  have hBn : ‖Bp‖ ≤ M₀ := hBn
  have hcol : Rp *ᵥ φ = Bp *ᵥ fun c => Ω c.1 * ξb c.2 := hcol
  rw [sqrt_rpow_neg_two_mul'] at hadj
  -- The supports of `B₀` and `R₀`.
  obtain ⟨PB, AB, hPB, hBsum⟩ :=
    restoringTransport_restoringColumnGlobal_eq_sum Ω X Y hXY E p blank blank Q Tq
  have hBsum : Bp = ∑ i ∈ E ×ˢ Finset.univ, PB i ⊗ₖ AB i := hBsum
  have hBblocks : ∀ x y : RegionalConfiguration q X × RegionalConfiguration q X,
      (Matrix.of fun σ τ => Bp (σ, x) (τ, y)) ∈ supportedOperators q (S₀ : Set (Site Λ)) := by
    intro x y
    rw [hBsum, ← hXYS]
    exact block_mem_supportedOperators_of_eq_sum _ hPB AB x y
  obtain ⟨PR, hPR, hRsum⟩ :=
    restoringTransport_restoringGlobal_eq_sum Ω X Y hXY E p blank blank Q Tq
  have hRsum : Rp = ∑ x ∈ E, PR x ⊗ₖ (Entropy.basisColumn x blank ⊗ₖ
      (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ)) := hRsum
  -- Anchors and the exact positive constraints.
  let a : AdmissibleSupport Λ R → Site Λ := fun Z => Z.2.1.choose
  have ha : ∀ Z, a Z ∈ Z.1 := fun Z => Z.2.1.choose_spec
  let k := fun i : AdmissibleSupport Λ R =>
    positiveConstraint cs (centeredFilter pw (Δ / 2) h.operator Ω (h.term i))
  obtain ⟨-, hk, -⟩ := latticePositiveConstraints_of_locality hpw R hJ hΔ htail Λ h a ha E₀ Ω hgs
  have hk : ∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0 := hk
  let Pr := fun i : AdmissibleSupport Λ R => a i ∈ graphNeighborhood Λ r S₀
  let tt : ℝ≥0 := ⟨t, ht0⟩
  have htt : (tt : ℝ) = t := rfl
  let μ := PoissonWord.measure (AdmissibleSupport Λ R) tt
  -- The vector `ζ = R₀ φ`, its excited component and the blank pair `ξ`.
  let ζ : Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ :=
    Rp *ᵥ φ
  let Pg := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))
  let ξe : EuclideanSpace ℂ (Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X)) :=
    toEuclideanLin ((1 - Pg) ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ))
        (WithLp.toLp 2 ζ)
  have hζn : ‖WithLp.toLp 2 ζ‖ ≤ M₀ := by
    have h := Rp.l2_opNorm_mulVec (WithLp.toLp 2 φ)
    rw [hφ1, mul_one] at h
    exact h.trans hRn
  have hPg : IsStarProjection Pg :=
    Entropy.blankOuterProduct_isStarProjection _ (by simpa using hΩ)
  have hξen : ‖ξe‖ ≤ M₀ := by
    have h := ((1 - Pg) ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
      (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)).l2_opNorm_mulVec
        (WithLp.toLp 2 ζ)
    have h1 : ‖(1 - Pg) ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
        (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)‖ ≤ 1 :=
      (l2_opNorm_kronecker_one_le _).trans hPg.one_sub.norm_le
    calc ‖ξe‖ ≤ _ := h
      _ ≤ 1 * M₀ := mul_le_mul h1 hζn (norm_nonneg _) zero_le_one
      _ = M₀ := one_mul _
  have hξb : ‖WithLp.toLp 2 ξb‖ = 1 := by
    have h := EuclideanSpace.norm_vecKron (WithLp.toLp 2 blank) (WithLp.toLp 2 (U *ᵥ blank))
    have hUb : ‖WithLp.toLp 2 (U *ᵥ blank)‖ = 1 := by
      rw [norm_toLp_mulVec_of_conjTranspose_mul_self hU', hblank]
    rw [hblank, hUb, mul_one] at h
    exact h
  -- The three random variables on one clock realization.
  let Xrv : PoissonWord.Word (AdmissibleSupport Λ R) → ℝ := fun u =>
    ‖toEuclideanLin (contractionWord k u.1 u.2 ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) ξe‖
  let Dl : List (AdmissibleSupport Λ R) → Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X) → ℂ := fun l =>
    ((l.reverse.map fun i => CFC.sqrt (1 - k i)).prod ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ
        (Bp *ᵥ fun x => WithLp.ofLp Ω x.1 * ξb x.2)
  let Yrv : PoissonWord.Word (AdmissibleSupport Λ R) → ℝ := fun u =>
    ‖WithLp.toLp 2 (Dl (List.ofFn u.2) - Dl ((List.ofFn u.2).filter fun i => decide (Pr i)))‖
  let Dret : PoissonWord.Word (AdmissibleSupport Λ R) →
      Matrix (Configuration Λ q) (Configuration Λ q) ℂ := fun u =>
    contractionWord (fun i : {i // Pr i} => k i) (PoissonWord.partitionWords Pr u).1.1
      (PoissonWord.partitionWords Pr u).1.2
  let kr := fun i : {i // Pr i} => siteExpectation q (graphBall (domainGraph Λ) (a i) r) (k i)
  let Lt : PoissonWord.Word (AdmissibleSupport Λ R) →
      Matrix (Configuration Λ q) (Configuration Λ q) ℂ := fun u =>
    contractionWord kr (PoissonWord.partitionWords Pr u).1.1
      (PoissonWord.partitionWords Pr u).1.2
  let Zrv : PoissonWord.Word (AdmissibleSupport Λ R) → ℝ := fun u => M₀ * ‖Dret u - Lt u‖
  obtain ⟨hXint, hXle⟩ := latticeConstraintWord_excitedProjection_decay hpw R hJ hΔ Λ h E₀ Ω
    hgs (WithLp.toLp 2 ζ) tt
  have hXint : Integrable (fun u => Xrv u ^ 2) μ := hXint
  have hXle : (∫ u, Xrv u ^ 2 ∂μ) ≤ Real.exp (-(Δ / cs) * t) * ‖ξe‖ ^ 2 := hXle
  obtain ⟨hYint, hYle⟩ := latticeConstraintWord_omission_of_positiveConstraints
    hpw R hC₃ hc₃ (latticePositiveConstraints_of_locality hpw R hJ hΔ htail) Λ h a ha E₀ Ω hgs
    _ S₀ Bp hBblocks ξb hξb r tt
  have hYint : Integrable Yrv μ := hYint
  have hYle : (∫ u, Yrv u ∂μ) ≤ Ao * t * S₀.card * ‖Bp‖ *
      Real.exp (vo * t - γ * (r : ℝ) ^ α) := hYle
  obtain ⟨hZint, hZle, hLt⟩ := latticeConstraintWord_truncation_of_positiveConstraints
    R hC₃ (latticePositiveConstraints_of_locality hpw R hJ hΔ htail) Λ h a ha E₀ Ω hgs S₀ r tt
  have hZint : Integrable (fun u => ‖Dret u - Lt u‖) μ := hZint
  have hZle : (∫ u, ‖Dret u - Lt u‖ ∂μ) ≤ Ct * t * S₀.card * (1 + (r : ℝ)) ^ 2 *
      Real.exp (-(ct * (r : ℝ) ^ α)) := hZle
  have hLt : ∀ u, ‖Lt u‖ ≤ 1 ∧ Lt u ∈ supportedOperators q
      (graphNeighborhood Λ (2 * r) S₀ : Set (Site Λ)) := hLt
  -- Markov's inequality and a union bound: a good realization.
  have hrα : 0 ≤ (r : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg r) α
  have hS0 : (0 : ℝ) ≤ S₀.card := Nat.cast_nonneg _
  have hM₀0 : 0 ≤ M₀ := (Real.exp_pos _).le
  obtain ⟨u0, hXu, hYu, hZu⟩ := good_realization_of_threshold_le hg hvo.le hc hCg hC₀.le hα hK1
    n hNg I w hI0 hw0 S₀.card hcard μ Xrv Yrv Zrv hXint
    (Filter.Eventually.of_forall fun u => norm_nonneg _) hYint
    (Filter.Eventually.of_forall fun u => mul_nonneg hM₀0 (norm_nonneg _))
    (hZint.const_mul M₀)
    (by
      have h1 : Real.exp (-(Δ / cs) * t) * ‖ξe‖ ^ 2 ≤ Real.exp (-(g * t)) * M₀ ^ 2 := by
        rw [neg_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξen 2)
          (Real.exp_pos _).le
      exact (hXle.trans h1).trans_eq (mul_comm _ _))
    (by
      have hCgt : 0 ≤ Cg * t * S₀.card := mul_nonneg (mul_nonneg hCg ht0) hS0
      have e1 : Real.exp (vo * t - γ * (r : ℝ) ^ α) ≤ Real.exp (vo * t - c * (r : ℝ) ^ α) :=
        Real.exp_le_exp.mpr
          (sub_le_sub_left (mul_le_mul_of_nonneg_right (min_le_right ct γ) hrα) _)
      have e2 : Ao * t * S₀.card * ‖Bp‖ ≤ Cg * t * S₀.card * M₀ :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hCt) ht0)
          hS0) hBn (norm_nonneg _) hCgt
      exact hYle.trans (mul_le_mul e2 e1 (Real.exp_pos _).le (mul_nonneg hCgt hM₀0)))
    (by
      rw [integral_const_mul]
      have hr2 : (0 : ℝ) ≤ (1 + (r : ℝ)) ^ 2 := sq_nonneg _
      have hCgt : 0 ≤ Cg * t * S₀.card * (1 + (r : ℝ)) ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg hCg ht0) hS0) hr2
      have e1 : Real.exp (-(ct * (r : ℝ) ^ α)) ≤ Real.exp (-(c * (r : ℝ) ^ α)) :=
        Real.exp_le_exp.mpr
          (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left ct γ) hrα))
      have e2 : Ct * t * S₀.card * (1 + (r : ℝ)) ^ 2 ≤ Cg * t * S₀.card * (1 + (r : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hAo) ht0) hS0) hr2
      have e3 := mul_le_mul_of_nonneg_left (hZle.trans (mul_le_mul e2 e1 (Real.exp_pos _).le
        hCgt)) hM₀0
      exact e3.trans_eq (by ring))
  let ε : ℝ := ((n : ℝ) ^ K)⁻¹
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hn1))
  -- The enlarged sites and the transported operators and vectors.
  let sp := ancillaSplit q X
  let N := graphNeighborhood Λ (2 * r) S₀
  have hS₀N : S₀ ⊆ N := by
    classical
    exact fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, SimpleGraph.Walk.nil,
      by simp⟩
  let I₂ := (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
    (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)
  have hsubk (A B : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :
      (A - B) ⊗ₖ I₂ = A ⊗ₖ I₂ - B ⊗ₖ I₂ := by
    ext i j
    simp only [kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  let Dfull := contractionWord k u0.1 u0.2
  have hkle : ∀ i, k i ≤ 1 := fun i => (hk i).2.1
  have hkΩ : ∀ i, k i *ᵥ WithLp.ofLp Ω = 0 := fun i => (hk i).2.2
  have hR₀supp : Rp.submatrix sp sp ∈ supportedOperators q
      ((N.disjSum (Finset.univ.disjSum ∅) : Finset (AncillaSites Λ X)) :
        Set (AncillaSites Λ X)) := by
    rw [hRsum]
    exact supportedOperators_mono (Finset.coe_subset.mpr
      (Finset.disjSum_mono (hXYS ▸ hS₀N) le_rfl))
      (sum_kronecker_submatrix_ancillaSplit_mem_supportedOperators E hPR _)
  obtain ⟨U₁, hU₁supp, hU₁unit, hU₁err⟩ := exists_ancilla_unitary_of_good_realization hR₀supp
    (hLt u0).2 (D := Dfull) (Dret := Dret u0) (g := (Pg ⊗ₖ I₂) *ᵥ ζ) (M₀ := M₀) (ε := ε)
    (a := 3 * ε + ε) hφ1 hη1 hζn
    (by
      rw [mulVec_mulVec, ← mul_kronecker_mul, Matrix.one_mul,
        contractionWord_mul_vecMulVec_self k hkle hkΩ])
    hgr
    (by
      have hsub : Rp *ᵥ φ - (Pg ⊗ₖ I₂) *ᵥ ζ = ((1 - Pg) ⊗ₖ I₂) *ᵥ ζ := by
        rw [hsubk, sub_mulVec, one_kronecker_one, one_mulVec]
      rw [hsub]
      exact hXu)
    (by
      rw [hsubk, sub_mulVec, hcol]
      have h1 : Dfull = ((List.ofFn u0.2).reverse.map fun i => CFC.sqrt (1 - k i)).prod :=
        contractionWord_eq_prod_reverse k _ _
      have h2 : Dret u0 = (((List.ofFn u0.2).filter fun i => decide (Pr i)).reverse.map
          fun i => CFC.sqrt (1 - k i)).prod := contractionWord_partitionWords_fst Pr k u0
      rw [h1, h2]
      exact hYu)
    hZu
    (by
      have hfix : toEuclideanCLM (𝕜 := ℂ) (Dret u0)ᴴ Ω = Ω := by
        apply WithLp.ofLp_injective 2
        rw [ofLp_toEuclideanCLM]
        exact conjTranspose_contractionWord_mulVec_self (fun i : {i // Pr i} => k i)
          (fun i => hkle i) (fun i => hkΩ i) _ _
      have hLΩ := norm_truncated_adjoint_sub_le (L' := Lt u0) hfix hΩ.le hM₀ hZu
      have h := hadj (Lt u0)
      have hLΩ' : ‖WithLp.toLp 2 ((Lt u0)ᴴ *ᵥ WithLp.ofLp Ω) - Ω‖ ≤ ε := hLΩ
      linarith only [h, hLΩ'])
  -- The entropy comparison on the enlarged sites.
  have hδ : ‖WithLp.toLp 2 (U₁ *ᵥ (φ ∘ sp)) - WithLp.toLp 2 (η ∘ sp)‖ ≤
      9 * (n : ℝ) ^ (-(K : ℝ) / 2) := by
    rw [← sqrt_inv_pow_eq_rpow]
    exact hU₁err.trans (unitary_error_le hε0 hε1)
  have hdim : (X.card : ℝ) * Real.log q ≤ C₂ * (n : ℝ) ^ 2 := by
    have hX : (X.card : ℝ) ≤ C₀ * (n : ℝ) ^ 2 :=
      (Nat.cast_le.mpr (Finset.card_le_card hXS)).trans hcard
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    calc (X.card : ℝ) * Real.log q ≤ C₀ * (n : ℝ) ^ 2 * Real.log q :=
          mul_le_mul_of_nonneg_right hX hlogq
      _ = C₂ * (n : ℝ) ^ 2 := by rw [hC₂def]; ring
  refine (mutualInformation_le_of_ancilla_unitary hΩ hXY (hXS.trans hS₀N) hJset hblank hblank
    hφ1 hη1 hU₁supp hU₁unit hn1 le_rfl hδ hdim X' hX').trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The constant `C₂` of Proposition 10.2 at the integer `M`, at the named filter-locality
constants `C₃ = latticePositiveConstraintConst R J Δ p` and
`c₃ = latticePositiveConstraintRate R J Δ p` of the positive constraints, `p = 10⁶`
(`09-amplification.tex`, lines 453–499 and 541–569, with Proposition 4.3, `03-quasilocal.tex`,
lines 220–334). It depends only on `q, R, J, Δ, C₀, M`. -/
noncomputable def amplificationConstantExplicit (q R : ℕ) (J Δ C₀ : ℝ) (M : ℕ) : ℝ :=
  amplificationConstant q R J Δ C₀
    (latticePositiveConstraintConst R J Δ Exponents.amplificationPower)
    (latticePositiveConstraintRate R J Δ Exponents.amplificationPower) M

/-- The threshold `N₂` of Proposition 10.2 at the integer `M`, at the named filter-locality
constants `C₃ = latticePositiveConstraintConst R J Δ p` and
`c₃ = latticePositiveConstraintRate R J Δ p` of the positive constraints, `p = 10⁶`
(`09-amplification.tex`, lines 304–322 and 453–499). It depends only on `q, R, J, Δ, C₀, M`. -/
noncomputable def amplificationThresholdExplicit (q R : ℕ) (J Δ C₀ : ℝ) (M : ℕ) : ℕ :=
  amplificationThreshold q R J Δ C₀
    (latticePositiveConstraintConst R J Δ Exponents.amplificationPower)
    (latticePositiveConstraintRate R J Δ Exponents.amplificationPower) M

/-- **Proposition 10.2 at the named constants** (`prop:amplification`, `09-amplification.tex`
lines 261–296, proof at lines 298–576), for the Hamiltonian parameters `q, R, J`, a gap
`Δ > 0`, `C₀ > 0` and an integer `M`. The conclusion of `AmplificationBound` holds with the
constant `C₂ = amplificationConstantExplicit q R J Δ C₀ M` and the threshold
`max N₂ (Exponents.collarRadiusThreshold C₂ 1)`, `N₂ = amplificationThresholdExplicit q R J Δ C₀ M`.
No sign condition on `J` is needed. -/
theorem amplificationBound_explicit (q R : ℕ) {J Δ C₀ : ℝ} (hΔ : 0 < Δ) (hC₀ : 0 < C₀)
    (M : ℕ) :
    ∀ n : ℕ, 2 ≤ n → max (amplificationThresholdExplicit q R J Δ C₀ M)
        (Exponents.collarRadiusThreshold (amplificationConstantExplicit q R J Δ C₀ M) 1) ≤ n →
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
        ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (T : Finset (ℤ × ℤ)),
            ((A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
              C₀ * (n : ℝ) ^ 2 →
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
            ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                A.filter fun x ↦ x.val ∈ T)).card : ℝ) ≤ C₀ * n →
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
              C₀ * n →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                (A.filter fun x ↦ x.val ∈ T)
                (A.filter fun x ↦ x.val ∈ ambientDilation T
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
              C₀ * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) →
            ∃ r : ℕ, (r : ℝ) ≤ amplificationConstantExplicit q R J Δ C₀ M *
                (n : ℝ) ^ (Exponents.radiusExponent : ℝ) ∧
              (∀ X ⊆ A.filter (fun x ↦ x.val ∈ T), ∀ Jset : Finset (Site Λ),
                Disjoint Jset (graphNeighborhood Λ (2 * r)
                  (A.filter fun x ↦ x.val ∈ ambientDilation T
                    ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)) →
                FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X Jset ≤
                  amplificationConstantExplicit q R J Δ C₀ M * ((n : ℝ) ^ M)⁻¹) ∧
              ((∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
                  (⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ : ℝ) +
                      (n : ℝ) ^ (Exponents.beta : ℝ) <
                    (Scan.ambientSupDistance t z : ℝ)) →
                graphNeighborhood Λ (2 * r)
                    (A.filter fun x ↦ x.val ∈ ambientDilation T
                      ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) ⊆ A) := by
  have hpw : 1 ≤ Exponents.amplificationPower := by norm_num [Exponents.amplificationPower]
  exact amplificationBound_of_locality (q := q) (R := R)
    (C₃ := latticePositiveConstraintConst R J Δ Exponents.amplificationPower)
    (c₃ := latticePositiveConstraintRate R J Δ Exponents.amplificationPower) hΔ hC₀
    (latticePositiveConstraintConst_nonneg R J Δ Exponents.amplificationPower)
    (latticePositiveConstraintRate_pos hpw R J hΔ)
    (fun hH hΩ hh hhJ L hcontr hunit hherm hfix _ hl hτ =>
      norm_latticePositiveConstraint_sub_map_le hpw R hΔ hH hΩ hh hhJ L hcontr hunit hherm hfix
        hl hτ) M

/-- **Proposition 10.2** (`prop:amplification`, `09-amplification.tex` lines 261–296, proof at
lines 298–576), for the Hamiltonian parameters `q, R, J` and every gap `Δ > 0`. Fix `C₀ > 0`
and an integer `M ≥ 1`. Beyond a threshold chosen before the domain,
the Hamiltonian, the cut and the target, the collar hypotheses give an integer radius
`r ≤ C_M n^((1-ε)/α)` such that every part of `X = A ∩ T` has mutual information at most
`C_M n^(-M)` with every set avoiding `N_{2r}(S₀)`, and `N_{2r}(S₀) ⊆ A` under the cut clearance
`dist_∞(T, Z) > L + n^β`. The constant and the threshold are those of
`amplificationBound_explicit`. -/
theorem amplificationBound {q R : ℕ} {J Δ : ℝ} (hΔ : 0 < Δ) : AmplificationBound q R J Δ := by
  intro C₀ hC₀ M _
  exact ⟨_, _, amplificationBound_explicit (J := J) q R hΔ hC₀ M⟩

/-- **Theorem 1.1 from Propositions 9.6 and 11.2.** With Proposition 10.2 proved, the uniform
area law follows from the sublinear collar bound and the two-family decomposition. This is
the source proof of Theorem 1.1 (`10-geometry.tex`, lines 803–857); it does not prove
Propositions 9.6 and 11.2, so it is not a proof of Theorem 1.1. -/
theorem uniformAreaLaw_of_collar_twoFamilies
    (hconst : ∀ q : ℕ, 1 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
      ∃ D₀ Ctpl : ℝ, SublinearCollarBound q R J Δ D₀ Ctpl ∧ TwoFamilyDecomposition D₀ Ctpl) :
    UniformAreaLaw :=
  uniformAreaLaw_of_collar_amplification_twoFamilies hconst
    fun _ _ _ _ _ _ hΔ => amplificationBound hΔ

end TNLean.PEPS.AreaLaw
