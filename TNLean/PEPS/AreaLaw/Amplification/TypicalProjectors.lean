/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TailParameter
import TNLean.PEPS.AreaLaw.ZeroBoundary
import QICLean.Entropy.TypicalDensity

/-!
# Typical projectors of the amplification proposition

The proof of the amplification proposition begins with three spectral projections
`P_X, T_Y, Q_{S_0}`, one for each of the cuts `X, Y, S_0`. Each projects onto the
positive eigenvalues of the regional state of the original ground vector whose
surprisal lies within `w = n^(3/5)` of the regional entropy. This module constructs
them from Lemma 3.1 (`lem:tail`). A cut with at most `C₀ n` crossing edges has tail
parameter at most a constant times `n`, so the failure probability
`1 - tr(ρ P)` of its projection is at most `C exp(-c n^(1/10))`. For every fixed
integer `K`, this is at most `δ = n^(-2K)` beyond a threshold.

The constants and the threshold depend only on the local dimension, the range, the
interaction bound, the gap, `C₀` and `K`. They are chosen before the domain, the
Hamiltonian, the ground vector and the cut. Selected eigenvalues are positive, so no
invertibility of a marginal is assumed.

## Main statements

* `typicalProjection`: the spectral projection of a regional state onto its typical
  positive spectrum.
* `typicalProjection_failure_le_surprisalTail`: the failure probability of a typical
  projection is at most the surprisal tail, together with its projection and
  eigenvalue-window properties.
* `exists_typicalProjection_failure_le_stretchedExp`: failure probability at most
  `C exp(-c n^(1/10))` at width `n^(3/5)`.
* `exists_typicalProjection_failure_le_inv_pow`: failure probability at most
  `n^(-2K)`, `eq:amplification-typical-error`.
* `exists_typicalProjectors_three_cuts`: the three projections of the proof, with
  their common error `δ = n^(-2K)`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`,
  lines 304–322, `eq:amplification-typical-error`; Lemma 3.1 (`lem:tail`),
  `02-initial.tex`, lines 34–69, and `eq:initial-local-tail-parameter`, lines 202–206.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix Filter Topology

namespace TNLean.PEPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- The spectral projection of the regional state of `Ω` on `Y` onto the positive
eigenvalues whose surprisal lies within `w` of the regional entropy, such as
`P_X, T_Y, Q_{S_0}` in the proof of the amplification proposition.
Source: `09-amplification.tex`, lines 304–313. -/
noncomputable def typicalProjection (Λ : Finset (ℤ × ℤ)) (q : ℕ) (Ω : StateSpace Λ q)
    (Y : Finset (Site Λ)) (w : ℝ) :
    Matrix ({x : Site Λ // x ∈ Y} → Fin q) ({x : Site Λ // x ∈ Y} → Fin q) ℂ :=
  (reducedState_isHermitian Λ q Ω Y).spectralSelection
    (Entropy.typicalSet (reducedState_isHermitian Λ q Ω Y).eigenvalues
      (regionalEntropy Λ q Ω Y) w)

/-- The probability that a selected spectral projection succeeds is the mass of the
selected eigenvalues. -/
private theorem trace_mul_spectralSelection {n : Type*} [Fintype n]
    [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (E : Finset n) :
    (ρ * hρ.spectralSelection E).trace = (hρ.spectralRestrictionMass E : ℂ) := by
  conv_lhs => arg 1; arg 1; rw [hρ.spectral_theorem]
  rw [IsHermitian.spectralSelection, ← map_mul, Unitary.conjStarAlgAut_apply,
    trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, diagonal_mul_diagonal,
    trace_diagonal, IsHermitian.spectralRestrictionMass]
  push_cast
  simp only [Function.comp_apply, mul_ite, mul_one, mul_zero, RCLike.ofReal_eq_complex_ofReal]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Typical projection of one cut.** For a unit vector `Ω`, a region `Y` and a width
`w`, the typical projection is an orthogonal projection commuting with the regional
state. Its selected eigenvalues are positive and lie in `[e^{-S-w}, e^{-S+w}]`, and its
failure probability `1 - tr(ρ_Y P)` is at most the surprisal tail at `w`.
Source: `09-amplification.tex`, lines 304–313 and 319–321. -/
theorem typicalProjection_failure_le_surprisalTail (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (Y : Finset (Site Λ)) (w : ℝ) :
    IsStarProjection (typicalProjection Λ q Ω Y w) ∧
      Commute (typicalProjection Λ q Ω Y w) (reducedState Λ q Ω Y) ∧
      (∀ i ∈ Entropy.typicalSet (reducedState_isHermitian Λ q Ω Y).eigenvalues
          (regionalEntropy Λ q Ω Y) w,
        0 < (reducedState_isHermitian Λ q Ω Y).eigenvalues i ∧
          Real.exp (-regionalEntropy Λ q Ω Y - w) ≤
            (reducedState_isHermitian Λ q Ω Y).eigenvalues i ∧
          (reducedState_isHermitian Λ q Ω Y).eigenvalues i ≤
            Real.exp (-regionalEntropy Λ q Ω Y + w)) ∧
      1 - (reducedState Λ q Ω Y * typicalProjection Λ q Ω Y w).trace.re ≤
        Entropy.surprisalTail (reducedState_isHermitian Λ q Ω Y).eigenvalues
          (regionalEntropy Λ q Ω Y) w := by
  have hρ := reducedState_posSemidef Λ q Ω Y
  refine ⟨(reducedState_isHermitian Λ q Ω Y).isStarProjection_spectralSelection _,
    (reducedState_isHermitian Λ q Ω Y).commute_spectralSelection _,
    fun i hi ↦ ⟨(Entropy.mem_typicalSet.mp hi).1, Entropy.exp_le_of_mem_typicalSet hi⟩, ?_⟩
  have hm := Entropy.one_sub_surprisalTail_le_typicalMass hρ.eigenvalues_nonneg
    (posSemidef_trace_one_eigenvalues_sum_one hρ (trace_reducedState Ω hΩ Y))
    (regionalEntropy Λ q Ω Y) w
  rw [typicalProjection, trace_mul_spectralSelection, Complex.ofReal_re]
  change 1 - Entropy.typicalMass _ _ _ ≤ _
  linarith

/-- The constant `c = (32 √((1 + J/Δ) C (1 + C₀)))⁻¹` of the stretched-exponential
failure bound, with `C = tailParameterConstant q R`. -/
private noncomputable def failureRate (q R : ℕ) (J Δ C₀ : ℝ) : ℝ :=
  (32 * Real.sqrt ((1 + J / Δ) * (tailParameterConstant q R * (1 + C₀))))⁻¹

/-- **Failure probability of a typical projection.** There are constants `C, c > 0`,
depending only on `q, R, J, Δ` and `C₀`, such that for every scale `n ≥ 1`, every
gapped ground vector `Ω` of a finite-range Hamiltonian on a finite domain and every cut
`Y` with at most `C₀ n` crossing edges, the typical projection at width `n^(3/5)` fails
with probability at most `C exp(-c n^(1/10))`.
Source: `09-amplification.tex`, lines 304–317, from Lemma 3.1, `02-initial.tex`,
lines 64–69, and `eq:initial-local-tail-parameter`, lines 202–206. -/
theorem exists_typicalProjection_failure_le_stretchedExp (hq : 1 ≤ q) (R : ℕ)
    (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ Y : Finset (Site Λ), ((edgeBoundary Λ Y).card : ℝ) ≤ C₀ * n →
          1 - (reducedState Λ q Ω Y *
              typicalProjection Λ q Ω Y ((n : ℝ) ^ ((3 : ℝ) / 5))).trace.re ≤
            C * Real.exp (-(c * (n : ℝ) ^ ((1 : ℝ) / 10))) := by
  have hT := one_le_tailParameterConstant hq R
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  refine ⟨2 * Real.exp (Real.exp 1 / 2), failureRate q R J Δ C₀, by positivity,
    by unfold failureRate; positivity, ?_⟩
  intro n hn Λ h E₀ Ω hgs Y hY
  set w : ℝ := (n : ℝ) ^ ((3 : ℝ) / 5)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨-, -, -, hfail⟩ := typicalProjection_failure_le_surprisalTail Ω hgs.1 Y w
  have htail := (h.surprisalTail_reducedState_le hJ hΔ hgs Y w).trans (min_le_right _ _)
  refine hfail.trans (htail.trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  rw [Real.exp_le_exp, neg_le_neg_iff]
  -- the tail parameter is at most `C (1 + C₀) n`
  set B := cutLogBudget Λ q R Y
  have hB1 : 1 ≤ B := Entropy.one_le_cutLogBudget _ _
  have hBn : B ≤ tailParameterConstant q R * (1 + C₀) * n := by
    refine (cutLogBudget_le_edgeBoundary hq R Y).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    nlinarith
  set D := Real.sqrt ((1 + J / Δ) * (tailParameterConstant q R * (1 + C₀)))
  have hD : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hsqrt : Real.sqrt ((1 + J / Δ) * B) ≤ D * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt
      ((mul_le_mul_of_nonneg_left hBn (by positivity)).trans_eq (by ring))
  have hpow : (n : ℝ) ^ ((1 : ℝ) / 10) * (n : ℝ) ^ ((1 : ℝ) / 2) = w := by
    rw [← Real.rpow_add hn0]; norm_num [w]
  have hpos : 0 < Real.sqrt ((1 + J / Δ) * B) := Real.sqrt_pos.mpr (by positivity)
  rw [le_div_iff₀ (by positivity), failureRate, ← hpow]
  calc (32 * D)⁻¹ * (n : ℝ) ^ ((1 : ℝ) / 10) * (32 * Real.sqrt ((1 + J / Δ) * B))
      ≤ (32 * D)⁻¹ * (n : ℝ) ^ ((1 : ℝ) / 10) * (32 * (D * (n : ℝ) ^ ((1 : ℝ) / 2))) := by
        gcongr
    _ = (n : ℝ) ^ ((1 : ℝ) / 10) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        field_simp

/-- A stretched exponential `C exp(-c n^(1/10))` is eventually at most `n^(-s)`. -/
private theorem eventually_stretchedExp_le_rpow_neg {C c : ℝ} (hc : 0 < c) (s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(c * (n : ℝ) ^ ((1 : ℝ) / 10))) ≤ (n : ℝ) ^ (-s) := by
  have hx : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * s) c hc).comp hx
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 * s) * Real.exp (-c * (n : ℝ) ^ ((1 : ℝ) / 10)) ≤
        (max C 1)⁻¹ :=
    hlim.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : ((n : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 * s) = (n : ℝ) ^ s := by
    rw [← Real.rpow_mul hn0.le]; ring_nf
  rw [hpow, neg_mul] at hn
  have hs : 0 < (n : ℝ) ^ s := Real.rpow_pos_of_pos hn0 s
  have hC : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set e := Real.exp (-(c * (n : ℝ) ^ ((1 : ℝ) / 10)))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hone : max C 1 * ((n : ℝ) ^ s * e) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hn hC.le).trans_eq (mul_inv_cancel₀ hC.ne')
  have hCe : C * ((n : ℝ) ^ s * e) ≤ max C 1 * ((n : ℝ) ^ s * e) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hs.le he)
  rw [Real.rpow_neg hn0.le, ← one_div, le_div_iff₀ hs]
  nlinarith

/-- **Typical error of one cut, `eq:amplification-typical-error`.** For every integer
`K`, there is a threshold, depending only on `q, R, J, Δ, C₀` and `K`, beyond which the
typical projection at width `n^(3/5)` of every cut with at most `C₀ n` crossing edges
fails with probability at most `δ = n^(-2K)`.
Source: `09-amplification.tex`, lines 304–318, `eq:amplification-typical-error`. -/
theorem exists_typicalProjection_failure_le_inv_pow (hq : 1 ≤ q) (R : ℕ)
    (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (n : ℕ), N ≤ n → ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ Y : Finset (Site Λ), ((edgeBoundary Λ Y).card : ℝ) ≤ C₀ * n →
          1 - (reducedState Λ q Ω Y *
              typicalProjection Λ q Ω Y ((n : ℝ) ^ ((3 : ℝ) / 5))).trace.re ≤
            (n : ℝ) ^ (-(2 * K : ℝ)) := by
  obtain ⟨C, c, -, hc, hfail⟩ :=
    exists_typicalProjection_failure_le_stretchedExp (J := J) hq R hJ hΔ hC₀
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((eventually_stretchedExp_le_rpow_neg (C := C) hc (2 * K)).and (eventually_ge_atTop 1))
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro n hn Λ h E₀ Ω hgs Y hY
  obtain ⟨hle, hn1⟩ := hN n ((le_max_left _ _).trans hn)
  exact (hfail n hn1 Λ h E₀ Ω hgs Y hY).trans hle

/-- **The three typical projectors of the amplification proposition.** For every
integer `K`, beyond a threshold depending only on `q, R, J, Δ, C₀` and `K`, the
following holds for every gapped ground vector `Ω` of a finite-range Hamiltonian on a
finite domain and every three cuts `X, Y, S₀` with at most `C₀ n` crossing edges each.
The typical projections `P_X, T_Y, Q_{S₀}` at width `w = n^(3/5)` are orthogonal
projections commuting with their regional states, their selected eigenvalues are
positive and lie within `e^{±w}` of `e^{-S}`, and each fails with probability at most
`δ = n^(-2K)`.
Source: `09-amplification.tex`, lines 304–322, `eq:amplification-typical-error`. -/
theorem exists_typicalProjectors_three_cuts (hq : 1 ≤ q) (R : ℕ)
    (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (K : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (n : ℕ), N ≤ n → ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ X Y S₀ : Finset (Site Λ),
          ((edgeBoundary Λ X).card : ℝ) ≤ C₀ * n →
          ((edgeBoundary Λ Y).card : ℝ) ≤ C₀ * n →
          ((edgeBoundary Λ S₀).card : ℝ) ≤ C₀ * n →
          ∀ Z ∈ ({X, Y, S₀} : Finset (Finset (Site Λ))),
            let w := (n : ℝ) ^ ((3 : ℝ) / 5)
            let p := (reducedState_isHermitian Λ q Ω Z).eigenvalues
            let S := regionalEntropy Λ q Ω Z
            IsStarProjection (typicalProjection Λ q Ω Z w) ∧
              Commute (typicalProjection Λ q Ω Z w) (reducedState Λ q Ω Z) ∧
              (∀ i ∈ Entropy.typicalSet p S w,
                0 < p i ∧ Real.exp (-S - w) ≤ p i ∧ p i ≤ Real.exp (-S + w)) ∧
              1 - (reducedState Λ q Ω Z * typicalProjection Λ q Ω Z w).trace.re ≤
                (n : ℝ) ^ (-(2 * K : ℝ)) := by
  classical
  obtain ⟨N, hN1, hN⟩ := exists_typicalProjection_failure_le_inv_pow (J := J) hq R hJ hΔ hC₀ K
  refine ⟨N, hN1, ?_⟩
  intro n hn Λ h E₀ Ω hgs X Y S₀ hX hY hS Z hZ
  have hZb : ((edgeBoundary Λ Z).card : ℝ) ≤ C₀ * n := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl | rfl <;> assumption
  obtain ⟨hproj, hcomm, hwin, -⟩ :=
    typicalProjection_failure_le_surprisalTail Ω hgs.1 Z ((n : ℝ) ^ ((3 : ℝ) / 5))
  exact ⟨hproj, hcomm, hwin, hN n hn Λ h E₀ Ω hgs Z hZb⟩

end TNLean.PEPS.AreaLaw
