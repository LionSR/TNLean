/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceBootstrapEntropy
import TNLean.PEPS.AreaLaw.Scan.RectangleSourceEntropy
import TNLean.PEPS.AreaLaw.Scan.RectangleBootstrapGeometry
import TNLean.PEPS.AreaLaw.Scan.BoxEntropySupremum
import TNLean.PEPS.AreaLaw.Scan.ExponentBootstrap

/-!
# The physical safe-box exponent bootstrap

The actual rough scanner is instantiated on every weakly safe integer
rectangle, including thin rectangles and empty physical intersections. The
current uniform box estimate supplies its original-state target and prefix
inputs. One coefficient covers every current exponent above the fixed cutoff.
The scanner conclusion is restored to the original state before the literal
box supremum is taken; bounded rectangle sizes are covered by the volume bound.
The accepted finite exponent iteration then reaches the fixed box exponent.

Source: OpenAI area-law manuscript, `08-scanner.tex`, Proposition 9.5,
lines 681--805, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

/-- The explicit threshold of one physical bootstrap round at current safe-box coefficient
`Cbox`: the larger of the rough-scanner threshold `sourceBootstrapEntropyThreshold`, with
multiplicity `2^(2R(R+1))`, charge constant `3` times the multiplicity, target-size
coefficient `1` and entropy input `weakRectangleSourceEntropyCoefficient e_* Cbox`, and the
rectangle geometry threshold `roundedClearanceThreshold 24 Ctr ℓ`. Source: `08-scanner.tex`,
lines 693--796. -/
noncomputable def boxImprovementThreshold (q R : ℕ) {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (J Δ Ctr ct Cent eent Cen een Cbox : ℝ) : ℕ :=
  let multiplicity : ℕ := 2 ^ ((1 + 2 * R * (R + 1)) - 1)
  max (CollarScan.sourceBootstrapEntropyThreshold q R he₀ he₀₁ Ctr ct Cent eent Cen een
      (Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J) (3 * (multiplicity : ℝ)) 1
      (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) Cbox) multiplicity)
    (roundedClearanceThreshold 24 Ctr (BootstrapParameters.ell e₀))

/-- The explicit constant of one physical bootstrap round at current safe-box coefficient `Cbox`:
`576 C_out + N² log q + 1`, where `C_out` is the restored rough-budget coefficient of the input
`weakRectangleSourceEntropyCoefficient e_* Cbox` and `N = boxImprovementThreshold`.
Source: `08-scanner.tex`, lines 693--796. -/
noncomputable def boxImprovementConstant (q R : ℕ) {e₀ : ℝ} (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (J Δ Ctr ct Cent eent Cen een Cbox : ℝ) : ℝ :=
  576 * bootstrapRestoredBudgetCoefficient q
      (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) Cbox) +
    (boxImprovementThreshold q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een Cbox : ℝ) ^ 2 *
      Real.log q + 1

/-- The constant of one physical bootstrap round is positive. Source: `08-scanner.tex`,
lines 693--796. -/
theorem boxImprovementConstant_pos {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {e₀ : ℝ} (he₀ : 0 < e₀)
    (he₀₁ : e₀ < 1) (J Δ Ctr ct Cent eent Cen een : ℝ) {Cbox : ℝ} (hCbox : 0 ≤ Cbox) :
    0 < boxImprovementConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een Cbox := by
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hCe := weakRectangleSourceEntropyCoefficient_nonneg
    (by norm_num [Exponents.boxError] : (0 : ℝ) < Exponents.boxError) hCbox
  have hCout : 0 ≤ bootstrapRestoredBudgetCoefficient q
      (weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) Cbox) :=
    mul_nonneg (by unfold bootstrapRestoredBudgetBaseCoefficient; linarith) (by positivity)
  exact add_pos_of_nonneg_of_pos
    (add_nonneg (mul_nonneg (by norm_num) hCout) (mul_nonneg (sq_nonneg _) hlq)) one_pos

open Classical in
/-- The genuine physical one-step improvement with the explicit constant
`boxImprovementConstant`, uniformly in the current exponent, the current coefficient `Cbox` and
the safety parameter. The truncation constant `Ctr` and the transport constants
`ct, Cent, eent, Cen, een` remain existential and are chosen before `Cbox`.
Source: `08-scanner.tex`, lines 693--796. -/
theorem exists_uniform_boxEntropy_improvement_of_threshold_le
    (q R : ℕ) (hq : 1 ≤ q) {J Δ e₀ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1) :
    let he₀pos : 0 < e₀ := lt_trans (by norm_num [Exponents.boxError]) he₀
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
      ∀ Cbox : ℝ, 0 ≤ Cbox →
      ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      ∀ D₀ : ℕ, 1 ≤ D₀ →
        (∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤ Cbox * (r : ℝ) ^ (1 + e)) →
        ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
          boxImprovementConstant q R he₀pos he₀₁ J Δ Ctr ct Cent eent Cen een Cbox *
            (r : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
  intro he₀pos
  classical
  let : NeZero q := ⟨by omega⟩
  let F := BootstrapParameters.scannerExponents e₀ he₀pos he₀₁
  let multiplicity : ℕ := 2 ^ ((1 + 2 * R * (R + 1)) - 1)
  let C₁ : ℝ := 3 * (multiplicity : ℝ)
  have hC₁ : 0 < C₁ := by dsimp only [C₁, multiplicity]; positivity
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, hsource⟩ :=
    CollarScan.exists_sourceBootstrap_entropy_improvement_of_threshold_le hq R hJ hΔ
      (by norm_num : (0 : ℝ) ≤ 1) hC₁ multiplicity le_rfl he₀ he₀₁
  refine ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, fun Cbox hCbox ↦ ?_⟩
  have hb : (0 : ℝ) < Exponents.boxError := by norm_num [Exponents.boxError]
  let Ce := weakRectangleSourceEntropyCoefficient (Exponents.boxError : ℝ) Cbox
  have hentropy := weakRectangle_source_entropy_bounds _ Cbox hb hCbox
  have hsource := hsource Ce (weakRectangleSourceEntropyCoefficient_nonneg hb hCbox)
  let Ns := CollarScan.sourceBootstrapEntropyThreshold q R he₀pos he₀₁ Ctr ct Cent eent Cen een
    (Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J) C₁ 1 Ce multiplicity
  let Ng := roundedClearanceThreshold 24 Ctr F.ell
  let N := max Ns Ng
  let Cout := bootstrapRestoredBudgetCoefficient q Ce
  have hCout : 0 ≤ Cout := mul_nonneg (by
    have := weakRectangleSourceEntropyCoefficient_nonneg hb hCbox
    have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
    unfold bootstrapRestoredBudgetBaseCoefficient; linarith) (by positivity)
  let Crect := 576 * Cout
  have hCrect : 0 ≤ Crect := by dsimp only [Crect]; positivity
  intro e he hee₀ D₀ hD₀ hbox
  have hepos : 0 < e := lt_trans (by norm_num [Exponents.boxError]) he
  have hp : 0 ≤ 1 + (1 - BootstrapParameters.ell e₀) * e := by
    have hθ : 0 < 1 - BootstrapParameters.ell e₀ := sub_pos.mpr F.ell_lt_one
    positivity
  refine boxEntropy_power_le_of_large_rectangles (C := Crect) hq hCrect hp N ?_
  intro Λ h E₀ Ω hgs A Q hsafe hQN
  let : LinearOrder (AdmissibleSupport Λ R) :=
    LinearOrder.lift' (Fintype.equivFin (AdmissibleSupport Λ R))
      (Fintype.equivFin (AdmissibleSupport Λ R)).injective
  let S := rectangleBootstrapScanner Q A R F Ctr C₁
  have hQNs : Ns ≤ Q.size := (le_max_left Ns Ng).trans hQN
  have hQNg : Ng ≤ Q.size := (le_max_right Ns Ng).trans hQN
  obtain ⟨hT, hgraph, hA, hn24, hsn, hdepth, hanchor, hmult, hcard,
      hLpos, hL, hbudget, hrows, hclear, hregion, _, _⟩ :=
    rectangleBootstrapScanner_geometry_of_threshold_le F hCtr.le A Q R C₁ hD₀ hQNg hsafe
  have hnS : Ns ≤ S.n := hQNs.trans hsn
  have hphysical : ∀ Q' : IntRect, IsSafe Λ A D₀ Q' →
      regionalEntropy Λ q Ω (rectRegion A Q') ≤ Cbox * (Q'.size : ℝ) ^ (1 + e) :=
    fun Q' hsafe' ↦ regionalEntropy_le_of_boxEntropy_power hq (by linarith)
      hbox h hgs A Q' hsafe'
  obtain ⟨htarget, hprefix⟩ := hentropy Λ q D₀ Ω hgs.1 A Q hT hsafe
    S.n (F.L S.n) hsn hLpos hL hbudget e he.le hphysical
  have htarget' : regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ Q.toFinset) ≤
      Ce * (S.n : ℝ) ^ (1 + e) := htarget
  have hprefix' : ∀ j : ℕ, j ≤ F.L S.n →
      regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
        Ce * ((S.n : ℝ) * (F.L S.n : ℝ) ^ e + S.n) := hprefix
  have hresult := hsource e he hee₀ Λ Q.toFinset hT h S E₀ Ω hgs hgraph hanchor hnS
    rfl rfl rfl rfl rfl (by simpa only [one_mul] using hcard)
    hdepth hrows hmult hclear htarget' hprefix'
  rw [hregion] at hresult
  have hp2 : 1 + (1 - BootstrapParameters.ell e₀) * e ≤ 2 := by
    have hell : 0 ≤ BootstrapParameters.ell e₀ := F.ell_pos.le
    nlinarith [mul_nonneg hell hepos.le]
  have hbase : (24 : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) ≤ 576 := by
    have hb := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 24) hp2
    norm_num at hb ⊢
    exact hb
  calc
    regionalEntropy Λ q Ω (rectRegion A Q) ≤
        Cout * (S.n : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := hresult
    _ = Cout * ((24 : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) *
        (Q.size : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e)) := by
      rw [hn24, Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
    _ ≤ Cout * (576 * (Q.size : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (Nat.cast_nonneg Q.size) _)) hCout
    _ = Crect * (Q.size : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
      dsimp only [Crect]; ring

/-- The genuine physical one-step improvement, uniformly in the current
exponent and safety parameter. Its input is only the current safe-box power;
its output has exponent multiplied by the single fixed bootstrap contraction.
All coefficients precede every finite domain, state, cut and rectangle in the
literal box supremum. Source: `08-scanner.tex`, lines 693--796. -/
theorem exists_uniform_boxEntropy_improvement
    (q R : ℕ) (hq : 1 ≤ q) {J Δ e₀ Cbox : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1) (hCbox : 0 ≤ Cbox) :
    ∃ C : ℝ, 0 < C ∧
      ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      ∀ D₀ : ℕ, 1 ≤ D₀ →
        (∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤ Cbox * (r : ℝ) ^ (1 + e)) →
        ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
          C * (r : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, _, _, hall⟩ :=
    exists_uniform_boxEntropy_improvement_of_threshold_le q R hq hJ hΔ he₀ he₀₁
  exact ⟨_, boxImprovementConstant_pos hq R _ he₀₁ J Δ Ctr ct Cent eent Cen een hCbox,
    hall Cbox hCbox⟩

/-- The safe-box constant `C_box` of Proposition 9.5 from an initial safe-box bound
`C₀ r^(1 + e₀)`: the bootstrap constant `boxBootstrapConstant (log q) G (fun _ ↦ 1) C₀ m`
after `m = boxBootstrapRounds e₀ e_* ℓ` rounds, where `ℓ = (1 - e₀) / 200000` and
`G = boxImprovementConstant` is the constant of one physical round. Source: `08-scanner.tex`,
lines 788--803. -/
noncomputable def physicalBoxBootstrapConstant (q R : ℕ) {e₀ : ℝ} (he₀ : 0 < e₀)
    (he₀₁ : e₀ < 1) (J Δ Ctr ct Cent eent Cen een C₀ : ℝ) : ℝ :=
  boxBootstrapConstant (Real.log q)
    (boxImprovementConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een) (fun _ ↦ 1) C₀
    (boxBootstrapRounds e₀ (Exponents.boxError : ℝ) (BootstrapParameters.ell e₀))

/-- The physical safe-box estimate at the fixed source exponent with the explicit constant
`physicalBoxBootstrapConstant`, from any initial safe-box bound `C₀ r^(1 + e₀)` with
`0 ≤ C₀` and `0 < e₀ < 1`, uniform over safety parameters `D₀ > 2R + 10`. The truncation
constant `Ctr` and the transport constants `ct, Cent, eent, Cen, een` remain existential.
Source: Proposition 9.5, `08-scanner.tex`, lines 681--805. -/
theorem exists_boxEntropy_le_boxError_of_initial
    (q R : ℕ) (hq : 1 ≤ q) {J Δ C₀ e₀ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC₀ : 0 ≤ C₀)
    (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (hinitial : ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
      ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤ C₀ * (r : ℝ) ^ (1 + e₀)) :
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
      ∀ D₀ : ℕ, 2 * R + 10 < D₀ → ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
        physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀ *
          (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  have hε : (0 : ℝ) < Exponents.boxError := by norm_num [Exponents.boxError]
  obtain ⟨_, _, hℓ, hℓ₁, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  have hconstants : ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
      ∀ Cbox : ℝ, 0 ≤ Cbox →
      ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      ∀ D₀ : ℕ, 1 ≤ D₀ →
        (∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤ Cbox * (r : ℝ) ^ (1 + e)) →
        ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
          boxImprovementConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een Cbox *
            (r : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
    by_cases h : (Exponents.boxError : ℝ) < e₀
    · exact exists_uniform_boxEntropy_improvement_of_threshold_le q R hq hJ hΔ h he₀₁
    · exact ⟨1, 1, 0, 0, 0, 0, one_pos, one_pos,
        fun _ _ e he hee₀ ↦ absurd (he.trans_le hee₀) h⟩
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, himprove⟩ := hconstants
  refine ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, fun D₀ hD₀ r hr ↦ ?_⟩
  let I := {D₀ : ℕ // 2 * R + 10 < D₀}
  let B := fun (i : I) (r : ℕ) ↦ boxEntropy q R J Δ i.val r
  have hvolume : ∀ i r, 1 ≤ r → B i r ≤ Real.log q * (r : ℝ) ^ 2 := by
    intro i r _
    simpa only [mul_comm] using boxEntropy_le_sq_mul_log (R := R) (J := J) (Δ := Δ)
      (D₀ := i.val) hq r
  exact uniform_power_bound_of_boxBootstrapRounds (F := B) (N := fun _ ↦ 1)
    (Real.log_nonneg (by exact_mod_cast hq)) he₀ hε hℓ hℓ₁ hC₀
    (fun _ hC ↦ (boxImprovementConstant_pos hq R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een hC).le)
    hvolume (fun i r hr ↦ hinitial i.val i.property r hr)
    (fun e C he hee₀ hC hcurrent i r hr ↦
      himprove C hC e he hee₀ i.val (by have := i.property; omega) (hcurrent i) r hr)
    ⟨D₀, hD₀⟩ r hr

/-- The physical safe-box estimate at the fixed source exponent, with one
constant before every safety parameter, finite system and positive scale.
The initial exponent comes from the genuine initial safe-box theorem; the
improvement premise of finite iteration is supplied by the preceding actual
rough-scanner construction. Source: Proposition 9.5, `08-scanner.tex`, lines 681--805. -/
theorem exists_boxEntropy_le_boxError
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
      ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
        C * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  obtain ⟨C₀, e₀, he₀, he₀₁, hinitial⟩ := exists_boxEntropy_le_rpow q R hq hJ hΔ
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, _, _, hbox⟩ :=
    exists_boxEntropy_le_boxError_of_initial q R hq hJ hΔ (zero_le_one.trans (le_max_left 1 C₀))
      he₀ he₀₁ fun D₀ hD₀ r hr ↦ (hinitial D₀ hD₀ r hr).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 C₀) (Real.rpow_nonneg (Nat.cast_nonneg r) _))
  exact ⟨_, boxBootstrapConstant_pos (Real.log_nonneg (by exact_mod_cast hq))
    (one_pos.trans_le (le_max_left 1 C₀))
    (fun _ hC ↦ boxImprovementConstant_pos hq R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een hC) _, hbox⟩

end TNLean.PEPS.AreaLaw.Scan
