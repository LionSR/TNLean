/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.CollarInformation
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxBootstrap
import TNLean.PEPS.AreaLaw.Scan.TemplateFinalInformation
import TNLean.PEPS.AreaLaw.Scan.BoxClearanceComparison

/-!
# The physical sublinear collar bound

For every real clearance greater than 2R+10, the physical safe-box entropy
estimate gives the sublinear mutual-information bound for the original ground
state. The same constant and scale threshold apply to every finite domain,
Hamiltonian, ground state, cut, and separated template. The collar cut and
volume estimates then give all assertions of Proposition 9.6.

The proof uses the integer clearance 2R+10 internally, after transferring the
physical safe-box estimate from clearance 2R+11 by subdivision. Separation at
the prescribed real clearance implies separation at this integer clearance.
No scanner or mutual-information estimate is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943; the real safety
parameter is specified in `02-initial.tex`, line 225,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- The safe-box constant at clearance `2R + 10` obtained by subdivision from a safe-box
constant `Cbox` at clearance `2R + 11`: `4 Cbox + 4 log q + 1`. Source: area-law
Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943. -/
noncomputable def collarBoxConstant (q : ℕ) (Cbox : ℝ) : ℝ :=
  4 * Cbox + 4 * Real.log q + 1

/-- The constant `C₁ = max (C_m / 2) 10` of the sublinear collar bound, where
`C_m = collarConstant q J Δ (collarBoxConstant q Cbox)` is the collar information coefficient at
the subdivided safe-box constant. Source: area-law Proposition 9.6, `08-scanner.tex`,
lines 808–827 and 942–943. -/
noncomputable def sublinearCollarConstant (q : ℕ) (J Δ Cbox : ℝ) : ℝ :=
  max (Scan.collarConstant q J Δ (collarBoxConstant q Cbox) / 2) 10

/-- The threshold `N₁ = collarThreshold q R J Δ (collarBoxConstant q Cbox) Ctr ct Cent eent Cen een`
of the sublinear collar bound, at the subdivided safe-box constant. Source: area-law
Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943. -/
noncomputable def sublinearCollarThreshold (q R : ℕ) (J Δ Cbox Ctr ct Cent eent Cen een : ℝ) :
    ℕ :=
  Scan.collarThreshold q R J Δ (collarBoxConstant q Cbox) Ctr ct Cent eent Cen een

/-- **Proposition 9.6 at a named constant, threshold and truncation constant.** The sublinear
collar bound of `sublinearCollarBound_real_of_boxEntropy` from a safe-box bound
`Cbox r^(1 + ε_box)` at clearance `2R + 11`, with the truncation constant
`latticeTruncationRadiusConstant R J Δ 10` and any transport constants `c₀, Cent, eent, Cen, een`
with `0 < c₀` satisfying the finite-family transport bound, such as QICLean's universal transport
constants. Source: area-law Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943. -/
theorem sublinearCollarBound_real_of_boxEntropy_explicit
    (q R : ℕ) (hq : 1 ≤ q) {J Δ D₀ Ctpl Cbox : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hD₀ : 2 * (R : ℝ) + 10 < D₀)
    (hCtpl : 24 ≤ Ctpl) (hCbox : 0 ≤ Cbox)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ (2 * R + 11) r ≤
      Cbox * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)))
    {c₀ Cent eent Cen een : ℝ} (hc₀ : 0 < c₀)
    (htr : Scan.CollarScan.FiniteFamilyTransportBound c₀ Cent eent Cen een) :
      ∀ n s₀ : ℕ, sublinearCollarThreshold q R J Δ Cbox (latticeTruncationRadiusConstant R J Δ 10)
          c₀ Cent eent Cen een ≤ n →
        ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
          ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            ∀ A : Finset (Site Λ), ∀ T : Geometry.Template Ctpl n s₀,
              T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) →
              ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s₀ →
              FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                  (A.filter fun x ↦ x.val ∈ T.points)
                  (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                    ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
                sublinearCollarConstant q J Δ Cbox *
                  (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) ∧
              ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤
                sublinearCollarConstant q J Δ Cbox * n ∧
              ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
                sublinearCollarConstant q J Δ Cbox * n ∧
              ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                  A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤
                sublinearCollarConstant q J Δ Cbox * n ∧
              ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
                sublinearCollarConstant q J Δ Cbox * (n : ℝ) ^ 2 := by
  let d : ℕ := 2 * R + 10
  have hd : 3 ≤ d := by dsimp only [d]; omega
  have hp : 0 ≤ 1 + (Exponents.boxError : ℝ) := by
    norm_num [Exponents.boxError]
  have hweak := boxEntropy_power_le_of_succ_clearance
    (R := R) (D := d) (J := J) (Δ := Δ) (p := 1 + (Exponents.boxError : ℝ))
    hq hd hCbox hp hbox
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hCw : 0 ≤ collarBoxConstant q Cbox := by unfold collarBoxConstant; linarith
  have hinfo := Scan.template_final_mutualInformation_of_boxEntropy_explicit q R d hq
      (by omega) hJ hΔ hCtpl hCw hweak hc₀ htr
  have hdreal : (d : ℝ) < D₀ := by
    simpa only [d, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hD₀
  have hD₀1 : (1 : ℝ) ≤ D₀ := by
    linarith [show (0 : ℝ) ≤ (R : ℝ) from Nat.cast_nonneg R]
  refine sublinearCollarBound_of_mutualInformation_le_at hCtpl hD₀1 _ _ ?_
  intro n s₀ hn Λ h E₀ Ω hgs A T hsep hL
  have hsep' : T.IsSeparated (d : ℝ) (Geometry.boundaryEndpoints Λ A) := by
    intro t ht z hz
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdreal.le (by norm_num : (0 : ℝ) ≤ 4))
        (Nat.cast_nonneg s₀)) (hsep t ht z hz)
  have hi := (hinfo n s₀ hn Λ h E₀ Ω hgs A T hsep' hL).2
  dsimp only [Exponents.scannerEll, Exponents.amplificationEpsilon] at hi ⊢
  nlinarith only [hi]

/-- **Proposition 9.6 at a named constant and threshold.** Let `Cbox ≥ 0` bound the safe-box
entropy at clearance `2R + 11` by `Cbox r^(1 + ε_box)`. Subdivision gives the same estimate at
clearance `2R + 10` with the constant `collarBoxConstant q Cbox`. Then for every real clearance
`D₀ > 2R + 10` and every template constant `Ctpl ≥ 24`, all assertions of the sublinear collar
bound hold with the constant `sublinearCollarConstant q J Δ Cbox` from the threshold
`sublinearCollarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een` on. The truncation constant
`Ctr` and the transport constants `ct, Cent, eent, Cen, een` are existential; they depend only
on `q, R, J, Δ`.

Source: area-law Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943, with the real
safety parameter of `02-initial.tex`, line 225, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem sublinearCollarBound_real_of_boxEntropy
    (q R : ℕ) (hq : 1 ≤ q) {J Δ D₀ Ctpl Cbox : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hD₀ : 2 * (R : ℝ) + 10 < D₀)
    (hCtpl : 24 ≤ Ctpl) (hCbox : 0 ≤ Cbox)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ (2 * R + 11) r ≤
      Cbox * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ))) :
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
      ∀ n s₀ : ℕ, sublinearCollarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een ≤ n →
        ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
          ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            ∀ A : Finset (Site Λ), ∀ T : Geometry.Template Ctpl n s₀,
              T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) →
              ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s₀ →
              FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                  (A.filter fun x ↦ x.val ∈ T.points)
                  (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                    ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
                sublinearCollarConstant q J Δ Cbox *
                  (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) ∧
              ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤
                sublinearCollarConstant q J Δ Cbox * n ∧
              ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
                sublinearCollarConstant q J Δ Cbox * n ∧
              ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                  A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤
                sublinearCollarConstant q J Δ Cbox * n ∧
              ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
                sublinearCollarConstant q J Δ Cbox * (n : ℝ) ^ 2 := by
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, htr⟩ := Scan.CollarScan.exists_finiteFamilyTransportBound
  exact ⟨_, c₀, Cent, eent, Cen, een,
    latticeTruncationRadiusConstant_pos R hΔ (by norm_num : (0 : ℝ) ≤ 10), hc₀,
    sublinearCollarBound_real_of_boxEntropy_explicit q R hq hJ hΔ hD₀ hCtpl hCbox hbox hc₀ htr⟩

/-- **Proposition 9.6 from an initial safe-box estimate, at named constants.** From an initial
bound `C₀ r^(1 + e₀)` on the safe-box entropy, uniform over clearances greater than `2R + 10`,
with `0 ≤ C₀` and `0 < e₀ < 1`, the safe-box bootstrap gives the constant
`Cbox = physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀` at the
improved exponent, and `sublinearCollarBound_real_of_boxEntropy` at this `Cbox` gives all
assertions of the sublinear collar bound with the constant `sublinearCollarConstant q J Δ Cbox`
from the threshold `sublinearCollarThreshold q R J Δ Cbox Ctr' ct' Cent' eent' Cen' een'` on.
The two families of truncation and transport constants are existential and depend only on
`q, R, J, Δ, C₀` and `e₀`.

Source: area-law Propositions 9.5 and 9.6, `08-scanner.tex`, lines 681–805, 808–827 and
942–943. -/
theorem sublinearCollarBound_real_of_initial
    (q R : ℕ) (hq : 1 ≤ q) {J Δ D₀ Ctpl C₀ e₀ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hD₀ : 2 * (R : ℝ) + 10 < D₀)
    (hCtpl : 24 ≤ Ctpl) (hC₀ : 0 ≤ C₀) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (hinitial : ∀ D : ℕ, 2 * R + 10 < D →
      ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D r ≤ C₀ * (r : ℝ) ^ (1 + e₀)) :
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
    ∃ Ctr' ct' Cent' eent' Cen' een' : ℝ, 0 < Ctr' ∧ 0 < ct' ∧
      ∀ n s₀ : ℕ, sublinearCollarThreshold q R J Δ
          (Scan.physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀)
          Ctr' ct' Cent' eent' Cen' een' ≤ n →
        ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
          ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            ∀ A : Finset (Site Λ), ∀ T : Geometry.Template Ctpl n s₀,
              T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) →
              ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s₀ →
              FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                  (A.filter fun x ↦ x.val ∈ T.points)
                  (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                    ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
                sublinearCollarConstant q J Δ
                  (Scan.physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀) *
                    (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) ∧
              ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤
                sublinearCollarConstant q J Δ
                  (Scan.physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀) *
                    n ∧
              ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
                sublinearCollarConstant q J Δ
                  (Scan.physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀) *
                    n ∧
              ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                  A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤
                sublinearCollarConstant q J Δ
                  (Scan.physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀) *
                    n ∧
              ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
                sublinearCollarConstant q J Δ
                  (Scan.physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀) *
                    (n : ℝ) ^ 2 := by
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, hboot⟩ :=
    Scan.exists_boxEntropy_le_boxError_of_initial q R hq hJ hΔ hC₀ he₀ he₀₁ hinitial
  have hCbox :
      0 ≤ Scan.physicalBoxBootstrapConstant q R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een C₀ :=
    Scan.boxBootstrapConstant_nonneg (Real.log_nonneg (by exact_mod_cast hq)) hC₀
      (fun _ hC ↦ (Scan.boxImprovementConstant_pos hq R he₀ he₀₁ J Δ Ctr ct Cent eent Cen een
        hC).le) _
  exact ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct,
    sublinearCollarBound_real_of_boxEntropy q R hq hJ hΔ hD₀ hCtpl hCbox
      (hboot _ (by omega))⟩

/-- The sublinear collar bound for every real clearance allowed by the source.
Source: area-law Proposition 9.6, `08-scanner.tex`, lines 808–827 and 942–943,
with the real safety parameter of `02-initial.tex`, line 225, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The original-state information estimate follows from the physical safe-box
bootstrap and the proved integer-clearance comparison. -/
theorem sublinearCollarBound_real
    (q R : ℕ) (hq : 1 ≤ q) {J Δ D₀ Ctpl : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hD₀ : 2 * (R : ℝ) + 10 < D₀)
    (hCtpl : 24 ≤ Ctpl) :
    SublinearCollarBound q R J Δ D₀ Ctpl := by
  obtain ⟨Cb, hCb, hbox⟩ := Scan.exists_boxEntropy_le_boxError q R hq hJ hΔ
  obtain ⟨_, _, _, _, _, _, _, _, hcol⟩ :=
    sublinearCollarBound_real_of_boxEntropy q R hq hJ hΔ hD₀ hCtpl hCb.le (hbox _ (by omega))
  exact ⟨_, _, hcol⟩

/-- **Proposition 9.6 at explicit constants.** For every real clearance `D₀ > 2R + 10` and every
template constant `Ctpl ≥ 24`, all assertions of the sublinear collar bound
`SublinearCollarBound q R J Δ D₀ Ctpl` hold with the constant
`C₁ = sublinearCollarConstant q J Δ Cbox` from the threshold
`N₁ = sublinearCollarThreshold q R J Δ Cbox (latticeTruncationRadiusConstant R J Δ 10) c₀ Cent
eent Cen een` on, where `Cbox = Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een` is
the safe-box constant of Proposition 9.5 bootstrapped from the explicit initial box estimate at
the truncation constant `latticeTruncationRadiusConstant R J Δ 2`. The single transport tuple
`c₀, Cent, eent, Cen, een`, with `0 < c₀` and the finite-family transport bound, serves both the
safe-box bootstrap and the collar scanner; QICLean's universal transport constants are one such
tuple. Source: area-law Propositions 9.5 and 9.6, `08-scanner.tex`, lines 681–805, 808–827 and
942–943, with the real safety parameter of `02-initial.tex`, line 225. -/
theorem sublinearCollarBound_real_explicit
    (q R : ℕ) (hq : 1 ≤ q) {J Δ D₀ Ctpl : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hD₀ : 2 * (R : ℝ) + 10 < D₀)
    (hCtpl : 24 ≤ Ctpl) (c₀ Cent eent Cen een : ℝ) (hc₀ : 0 < c₀)
    (htr : Scan.CollarScan.FiniteFamilyTransportBound c₀ Cent eent Cen een) :
    ∀ n s₀ : ℕ, sublinearCollarThreshold q R J Δ
        (Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een)
        (latticeTruncationRadiusConstant R J Δ 10) c₀ Cent eent Cen een ≤ n →
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
        ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ A : Finset (Site Λ), ∀ T : Geometry.Template Ctpl n s₀,
            T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) →
            ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s₀ →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                (A.filter fun x ↦ x.val ∈ T.points)
                (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
              sublinearCollarConstant q J Δ
                  (Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een) *
                (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) ∧
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤
              sublinearCollarConstant q J Δ
                (Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een) * n ∧
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
              sublinearCollarConstant q J Δ
                (Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een) * n ∧
            ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤
              sublinearCollarConstant q J Δ
                (Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een) * n ∧
            ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
              sublinearCollarConstant q J Δ
                (Scan.physicalBoxConstantExplicit q R J Δ c₀ Cent eent Cen een) * (n : ℝ) ^ 2 :=
  sublinearCollarBound_real_of_boxEntropy_explicit q R hq hJ hΔ hD₀ hCtpl
    (Scan.physicalBoxConstantExplicit_nonneg q R hq hJ hΔ c₀ Cent eent Cen een)
    (Scan.boxEntropy_le_boxError_explicit q R hq hJ hΔ hc₀ htr _ (by omega)) hc₀ htr

end TNLean.PEPS.AreaLaw
