/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.MutualInformation.PhysicalBuffer
import QICLean.Analysis.Parameter.LocalizationParameters
import QICLean.Spectral.Filter.Gaussian.Reindex
import QICLean.ManyBody.Entropy.RegionPurificationSplitting
import QICLean.Entropy.MutualInformation.ProductMarginals
import TNLean.PEPS.Approximation.DoubledHamiltonian.SupportedPhysicalBufferGaussian
import TNLean.PEPS.Approximation.DoubledHamiltonian.TwoSheetBufferFilter
import QICLean.Spectral.Perturbation.ResidualComparison
import QICLean.ManyBody.Entropy.RegionalReset
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import QICLean.ManyBody.Sites.SupportedUnitary

/-!
# The supported unitary of the information reset

Let `Ω` be a gapped ground state of an open square Hamiltonian, and let `R, C` be disjoint
physical regions with `I_Ω(R : C) ≤ b`. On two replicas put `Ψ = Ω ⊗ Ω` and `Φ = F_R Ψ`,
where `F_R` exchanges the replicas on `R`. With `B = 1 + b + log L`, this module constructs a
unitary `U` on the doubled system with

* `U` acting on the graph neighborhood of radius `ℓ = ⌈K B⌉` of the buffer `Q = (R ∪ C)ᶜ` and
  of the endpoints of the edges crossing `R`;
* `‖U Ψ - Φ‖ ≤ C L^(-r)`.

The constants `C, K` depend only on `q, J, Δ` and the exponent `r`, and are named:
`K = resetRadius J Δ r` and `C = resetUnitaryPrefactor J Δ r`, built from the Gaussian
variance and cutoff coefficients `resetVariance Δ r` and `resetCutoff Δ r` and from the
localization prefactor and velocity of the doubled square Hamiltonian. No gap of a restricted
Hamiltonian, rank bound or bound on purifying dimensions is assumed.

The proof composes the physical-buffer Gaussian filter, its dimension-uniform parameter
choice, the localization of the truncated Gaussian integral on the square, and the polar
correction on the same support. It first identifies the regional mutual information with the
relative entropy of the joint regional state from the product of its marginals, and the
regional sheet swap with the partial swap of the retained regional registers.

## Main statements

* `TNLean.PEPS.Approximation.resetRadius`, `TNLean.PEPS.Approximation.resetFilterPrefactor`,
  `TNLean.PEPS.Approximation.resetUnitaryPrefactor`: the constants of the reset.
* `ManyBody.SquareInteraction.reset_localized_filter`,
  `ManyBody.SquareInteraction.reset_unitary`: the statements below with
  these constants.
* `ManyBody.SquareInteraction.exists_reset_localized_filter`: the localized
  two-sided filter of `eq:info-local-two-sided`.
* `ManyBody.SquareInteraction.exists_reset_unitary`: the unitary of
  `eq:info-reset-unitary`.

The steps that do not depend on the geometry of the sites are QICLean's: the Gaussian
coefficients `GaussianFilter.resetVariance` and `GaussianFilter.resetCutoff`, the two-sided
Gaussian filter `GaussianFilter.regional_physicalBuffer_filter` of `eq:info-gaussian-two-sided`
on two replicas, read on the two sheets by
`TNLean.PEPS.Approximation.regional_physicalBuffer_filter_twoSheet`, and the polar step
`ManyBody.exists_supported_unitary_of_two_sided` of `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`,
  lines 355–599, equations `eq:info-reset-overlap`, `eq:info-gaussian-two-sided`,
  `eq:info-local-two-sided`, `eq:info-reset-polar-errors` and `eq:info-reset-unitary`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph SquareInteraction)

open Matrix MeasureTheory ProbabilityTheory QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator NNReal ComplexOrder

open ManyBody (IsGapped groundSpace)

open GaussianFilter (resetCutoff resetCutoff_pos resetVariance)

namespace TNLean.PEPS.Approximation

/-! ### The constants of the information reset -/

/-- The localization radius coefficient `K = (v T₀ + 15 + r) / μ` of the information reset,
with the velocity `v = squareLocalizationVelocity J`, the decay rate `μ = 1/2` and the
cutoff `T₀ = resetCutoff Δ r`; the support radius at size `L` is `⌈K (1 + b + log L)⌉`.
Source: `K_loc` of `02-information.tex`, lines 551–554, chosen after `T₀`. -/
noncomputable def resetRadius (J Δ r : ℝ) : ℝ :=
  (squareLocalizationVelocity J * resetCutoff Δ r + 15 + r) / (1 / 2)

/-- The prefactor `C' (1 + 8J) (1 + T₀) + 3` of the two residuals of the localized filter of
the information reset, with `C' = squareLocalizationPrefactor`, `T₀ = resetCutoff Δ r`. The
summand `3` bounds the Gaussian and truncation errors, the rest the localization error.
Source: `02-information.tex`, lines 551–562, equation `eq:info-local-two-sided`. -/
noncomputable def resetFilterPrefactor (J Δ r : ℝ) : ℝ :=
  squareLocalizationPrefactor * (1 + 8 * J) * (1 + resetCutoff Δ r) + 3

/-- The prefactor `2 C` of the error `‖U Ψ - Φ‖ ≤ 2 C L^(-r)` of the unitary of the
information reset, with `C = resetFilterPrefactor J Δ r`.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
noncomputable def resetUnitaryPrefactor (J Δ r : ℝ) : ℝ := 2 * resetFilterPrefactor J Δ r

theorem resetRadius_pos {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    0 < resetRadius J Δ r := by
  have := squareLocalizationVelocity_nonneg hJ
  have := resetCutoff_pos hΔ hr
  unfold resetRadius; positivity

theorem resetFilterPrefactor_pos {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    0 < resetFilterPrefactor J Δ r := by
  have := squareLocalizationPrefactor_pos
  have := resetCutoff_pos hΔ hr
  unfold resetFilterPrefactor; positivity

theorem resetUnitaryPrefactor_pos {J Δ r : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    0 < resetUnitaryPrefactor J Δ r :=
  mul_pos two_pos (resetFilterPrefactor_pos hJ hΔ hr)

/-- The closed form `K = 1280 e² (J/Δ)(30 + r) + 2 r + 30` of the localization radius
coefficient of the information reset. -/
theorem resetRadius_eq (J Δ r : ℝ) :
    resetRadius J Δ r = 1280 * Real.exp 2 * (J / Δ) * (30 + r) + 2 * r + 30 := by
  rw [resetRadius, squareLocalizationVelocity_eq, resetCutoff]
  ring

/-- The closed form of the unitary prefactor of the information reset,
`2 (64 e^{3/2} / (1 - e^{-1/2}) (1 + 8J) (1 + 2 (30 + r) / Δ) + 3)`. -/
theorem resetUnitaryPrefactor_eq (J Δ r : ℝ) :
    resetUnitaryPrefactor J Δ r =
      2 * (64 * Real.exp (3 / 2) / (1 - Real.exp (-(1 / 2))) * (1 + 8 * J) *
        (1 + 2 * (30 + r) / Δ) + 3) := by
  rw [resetUnitaryPrefactor, resetFilterPrefactor, squareLocalizationPrefactor_eq, resetCutoff]

/-- **The localized two-sided filter of the information reset, with explicit constants.**
The statement of `ManyBody.SquareInteraction.exists_reset_localized_filter` holds with the radius
coefficient `K = resetRadius J Δ r` and the residual prefactor
`C = resetFilterPrefactor J Δ r`. They are built from the localization prefactor and
velocity of the doubled square Hamiltonian, the decay rate `1/2`, and the Gaussian cutoff
`T₀ = resetCutoff Δ r`.
Source: `02-information.tex`, lines 355–562, with `K_loc` at lines 551–554. -/
theorem _root_.ManyBody.SquareInteraction.reset_localized_filter (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
        (_ : ∀ i, ‖h.term i‖ ≤ J) (E₀ : ℝ) (Ω : StateSpace L q),
      ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
      ManyBody.regionMutualInformation Ω R C₀ ≤ b →
      let Q := (R ∪ C₀)ᶜ
      let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q)
        fun _ ↦ Fin q
      let p := pr.symm.trans
        (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
      let Λ := ManyBody.rectangularDomain L L
      let a := ManyBody.rectangleSiteEquiv L L
      let e := ManyBody.rectangleConfigurationEquiv L L (q * q)
      let F := reindex (p.trans e) (p.trans e) (reindex pr pr (ManyBody.pairSwapOp R))
      let ψ : (↥Λ → Fin (q * q)) → ℂ := fun c ↦
        Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
      let boundary : Finset (Edge (squareLatticeGraph L L)) :=
        Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R)
      let Z := boundary.biUnion fun x ↦
        ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
      let B := ManyBody.graphNeighborhood (ManyBody.planeDomainGraph Λ) (Q.image a ∪ Z.image a)
        ⌈resetRadius J Δ r * (1 + b + Real.log L)⌉₊
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
      ∃ (z : ℝ) (M : Matrix (↥Λ → Fin (q * q))
          (↥Λ → Fin (q * q)) ℂ),
        Real.exp (-2 * b) ≤ z ∧
        M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧ ‖M‖ ≤ 1 ∧
        ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
          resetFilterPrefactor J Δ r * Real.exp (-10 * b) * (L : ℝ) ^ (-r) ∧
        ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
          resetFilterPrefactor J Δ r * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by
  intro L hL h hh hhJ E₀ Ω hΩ hgap hspan R C₀ hRC b hb hI Q pr p Λ a e F ψ boundary Z B
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hcoef : squareLocalizationVelocity J * resetCutoff Δ r + 15 + r ≤
      1 / 2 * resetRadius J Δ r := by
    rw [resetRadius]; apply le_of_eq; ring
  set Cg := squareLocalizationPrefactor with hCgdef
  set v := squareLocalizationVelocity J with hvdef
  set T₀ := resetCutoff Δ r with hT₀def
  set K := resetRadius J Δ r with hKdef
  have hCg : 0 < Cg := squareLocalizationPrefactor_pos
  have hT₀ : 0 < T₀ := resetCutoff_pos hΔ hr
  obtain ⟨hψn, hφn, W, z, hW, hz, hfil⟩ :=
    regional_physicalBuffer_filter_twoSheet.{0, 0} hΔ hr q R C₀ hRC (p.trans e) h.hamiltonian E₀ Ω b
      hh hΩ hgap hspan hb hI
  obtain ⟨hT, hfwd, hrev⟩ := hfil L hL1
  obtain ⟨U, -, -, -, -, hM⟩ :=
      ManyBody.SquareInteraction.supported_buffer_gaussian_integral q hq J hJ
    L h hh hhJ R C₀ hRC W ⌈K * (1 + b + Real.log L)⌉₊
  obtain ⟨hMsupp, hMnorm, hMerr⟩ := hM (Real.toNNReal (resetVariance Δ r * (1 + b + Real.log L)))
    (T₀ * (1 + b + Real.log L)) hT
  have hlocb := GaussianFilter.localization_error_bound_of_parameter_constant (L := (L : ℝ))
    (C := Cg * (1 + 8 * J)) hT₀.le (by norm_num : (0 : ℝ) ≤ 1 / 2) hr hcoef hb hL1
    (by positivity)
  have hT₀B : 0 ≤ 1 + b + Real.log L := by
    have := Real.log_nonneg hL1
    linarith
  have hδ : ‖W‖ * Cg * (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L))) *
      Real.exp (v * (T₀ * (1 + b + Real.log L)) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) ≤
      Cg * (1 + 8 * J) * (1 + T₀) * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by
    refine le_trans ?_ hlocb
    have hTB : 0 ≤ T₀ * (1 + b + Real.log L) := mul_nonneg hT₀.le hT₀B
    have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
    have hpoly : (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L))) ≤
        (1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L)) := by
      set T' := T₀ * (1 + b + Real.log L)
      have hL4 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 * (1 + T') := by
        have h₁ : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 := by
          rw [show (L : ℝ) ^ 4 = (L : ℝ) ^ 2 * (L : ℝ) ^ 2 by ring]
          exact le_mul_of_one_le_right (by positivity) hL2
        exact h₁.trans (le_mul_of_one_le_right (by positivity) (by linarith))
      have h8 : 8 * J * (L : ℝ) ^ 4 * T' ≤ 8 * J * (L : ℝ) ^ 4 * (1 + T') :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * T')
          = (L : ℝ) ^ 2 + 8 * J * (L : ℝ) ^ 4 * T' := by ring
        _ ≤ (L : ℝ) ^ 4 * (1 + T') + 8 * J * (L : ℝ) ^ 4 * (1 + T') := add_le_add hL4 h8
        _ = (1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T') := by ring
    rw [show v * (T₀ * (1 + b + Real.log L)) = v * T₀ * (1 + b + Real.log L) by ring]
    calc ‖W‖ * Cg * (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L))) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊)
        = ‖W‖ * Cg * ((L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * (T₀ * (1 + b + Real.log L)))) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by ring
      _ ≤ 1 * Cg * ((1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L))) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by
          gcongr
      _ = Cg * (1 + 8 * J) * (L : ℝ) ^ 4 * (1 + T₀ * (1 + b + Real.log L)) *
          Real.exp (v * T₀ * (1 + b + Real.log L) - 1 / 2 * ⌈K * (1 + b + Real.log L)⌉₊) := by
          ring
  obtain ⟨h₁, h₂⟩ := Matrix.norm_two_sided_le_of_norm_sub_le (ψ := WithLp.toLp 2 ψ)
    (φ := WithLp.toLp 2 (F *ᵥ ψ)) hψn hφn (hMerr.trans hδ) hfwd hrev
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply] at h₁ h₂
  refine ⟨hψn, hφn, z, _, hz, hMsupp, hMnorm.trans hW, h₁.trans_eq ?_, h₂.trans_eq ?_⟩ <;>
    rw [resetFilterPrefactor, ← hCgdef, ← hT₀def] <;> ring

/-- **The localized two-sided filter of the information reset.** For a gap `Δ > 0` and an
exponent `r ≥ 0` there are constants `C, K` with the following property. Let `Ω` be a gapped
ground state of an open square Hamiltonian, `R, C₀` disjoint regions with
`I_Ω(R : C₀) ≤ b`, and `B = 1 + b + log L`. On the paired sites put `Ψ = Ω ⊗ Ω` and
`Φ = F_R Ψ`. Then there are a real `z ≥ exp (-2 b)` and a contraction `M` acting on the
graph neighborhood of radius `⌈K B⌉` of the buffer and of the endpoints of the edges crossing
`R`, with `‖M Ψ - z Φ‖` and `‖Mᴴ Φ - z Ψ‖` at most `C exp (-10 b) L^(-r)`.
Source: `02-information.tex`, lines 355–562, equations `eq:info-reset-overlap` and
`eq:info-local-two-sided`. -/
theorem _root_.ManyBody.SquareInteraction.exists_reset_localized_filter (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
          (_ : ∀ i, ‖h.term i‖ ≤ J) (E₀ : ℝ) (Ω : StateSpace L q),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
        ManyBody.regionMutualInformation Ω R C₀ ≤ b →
        let Q := (R ∪ C₀)ᶜ
        let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q)
          fun _ ↦ Fin q
        let p := pr.symm.trans
          (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
        let Λ := ManyBody.rectangularDomain L L
        let a := ManyBody.rectangleSiteEquiv L L
        let e := ManyBody.rectangleConfigurationEquiv L L (q * q)
        let F := reindex (p.trans e) (p.trans e) (reindex pr pr (ManyBody.pairSwapOp R))
        let ψ : (↥Λ → Fin (q * q)) → ℂ := fun c ↦
          Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun x ↦
          ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
        let B := ManyBody.graphNeighborhood (ManyBody.planeDomainGraph Λ)
          (Q.image a ∪ Z.image a) ⌈K * (1 + b + Real.log L)⌉₊
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ (z : ℝ) (M : Matrix (↥Λ → Fin (q * q))
            (↥Λ → Fin (q * q)) ℂ),
          Real.exp (-2 * b) ≤ z ∧
          M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧ ‖M‖ ≤ 1 ∧
          ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
            C * Real.exp (-10 * b) * (L : ℝ) ^ (-r) ∧
          ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
            C * Real.exp (-10 * b) * (L : ℝ) ^ (-r) :=
  ⟨resetFilterPrefactor J Δ r, resetRadius J Δ r, resetFilterPrefactor_pos hJ hΔ hr,
    resetRadius_pos hJ hΔ hr, ManyBody.SquareInteraction.reset_localized_filter q hq J hJ hΔ hr⟩

/-- **The unitary of the information reset, with explicit constants.** The statement of
`ManyBody.SquareInteraction.exists_reset_unitary` holds with the radius coefficient
`K = resetRadius J Δ r` and the error prefactor `C = resetUnitaryPrefactor J Δ r`, twice the
residual prefactor of the localized filter.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
theorem _root_.ManyBody.SquareInteraction.reset_unitary (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
        (_ : ∀ i, ‖h.term i‖ ≤ J) (E₀ : ℝ) (Ω : StateSpace L q),
      ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
      ManyBody.regionMutualInformation Ω R C₀ ≤ b →
      let Q := (R ∪ C₀)ᶜ
      let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q)
        fun _ ↦ Fin q
      let p := pr.symm.trans
        (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
      let Λ := ManyBody.rectangularDomain L L
      let a := ManyBody.rectangleSiteEquiv L L
      let e := ManyBody.rectangleConfigurationEquiv L L (q * q)
      let F := reindex (p.trans e) (p.trans e) (reindex pr pr (ManyBody.pairSwapOp R))
      let ψ : (↥Λ → Fin (q * q)) → ℂ := fun c ↦
        Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
      let boundary : Finset (Edge (squareLatticeGraph L L)) :=
        Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R)
      let Z := boundary.biUnion fun x ↦
        ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
      let B := ManyBody.graphNeighborhood (ManyBody.planeDomainGraph Λ) (Q.image a ∪ Z.image a)
        ⌈resetRadius J Δ r * (1 + b + Real.log L)⌉₊
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
      ∃ U : Matrix (↥Λ → Fin (q * q)) (↥Λ → Fin (q * q)) ℂ,
        U ∈ unitaryGroup (↥Λ → Fin (q * q)) ℂ ∧
        U ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
        ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
            resetUnitaryPrefactor J Δ r * (L : ℝ) ^ (-r) := by
  intro L hL h hh hhJ E₀ Ω hΩ hgap hspan R C₀ hRC b hb hI Q pr p Λ a e F ψ boundary Z B
  obtain ⟨hψn, hφn, z, M, hz, hMsupp, -, hfwd, hrev⟩ :=
    ManyBody.SquareInteraction.reset_localized_filter q hq J hJ hΔ hr L hL h hh hhJ E₀ Ω hΩ hgap
        hspan R C₀ hRC b
      hb hI
  obtain ⟨U, hU, hUsupp, hUerr⟩ := ManyBody.exists_supported_unitary_of_two_sided
    (ψ := WithLp.toLp 2 ψ) (φ := WithLp.toLp 2 (F *ᵥ ψ)) hMsupp hb hz hfwd hrev
  exact ⟨hψn, hφn, U, hU, hUsupp, hUerr⟩

/-- **The unitary of the information reset.** For a gap `Δ > 0` and an exponent `r ≥ 0` there
are constants `C, K` with the following property. Let `Ω` be a gapped ground state of an open
square Hamiltonian, `R, C₀` disjoint regions with `I_Ω(R : C₀) ≤ b`, and
`B = 1 + b + log L`. On the paired sites put `Ψ = Ω ⊗ Ω` and `Φ = F_R Ψ`. Then a unitary
acting on the graph neighborhood of radius `⌈K B⌉` of the buffer and of the endpoints of the
edges crossing `R` satisfies `‖U Ψ - Φ‖ ≤ C L^(-r)`. It is the polar factor of
`M / z` on the same support; the norm `‖M / z‖ ≤ exp (2 b)` is paid by the factor
`exp (-10 b)` of the two-sided errors, and no unitary dilation is used.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
theorem _root_.ManyBody.SquareInteraction.exists_reset_unitary (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareInteraction L q) (_ : h.hamiltonian.IsHermitian)
          (_ : ∀ i, ‖h.term i‖ ≤ J) (E₀ : ℝ) (Ω : StateSpace L q),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
        ManyBody.regionMutualInformation Ω R C₀ ≤ b →
        let Q := (R ∪ C₀)ᶜ
        let pr := Equiv.arrowProdEquivProdArrow (SquareLatticeVertex L L) (fun _ ↦ Fin q)
          fun _ ↦ Fin q
        let p := pr.symm.trans
          (Equiv.arrowCongr (Equiv.refl (SquareLatticeVertex L L)) finProdFinEquiv)
        let Λ := ManyBody.rectangularDomain L L
        let a := ManyBody.rectangleSiteEquiv L L
        let e := ManyBody.rectangleConfigurationEquiv L L (q * q)
        let F := reindex (p.trans e) (p.trans e) (reindex pr pr (ManyBody.pairSwapOp R))
        let ψ : (↥Λ → Fin (q * q)) → ℂ := fun c ↦
          Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (ManyBody.IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun x ↦
          ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
        let B := ManyBody.graphNeighborhood (ManyBody.planeDomainGraph Λ)
          (Q.image a ∪ Z.image a) ⌈K * (1 + b + Real.log L)⌉₊
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ U : Matrix (↥Λ → Fin (q * q)) (↥Λ → Fin (q * q)) ℂ,
          U ∈ unitaryGroup (↥Λ → Fin (q * q)) ℂ ∧
          U ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
          ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ C * (L : ℝ) ^ (-r) :=
  ⟨resetUnitaryPrefactor J Δ r, resetRadius J Δ r, resetUnitaryPrefactor_pos hJ hΔ hr,
    resetRadius_pos hJ hΔ hr, ManyBody.SquareInteraction.reset_unitary q hq J hJ hΔ hr⟩

end TNLean.PEPS.Approximation
