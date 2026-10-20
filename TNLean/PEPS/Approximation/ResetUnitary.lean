/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GaussianFilter.PhysicalBufferUniform
import QICLean.Analysis.GaussianFilter.LocalizationParameters
import QICLean.Analysis.GaussianFilter.Reindex
import QICLean.Entropy.FiniteProductSplitting
import QICLean.Entropy.ProductMarginals
import TNLean.PEPS.Approximation.SupportedPhysicalBufferGaussian
import TNLean.Lattice.RegionalReset

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
* `TNLean.PEPS.Approximation.SquareHamiltonian.reset_localized_filter`,
  `TNLean.PEPS.Approximation.SquareHamiltonian.reset_unitary`: the statements below with
  these constants.
* `TNLean.PEPS.Approximation.SquareHamiltonian.exists_reset_localized_filter`: the localized
  two-sided filter of `eq:info-local-two-sided`.
* `TNLean.PEPS.Approximation.SquareHamiltonian.exists_reset_unitary`: the unitary of
  `eq:info-reset-unitary`.

The steps that do not depend on the geometry of the sites are stated in
`TNLean.Lattice.RegionalReset`: the regional swap in the coordinates of the two regions and the
buffer, the Gaussian coefficients `TNLean.Lattice.resetVariance` and
`TNLean.Lattice.resetCutoff`, the two-sided Gaussian filter
`TNLean.Lattice.exists_regional_physicalBuffer_filter` of `eq:info-gaussian-two-sided` in
arbitrary coordinates of the two replicas, and the polar step
`TNLean.Lattice.exists_supported_unitary_of_two_sided` of `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`,
  lines 355–599, equations `eq:info-reset-overlap`, `eq:info-gaussian-two-sided`,
  `eq:info-local-two-sided`, `eq:info-reset-polar-errors` and `eq:info-reset-unitary`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix MeasureTheory ProbabilityTheory QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator NNReal ComplexOrder
open TNLean.Lattice

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
The statement of `SquareHamiltonian.exists_reset_localized_filter` holds with the radius
coefficient `K = resetRadius J Δ r` and the residual prefactor
`C = resetFilterPrefactor J Δ r`. They are built from the localization prefactor and
velocity of the doubled square Hamiltonian, the decay rate `1/2`, and the Gaussian cutoff
`T₀ = resetCutoff Δ r`.
Source: `02-information.tex`, lines 355–562, with `K_loc` at lines 551–554. -/
theorem SquareHamiltonian.reset_localized_filter (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
      h.IsGappedGroundState E₀ Ω Δ →
      ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C₀ ≤ b →
      let Q := (R ∪ C₀)ᶜ
      let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
      let Λ := AreaLaw.rectangularDomain L L
      let a := AreaLaw.rectangleSiteEquiv L L
      let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
      let F := reindex (p.trans e) (p.trans e) (TNLean.Lattice.sheetSwapOp q R)
      let ψ : Lattice.Configuration Λ (q * q) → ℂ := fun c ↦
        Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
      let boundary : Finset (Edge (squareLatticeGraph L L)) :=
        Finset.univ.filter (IsRegionBoundaryEdge R)
      let Z := boundary.biUnion fun x ↦
        ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
      let B := Lattice.graphNeighborhood Λ ⌈resetRadius J Δ r * (1 + b + Real.log L)⌉₊
        (Q.image a ∪ Z.image a)
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
      ∃ (z : ℝ) (M : Matrix (Lattice.Configuration Λ (q * q))
          (Lattice.Configuration Λ (q * q)) ℂ),
        Real.exp (-2 * b) ≤ z ∧
        M ∈ supportedOperators (q * q) (B : Set (Lattice.Site Λ)) ∧ ‖M‖ ≤ 1 ∧
        ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
          resetFilterPrefactor J Δ r * Real.exp (-10 * b) * (L : ℝ) ^ (-r) ∧
        ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
          resetFilterPrefactor J Δ r * Real.exp (-10 * b) * (L : ℝ) ^ (-r) := by
  intro L hL h E₀ Ω hgs R C₀ hRC b hb hI Q p Λ a e F ψ boundary Z B
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
    regional_physicalBuffer_filter.{0, 0} hΔ hr q R C₀ hRC (p.trans e) h.operator E₀ Ω b hgs
      hb hI
  obtain ⟨hT, hfwd, hrev⟩ := hfil L hL1
  obtain ⟨U, -, -, -, -, hM⟩ := SquareHamiltonian.supported_buffer_gaussian_integral q hq J hJ
    L h R C₀ hRC W ⌈K * (1 + b + Real.log L)⌉₊
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
  obtain ⟨h₁, h₂⟩ := norm_two_sided_le_of_norm_sub_le hψn hφn (hMerr.trans hδ) hfwd hrev
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
theorem SquareHamiltonian.exists_reset_localized_filter (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C₀ ≤ b →
        let Q := (R ∪ C₀)ᶜ
        let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
        let Λ := AreaLaw.rectangularDomain L L
        let a := AreaLaw.rectangleSiteEquiv L L
        let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
        let F := reindex (p.trans e) (p.trans e) (TNLean.Lattice.sheetSwapOp q R)
        let ψ : Lattice.Configuration Λ (q * q) → ℂ := fun c ↦
          Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun x ↦
          ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
        let B := Lattice.graphNeighborhood Λ ⌈K * (1 + b + Real.log L)⌉₊
          (Q.image a ∪ Z.image a)
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ (z : ℝ) (M : Matrix (Lattice.Configuration Λ (q * q))
            (Lattice.Configuration Λ (q * q)) ℂ),
          Real.exp (-2 * b) ≤ z ∧
          M ∈ supportedOperators (q * q) (B : Set (Lattice.Site Λ)) ∧ ‖M‖ ≤ 1 ∧
          ‖WithLp.toLp 2 (M *ᵥ ψ) - (z : ℂ) • WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
            C * Real.exp (-10 * b) * (L : ℝ) ^ (-r) ∧
          ‖WithLp.toLp 2 (Mᴴ *ᵥ (F *ᵥ ψ)) - (z : ℂ) • WithLp.toLp 2 ψ‖ ≤
            C * Real.exp (-10 * b) * (L : ℝ) ^ (-r) :=
  ⟨resetFilterPrefactor J Δ r, resetRadius J Δ r, resetFilterPrefactor_pos hJ hΔ hr,
    resetRadius_pos hJ hΔ hr, SquareHamiltonian.reset_localized_filter q hq J hJ hΔ hr⟩

/-- **The unitary of the information reset, with explicit constants.** The statement of
`SquareHamiltonian.exists_reset_unitary` holds with the radius coefficient
`K = resetRadius J Δ r` and the error prefactor `C = resetUnitaryPrefactor J Δ r`, twice the
residual prefactor of the localized filter.
Source: `02-information.tex`, lines 563–599, equations `eq:info-reset-polar-errors` and
`eq:info-reset-unitary`. -/
theorem SquareHamiltonian.reset_unitary (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
      h.IsGappedGroundState E₀ Ω Δ →
      ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
      FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C₀ ≤ b →
      let Q := (R ∪ C₀)ᶜ
      let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
      let Λ := AreaLaw.rectangularDomain L L
      let a := AreaLaw.rectangleSiteEquiv L L
      let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
      let F := reindex (p.trans e) (p.trans e) (TNLean.Lattice.sheetSwapOp q R)
      let ψ : Lattice.Configuration Λ (q * q) → ℂ := fun c ↦
        Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
      let boundary : Finset (Edge (squareLatticeGraph L L)) :=
        Finset.univ.filter (IsRegionBoundaryEdge R)
      let Z := boundary.biUnion fun x ↦
        ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
      let B := Lattice.graphNeighborhood Λ ⌈resetRadius J Δ r * (1 + b + Real.log L)⌉₊
        (Q.image a ∪ Z.image a)
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
      ∃ U : Matrix (Lattice.Configuration Λ (q * q)) (Lattice.Configuration Λ (q * q)) ℂ,
        U ∈ unitaryGroup (Lattice.Configuration Λ (q * q)) ℂ ∧
        U ∈ supportedOperators (q * q) (B : Set (Lattice.Site Λ)) ∧
        ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤
            resetUnitaryPrefactor J Δ r * (L : ℝ) ^ (-r) := by
  intro L hL h E₀ Ω hgs R C₀ hRC b hb hI Q p Λ a e F ψ boundary Z B
  obtain ⟨hψn, hφn, z, M, hz, hMsupp, -, hfwd, hrev⟩ :=
    SquareHamiltonian.reset_localized_filter q hq J hJ hΔ hr L hL h E₀ Ω hgs R C₀ hRC b hb hI
  obtain ⟨U, hU, hUsupp, hUerr⟩ := exists_supported_unitary_of_two_sided B hMsupp hb hz hfwd hrev
    (resetFilterPrefactor_pos hJ hΔ hr).le (by positivity)
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
theorem SquareHamiltonian.exists_reset_unitary (q : ℕ) (hq : 1 ≤ q) (J : ℝ)
    (hJ : 0 ≤ J) {Δ r : ℝ} (hΔ : 0 < Δ) (hr : 0 ≤ r) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ (R C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C₀ → ∀ b : ℝ, 0 ≤ b →
        FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C₀ ≤ b →
        let Q := (R ∪ C₀)ᶜ
        let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
        let Λ := AreaLaw.rectangularDomain L L
        let a := AreaLaw.rectangleSiteEquiv L L
        let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
        let F := reindex (p.trans e) (p.trans e) (TNLean.Lattice.sheetSwapOp q R)
        let ψ : Lattice.Configuration Λ (q * q) → ℂ := fun c ↦
          Ω ((p.trans e).symm c).1 * Ω ((p.trans e).symm c).2
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun x ↦
          ({x.1.1, x.1.2} : Finset (SquareLatticeVertex L L))
        let B := Lattice.graphNeighborhood Λ ⌈K * (1 + b + Real.log L)⌉₊
          (Q.image a ∪ Z.image a)
        ‖WithLp.toLp 2 ψ‖ = 1 ∧ ‖WithLp.toLp 2 (F *ᵥ ψ)‖ = 1 ∧
        ∃ U : Matrix (Lattice.Configuration Λ (q * q)) (Lattice.Configuration Λ (q * q)) ℂ,
          U ∈ unitaryGroup (Lattice.Configuration Λ (q * q)) ℂ ∧
          U ∈ supportedOperators (q * q) (B : Set (Lattice.Site Λ)) ∧
          ‖WithLp.toLp 2 (U *ᵥ ψ) - WithLp.toLp 2 (F *ᵥ ψ)‖ ≤ C * (L : ℝ) ^ (-r) :=
  ⟨resetUnitaryPrefactor J Δ r, resetRadius J Δ r, resetUnitaryPrefactor_pos hJ hΔ hr,
    resetRadius_pos hJ hΔ hr, SquareHamiltonian.reset_unitary q hq J hJ hΔ hr⟩

end TNLean.PEPS.Approximation
