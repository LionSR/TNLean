/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteExpectationOrder
import TNLean.Circuit.LiebRobinson.GraphLocalization
import QICLean.Analysis.SpectralFilter.FilterLocality

/-!
# Positive quasi-local constraints from a global gap

Let `H = ∑ₖ hₖ` be a finite-range interaction on a finite graph, with a unit ground vector
`Ω` and the global gap `H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)`. Filtering each term with the spectral
filter of width `Δ / 2`, centering it at `Ω`, and taking absolute values gives positive
contractions `kᵢ = |Mᵢ| / c_*` with `kᵢ Ω = 0` and `∑ᵢ kᵢ ≥ c_*⁻¹ (H - E₀ I) ≥ g (I - P_Ω)`,
`g = Δ / c_*`. The ball expectations `k_{i,l} = E_{i,l}(kᵢ)` are positive contractions with
`‖kᵢ - k_{i,l}‖ ≤ C e^{-c l^α}`, `α = p / (p + 1)`, and each `kᵢ` acts on the connected
component of its anchor. The constants are chosen before the graph and the interaction.

The spectral part comes from `SpectralFilter.positive_replacement`. The locality estimate
instantiates `SpectralFilter.exists_norm_positiveConstraint_sub_map_le` with the normalized
site expectation onto the graph ball, whose localization hypothesis is
`QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphBall_le`.

The graph is a general finite graph with the support, multiplicity and sphere-growth bounds
used by the propagation estimate; the induced lattice domains of the source satisfy them.

## Main results

* `TNLean.PEPS.AreaLaw.positiveConstraint_mem_supportedOperators_component`: exact support
  in the connected component of the anchor.
* `TNLean.PEPS.AreaLaw.exists_positiveQuasilocalConstraints`: Proposition 4.3.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.3 (`prop:positive`), section file `03-quasilocal.tex`, lines 220–334.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit SpectralFilter

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If every evolved operator `τ_t(A)` commutes with `B`, so does the filtered operator. -/
theorem commute_filterIntegral_of_forall_commute {p : ℕ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    {H A B : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hH : H.IsHermitian)
    (h : ∀ t : ℝ, Commute (Matrix.hermitianUnitaryPath H t * A *
      Matrix.hermitianUnitaryPath H (-t)) B) :
    Commute (filterIntegral p δ H A) B := by
  let Φ : Matrix (ι → Fin q) (ι → Fin q) ℂ →L[ℂ] Matrix (ι → Fin q) (ι → Fin q) ℂ :=
    (ContinuousLinearMap.mul ℂ _).flip B - ContinuousLinearMap.mul ℂ _ B
  have hΦ : ∀ X, Φ X = X * B - B * X := fun X => rfl
  have h0 : Φ (filterIntegral p δ H A) = 0 := by
    rw [filterIntegral, ← Φ.integral_comp_comm (integrable_filterIntegrand hp hδ hH A)]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)).trans (integral_zero ℝ _)
    change Φ ((spectralKernel p δ t : ℂ) • _) = 0
    rw [map_smul, hΦ, (h t).eq, sub_self, smul_zero]
  rw [hΦ, sub_eq_zero] at h0
  exact h0

/-- **Exact component support** (Proposition 4.3, `03-quasilocal.tex`, lines 244–245 and
330–334): each positive constraint acts on the connected component of its anchor. -/
theorem positiveConstraint_mem_supportedOperators_component [NeZero q] {p : ℕ} (hp : 1 ≤ p)
    {δ : ℝ} (hδ : 0 < δ) {κ : Type*} [Fintype κ]
    (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators q (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (c : ℝ) (i : κ) :
    positiveConstraint c (centeredFilter p δ (∑ k, h k) Ω (h i)) ∈
      supportedOperators q {x | G.Reachable (a i) x} := by
  classical
  set H := ∑ k, h k
  have hH : H.IsHermitian := by
    simp only [H, Matrix.IsHermitian, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun k _ => hHerm k
  set C : Set ι := {x | G.Reachable (a i) x}
  have hReach : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.Reachable x z := fun k x hx z hz =>
    SimpleGraph.reachable_of_edist_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top R) (hDiam k x hx z hz))
  have hClosed : ∀ k, (X k : Set ι) ⊆ C ∨ Disjoint (X k : Set ι) C := by
    intro k
    by_cases hk : ∃ x ∈ X k, G.Reachable (a i) x
    · obtain ⟨x, hx, hax⟩ := hk
      exact Or.inl fun z hz => hax.trans (hReach k x hx z hz)
    · push Not at hk
      exact Or.inr (Set.disjoint_left.mpr fun x hx hxC => hk x hx hxC)
  have hXi : (X i : Set ι) ⊆ C := fun z hz => hReach i (a i) (ha i) z hz
  set K : Finset ι := Finset.univ.filter fun x => G.Reachable (a i) x
  have hK : (K : Set ι) = C := by ext x; simp [K, C]
  rw [← hK]
  refine mem_supportedOperators_of_forall_commute K fun B hB => ?_
  rw [hK] at hB
  have hτ : ∀ t : ℝ, Commute (Matrix.hermitianUnitaryPath H t * h i *
      Matrix.hermitianUnitaryPath H (-t)) B := fun t =>
    commute_heisenbergEvolution_of_closed h (fun k => (X k : Set ι)) hSupport C Cᶜ hClosed
      disjoint_compl_right (supportedOperators_mono hXi (hSupport i)) hB t
  have hF := commute_filterIntegral_of_forall_commute hp hδ hH hτ
  have hM : Commute (centeredFilter p δ H Ω (h i)) B :=
    hF.sub_left ((Commute.one_left B).smul_left _)
  have hMh := isHermitian_centeredFilter p δ hH Ω (hHerm i)
  exact (hM.cfcAbs_of_isHermitian hMh).smul_left _

/-- The prefactor of the graph-ball localization estimate, with `|K_g|` in place of `K_g`. -/
noncomputable def localizationPrefactor (R : ℕ) (Kg : ℝ) (kg : ℕ) : ℝ :=
  2 * Real.exp R * |Kg| * (2 ^ kg * kg.factorial * Real.exp (1 / 2) /
    (1 - Real.exp (-(1 / 2))))

theorem localizationPrefactor_nonneg (R : ℕ) (Kg : ℝ) (kg : ℕ) :
    0 ≤ localizationPrefactor R Kg kg := by
  have : 0 < 1 - Real.exp (-(1 / 2) : ℝ) := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : (-(1 / 2) : ℝ) < 0); linarith
  unfold localizationPrefactor; positivity

/-- **Positive replacement of the Hamiltonian** (Proposition 4.3, `prop:positive`,
`03-quasilocal.tex`, lines 220–246). Fix `p ≥ 1`, the range `R`, the support size `v_R`, the
site budget `b₀`, the sphere growth `K_g (d + 1)^{k_g}`, `J ≥ 0` and `Δ > 0`. There are
`C ≥ 0` and `c > 0` such that for every finite graph and every Hermitian interaction family
with these bounds and `‖hₖ‖ ≤ J`, every unit `Ω` with `H Ω = E₀ Ω` and
`H - E₀ I ≥ Δ (I - |Ω⟩⟨Ω|)`: the constraints `kᵢ = |Mᵢ| / c_*` (`δ = Δ / 2`) satisfy
`0 ≤ kᵢ ≤ I`, `kᵢ Ω = 0`, `∑ᵢ kᵢ ≥ c_*⁻¹ (H - E₀ I) ≥ (Δ / c_*) (I - |Ω⟩⟨Ω|)`
(`eq:quasilocal-positive`); for every radius `l` the ball expectation
`k_{i,l} = E_{N_l(aᵢ)}(kᵢ)` lies in `[0, I]` and `‖kᵢ - k_{i,l}‖ ≤ C e^{-c l^α}`
(`eq:quasilocal-positive-tail`); and `kᵢ` acts on the connected component of `aᵢ`. -/
theorem exists_positiveQuasilocalConstraints {p : ℕ} (hp : 1 ≤ p) (R vR : ℕ) (b₀ Kg : ℝ)
    (kg : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
        (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι), (∀ k, a k ∈ X k) →
        ∀ (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ), (∀ k, (h k).IsHermitian) →
        (∀ k, h k ∈ supportedOperators q (X k : Set ι)) →
        (∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R) →
        (∀ k, (X k).card ≤ vR) →
        (∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀) →
        (∀ x (d : ℕ),
          ((Finset.univ.filter fun y => G.edist x y = d).card : ℝ) ≤ Kg * ((d : ℝ) + 1) ^ kg) →
        (∀ k, ‖h k‖ ≤ J) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (ι → Fin q)), ‖Ω‖ = 1 →
        (∑ k, h k) *ᵥ WithLp.ofLp Ω = (E₀ : ℂ) • WithLp.ofLp Ω →
        ((∑ k, h k) - (E₀ : ℂ) • 1 -
          (Δ : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
        let cs := positiveNormalization p (Δ / 2) J
        let k := fun i => positiveConstraint cs (centeredFilter p (Δ / 2) (∑ j, h j) Ω (h i))
        (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) ∧
        cs⁻¹ • ((∑ j, h j) - (E₀ : ℂ) • 1) ≤ ∑ i, k i ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          cs⁻¹ • ((∑ j, h j) - (E₀ : ℂ) • 1) ∧
        (∀ i (l : ℕ), 0 ≤ siteExpectation q (graphBall G (a i) l) (k i) ∧
          siteExpectation q (graphBall G (a i) l) (k i) ≤ 1 ∧
          ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
            C * Real.exp (-(c * (l : ℝ) ^ kernelExponent p))) ∧
        (∀ i, k i ∈ supportedOperators q {x | G.Reachable (a i) x}) := by
  set CL := localizationPrefactor R Kg kg
  set v : ℝ := |2 * vR * b₀ * Real.exp (2 * R)| + 1
  obtain ⟨C₃, c₃, hC₃, hc₃, htail⟩ := exists_norm_positiveConstraint_sub_map_le hp
    (C := CL) (v := v) (c := 1 / 2) hΔ hJ (localizationPrefactor_nonneg R Kg kg)
    (by positivity) (by norm_num)
  refine ⟨C₃, c₃, hC₃, hc₃, ?_⟩
  intro q _ ι _ _ κ _ G X a ha h hHerm hSupport hDiam hCard hBudget hGrowth hJh E₀ Ω hΩ hHΩ
    hgap cs k
  obtain ⟨hk, hsum, hgapk⟩ := positive_replacement hp hΔ hΩ hHΩ hgap h hHerm hJh rfl
  refine ⟨hk, hsum, hgapk, fun i l => ?_, fun i =>
    positiveConstraint_mem_supportedOperators_component hp (half_pos hΔ) G X a ha h hHerm
      hSupport R hDiam Ω cs i⟩
  set H := ∑ j, h j
  have hH : H.IsHermitian := by
    simp only [H, Matrix.IsHermitian, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun j _ => hHerm j
  set K := graphBall G (a i) l
  obtain ⟨hk0, hk1, -⟩ := hk i
  refine ⟨siteExpectation_nonneg K hk0, siteExpectation_le_one K hk1, ?_⟩
  set M := centeredFilter p (Δ / 2) H Ω (h i)
  have hMh : M.IsHermitian := isHermitian_centeredFilter p _ hH Ω (hHerm i)
  have hfix : siteExpectationLM q K (CFC.abs (siteExpectationLM q K M)) =
      CFC.abs (siteExpectationLM q K M) := by
    simp only [siteExpectationLM_apply]
    exact siteExpectation_abs_of_mem_supportedOperators K (isHermitian_siteExpectation K hMh)
      (siteExpectation_mem_supportedOperators K M)
  have hloc : ∀ t : ℝ, ‖Matrix.hermitianUnitaryPath H t * h i *
        Matrix.hermitianUnitaryPath H (-t) - siteExpectationLM q K
          (Matrix.hermitianUnitaryPath H t * h i * Matrix.hermitianUnitaryPath H (-t))‖ ≤
      ‖h i‖ * min 2 (CL * Real.exp (v * |t| - 1 / 2 * (l : ℝ))) := by
    intro t
    have hLR := norm_heisenberg_sub_siteExpectation_graphBall_le G X a ha h hHerm hSupport R
      hDiam vR hCard b₀ hBudget Kg kg hGrowth i (hSupport i) l t
    rw [heisenbergEvolution_eq_hermitianUnitaryPath] at hLR
    refine hLR.trans (mul_le_mul_of_nonneg_left (min_le_min_left _ ?_) (norm_nonneg _))
    have hKg : Kg ≤ |Kg| := le_abs_self Kg
    have hpos : 0 < 1 - Real.exp (-(1 / 2) : ℝ) := by
      have := Real.exp_lt_one_iff.mpr (by norm_num : (-(1 / 2) : ℝ) < 0); linarith
    have hA : 0 ≤ (2 : ℝ) ^ kg * kg.factorial * Real.exp (1 / 2) /
        (1 - Real.exp (-(1 / 2))) := by positivity
    have hexp : Real.exp (2 * vR * b₀ * Real.exp (2 * R) * |t| - l / 2) ≤
        Real.exp (v * |t| - 1 / 2 * (l : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : 2 * vR * b₀ * Real.exp (2 * R) ≤ v := by
        have := le_abs_self (2 * vR * b₀ * Real.exp (2 * R)); simp only [v]; linarith
      have := mul_le_mul_of_nonneg_right h1 (abs_nonneg t)
      linarith
    refine mul_le_mul ?_ hexp (Real.exp_pos _).le (localizationPrefactor_nonneg R Kg kg)
    simp only [CL, localizationPrefactor]
    gcongr
  exact htail hH hΩ (hHerm i) (hJh i) (siteExpectationLM q K) (norm_siteExpectation_le K)
    (siteExpectation_one K) (fun Y hY => isHermitian_siteExpectation K hY) hfix
    (Nat.cast_nonneg l) hloc

end TNLean.PEPS.AreaLaw
