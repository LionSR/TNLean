/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Sites.Twirl
import QICLean.ManyBody.Dynamics.GraphLocalization
import QICLean.ManyBody.Dynamics.CommutatorRecursion
import QICLean.Spectral.Filter.FilterLocality
import QICLean.Analysis.Norm.RootChannel

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
`ManyBody.norm_heisenberg_sub_regionExpectation_graphBall_le`.

The graph is a general finite graph with the support, multiplicity and sphere-growth bounds
used by the propagation estimate; the induced lattice domains of the source satisfy them.

## Main results

* `TNLean.PEPS.AreaLaw.positiveConstraint_mem_supportedOperators_component`: exact support
  in the connected component of the anchor.
* `TNLean.PEPS.AreaLaw.exists_positiveQuasilocalConstraints`: Proposition 4.3.
* `TNLean.PEPS.AreaLaw.sqrt_mul_exp_neg`, `TNLean.PEPS.AreaLaw.quasilocalRoots`: square roots of the
  positive constraints and their local channels.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.3 (`prop:positive`), section file `03-quasilocal.tex`, lines 220–334.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

section PositiveConstraints

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

universe u

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

open Classical in
/-- **Exact component support** (Proposition 4.3, `03-quasilocal.tex`, lines 244–245 and
330–334): each positive constraint acts on the connected component of its anchor. -/
theorem positiveConstraint_mem_supportedOperators_component {p : ℕ} (hp : 1 ≤ p)
    {δ : ℝ} (hδ : 0 < δ) {κ : Type*} [Fintype κ]
    (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (X k : Finset ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (c : ℝ) (i : κ) :
    positiveConstraint c (centeredFilter p δ (∑ k, h k) Ω (h i)) ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q)
          (Finset.univ.filter fun x ↦ G.Reachable (a i) x) := by
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
  have hClosedK : ∀ k, X k ⊆ K ∨ Disjoint (X k) K := fun k => by
    rw [← Finset.coe_subset, ← Finset.disjoint_coe, hK]
    exact hClosed k
  have hiK : h i ∈ ManyBody.supportedOperators (fun _ : ι ↦ Fin q) K :=
    (ManyBody.supportedOperators_mono (by rw [← Finset.coe_subset, hK]; exact hXi) (hSupport i))
  let Φ : ManyBody.Interaction (fun _ : ι ↦ Fin q) X :=
    ⟨h, fun k => (hSupport k)⟩
  refine ManyBody.mem_supportedOperators_iff_forall_commute.mpr fun B hB => ?_
  have hτ : ∀ t : ℝ, Commute (Matrix.hermitianUnitaryPath H t * h i *
      Matrix.hermitianUnitaryPath H (-t)) B := fun t =>
    ManyBody.commute_heisenbergEvolution_of_closed Φ K Kᶜ hClosedK disjoint_compl_right hiK hB t
  have hF := commute_filterIntegral_of_forall_commute hp hδ hH hτ
  have hM : Commute (centeredFilter p δ H Ω (h i)) B :=
    hF.sub_left ((Commute.one_left B).smul_left _)
  have hMh := isHermitian_centeredFilter p δ hH Ω (hHerm i)
  have hA : Commute (CFC.abs (centeredFilter p δ H Ω (h i))) B := by
    rw [CFC.abs_eq_cfc_norm _ hMh.isSelfAdjoint]
    exact hM.cfc_real _
  exact hA.smul_left _

/-- The prefactor of the graph-ball localization estimate, with `|K_g|` in place of `K_g`. -/
noncomputable def localizationPrefactor (R : ℕ) (Kg : ℝ) (kg : ℕ) : ℝ :=
  2 * Real.exp R * |Kg| * (2 ^ kg * kg.factorial * Real.exp (1 / 2) /
    (1 - Real.exp (-(1 / 2))))

theorem localizationPrefactor_nonneg (R : ℕ) (Kg : ℝ) (kg : ℕ) :
    0 ≤ localizationPrefactor R Kg kg := by
  have : 0 < 1 - Real.exp (-(1 / 2) : ℝ) := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : (-(1 / 2) : ℝ) < 0); linarith
  unfold localizationPrefactor; positivity

/-- The time rate `v = |2 v_R b₀ e^{2R}| + 1` of the graph-ball localization estimate
(`eq:quasilocal-lr-ce`, `03-quasilocal.tex`, lines 53–66), raised by one so that it is
positive. It is the velocity fed to the filter-locality estimate in the proof of
Proposition 4.3 (`03-quasilocal.tex`, lines 270–285). -/
noncomputable def localizationVelocity (R vR : ℕ) (b₀ : ℝ) : ℝ :=
  |2 * vR * b₀ * Real.exp (2 * R)| + 1

theorem localizationVelocity_pos (R vR : ℕ) (b₀ : ℝ) : 0 < localizationVelocity R vR b₀ := by
  unfold localizationVelocity; positivity

open Classical in
/-- **Positive replacement of the Hamiltonian, with named constants** (Proposition 4.3,
`prop:positive`, `03-quasilocal.tex`, lines 220–334). Let `C₃, c₃` be the constants of the
filter-locality tail of the positive constraints for the localization constants
`C = localizationPrefactor R K_g k_g`, `v = localizationVelocity R v_R b₀` and `c = 1/2`:
the hypothesis `htail` is the conclusion of
`SpectralFilter.exists_norm_positiveConstraint_sub_map_le` at these constants. Then every
conclusion of `exists_positiveQuasilocalConstraints` holds with `C = C₃` and `c = c₃`.
At `C₃ = positiveConstraintLocalityConst p Δ J (localizationPrefactor R K_g k_g) (1 / 2)` and
`c₃ = positiveConstraintLocalityRate p Δ (localizationVelocity R v_R b₀) (1 / 2)`, `htail` is
`SpectralFilter.norm_positiveConstraint_sub_map_le`; see
`positiveQuasilocalConstraints_explicit`. -/
theorem positiveQuasilocalConstraints_of_locality {p : ℕ} (hp : 1 ≤ p) (R vR : ℕ) (b₀ Kg : ℝ)
    (kg : ℕ) {J Δ C₃ c₃ : ℝ} (hΔ : 0 < Δ)
    (htail : ∀ {n : Type u} [Fintype n] [DecidableEq n]
      {H : Matrix n n ℂ} {Ω : EuclideanSpace ℂ n} {h : Matrix n n ℂ},
      H.IsHermitian → ‖Ω‖ = 1 → h.IsHermitian → ‖h‖ ≤ J →
      ∀ (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ), (∀ X, ‖L X‖ ≤ ‖X‖) → L 1 = 1 →
      (∀ X, X.IsHermitian → (L X).IsHermitian) →
      L (CFC.abs (L (centeredFilter p (Δ / 2) H Ω h))) =
        CFC.abs (L (centeredFilter p (Δ / 2) H Ω h)) →
      ∀ {l : ℝ}, 0 ≤ l →
      (∀ t : ℝ, ‖Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t) -
          L (Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t))‖ ≤
        ‖h‖ * min 2 (localizationPrefactor R Kg kg *
          Real.exp (localizationVelocity R vR b₀ * |t| - 1 / 2 * l))) →
      ‖positiveConstraint (positiveNormalization p (Δ / 2) J) (centeredFilter p (Δ / 2) H Ω h) -
          L (positiveConstraint (positiveNormalization p (Δ / 2) J)
            (centeredFilter p (Δ / 2) H Ω h))‖ ≤
        C₃ * Real.exp (-(c₃ * l ^ kernelExponent p))) :
    ∀ {q : ℕ} [NeZero q] {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
      (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι), (∀ k, a k ∈ X k) →
      ∀ (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ), (∀ k, (h k).IsHermitian) →
      (∀ k, h k ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (X k : Finset ι)) →
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
      (∀ i (l : ℕ), 0 ≤ ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i) ∧
        ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i) ≤ 1 ∧
        ‖k i - ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i)‖ ≤
          C₃ * Real.exp (-(c₃ * (l : ℝ) ^ kernelExponent p))) ∧
      (∀ i, k i ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
          (Finset.univ.filter fun x ↦ G.Reachable (a i) x)) := by
  set CL := localizationPrefactor R Kg kg
  set v := localizationVelocity R vR b₀
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
  set K := ManyBody.graphBall G (a i) l
  obtain ⟨hk0, hk1, -⟩ := hk i
  refine ⟨(Matrix.nonneg_iff_posSemidef.mpr (ManyBody.posSemidef_regionExpectation (D := K)
      (Matrix.nonneg_iff_posSemidef.mp hk0))), ((ManyBody.regionExpectation_mono (D :=
          K) hk1).trans_eq ManyBody.regionExpectation_one), ?_⟩
  set M := centeredFilter p (Δ / 2) H Ω (h i)
  have hMh : M.IsHermitian := isHermitian_centeredFilter p _ hH Ω (hHerm i)
  have hfix : ManyBody.regionExpectationLM K (CFC.abs (ManyBody.regionExpectationLM K M)) =
      CFC.abs (ManyBody.regionExpectationLM K M) := by
    simp only [ManyBody.regionExpectationLM_apply]
    exact (ManyBody.regionExpectation_of_mem_supportedOperators (D := K)
        (ManyBody.abs_mem_supportedOperators
          (ManyBody.regionExpectation_mem_supportedOperators K M)))
  have hloc : ∀ t : ℝ, ‖Matrix.hermitianUnitaryPath H t * h i *
        Matrix.hermitianUnitaryPath H (-t) - ManyBody.regionExpectationLM K
          (Matrix.hermitianUnitaryPath H t * h i * Matrix.hermitianUnitaryPath H (-t))‖ ≤
      ‖h i‖ * min 2 (CL * Real.exp (v * |t| - 1 / 2 * (l : ℝ))) := by
    intro t
    let Φ : ManyBody.Interaction (fun _ : ι ↦ Fin q) X :=
      ⟨h, fun k => (hSupport k)⟩
    have hLR := ManyBody.norm_heisenberg_sub_regionExpectation_graphBall_le G Φ a ha hHerm R
      hDiam vR hCard b₀ hBudget Kg kg hGrowth i (Φ.mem i) l t
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
        have := le_abs_self (2 * vR * b₀ * Real.exp (2 * R))
        simp only [v, localizationVelocity]; linarith
      have := mul_le_mul_of_nonneg_right h1 (abs_nonneg t)
      linarith
    refine mul_le_mul ?_ hexp (Real.exp_pos _).le (localizationPrefactor_nonneg R Kg kg)
    simp only [CL, localizationPrefactor]
    gcongr
  exact htail hH hΩ (hHerm i) (hJh i) (ManyBody.regionExpectationLM K)
    (fun B ↦ ManyBody.norm_regionExpectation_le B)
    (ManyBody.regionExpectation_one (D := K)) (fun Y hY =>
        (ManyBody.isHermitian_regionExpectation (D := K) hY)) hfix
    (Nat.cast_nonneg l) hloc

open Classical in
/-- **Positive replacement of the Hamiltonian, at the named filter-locality constants**
(Proposition 4.3, `prop:positive`, `03-quasilocal.tex`, lines 220–334). Every conclusion of
`exists_positiveQuasilocalConstraints` holds with
`C = positiveConstraintLocalityConst p Δ J (localizationPrefactor R K_g k_g) (1 / 2)` and
`c = positiveConstraintLocalityRate p Δ (localizationVelocity R v_R b₀) (1 / 2)`. -/
theorem positiveQuasilocalConstraints_explicit {p : ℕ} (hp : 1 ≤ p) (R vR : ℕ) (b₀ Kg : ℝ)
    (kg : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∀ {q : ℕ} [NeZero q] {ι : Type u} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
      (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι), (∀ k, a k ∈ X k) →
      ∀ (h : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ), (∀ k, (h k).IsHermitian) →
      (∀ k, h k ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (X k : Finset ι)) →
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
      (∀ i (l : ℕ), 0 ≤ ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i) ∧
        ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i) ≤ 1 ∧
        ‖k i - ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i)‖ ≤
          positiveConstraintLocalityConst p Δ J (localizationPrefactor R Kg kg) (1 / 2) *
            Real.exp (-(positiveConstraintLocalityRate p Δ (localizationVelocity R vR b₀) (1 / 2) *
              (l : ℝ) ^ kernelExponent p))) ∧
      (∀ i, k i ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
          (Finset.univ.filter fun x ↦ G.Reachable (a i) x)) :=
  positiveQuasilocalConstraints_of_locality hp R vR b₀ Kg kg hΔ
    (fun hH hΩ hh hhJ L hcontr hunit hherm hfix _ hl hτ =>
      norm_positiveConstraint_sub_map_le hp hΔ hJ (localizationPrefactor_nonneg R Kg kg)
        (localizationVelocity_pos R vR b₀) one_half_pos hH hΩ hh hhJ L hcontr hunit hherm hfix
        hl hτ)

open Classical in
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
        (∀ k, h k ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (X k : Finset ι)) →
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
        (∀ i (l : ℕ), 0 ≤ ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i) ∧
          ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i) ≤ 1 ∧
          ‖k i - ManyBody.regionExpectation (ManyBody.graphBall G (a i) l) (k i)‖ ≤
            C * Real.exp (-(c * (l : ℝ) ^ kernelExponent p))) ∧
        (∀ i, k i ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
            (Finset.univ.filter fun x ↦ G.Reachable (a i) x)) := by
  obtain ⟨C₃, c₃, hC₃, hc₃, htail⟩ := exists_norm_positiveConstraint_sub_map_le hp hΔ hJ
    (localizationPrefactor_nonneg R Kg kg) (localizationVelocity_pos R vR b₀) one_half_pos
  exact ⟨C₃, c₃, hC₃, hc₃, positiveQuasilocalConstraints_of_locality hp R vR b₀ Kg kg hΔ htail⟩

end TNLean.PEPS.AreaLaw

end PositiveConstraints

section QuasilocalRoots

/-!
## Square roots of the positive constraints and their local channels

For a positive contraction `k` with `k Ω = 0` and its expectation `k_l = E_K(k)` onto a set
of sites `K`, the square roots `G = (I - k)^{1/2}`, `K = k^{1/2}` and their local versions are
positive contractions, `G Ω = Ω`, `K Ω = 0`, and the root tails are bounded by the square
root of `‖k - k_l‖`. The root channels `ℰ(B) = G B G + K B K` are unital, completely
positive, and contractive after adjoining an arbitrary auxiliary system, and their
difference is bounded uniformly in the auxiliary dimension. The local channel fixes every
operator commuting with all operators acting on `K`, in particular every operator acting
outside `K`. Applied to the constraints of Proposition 4.3, whose tails are
`C e^{-c l^α}`, all these bounds are `C' e^{-(c/2) l^α}`.

### Main results

* `TNLean.PEPS.AreaLaw.quasilocalRoots`: Lemma 4.4 for one constraint and one radius.
* `TNLean.PEPS.AreaLaw.sqrt_mul_exp_neg`: `√(C e^{-c x}) = √C e^{-(c/2) x}`.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 4.4 (`lem:quasilocal-roots`), section file `03-quasilocal.tex`, lines 336–389.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit Matrix

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `√(C e^{-c x}) = √C e^{-(c/2) x}`. -/
theorem sqrt_mul_exp_neg (C c x : ℝ) :
    Real.sqrt (C * Real.exp (-(c * x))) = Real.sqrt C * Real.exp (-(c / 2 * x)) := by
  rw [Real.sqrt_mul' _ (Real.exp_pos _).le]
  congr 1
  rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

/-- **Square roots and local channels** (Lemma 4.4, `lem:quasilocal-roots`,
`03-quasilocal.tex`, lines 336–389), for one constraint `k` with `0 ≤ k ≤ I`, `k Ω = 0`,
and its expectation `k_l = E_K(k)` with `‖k - k_l‖ ≤ ε`. With `G = (I - k)^{1/2}`,
`K = k^{1/2}`, `G_l = (I - k_l)^{1/2}`, `K_l = k_l^{1/2}`:
the four roots are positive contractions; `G Ω = Ω`, `K Ω = 0`;
`‖G - G_l‖ + ‖K - K_l‖ ≤ 2 √ε` and `G_l² + K_l² = I` (`eq:quasilocal-root-tail`);
both root channels are unital, and for every finite auxiliary system they are positive and
contractive on the extended algebra, with
`‖(ℰ - ℰ_l) ⊗ id‖ ≤ 4 √ε` (`eq:quasilocal-channel-tail`); and `ℰ_l` fixes every operator
commuting with all operators acting on `K`. -/
theorem quasilocalRoots (K : Finset ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) {Ω : (ι → Fin q) → ℂ} (hkΩ : k *ᵥ Ω = 0) {ε : ℝ}
    (hε : ‖k - ManyBody.regionExpectation K k‖ ≤ ε) :
    let kl := ManyBody.regionExpectation K k
    let G := CFC.sqrt (1 - k)
    let Kr := CFC.sqrt k
    let Gl := CFC.sqrt (1 - kl)
    let Kl := CFC.sqrt kl
    (0 ≤ G ∧ G ≤ 1) ∧ (0 ≤ Kr ∧ Kr ≤ 1) ∧ (0 ≤ Gl ∧ Gl ≤ 1) ∧ (0 ≤ Kl ∧ Kl ≤ 1) ∧
      G *ᵥ Ω = Ω ∧ Kr *ᵥ Ω = 0 ∧
      ‖G - Gl‖ + ‖Kr - Kl‖ ≤ 2 * Real.sqrt ε ∧ Gl * Gl + Kl * Kl = 1 ∧
      rootChannel G Kr 1 = 1 ∧ rootChannel Gl Kl 1 = 1 ∧
      (∀ (κ : Type*) [Fintype κ] [DecidableEq κ] (B : Matrix ((ι → Fin q) × κ) _ ℂ),
        (0 ≤ B → 0 ≤ rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B ∧
          0 ≤ rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B) ∧
        ‖rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
        ‖rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
        ‖rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B -
            rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B‖ ≤
          4 * Real.sqrt ε * ‖B‖) ∧
      (∀ B : Matrix (ι → Fin q) (ι → Fin q) ℂ,
        (∀ A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) K, Commute A B) →
            rootChannel Gl Kl B = B) := by
  intro kl G Kr Gl Kl
  have hl₀ : 0 ≤ kl := Matrix.nonneg_iff_posSemidef.mpr (ManyBody.posSemidef_regionExpectation (D
      := K) (Matrix.nonneg_iff_posSemidef.mp hk₀))
  have hl₁ : kl ≤ 1 := (ManyBody.regionExpectation_mono (D := K) hk₁).trans_eq
      ManyBody.regionExpectation_one
  have hG : 0 ≤ G := CFC.sqrt_nonneg _
  have hKr : 0 ≤ Kr := CFC.sqrt_nonneg _
  have hGl : 0 ≤ Gl := CFC.sqrt_nonneg _
  have hKl : 0 ≤ Kl := CFC.sqrt_nonneg _
  have hG1 : G ≤ 1 := sqrt_le_one (sub_le_self _ hk₀)
  have hKr1 : Kr ≤ 1 := sqrt_le_one hk₁
  have hGl1 : Gl ≤ 1 := sqrt_le_one (sub_le_self _ hl₀)
  have hKl1 : Kl ≤ 1 := sqrt_le_one hl₁
  have hGn : ‖G‖ ≤ 1 := norm_le_one_of_nonneg_of_le_one hG hG1
  have hKrn : ‖Kr‖ ≤ 1 := norm_le_one_of_nonneg_of_le_one hKr hKr1
  have hGln : ‖Gl‖ ≤ 1 := norm_le_one_of_nonneg_of_le_one hGl hGl1
  have hKln : ‖Kl‖ ≤ 1 := norm_le_one_of_nonneg_of_le_one hKl hKl1
  have hsq : G * G + Kr * Kr = 1 := sqrt_one_sub_mul_add_sqrt_mul hk₀ hk₁
  have hsql : Gl * Gl + Kl * Kl = 1 := sqrt_one_sub_mul_add_sqrt_mul hl₀ hl₁
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have htG : ‖G - Gl‖ ≤ Real.sqrt ε :=
    (norm_sqrt_one_sub_sub_le hk₁ hl₁).trans (Real.sqrt_le_sqrt hε)
  have htK : ‖Kr - Kl‖ ≤ Real.sqrt ε :=
    (norm_sqrt_sub_le hk₀ hl₀).trans (Real.sqrt_le_sqrt hε)
  have hGh : G.IsHermitian := hG.isSelfAdjoint
  have hKh : Kr.IsHermitian := hKr.isSelfAdjoint
  have hGlh : Gl.IsHermitian := hGl.isSelfAdjoint
  have hKlh : Kl.IsHermitian := hKl.isSelfAdjoint
  refine ⟨⟨hG, hG1⟩, ⟨hKr, hKr1⟩, ⟨hGl, hGl1⟩, ⟨hKl, hKl1⟩,
    sqrt_one_sub_mulVec_eq_self hk₁ hkΩ, sqrt_mulVec_eq_zero hk₀ hkΩ, by linarith, hsql,
    rootChannel_one hsq, rootChannel_one hsql, fun κ _ _ B => ⟨fun hB =>
      ⟨rootChannel_kronecker_nonneg hGh hKh hB, rootChannel_kronecker_nonneg hGlh hKlh hB⟩,
      norm_rootChannel_kronecker_le hGh hKh hsq B, norm_rootChannel_kronecker_le hGlh hKlh hsql B,
      ?_⟩, fun B hB => ?_⟩
  · refine (norm_rootChannel_kronecker_sub_le G Kr Gl Kl B).trans ?_
    have hs := Real.sqrt_nonneg ε
    have hB := norm_nonneg B
    have h1 : (‖G‖ + ‖Gl‖) * ‖G - Gl‖ + (‖Kr‖ + ‖Kl‖) * ‖Kr - Kl‖ ≤ 4 * Real.sqrt ε := by
      have a1 : (‖G‖ + ‖Gl‖) * ‖G - Gl‖ ≤ 2 * Real.sqrt ε :=
        mul_le_mul (by linarith) htG (norm_nonneg _) (by norm_num)
      have a2 : (‖Kr‖ + ‖Kl‖) * ‖Kr - Kl‖ ≤ 2 * Real.sqrt ε :=
        mul_le_mul (by linarith) htK (norm_nonneg _) (by norm_num)
      linarith
    exact mul_le_mul_of_nonneg_right h1 hB
  · exact rootChannel_sqrt_eq_self_of_commute hl₀ hl₁
      (hB _ (ManyBody.regionExpectation_mem_supportedOperators K k))

end TNLean.PEPS.AreaLaw

end QuasilocalRoots
