/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelGroundVectors
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelSpatialOmission
import TNLean.PEPS.AreaLaw.LatticeConstraints

/-!
# Omitting distant events on finite lattice domains

This file proves the omission clause of the local-products lemma on a finite
domain `Λ ⊆ ℤ²` with its induced graph. For positive contractions `k_i`
anchored at `a_i` with bounded multiplicity and stretched-exponential
localization tails, run the full Poisson word and keep the events whose
anchors lie within distance `r` of `S`. Both the channel words and, on a
common zero vector `Ω` of the constraints, the products of the roots
`(I - k_i)^{1/2}` differ in expectation by at most
`C t |S| ‖B‖ e^{v t - c r^α}`. The constants depend only on the tail constants
and the multiplicity bound. The last theorem specializes to the exact positive
constraints of a gapped lattice Hamiltonian.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, Lemma 10.1, lines 42–72, proof at lines 188–226, at
revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit SpectralFilter Matrix MeasureTheory
open scoped BigOperators Kronecker ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder
  ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- The Euclidean norm of a product vector is the product of the two norms. -/
private theorem norm_toLp_prod_vector {n m : Type*} [Fintype n] [Fintype m]
    (Ω : n → ℂ) (ξ : m → ℂ) :
    ‖WithLp.toLp 2 (fun p : n × m => Ω p.1 * ξ p.2)‖ =
      ‖WithLp.toLp 2 Ω‖ * ‖WithLp.toLp 2 ξ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp [mul_pow]

/-- A site outside the graph neighborhood of radius `r` of `S` is at extended
distance more than `r` from every site of `S`. -/
private theorem lt_edist_of_notMem_graphNeighborhood {Λ : Finset (ℤ × ℤ)}
    {S : Finset (Site Λ)} {r : ℕ} {y : Site Λ} (hy : y ∉ graphNeighborhood Λ r S) :
    ∀ s ∈ S, ENNReal.ofReal (r : ℝ) < ((domainGraph Λ).edist y s : ℝ≥0∞) := by
  classical
  intro s hs
  rw [ENNReal.ofReal_natCast]
  by_contra hle
  have hle' : (domainGraph Λ).edist y s ≤ r := by
    rw [not_lt] at hle
    exact_mod_cast hle
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hle')
  apply hy
  simp only [graphNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨s, hs, w.reverse, ?_⟩
  rw [SimpleGraph.Walk.length_reverse]
  exact_mod_cast hw.le.trans hle'

/-- **Expected channel omission on a lattice domain**
(`eq:amplification-channel-omission`, `09-amplification.tex`, lines 203–215).
For tail constants `C ≥ 0`, `c > 0`, `0 < α ≤ 1` and a multiplicity bound `μ`,
there are `A ≥ 0` and `v, γ > 0` with the following property. Let `k_i` be
positive contractions on a finite domain `Λ`, anchored at `a_i` with at most `μ`
labels per site, with `‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}` for all `l`. Let
`B` act on `S` and a finite spectator, and let every label outside `P` be at
distance more than `r` from `S`. Then the norm of the difference between the
full channel word and its retained subword, on the same Poisson realization,
is integrable with expectation at most `A t |S| ‖B‖ e^{v t - γ r^α}`. -/
theorem exists_domain_integrable_and_integral_channelWordOmissionDefect_le
    {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ A v γ : ℝ, 0 ≤ A ∧ 0 < v ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
        (a : κ → Site Λ) (k : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        (∀ i (l : ℕ), ‖k i - siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (P : κ → Prop) [DecidablePred P]
          (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset (Site Λ))
          (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
            supportedOperators q (S : Set (Site Λ))) →
          ∀ (r : ℝ), 0 ≤ r →
            (∀ i, ¬ P i → ∀ s ∈ S,
              ENNReal.ofReal r < ((domainGraph Λ).edist (a i) s : ℝ≥0∞)) →
            ∀ t : ℝ≥0,
              Integrable (fun w : PoissonWord.Word κ =>
                channelWordOmissionDefect k P (List.ofFn w.2) B) (PoissonWord.measure κ t) ∧
              (∫ w : PoissonWord.Word κ,
                channelWordOmissionDefect k P (List.ofFn w.2) B ∂PoissonWord.measure κ t) ≤
                A * t * S.card * ‖B‖ * Real.exp (v * t - γ * r ^ α) := by
  obtain ⟨A, v, γ, hA, hv, hγ, _, hbound⟩ :=
    exists_integrable_and_integral_channelWordOmissionDefect_le hC (K := 2) zero_le_two
      hμ hc hα hα₁
  refine ⟨A, v, γ, hA, hv, hγ, ?_⟩
  intro q _ Λ κ _ a k hk₀ hk₁ hfiber htail P _ Aux _ _ S B hB r hr hfar t
  classical
  let N := Finset.univ.sup fun i : κ => Finset.univ.sup ((domainGraph Λ).dist (a i))
  have hN (i : κ) : Finset.univ.sup ((domainGraph Λ).dist (a i)) ≤ N :=
    Finset.le_sup (f := fun j => Finset.univ.sup ((domainGraph Λ).dist (a j)))
      (Finset.mem_univ i)
  exact hbound (Site Λ) κ Aux q (domainGraph Λ) a k hk₀ hk₁
    (fun i => mem_supportedOperators_reachable_of_forall_tail _ _ hc hα (htail i))
    card_graphBall_domainGraph_le hfiber N hN (fun i l _ => htail i l) P S B hB r hr hfar t

/-- **Omission of distant events from constraint products on a lattice domain**
(Lemma 10.1, `eq:amplification-product-omission`, `09-amplification.tex`,
lines 42–72, proof at lines 188–226).
For tail constants `C ≥ 0`, `c > 0`, `0 < α ≤ 1` and a multiplicity bound `μ`,
there are `A ≥ 0` and `v, γ > 0` with the following property. Let `k_i` be
positive contractions on a finite domain `Λ`, anchored at `a_i` with at most `μ`
labels per site, with `‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}` for all `l`, and
`k_i Ω = 0` for a unit vector `Ω`. Retain the labels with `d_Λ(a_i, S) ≤ r`. On
each realization `w` of the full Poisson word, let `D(w)` be the chronological
product of the roots `(I - k_i)^{1/2}` over all events, later factors on the
left, and `D_ret(w)` the same product over the retained events. If `B` acts on
`S` and a finite spectator, then for every unit spectator vector `ξ`, the norm
`‖(D - D_ret) B (Ω ⊗ ξ)‖` is integrable with expectation at most
`A t |S| ‖B‖ e^{v t - γ r^α}`. The source assumes `S` nonempty and `r ≥ 1`;
neither is needed here. -/
theorem exists_domainConstraintWord_omission
    {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ A v γ : ℝ, 0 ≤ A ∧ 0 < v ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
        (a : κ → Site Λ) (k : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        (∀ i (l : ℕ), ‖k i - siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (Ω : StateSpace Λ q), ‖Ω‖ = 1 → (∀ i, k i *ᵥ WithLp.ofLp Ω = 0) →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset (Site Λ))
          (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
            supportedOperators q (S : Set (Site Λ))) →
          ∀ (ξ : Aux → ℂ), ‖WithLp.toLp 2 ξ‖ = 1 → ∀ (r : ℕ) (t : ℝ≥0),
            let P := fun i : κ => a i ∈ graphNeighborhood Λ r S
            let D := fun u : List κ =>
              ((u.reverse.map fun i => CFC.sqrt (1 - k i)).prod ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ
                (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2)
            let F := fun w : PoissonWord.Word κ =>
              ‖WithLp.toLp 2 (D (List.ofFn w.2) -
                D ((List.ofFn w.2).filter fun i => decide (P i)))‖
            Integrable F (PoissonWord.measure κ t) ∧
            (∫ w, F w ∂PoissonWord.measure κ t) ≤
              A * t * S.card * ‖B‖ * Real.exp (v * t - γ * (r : ℝ) ^ α) := by
  obtain ⟨A, v, γ, hA, hv, hγ, hbound⟩ :=
    exists_domain_integrable_and_integral_channelWordOmissionDefect_le hC hμ hc hα hα₁
  refine ⟨A, v, γ, hA, hv, hγ, ?_⟩
  intro q _ Λ κ _ a k hk₀ hk₁ hfiber htail Ω hΩ hkΩ Aux _ _ S B hB ξ hξ r t P Dw F
  classical
  obtain ⟨hint, hle⟩ := hbound Λ κ a k hk₀ hk₁ hfiber htail P Aux S B hB (r : ℝ)
    (Nat.cast_nonneg r) (fun i hi => lt_edist_of_notMem_graphNeighborhood hi) t
  have hunit : ‖WithLp.toLp 2 (fun x : Configuration Λ q × Aux =>
      WithLp.ofLp Ω x.1 * ξ x.2)‖ = 1 := by
    rw [norm_toLp_prod_vector, hξ, mul_one]
    exact hΩ
  have hpt (w : PoissonWord.Word κ) :
      F w ≤ channelWordOmissionDefect k P (List.ofFn w.2) B := by
    have := norm_rootProduct_sub_le_channelWord_sub k hk₀ hk₁ hkΩ
      (List.ofFn w.2) ((List.ofFn w.2).filter fun i => decide (P i)) ξ B
    rwa [hunit, mul_one] at this
  have hFint : Integrable F (PoissonWord.measure κ t) :=
    hint.mono' Measurable.of_discrete.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hpt w)
  exact ⟨hFint, (integral_mono hFint hint hpt).trans hle⟩

/-- **Omission of distant events for the exact positive constraints**
(Lemma 10.1, `eq:amplification-product-omission`, applied to the constraints
of `eq:amplification-positive-system`; `09-amplification.tex`, lines 17–30,
42–72 and 188–226). For `p ≥ 1`, `R`, `J ≥ 0` and `Δ > 0` there are `A ≥ 0`
and `v, γ > 0` such that, for the exact positive constraints `k_i` of every
gapped lattice Hamiltonian with ground state `Ω`, every anchoring `a_i ∈ X_i`,
finite spectator, set `S`, radius `r`, time `t`, operator `B` acting on `S` and
the spectator, and unit spectator vector `ξ`, the expected norm of
`(D - D_ret) B (Ω ⊗ ξ)` is at most `A t |S| ‖B‖ e^{v t - γ r^α}` with
`α = p / (p + 1)`. The retained events are those with `d_Λ(a_i, S) ≤ r`. -/
theorem exists_latticeConstraintWord_omission {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ A v γ : ℝ, 0 ≤ A ∧ 0 < v ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset (Site Λ))
          (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
            supportedOperators q (S : Set (Site Λ))) →
          ∀ (ξ : Aux → ℂ), ‖WithLp.toLp 2 ξ‖ = 1 → ∀ (r : ℕ) (t : ℝ≥0),
            let P := fun i : AdmissibleSupport Λ R => a i ∈ graphNeighborhood Λ r S
            let k := fun i => positiveConstraint (positiveNormalization p (Δ / 2) J)
              (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
            let D := fun u : List (AdmissibleSupport Λ R) =>
              ((u.reverse.map fun i => CFC.sqrt (1 - k i)).prod ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ
                (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2)
            let F := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
              ‖WithLp.toLp 2 (D (List.ofFn w.2) -
                D ((List.ofFn w.2).filter fun i => decide (P i)))‖
            Integrable F (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
            (∫ w, F w ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
              A * t * S.card * ‖B‖ * Real.exp (v * t - γ * (r : ℝ) ^ kernelExponent p) := by
  obtain ⟨C, c, hC, hc, hpos⟩ := exists_latticePositiveConstraints hp R hJ hΔ
  obtain ⟨A, v, γ, hA, hv, hγ, hbound⟩ :=
    exists_domainConstraintWord_omission hC
      (μ := ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)) (Nat.cast_nonneg _)
      hc (kernelExponent_pos hp) (kernelExponent_le_one p)
  refine ⟨A, v, γ, hA, hv, hγ, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs Aux _ _ S B hB ξ hξ r t
  obtain ⟨hΩ, -, -⟩ := Matrix.isGappedGroundState_iff.mp hgs
  obtain ⟨-, hk, -, -, -, htail, -⟩ := hpos Λ h a ha E₀ Ω hgs
  exact hbound Λ (AdmissibleSupport Λ R) a _ (fun i => (hk i).1) (fun i => (hk i).2.1)
    (fun x => by exact_mod_cast card_anchor_fiber_le a ha x) (fun i l => (htail i l).2.2)
    Ω hΩ (fun i => (hk i).2.2) Aux S B hB ξ hξ r t

end TNLean.PEPS.AreaLaw
