/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LocalRootChannels
import TNLean.PEPS.AreaLaw.LatticeCounts
import TNLean.PEPS.AreaLaw.QuasilocalRoots
import TNLean.PEPS.AreaLaw.FiniteSetTruncationGap

/-!
# Positive constraints and truncation on an induced lattice domain

Proposition 4.3, Lemma 4.4 and Proposition 4.5 of the area-law manuscript, stated for the
model of Theorem 1.1: an arbitrary finite domain `Λ ⊂ ℤ²` with its induced nearest-neighbour
graph, a family `h` of Hermitian terms indexed by the nonempty supports of induced-graph
diameter at most `R` with `‖hᵢ‖ ≤ J`, an anchor `aᵢ ∈ Xᵢ` for every support, and a gapped
ground vector `Ω` of `H = ∑ᵢ hᵢ` with gap `Δ`. The graph counts that the general-graph
versions take as hypotheses (support size `v_R`, site budget `μ_R J`, ball and sphere growth
`2 (d + 1)²`, anchor multiplicity `μ_R`) are discharged by `LatticeCounts`. Every constant is
chosen before the domain, the interaction, the anchors and the ground vector: the constants of
Proposition 4.3 and Lemma 4.4 depend only on `p, R, J, Δ`, the constant `C₁` of
Proposition 4.5 only on `R, J, Δ, C₀`, and the crossing constant only on `q, R`; the source
allows `q, R, J, Δ` (`03-quasilocal.tex`, lines 41–42).

## Main results

* `TNLean.PEPS.AreaLaw.exists_latticePositiveConstraints`: Proposition 4.3.
* `TNLean.PEPS.AreaLaw.exists_latticeQuasilocalRoots`: Lemma 4.4.
* `TNLean.PEPS.AreaLaw.exists_latticeFiniteSetTruncation`: Proposition 4.5, truncation and
  ground-state part.
* `TNLean.PEPS.AreaLaw.exists_latticeFiniteSetTruncation_eigenspace_eq_span`: Proposition 4.5,
  truncation and ground-state part together with uniqueness of the truncated ground vector.
* `TNLean.PEPS.AreaLaw.exists_latticeCrossingBudget`,
  `TNLean.PEPS.AreaLaw.exists_latticeCutBudget_le_log`: Proposition 4.5, crossing count and
  cut budget; `TNLean.PEPS.AreaLaw.latticeCutBudget_le_log` gives the cut budget with the
  explicit constant `latticeCutBudgetConstant`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.3 (`prop:positive`), Lemma 4.4 (`lem:quasilocal-roots`) and Proposition 4.5
  (`prop:truncation`), section file `03-quasilocal.tex`, lines 220–534.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit SpectralFilter
open Matrix (rootChannel)

/-- **Positive replacement of the Hamiltonian on a lattice domain, with named constants**
(Proposition 4.3, `prop:positive`, `03-quasilocal.tex`, lines 220–334). Let `C₃, c₃` be the
constants of the filter-locality tail of the positive constraints for the lattice localization
constants `C = localizationPrefactor R 2 2`, `v = localizationVelocity R v_R (μ_R J)` and
`c = 1/2`, with `v_R = 1 + 2R(R + 1)` and `μ_R = 2^{2R(R+1)}`: the hypothesis `htail` is the
conclusion of `SpectralFilter.exists_norm_positiveConstraint_sub_map_le` at these constants.
Then every conclusion of `exists_latticePositiveConstraints` holds with `C = C₃`, `c = c₃`.
Once QICLean provides the named filter-locality constants, `htail` is
`SpectralFilter.norm_positiveConstraint_sub_map_le`, with
`C₃ = positiveConstraintLocalityConst p Δ J (localizationPrefactor R 2 2) (1 / 2)` and
`c₃ = positiveConstraintLocalityRate p Δ (localizationVelocity R v_R (μ_R J)) (1 / 2)`. -/
theorem latticePositiveConstraints_of_locality {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ C₃ c₃ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (htail : ∀ {n : Type} [Fintype n] [DecidableEq n]
      {H : Matrix n n ℂ} {Ω : EuclideanSpace ℂ n} {h : Matrix n n ℂ},
      H.IsHermitian → ‖Ω‖ = 1 → h.IsHermitian → ‖h‖ ≤ J →
      ∀ (L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ), (∀ X, ‖L X‖ ≤ ‖X‖) → L 1 = 1 →
      (∀ X, X.IsHermitian → (L X).IsHermitian) →
      L (CFC.abs (L (centeredFilter p (Δ / 2) H Ω h))) =
        CFC.abs (L (centeredFilter p (Δ / 2) H Ω h)) →
      ∀ {l : ℝ}, 0 ≤ l →
      (∀ t : ℝ, ‖Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t) -
          L (Matrix.hermitianUnitaryPath H t * h * Matrix.hermitianUnitaryPath H (-t))‖ ≤
        ‖h‖ * min 2 (localizationPrefactor R 2 2 * Real.exp (localizationVelocity R
          (1 + 2 * R * (R + 1)) (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J) * |t| -
            1 / 2 * l))) →
      ‖positiveConstraint (positiveNormalization p (Δ / 2) J) (centeredFilter p (Δ / 2) H Ω h) -
          L (positiveConstraint (positiveNormalization p (Δ / 2) J)
            (centeredFilter p (Δ / 2) H Ω h))‖ ≤
        C₃ * Real.exp (-(c₃ * l ^ kernelExponent p))) :
    ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
      (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
      ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
      let cs := positiveNormalization p (Δ / 2) J
      let k := fun i => positiveConstraint cs (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
      0 < cs ∧
      (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) ∧
      cs⁻¹ • (h.operator - (E₀ : ℂ) • 1) ≤ ∑ i, k i ∧
      ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
        cs⁻¹ • (h.operator - (E₀ : ℂ) • 1) ∧
      ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
        ∑ i, k i ∧
      (∀ i (l : ℕ), 0 ≤ siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i) ∧
        siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i) ≤ 1 ∧
        ‖k i - siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i)‖ ≤
          C₃ * Real.exp (-(c₃ * (l : ℝ) ^ kernelExponent p))) ∧
      (∀ i, k i ∈ supportedOperators q {x | (domainGraph Λ).Reachable (a i) x}) := by
  intro q _ Λ h a ha E₀ Ω hgs
  obtain ⟨hΩ, hHΩ, hgap⟩ := Matrix.isGappedGroundState_iff.mp hgs
  obtain ⟨hk, hsum, hgapk, htail, hcomp⟩ := positiveQuasilocalConstraints_of_locality hp R
    (1 + 2 * R * (R + 1)) (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J) 2 2 hΔ htail
    (q := q) (ι := Site Λ) (κ := AdmissibleSupport Λ R) (domainGraph Λ) (fun X => X.1) a ha
    h.term h.hermitian h.supported (fun X => X.2.edist_le) (fun X => X.2.card_le)
    (h.sum_norm_term_containing_le hJ) (card_domainGraph_sphere_le Λ) h.norm_le E₀ Ω hΩ hHΩ hgap
  exact ⟨positiveNormalization_pos p _ J, hk, hsum, hgapk, hgapk.trans hsum, htail, hcomp⟩

/-- **Positive replacement of the Hamiltonian on a lattice domain** (Proposition 4.3,
`prop:positive`, `03-quasilocal.tex`, lines 220–246). For `p ≥ 1`, `α = p / (p + 1)`,
`R`, `J ≥ 0` and `Δ > 0` there are `C ≥ 0`, `c > 0` such that for every `q ≥ 1`, every
finite domain `Λ`, every interaction `h` of range `R` and strength `J`, every choice of
anchors `aᵢ ∈ Xᵢ`, and every gapped ground vector `Ω` of `H` with gap `Δ`: with
`δ = Δ / 2`, `c_* > 0` and `kᵢ = |Mᵢ| / c_*`, one has `0 ≤ kᵢ ≤ I`, `kᵢ Ω = 0`,
`∑ᵢ kᵢ ≥ c_*⁻¹ (H - E₀ I) ≥ (Δ / c_*) (I - |Ω⟩⟨Ω|)` (`eq:quasilocal-positive`), so
`H_F = ∑ᵢ kᵢ ≥ g (I - |Ω⟩⟨Ω|)` with `g = Δ / c_*`: `H_F` has the ground vector `Ω`, ground
energy zero and gap at least `g` (lines 237–238); the ball
expectations `k_{i,l} = E_{N_l(aᵢ)}(kᵢ)` lie in `[0, I]` with
`‖kᵢ - k_{i,l}‖ ≤ C e^{-c l^α}` (`eq:quasilocal-positive-tail`); and `kᵢ` acts on the
connected component of `aᵢ`. -/
theorem exists_latticePositiveConstraints {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        let cs := positiveNormalization p (Δ / 2) J
        let k := fun i => positiveConstraint cs (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        0 < cs ∧
        (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) ∧
        cs⁻¹ • (h.operator - (E₀ : ℂ) • 1) ≤ ∑ i, k i ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          cs⁻¹ • (h.operator - (E₀ : ℂ) • 1) ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          ∑ i, k i ∧
        (∀ i (l : ℕ), 0 ≤ siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i) ∧
          siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i) ≤ 1 ∧
          ‖k i - siteExpectation q (graphBall (domainGraph Λ) (a i) l) (k i)‖ ≤
            C * Real.exp (-(c * (l : ℝ) ^ kernelExponent p))) ∧
        (∀ i, k i ∈ supportedOperators q {x | (domainGraph Λ).Reachable (a i) x}) := by
  obtain ⟨C₃, c₃, hC₃, hc₃, htail⟩ := exists_norm_positiveConstraint_sub_map_le hp hΔ hJ
    (localizationPrefactor_nonneg R 2 2) (localizationVelocity_pos R (1 + 2 * R * (R + 1))
      (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J)) one_half_pos
  exact ⟨C₃, c₃, hC₃, hc₃, latticePositiveConstraints_of_locality hp R hJ hΔ htail⟩

/-- **Square roots and local channels on a lattice domain** (Lemma 4.4,
`lem:quasilocal-roots`, `03-quasilocal.tex`, lines 336–389). For `p ≥ 1`, `R`, `J ≥ 0`,
`Δ > 0` there are `C ≥ 0`, `c > 0` such that, for the constraints `kᵢ` of
`exists_latticePositiveConstraints` and every radius `l`, with `k_{i,l} = E_{N_l(aᵢ)}(kᵢ)`,
`Gᵢ = (I - kᵢ)^{1/2}`, `Kᵢ = kᵢ^{1/2}`, `G_{i,l} = (I - k_{i,l})^{1/2}` and
`K_{i,l} = k_{i,l}^{1/2}`: the four roots are positive contractions, `Gᵢ Ω = Ω`, `Kᵢ Ω = 0`,
`‖Gᵢ - G_{i,l}‖ + ‖Kᵢ - K_{i,l}‖ ≤ C e^{-c l^α}` and `G_{i,l}² + K_{i,l}² = I`
(`eq:quasilocal-root-tail`); the channels `ℰᵢ(B) = Gᵢ B Gᵢ + Kᵢ B Kᵢ` and `ℰ_{i,l}` are unital,
and after adjoining any finite auxiliary system they are positive, contractive, and differ by at
most `C e^{-c l^α} ‖B‖` (`eq:quasilocal-channel-tail`); and `ℰ_{i,l}` fixes every operator
commuting with all operators acting on `N_l(aᵢ)`, also with an auxiliary system adjoined. -/
theorem exists_latticeQuasilocalRoots {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (i : AdmissibleSupport Λ R) (l : ℕ),
        let k := positiveConstraint (positiveNormalization p (Δ / 2) J)
          (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        let kl := siteExpectation q (graphBall (domainGraph Λ) (a i) l) k
        let G := CFC.sqrt (1 - k)
        let Kr := CFC.sqrt k
        let Gl := CFC.sqrt (1 - kl)
        let Kl := CFC.sqrt kl
        let ε := C * Real.exp (-(c * (l : ℝ) ^ kernelExponent p))
        (0 ≤ G ∧ G ≤ 1) ∧ (0 ≤ Kr ∧ Kr ≤ 1) ∧ (0 ≤ Gl ∧ Gl ≤ 1) ∧ (0 ≤ Kl ∧ Kl ≤ 1) ∧
        G *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω ∧ Kr *ᵥ WithLp.ofLp Ω = 0 ∧
        ‖G - Gl‖ + ‖Kr - Kl‖ ≤ ε ∧ Gl * Gl + Kl * Kl = 1 ∧
        rootChannel G Kr 1 = 1 ∧ rootChannel Gl Kl 1 = 1 ∧
        (∀ (κ : Type*) [Fintype κ] [DecidableEq κ]
            (B : Matrix (Configuration Λ q × κ) (Configuration Λ q × κ) ℂ),
          (0 ≤ B → 0 ≤ rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B ∧
            0 ≤ rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B) ∧
          ‖rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
          ‖rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
          ‖rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B -
              rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B‖ ≤ ε * ‖B‖ ∧
          ((∀ A ∈ supportedOperators q (graphBall (domainGraph Λ) (a i) l : Set (Site Λ)),
              Commute (A ⊗ₖ (1 : Matrix κ κ ℂ)) B) →
            rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B = B)) ∧
        (∀ B : Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
          (∀ A ∈ supportedOperators q (graphBall (domainGraph Λ) (a i) l : Set (Site Λ)),
            Commute A B) → rootChannel Gl Kl B = B) := by
  obtain ⟨C, c, hC, hc, hpos⟩ := exists_latticePositiveConstraints hp R hJ hΔ
  refine ⟨4 * Real.sqrt C, c / 2, by positivity, by positivity, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs i l k kl G Kr Gl Kl ε
  obtain ⟨-, hk, -, -, -, htail, -⟩ := hpos Λ h a ha E₀ Ω hgs
  have hsq := sqrt_mul_exp_neg C c ((l : ℝ) ^ kernelExponent p)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    quasilocalRoots (graphBall (domainGraph Λ) (a i) l) (hk i).1 (hk i).2.1 (hk i).2.2
      (htail i l).2.2
  have hε : 2 * Real.sqrt (C * Real.exp (-(c * (l : ℝ) ^ kernelExponent p))) ≤ ε := by
    rw [hsq]
    have : 0 ≤ Real.sqrt C * Real.exp (-(c / 2 * (l : ℝ) ^ kernelExponent p)) := by positivity
    simp only [ε]; linarith
  refine ⟨h1, h2, h3, h4, h5, h6, h7.trans hε, h8, h9, h10, fun κ _ _ B => ?_, h12⟩
  obtain ⟨b1, b2, b3, b4⟩ := h11 κ B
  refine ⟨b1, b2, b3, b4.trans (le_of_eq ?_), fun hB =>
    localRootChannel_eq_self_of_forall_commute _ (hk i).1 (hk i).2.1 hB⟩
  rw [hsq]; simp only [ε]; ring

/-- **Truncation near a finite set on a lattice domain** (Proposition 4.5, `prop:truncation`,
first part, `03-quasilocal.tex`, lines 405–433 and 457–505). Take `p = 1` in
`exists_latticePositiveConstraints`, so `α = 1/2`, and fix `R`, `J ≥ 0`, `Δ > 0`, `C₀ ≥ 0`.
There is `C₁ > 0`, depending only on `R, J, Δ, C₀`, such that for every lattice instance,
every real `n ≥ 2` and every `S₀` with `|S₀| ≤ C₀ n²`, with `r₀ = ⌈C₁ (log n)²⌉`,
`g = Δ / c_*` and `ε_n = min {n^{-1000}, g/4}`: each truncated constraint acts on its
designated support (`eq:quasilocal-variable-radius`) and is a positive contraction,
`‖H' - H_F‖ ≤ ε_n` for the truncated sum `H'` (`eq:quasilocal-truncation-error`), and `H'` has
a unit ground vector `Ω₀` with ground energy in `[0, ε_n]`, gap at least `g/2`,
`‖Ω₀ - e^{iθ} Ω‖ ≤ 2 √(ε_n / g)` for some phase and trace distance at most `√(2 ε_n / g)` from
`Ω` (`eq:quasilocal-ground-distance`). The source assumes `S₀` nonempty; the statement holds
without that assumption. -/
theorem exists_latticeFiniteSetTruncation (R : ℕ) {J Δ C₀ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC₀ : 0 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ n : ℝ, 2 ≤ n → ∀ S₀ : Finset (Site Λ), (S₀.card : ℝ) ≤ C₀ * n ^ 2 →
        let G := domainGraph Λ
        let cs := positiveNormalization 1 (Δ / 2) J
        let g := Δ / cs
        let k := fun i => positiveConstraint cs (centeredFilter 1 (Δ / 2) h.operator Ω (h.term i))
        let r₀ := ⌈C₁ * Real.log n ^ 2⌉₊
        let ε := min (n ^ (-1000 : ℝ)) (g / 4)
        let Ht := ∑ i, truncatedConstraint q G S₀ r₀ (a i) (k i)
        (∀ i, truncatedConstraint q G S₀ r₀ (a i) (k i) ∈
          supportedOperators q (designatedSupport G S₀ r₀ (a i) : Set (Site Λ))) ∧
        (∀ i, 0 ≤ truncatedConstraint q G S₀ r₀ (a i) (k i) ∧
          truncatedConstraint q G S₀ r₀ (a i) (k i) ≤ 1) ∧
        ‖Ht - ∑ i, k i‖ ≤ ε ∧
        ∃ (e : ℝ) (Ω₀ : StateSpace Λ q), ‖Ω₀‖ = 1 ∧
          Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧ 0 ≤ e ∧ e ≤ ε ∧
          (Ht - (e : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
            (1 - Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))).PosSemidef ∧
          (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) := by
  obtain ⟨C₁, hC₁, htr⟩ := exists_finiteSetTruncation_of_gap.{0, 0} R (1 + 2 * R * (R + 1))
    (((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J) 2 2 hJ hΔ (Kb := 2)
    (μ := ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)) zero_le_two (Nat.cast_nonneg _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs n hn S₀ hS₀
  obtain ⟨hΩ, hHΩ, hgap⟩ := Matrix.isGappedGroundState_iff.mp hgs
  exact @htr q _ (Site Λ) _ _ (AdmissibleSupport Λ R) _ (domainGraph Λ) (fun X => X.1) a ha
    h.term h.hermitian h.supported (fun X => X.2.edist_le) (fun X => X.2.card_le)
    (h.sum_norm_term_containing_le hJ) (card_domainGraph_sphere_le Λ) card_graphBall_domainGraph_le
    (fun x => by exact_mod_cast card_anchor_fiber_le a ha x) h.norm_le E₀ Ω hΩ hHΩ hgap n hn S₀
    hS₀

/-- **Truncation near a finite set on a lattice domain, with a unique ground vector**
(Proposition 4.5, `prop:truncation`, first part, `03-quasilocal.tex`, lines 405–433 and
457–505; lines 426–427: "its ground vector `\tilde\Omega` is unique"). With one constant `C₁`
and one truncation, every conclusion of `exists_latticeFiniteSetTruncation` holds, and in
addition the eigenspace of the truncated sum `H'` at its ground energy `e` is the line spanned by
its ground vector `Ω₀`. -/
theorem exists_latticeFiniteSetTruncation_eigenspace_eq_span (R : ℕ) {J Δ C₀ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC₀ : 0 ≤ C₀) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ n : ℝ, 2 ≤ n → ∀ S₀ : Finset (Site Λ), (S₀.card : ℝ) ≤ C₀ * n ^ 2 →
        let G := domainGraph Λ
        let cs := positiveNormalization 1 (Δ / 2) J
        let g := Δ / cs
        let k := fun i => positiveConstraint cs (centeredFilter 1 (Δ / 2) h.operator Ω (h.term i))
        let r₀ := ⌈C₁ * Real.log n ^ 2⌉₊
        let ε := min (n ^ (-1000 : ℝ)) (g / 4)
        let Ht := ∑ i, truncatedConstraint q G S₀ r₀ (a i) (k i)
        (∀ i, truncatedConstraint q G S₀ r₀ (a i) (k i) ∈
          supportedOperators q (designatedSupport G S₀ r₀ (a i) : Set (Site Λ))) ∧
        (∀ i, 0 ≤ truncatedConstraint q G S₀ r₀ (a i) (k i) ∧
          truncatedConstraint q G S₀ r₀ (a i) (k i) ≤ 1) ∧
        ‖Ht - ∑ i, k i‖ ≤ ε ∧
        ∃ (e : ℝ) (Ω₀ : StateSpace Λ q), ‖Ω₀‖ = 1 ∧
          Ht *ᵥ WithLp.ofLp Ω₀ = (e : ℂ) • WithLp.ofLp Ω₀ ∧ 0 ≤ e ∧ e ≤ ε ∧
          (Ht - (e : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
            (1 - Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))).PosSemidef ∧
          Module.End.eigenspace (Matrix.toEuclideanLin Ht) (e : ℂ) = Submodule.span ℂ {Ω₀} ∧
          (∃ θ : ℝ, ‖Ω₀ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) := by
  obtain ⟨C₁, hC₁, htr⟩ := exists_latticeFiniteSetTruncation R hJ hΔ hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs n hn S₀ hS₀
  obtain ⟨hsupp, hpos, herr, e, Ω₀, hΩ₀, hHΩ₀, he₀, heε, hgap, hθ, htd⟩ :=
    htr Λ h a ha E₀ Ω hgs n hn S₀ hS₀
  have hgs₀ := Matrix.isGappedGroundState_iff.mpr ⟨hΩ₀, hHΩ₀, hgap⟩
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J / 2 :=
    half_pos (div_pos hΔ (positiveNormalization_pos 1 _ J))
  exact ⟨hsupp, hpos, herr, e, Ω₀, hΩ₀, hHΩ₀, he₀, heε, hgap, hgs₀.eigenspace_eq_span hg, hθ,
    htd⟩

/-- **Crossing count and cut budget on a lattice domain** (Proposition 4.5, `prop:truncation`,
`eq:quasilocal-crossing-count` and `eq:quasilocal-cut-budget`, `03-quasilocal.tex`,
lines 434–451 and 505–518). For `q ≥ 1` and `R` there is `C ≥ 0`, depending only on `q` and
`R`, such that for every domain, every choice of anchors, every `S₀`, every `r₀` and every
`X ⊆ S₀`, with `b_X = |∂_Λ X|`: every designated support meeting both `X` and its complement
is the ball of radius `r₀` about its anchor, `|𝒞_X| ≤ C b_X (r₀ + 1)²`,
`log dᵢ ≤ C (r₀ + 1)²` for `i ∈ 𝒞_X`, and `ℬ_X ≤ C (1 + b_X) (r₀ + 1)⁶`. -/
theorem exists_latticeCrossingBudget {q : ℕ} (hq : 1 ≤ q) (R : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
      ∀ (S₀ : Finset (Site Λ)) (r₀ : ℕ) (X : Finset (Site Λ)), X ⊆ S₀ →
        (∀ i ∈ crossingLabels (domainGraph Λ) S₀ r₀ a X,
          designatedSupport (domainGraph Λ) S₀ r₀ (a i) = graphBall (domainGraph Λ) (a i) r₀) ∧
        ((crossingLabels (domainGraph Λ) S₀ r₀ a X).card : ℝ) ≤
          C * (edgeBoundary Λ X).card * ((r₀ : ℝ) + 1) ^ 2 ∧
        (∀ i ∈ crossingLabels (domainGraph Λ) S₀ r₀ a X,
          Real.log ((q : ℝ) ^ (designatedSupport (domainGraph Λ) S₀ r₀ (a i)).card) ≤
            C * ((r₀ : ℝ) + 1) ^ 2) ∧
        cutBudget q (domainGraph Λ) S₀ r₀ a X ≤
          C * (1 + (edgeBoundary Λ X).card) * ((r₀ : ℝ) + 1) ^ 6 := by
  set μ : ℝ := ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)
  have hμ : 0 ≤ μ := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  set K := max 1 (2 * μ * 2 * (1 + 2 * Real.log q) ^ 2)
  refine ⟨max (max (2 * μ * 2) (2 * Real.log q)) K, by positivity, ?_⟩
  intro Λ a ha S₀ r₀ X hX
  set G := domainGraph Λ
  have hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ := fun x => by
    simp only [μ]; exact_mod_cast card_anchor_fiber_le a ha x
  have hb : ((cutEdges G X).card : ℝ) ≤ (edgeBoundary Λ X).card := by
    exact_mod_cast card_cutEdges_le_card_edgeBoundary X
  have hr : (0 : ℝ) ≤ ((r₀ : ℝ) + 1) := by positivity
  have h1 : 2 * μ * 2 ≤ max (max (2 * μ * 2) (2 * Real.log q)) K :=
    (le_max_left _ _).trans (le_max_left _ _)
  have h2 : 2 * Real.log q ≤ max (max (2 * μ * 2) (2 * Real.log q)) K :=
    (le_max_right _ _).trans (le_max_left _ _)
  have h3 : K ≤ max (max (2 * μ * 2) (2 * Real.log q)) K := le_max_right _ _
  refine ⟨fun i hi => (truncationRadius_eq_of_mem_crossingLabels hX hi).2.2, ?_, fun i hi => ?_,
    ?_⟩
  · refine (card_crossingLabels_le G S₀ r₀ a hX hμ card_graphBall_domainGraph_le hMult).trans ?_
    calc 2 * μ * 2 * ((r₀ : ℝ) + 1) ^ 2 * (cutEdges G X).card
        ≤ 2 * μ * 2 * ((r₀ : ℝ) + 1) ^ 2 * (edgeBoundary Λ X).card := by gcongr
      _ ≤ _ := by
        rw [mul_right_comm]
        gcongr
  · refine (log_dim_le_of_mem_crossingLabels hq hX card_graphBall_domainGraph_le hi).trans ?_
    gcongr
  · refine (cutBudget_le hq G S₀ r₀ a hX zero_le_two hμ card_graphBall_domainGraph_le
      hMult).trans ?_
    gcongr

/-- The explicit cut-budget coefficient `max 1 (4 μ_R (1 + 2 log q)²)` on a lattice domain,
where `μ_R = 2^(2R(R+1))` bounds the labels per anchor and balls of radius `d` have at most
`2 (d + 1)²` sites (`03-quasilocal.tex`, lines 434–451 and 505–518). -/
noncomputable def latticeCutCoefficient (q R : ℕ) : ℝ :=
  max 1 (2 * ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * 2 * (1 + 2 * Real.log q) ^ 2)

/-- **The cut budget on a lattice domain, with an explicit coefficient**
(Proposition 4.5, `eq:quasilocal-cut-budget`, `03-quasilocal.tex`, lines 434–451 and
505–518): `ℬ_X ≤ latticeCutCoefficient q R (1 + b_X) (r₀ + 1)⁶` for every `X ⊆ S₀`. -/
theorem cutBudget_le_latticeCutCoefficient {q : ℕ} (hq : 1 ≤ q) (R : ℕ)
    (Λ : Finset (ℤ × ℤ)) (a : AdmissibleSupport Λ R → Site Λ) (ha : ∀ X, a X ∈ X.1)
    (S₀ : Finset (Site Λ)) (r₀ : ℕ) {X : Finset (Site Λ)} (hX : X ⊆ S₀) :
    cutBudget q (domainGraph Λ) S₀ r₀ a X ≤
      latticeCutCoefficient q R * (1 + (edgeBoundary Λ X).card) * ((r₀ : ℝ) + 1) ^ 6 := by
  refine (cutBudget_le hq _ S₀ r₀ a hX zero_le_two (Nat.cast_nonneg _)
    card_graphBall_domainGraph_le fun x => by exact_mod_cast card_anchor_fiber_le a ha x).trans ?_
  have hb : ((cutEdges (domainGraph Λ) X).card : ℝ) ≤ (edgeBoundary Λ X).card := by
    exact_mod_cast card_cutEdges_le_card_edgeBoundary X
  unfold latticeCutCoefficient
  gcongr

/-- The explicit constant `latticeCutCoefficient q R (1 + C₂) (C₁ + 2 / (log 2)²)⁶` of the
cut budget in terms of `n` (Proposition 4.5, last sentence, `03-quasilocal.tex`,
lines 452–455 and 519–520). -/
noncomputable def latticeCutBudgetConstant (q R : ℕ) (C₁ C₂ : ℝ) : ℝ :=
  latticeCutCoefficient q R * (1 + C₂) * (C₁ + 2 / Real.log 2 ^ 2) ^ 6

/-- The lattice cut-budget constant is nonnegative. -/
theorem latticeCutBudgetConstant_nonneg (q R : ℕ) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    0 ≤ latticeCutBudgetConstant q R C₁ C₂ := by
  have : 0 ≤ latticeCutCoefficient q R := zero_le_one.trans (le_max_left _ _)
  unfold latticeCutBudgetConstant
  positivity

/-- **The cut budget in terms of `n`, with an explicit constant** (Proposition 4.5, last
sentence, `03-quasilocal.tex`, lines 452–455 and 519–520): with `r₀ = ⌈C₁ (log n)²⌉`, every
`X ⊆ S₀` with `b_X ≤ C₂ n D`, `n ≥ 2` and `D ≥ 1` has
`ℬ_X ≤ latticeCutBudgetConstant q R C₁ C₂ · n D (log n)¹²`. -/
theorem latticeCutBudget_le_log {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (Λ : Finset (ℤ × ℤ)) (a : AdmissibleSupport Λ R → Site Λ)
    (ha : ∀ X, a X ∈ X.1) (S₀ X : Finset (Site Λ)) (hX : X ⊆ S₀) {n D : ℝ} (hn : 2 ≤ n)
    (hD : 1 ≤ D) (hb : ((edgeBoundary Λ X).card : ℝ) ≤ C₂ * n * D) :
    cutBudget q (domainGraph Λ) S₀ ⌈C₁ * Real.log n ^ 2⌉₊ a X ≤
      latticeCutBudgetConstant q R C₁ C₂ * (n * D * Real.log n ^ 12) :=
  le_of_cutBudget_le (zero_le_one.trans (le_max_left _ _)) hC₁ hC₂ hn hD hb
    (cutBudget_le_latticeCutCoefficient hq R Λ a ha S₀ _ hX)

/-- **The cut budget in terms of `n` on a lattice domain** (Proposition 4.5, last sentence,
`03-quasilocal.tex`, lines 452–455 and 519–520). For `q ≥ 1`, `R`, `C₁ ≥ 0` and `C₂ ≥ 0` there
is `C ≥ 0` such that, with `r₀ = ⌈C₁ (log n)²⌉`, every `X ⊆ S₀` with `b_X ≤ C₂ n D`, `n ≥ 2`
and `D ≥ 1` has `ℬ_X ≤ C n D (log n)¹²`. -/
theorem exists_latticeCutBudget_le_log {q : ℕ} (hq : 1 ≤ q) (R : ℕ) {C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
      ∀ (S₀ X : Finset (Site Λ)), X ⊆ S₀ → ∀ n D : ℝ, 2 ≤ n → 1 ≤ D →
        ((edgeBoundary Λ X).card : ℝ) ≤ C₂ * n * D →
        cutBudget q (domainGraph Λ) S₀ ⌈C₁ * Real.log n ^ 2⌉₊ a X ≤
          C * (n * D * Real.log n ^ 12) :=
  ⟨_, latticeCutBudgetConstant_nonneg q R hC₁ hC₂, fun Λ a ha S₀ X hX _ _ hn hD hb =>
    latticeCutBudget_le_log hq R hC₁ hC₂ Λ a ha S₀ X hX hn hD hb⟩

end TNLean.PEPS.AreaLaw
