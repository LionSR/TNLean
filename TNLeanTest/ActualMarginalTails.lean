/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualMarginalTails

/-!
# Actual truncated marginal regressions

The same physical ground-state premise gives every cut, including complementary
cuts and negative thresholds. The original centering vector is independent of
the truncated ground vector. Budget checks cover empty and full cuts, an empty
label type, zero local dimension, and two repeated labels on a retained component
at local dimensions one and two, including zero operators. The existential
signature and its consumers construct one witness from the original Hamiltonian,
including empty truncation sets and the empty domain at local dimension one.
The same witness retains both energy upper bounds and its phase and trace-distance
closeness to the original vector while controlling complementary cuts.
A nonzero-energy singleton and a two-dimensional spectator separate the physical
projector gap from identity extension.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan SpectralFilter
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
namespace TNLeanTest.ActualMarginalTails

section Budgets

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (S₀ : Finset V) (r₀ : ℕ) (a : I → V) (X : Finset V)

-- The equality itself does not require a nonzero local dimension.
example : cutBudget 0 G S₀ r₀ a X =
    Entropy.cutLogBudget
      (Entropy.crossingTerms (fun i => designatedSupport G S₀ r₀ (a i)) X)
      (Entropy.supportDim (fun _ : V => 0) ∘
        (fun i => designatedSupport G S₀ r₀ (a i))) :=
  cutBudget_eq_cutLogBudget 0 G S₀ r₀ a X

example (q : ℕ) : cutBudget q G S₀ r₀ a ∅ = 1 := cutBudget_empty q G S₀ r₀ a

example (q : ℕ) : cutBudget q G S₀ r₀ a Finset.univ = 1 := cutBudget_univ q G S₀ r₀ a

-- No containment premise is available for the complementary cut.
example (q : ℕ) : cutBudget q G S₀ r₀ a Xᶜ = cutBudget q G S₀ r₀ a X :=
  cutBudget_compl q G S₀ r₀ a X

example (q : ℕ) : 0 < cutBudget q G S₀ r₀ a X :=
  lt_of_lt_of_le zero_lt_one (one_le_cutBudget q G S₀ r₀ a X)

example (q : ℕ) (a₀ : Fin 0 → V) : cutBudget q G S₀ r₀ a₀ X = 1 := by
  simp [cutBudget, crossingLabels]

end Budgets

private theorem retained_support :
    designatedSupport (⊤ : SimpleGraph (Fin 2)) ∅ 0 0 = Finset.univ := by
  classical
  have hdist : setDist (⊤ : SimpleGraph (Fin 2)) ∅ 0 = ⊤ := by simp [setDist]
  rw [designatedSupport, hdist, ite_eq_left rfl]
  apply Finset.eq_univ_of_forall
  intro x
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hx : (0 : Fin 2) = x
  · subst x
    exact SimpleGraph.Reachable.refl _
  · exact (show (⊤ : SimpleGraph (Fin 2)).Adj 0 x from hx).reachable

private theorem repeated_crossing_labels :
    crossingLabels (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} =
      Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro i
  simp only [crossingLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [retained_support]
  exact ⟨⟨0, Finset.mem_univ _, by simp⟩, ⟨1, Finset.mem_univ _, by decide⟩⟩

-- Empty truncation sets retain components; they do not erase internal crossings.
-- Two identical anchors still contribute two terms, even at physical dimension one.
example : cutBudget 1 (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} = 3 := by
  norm_num [cutBudget, repeated_crossing_labels]

-- The geometric budget retains both labels even when both labelled operators vanish.
example : (∑ _i : Fin 2, (0 : Matrix (Fin 2 → Fin 1) (Fin 2 → Fin 1) ℂ)) = 0 ∧
    cutBudget 1 (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} = 3 := by
  norm_num [cutBudget, repeated_crossing_labels]

-- Qubit supports have dimension four: both copies of their positive logarithmic
-- contribution are counted separately, although the designated supports are equal.
private theorem repeated_qubit_budget :
    cutBudget 2 (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} =
      1 + 2 * Real.log (Real.exp 1 * 4) ^ 2 := by
  norm_num [cutBudget, repeated_crossing_labels, retained_support]

example : 1 < cutBudget 2 (⊤ : SimpleGraph (Fin 2)) ∅ 0
    (fun _ : Fin 2 => 0) {0} := by
  rw [repeated_qubit_budget]
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hlog : 0 < Real.log (Real.exp 1 * 4) := Real.log_pos (by linarith)
  nlinarith [sq_pos_of_pos hlog]

example : (∑ _i : Fin 2, (0 : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ)) = 0 ∧
    cutBudget 2 (⊤ : SimpleGraph (Fin 2)) ∅ 0 (fun _ : Fin 2 => 0) {0} =
      1 + 2 * Real.log (Real.exp 1 * 4) ^ 2 :=
  ⟨by simp, repeated_qubit_budget⟩

section Physical

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ} [NeZero q]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
    (h : LocalHamiltonian Λ q R J) (Ω Ωt : StateSpace Λ q)
    (hgraph : S.graph = domainGraph Λ) (hanchor : ∀ i, S.anchor i ∈ i.val)
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ) (e : ℝ)
    (hgs : IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2))

-- The original centering vector and the single ground vector remain separate.
example (X : Finset (Site Λ)) (u : ℝ)
    (hu : |u| ≤ Entropy.tailRadius (2 / (Δ / positiveNormalization 1 (Δ / 2) J))
      (cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X)) :
    Real.log (Entropy.surprisalMoment (reducedState_isHermitian Λ q Ωt X).eigenvalues u) ≤
      u * regionalEntropy Λ q Ωt X +
        512 * Real.exp 1 * (2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
          cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X * u ^ 2 :=
  S.log_surprisalMoment_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L hgs X hu

-- One premise is reused for all cuts and all real thresholds, with no history data.
example : ∀ (X : Finset (Site Λ)) (w : ℝ),
    Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
        (regionalEntropy Λ q Ωt X) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
            cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X))))) :=
  fun X w => S.surprisalTail_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L hgs X w

-- The marginal is genuinely that of Xᶜ; only the scalar budget is complemented.
example (X : Finset (Site Λ)) :
    Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt Xᶜ).eigenvalues
        (regionalEntropy Λ q Ωt Xᶜ) (-1) ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-((-1) / (32 * Real.sqrt
          ((1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)) *
            cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X))))) := by
  simpa only [cutBudget_compl] using
    S.surprisalTail_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L hgs Xᶜ (-1)

end Physical

-- Local dimension one is admitted by the physical theorem, without an extra J premise.
example {Λ : Finset (ℤ × ℤ)} {R : ℕ} {J Δ e : ℝ}
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (h : LocalHamiltonian Λ 1 R J)
    (Ω Ωt : StateSpace Λ 1) (hgraph : S.graph = domainGraph Λ)
    (hanchor : ∀ i, S.anchor i ∈ i.val) (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (L : ℕ)
    (hgs : IsGappedGroundState Λ 1 (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
      ((Δ / positiveNormalization 1 (Δ / 2) J) / 2)) (w : ℝ) :
    Entropy.surprisalTail (reducedState_isHermitian Λ 1 Ωt ∅).eigenvalues
        (regionalEntropy Λ 1 Ωt ∅) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt
          (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)))))) := by
  simpa only [cutBudget_empty, mul_one] using
    S.surprisalTail_truncated_reducedState_le h Ω hgraph hanchor hΔ hΩ L hgs ∅ w

-- This exact signature forces Ctr before q, the instance and scan, retains the
-- original Hamiltonian ground-state premise and source radius/cardinality bounds,
-- and chooses one e/Ωt with energy, phase and trace bounds before both cut families.
example
    (R : ℕ) {J Δ C₀ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC₀ : 0 ≤ C₀) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ))
        (h : LocalHamiltonian Λ q R J)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
        (E₀ : ℝ) (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        S.graph = domainGraph Λ →
        (∀ i, S.anchor i ∈ i.val) →
        ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        ((S.truncationSet L).card : ℝ) ≤ C₀ * (S.n : ℝ) ^ 2 →
        let g := Δ / positiveNormalization 1 (Δ / 2) J
        let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
        let B : Finset (Site Λ) → ℝ :=
          fun X => cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X
        ∃ (e : ℝ) (Ωt : StateSpace Λ q),
          IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt (g / 2) ∧
          0 ≤ e ∧ e ≤ ε ∧
          (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) ∧
          (∀ (X : Finset (Site Λ)) (u : ℝ),
            |u| ≤ Entropy.tailRadius (2 / g) (B X) →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt X).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt X +
                512 * Real.exp 1 * (2 / g) * B X * u ^ 2) ∧
          (∀ (X : Finset (Site Λ)) (w : ℝ),
            Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
              (regionalEntropy Λ q Ωt X) w ≤
              min 1 (2 * Real.exp (Real.exp 1 / 2) *
                Real.exp (-(w / (32 * Real.sqrt ((1 + 2 / g) * B X)))))) :=
  CollarScan.exists_truncated_reducedState_moment_tail_bounds R hJ hΔ hC₀

-- An empty truncation set discharges the size premise with C₀ = 0, even in a
-- nonempty domain. A single constructed vector retains both projected energy bounds,
-- phase/trace closeness, and simultaneous control of X and Xᶜ.
private theorem empty_truncation_witness (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ) (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
        ∀ L : ℕ, 2 ≤ S.n → S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        S.truncationSet L = ∅ →
        let g := Δ / positiveNormalization 1 (Δ / 2) J
        let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
        let B := fun X => cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X
        ∃ (e : ℝ) (Ωt : StateSpace Λ q),
          IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt (g / 2) ∧
          0 ≤ e ∧ e ≤ (S.n : ℝ) ^ (-1000 : ℝ) ∧ e ≤ g / 4 ∧
          (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤ 2 * Real.sqrt (ε / g)) ∧
          Matrix.traceDistance (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
            Real.sqrt (2 * ε / g) ∧
          ∀ (X : Finset (Site Λ)) (w : ℝ),
            (Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
                (regionalEntropy Λ q Ωt X) w ≤
              min 1 (2 * Real.exp (Real.exp 1 / 2) *
                Real.exp (-(w / (32 * Real.sqrt ((1 + 2 / g) * B X)))))) ∧
            (Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt Xᶜ).eigenvalues
                (regionalEntropy Λ q Ωt Xᶜ) (-w) ≤
              min 1 (2 * Real.exp (Real.exp 1 / 2) *
                Real.exp (-((-w) / (32 * Real.sqrt ((1 + 2 / g) * B X)))))) := by
  obtain ⟨Ctr, hCtr, htr⟩ :=
    CollarScan.exists_truncated_reducedState_moment_tail_bounds R hJ hΔ (le_refl (0 : ℝ))
  refine ⟨Ctr, hCtr, ?_⟩
  intro q _ Λ h S E₀ Ω hgs hgraph hanchor L hn hr hS₀
  obtain ⟨e, Ωt, htrgs, he0, he, hphase, htrace, _, htail⟩ :=
    htr Λ h S E₀ Ω hgs hgraph hanchor L hn hr (by simp [hS₀])
  refine ⟨e, Ωt, htrgs, he0, he.trans (min_le_left _ _),
    he.trans (min_le_right _ _), hphase, htrace, fun X w => ⟨htail X w, ?_⟩⟩
  simpa only [cutBudget_compl] using htail Xᶜ (-w)

-- The empty physical domain at local dimension one needs neither a nonempty
-- domain hypothesis nor a supplied truncated eigenvector. The anchor condition
-- and the truncation-size condition are discharged from emptiness.
example (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (h : LocalHamiltonian ∅ 1 R J)
        (S : CollarScan (Site ∅) (AdmissibleSupport ∅ R)) (E₀ : ℝ) (Ω : StateSpace ∅ 1),
        IsGappedGroundState ∅ 1 h.operator E₀ Ω Δ →
        S.graph = domainGraph ∅ → ∀ L : ℕ, 2 ≤ S.n →
        S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
        ∃ (e : ℝ) (Ωt : StateSpace ∅ 1),
          IsGappedGroundState ∅ 1 (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt
            ((Δ / positiveNormalization 1 (Δ / 2) J) / 2) := by
  obtain ⟨Ctr, hCtr, htr⟩ := empty_truncation_witness R hJ hΔ
  refine ⟨Ctr, hCtr, ?_⟩
  intro h S E₀ Ω hgs hgraph L hn hr
  have hanchor : ∀ i, S.anchor i ∈ i.val := by
    intro i
    exact (Finset.notMem_empty _ (S.anchor i).property).elim
  have hS₀ : S.truncationSet L = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x _
    exact Finset.notMem_empty _ x.property
  obtain ⟨e, Ωt, htrgs, _⟩ := htr ∅ h S E₀ Ω hgs hgraph hanchor L hn hr hS₀
  exact ⟨e, Ωt, htrgs⟩

-- The coordinate packaging retains a nonzero global energy, rather than
-- requiring termwise annihilation or silently setting e to zero.
example : Matrix.IsGappedGroundState (1 : Matrix (Fin 1) (Fin 1) ℂ) 1
    (EuclideanSpace.single 0 1) 3 := by
  apply Matrix.isGappedGroundState_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [PiLp.norm_single, norm_one]
  · simp only [Matrix.one_mulVec, Complex.ofReal_one, one_smul]
  · have hp : Matrix.vecMulVec
        (WithLp.ofLp (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1)))
        (star (WithLp.ofLp (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1)))) = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.vecMulVec, EuclideanSpace.single, PiLp.single_apply]
    simpa only [hp, Complex.ofReal_one, one_smul, sub_self, smul_zero] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef)

-- The same scalar Hamiltonian on a two-dimensional spectator does not have
-- the one-vector projector gap: its orthogonal basis vector has zero energy.
example : ¬ Matrix.IsGappedGroundState (1 : Matrix (Fin 2) (Fin 2) ℂ) 1
    (EuclideanSpace.single 0 1) 1 := by
  intro hgs
  have hd := (Matrix.isGappedGroundState_iff.mp hgs).2.2.diag_nonneg (i := (1 : Fin 2))
  norm_num [Matrix.vecMulVec, EuclideanSpace.single, PiLp.single_apply,
    Complex.nonneg_iff] at hd

-- An anchor in another component retains its entire positive constraint;
-- neither finite-radius truncation nor an empty operator replaces it.
example {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ} [NeZero q]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (h : LocalHamiltonian Λ q R J)
    (Ω : StateSpace Λ q) (L : ℕ) (i : AdmissibleSupport Λ R)
    (hfar : setDist S.graph (S.truncationSet L) (S.anchor i) = ⊤) :
    S.truncatedEnergyTerm h Ω Δ L i = h.positiveTerm Δ Ω i := by
  simp only [CollarScan.truncatedEnergyTerm, truncatedConstraint, ite_eq_left hfar]

-- With an empty truncation set this retention applies to every original label.
example {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ} [NeZero q]
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (h : LocalHamiltonian Λ q R J)
    (Ω : StateSpace Λ q) (L : ℕ) (hS₀ : S.truncationSet L = ∅) :
    (∑ i, S.truncatedEnergyTerm h Ω Δ L i) = ∑ i, h.positiveTerm Δ Ω i := by
  simp [CollarScan.truncatedEnergyTerm, truncatedConstraint, hS₀, setDist]

end TNLeanTest.ActualMarginalTails
