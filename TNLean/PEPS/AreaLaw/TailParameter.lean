/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialBuffer
import TNLean.PEPS.AreaLaw.MarginalTails

/-!
# The marginal-tail parameter of a general cut

For a finite-range Hamiltonian on a finite induced square-lattice domain, the parameter
`ℬ_A` of Lemma 3.1 of the area-law manuscript is at most a constant times
`1 + |∂_Λ A|`, for every cut `A`. An admissible support that meets both sides of the cut
contains two sites joined by a walk of length at most `R`, which crosses an edge of the
cut; so the support has a site within distance `R` of the endpoint of that edge inside
`A`. Each edge therefore accounts for at most `v_R μ_R` crossing supports, with
`v_R = 1 + 2R(R + 1)` the diamond count and `μ_R = 2^{v_R - 1}` the number of admissible
supports through a site.

Inserting this bound into the tail estimate of Lemma 3.1 gives the typical-spectrum
statement at the width `C_M √(1 + |∂_Λ A|) log (n + 2)`.

## Main results

* `card_crossingTerms_le_edgeBoundary`: at most `|∂_Λ A| v_R μ_R` admissible supports
  cross a cut `A`.
* `cutLogBudget_le_edgeBoundary`: `ℬ_A ≤ C (1 + |∂_Λ A|)`,
  `eq:initial-local-tail-parameter`, with `C = tailParameterConstant q R`.
* `concentrationWidth_le`: the concentration width is at most
  `C_M √(1 + |∂_Λ A|) log (n + 2)`, with `C_M = typicalWidthConstant q R J Δ M`.
* `LocalHamiltonian.one_sub_rpow_le_typicalMass_edgeBoundary`: the typical marginal
  spectrum at that width.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `02-initial.tex`, lines 202–212, `eq:initial-local-tail-parameter`
  and the concentration statement after it; the counts are those of
  `01-preliminaries.tex`, lines 81–102.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix

namespace TNLean.PEPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-! ### Counting the supports that cross a cut -/

/-- **Crossing supports of a general cut.** At most `|∂_Λ A| v_R μ_R` admissible supports
of range `R` meet both a region `A` and its complement, where `v_R = 1 + 2R(R + 1)` and
`μ_R = 2^{v_R - 1}`. Source: `02-initial.tex`, lines 202–206, with the counts of
`01-preliminaries.tex`, lines 81–102. -/
theorem card_crossingTerms_le_edgeBoundary (Λ : Finset (ℤ × ℤ)) (R : ℕ)
    (A : Finset (Site Λ)) :
    (Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).card ≤
      (edgeBoundary Λ A).card *
        ((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1)) := by
  classical
  -- the supports with a site within distance `R` of the endpoint of `e` inside `A`
  set near : Sym2 (Site Λ) → Finset (AdmissibleSupport Λ R) := fun e ↦
    Finset.univ.filter fun X ↦ ∃ z ∈ e, z ∈ A ∧ ∃ v ∈ X.1,
      ∃ p : (domainGraph Λ).Walk z v, p.length ≤ R
  have hcover : Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A ⊆
      (edgeBoundary Λ A).biUnion near := by
    intro X hX
    simp only [Entropy.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨⟨v, hvX, hvA⟩, w, hwX, hwA⟩ := hX
    obtain ⟨p, hp⟩ := X.2.2 v hvX w hwX
    obtain ⟨d, hd, hdA, hdA'⟩ := p.exists_boundary_dart (A : Set (Site Λ)) hvA hwA
    have hsupp := p.dart_fst_mem_support_of_mem_darts hd
    have hlen := (p.length_takeUntil_le_length hsupp).trans hp
    refine Finset.mem_biUnion.mpr ⟨s(d.fst, d.snd), ?_, ?_⟩
    · simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact ⟨d.adj, d.fst, hdA, d.snd, hdA', rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d.fst, Sym2.mem_mk_left _ _, hdA, v, hvX,
        (p.takeUntil d.fst hsupp).reverse, by simpa using hlen⟩
  have hcard : ∀ e ∈ edgeBoundary Λ A,
      (near e).card ≤ (1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) := by
    intro e he
    simp only [edgeBoundary, Finset.mem_filter] at he
    obtain ⟨-, x, hx, y, hy, rfl⟩ := he
    set ball : Finset (Site Λ) :=
      Finset.univ.filter fun v ↦ ∃ p : (domainGraph Λ).Walk x v, p.length ≤ R
    have hball : ball.card ≤ 1 + 2 * R * (R + 1) :=
      card_le_diamond_of_walks Subtype.val ball Subtype.val_injective
        (fun _ _ h ↦ latticeL1Distance_le_one_of_adj h) x R
        fun v hv ↦ (Finset.mem_filter.mp hv).2
    have hsub : near s(x, y) ⊆
        ball.biUnion fun v ↦ Finset.univ.filter fun X : AdmissibleSupport Λ R ↦ v ∈ X.1 := by
      intro X hX
      obtain ⟨-, z, hz, hzA, v, hvX, p, hp⟩ := Finset.mem_filter.mp hX
      obtain rfl : z = x := by
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · rfl
        · exact absurd hzA hy
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvX⟩⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ball.card * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
          Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦ card_admissibleSupport_containing_le v
      _ ≤ _ := Nat.mul_le_mul_right _ hball
  exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul _ _ _ hcard)

/-! ### The tail parameter -/

/-- The constant `C = v_R μ_R log² (e q^{v_R})` of `eq:initial-local-tail-parameter`, with
`v_R = 1 + 2R(R + 1)` and `μ_R = 2^{v_R - 1}`. It depends only on the local dimension and
the range. Source: `02-initial.tex`, lines 202–206. -/
noncomputable def tailParameterConstant (q R : ℕ) : ℝ :=
  ((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) *
    Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2

/-- The constant of `eq:initial-local-tail-parameter` is at least one for `q ≥ 1`. -/
theorem one_le_tailParameterConstant (hq : 1 ≤ q) (R : ℕ) : 1 ≤ tailParameterConstant q R := by
  have hq' : (1 : ℝ) ≤ (q : ℝ) ^ (1 + 2 * R * (R + 1)) := one_le_pow₀ (by exact_mod_cast hq)
  have hlog : 1 ≤ Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith [Real.exp_pos 1]
  have hcount : (1 : ℝ) ≤ ((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold tailParameterConstant
  nlinarith [one_le_pow₀ (n := 2) hlog]

/-- **The tail parameter of a general cut.** For local dimension `q ≥ 1`, the parameter of
Lemma 3.1 satisfies `ℬ_A ≤ C (1 + |∂_Λ A|)` for every cut `A` of a finite induced domain,
with `C = tailParameterConstant q R`.
Source: `02-initial.tex`, lines 202–206, `eq:initial-local-tail-parameter`. -/
theorem cutLogBudget_le_edgeBoundary (hq : 1 ≤ q) (R : ℕ) (A : Finset (Site Λ)) :
    cutLogBudget Λ q R A ≤ tailParameterConstant q R * (1 + (edgeBoundary Λ A).card) := by
  have hC := one_le_tailParameterConstant hq R
  have hcard : ((Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).card : ℝ) ≤
      (edgeBoundary Λ A).card *
        ((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) := by
    exact_mod_cast card_crossingTerms_le_edgeBoundary Λ R A
  have hb : (0 : ℝ) ≤ (edgeBoundary Λ A).card := Nat.cast_nonneg _
  calc cutLogBudget Λ q R A
      ≤ 1 + (Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).card *
          Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2 :=
        cutLogBudget_le_card hq _
    _ ≤ 1 + (edgeBoundary Λ A).card * tailParameterConstant q R := by
        rw [tailParameterConstant, ← mul_assoc]
        gcongr
    _ ≤ _ := by nlinarith

/-! ### The typical spectrum at the boundary width -/

/-- The constant `C_M = 32 √((1 + J/Δ) C) (M + (e/2 + log 2)/log 2)` of the concentration
statement after Lemma 3.1, with `C = tailParameterConstant q R`. It depends only on
`q, R, J, Δ` and `M`. Source: `02-initial.tex`, lines 207–212. -/
noncomputable def typicalWidthConstant (q R : ℕ) (J Δ M : ℝ) : ℝ :=
  32 * Real.sqrt ((1 + J / Δ) * tailParameterConstant q R) *
    (M + (Real.exp 1 / 2 + Real.log 2) / Real.log 2)

/-- The concentration width of a cut is at most `C_M √(1 + |∂_Λ A|) log (n + 2)`.
Source: `02-initial.tex`, lines 207–212. -/
theorem concentrationWidth_le (hq : 1 ≤ q) (R : ℕ) (hJ : 0 ≤ J) {Δ : ℝ} (hΔ : 0 < Δ)
    (A : Finset (Site Λ)) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    concentrationWidth Λ q R J Δ A n M ≤
      typicalWidthConstant q R J Δ M * Real.sqrt (1 + (edgeBoundary Λ A).card) *
        Real.log (n + 2) := by
  have hϑ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log two_pos (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hc : 0 < Real.exp 1 / 2 + Real.log 2 := by positivity
  have hsqrt : Real.sqrt ((1 + J / Δ) * cutLogBudget Λ q R A) ≤
      Real.sqrt ((1 + J / Δ) * tailParameterConstant q R) *
        Real.sqrt (1 + (edgeBoundary Λ A).card) := by
    rw [← Real.sqrt_mul (by have := one_le_tailParameterConstant hq R; positivity), mul_assoc]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (cutLogBudget_le_edgeBoundary hq R A)
      (by positivity))
  have hfactor : M * Real.log ((n : ℝ) + 2) + Real.exp 1 / 2 + Real.log 2 ≤
      (M + (Real.exp 1 / 2 + Real.log 2) / Real.log 2) * Real.log ((n : ℝ) + 2) := by
    have : Real.exp 1 / 2 + Real.log 2 ≤
        (Real.exp 1 / 2 + Real.log 2) / Real.log 2 * Real.log ((n : ℝ) + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hL hc.le
    linarith
  have hfactor_nonneg : 0 ≤ M * Real.log ((n : ℝ) + 2) + Real.exp 1 / 2 + Real.log 2 := by
    have := mul_nonneg hM (hlog2.le.trans hL)
    linarith
  calc concentrationWidth Λ q R J Δ A n M
      = 32 * Real.sqrt ((1 + J / Δ) * cutLogBudget Λ q R A) *
          (M * Real.log ((n : ℝ) + 2) + Real.exp 1 / 2 + Real.log 2) := rfl
    _ ≤ 32 * (Real.sqrt ((1 + J / Δ) * tailParameterConstant q R) *
          Real.sqrt (1 + (edgeBoundary Λ A).card)) *
          ((M + (Real.exp 1 / 2 + Real.log 2) / Real.log 2) * Real.log ((n : ℝ) + 2)) := by
        gcongr
    _ = _ := by
        unfold typicalWidthConstant
        ring

/-- The typical mass grows with the width of the window. -/
theorem typicalMass_le_typicalMass_of_le {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (S : ℝ) {w w' : ℝ} (h : w ≤ w') :
    Entropy.typicalMass p S w ≤ Entropy.typicalMass p S w' :=
  Finset.sum_le_sum_of_subset_of_nonneg (fun i hi ↦ by
    rw [Entropy.mem_typicalSet] at hi ⊢
    exact ⟨hi.1, hi.2.trans h⟩) fun i _ _ ↦ hp i

/-- **Typical marginal spectrum at the boundary width.** For a gapped ground vector of a
finite-range Hamiltonian with local dimension `q ≥ 1`, every cut `A`, every `n` and every
`M ≥ 0`, the positive eigenvalues of the regional state whose surprisal lies within
`C_M √(1 + |∂_Λ A|) log (n + 2)` of `S_Ω(A)` carry mass at least `1 - (n + 2)^{-M}`, with
`C_M = typicalWidthConstant q R J Δ M`. The manuscript states `n ≥ 1` and `M > 0`.
Source: `02-initial.tex`, lines 207–212. -/
theorem LocalHamiltonian.one_sub_rpow_le_typicalMass_edgeBoundary
    (h : LocalHamiltonian Λ q R J) (hq : 1 ≤ q) (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : StateSpace Λ q}
    (hΔ : 0 < Δ) (hgs : IsGappedGroundState Λ q h.operator E₀ Ω Δ) (A : Finset (Site Λ))
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    1 - ((n : ℝ) + 2) ^ (-M) ≤
      Entropy.typicalMass (reducedState_isHermitian Λ q Ω A).eigenvalues
        (regionalEntropy Λ q Ω A)
        (typicalWidthConstant q R J Δ M * Real.sqrt (1 + (edgeBoundary Λ A).card) *
          Real.log (n + 2)) :=
  (h.one_sub_rpow_le_typicalMass_reducedState hJ hΔ hgs A n M).trans
    (typicalMass_le_typicalMass_of_le (reducedState_posSemidef Λ q Ω A).eigenvalues_nonneg _
      (concentrationWidth_le hq R hJ hΔ A n hM))

end TNLean.PEPS.AreaLaw
