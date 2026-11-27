/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Polynomial.TailPowerSumUniqueness
import TNLean.MPS.FundamentalTheorem.SectorBNT.UnblockedPeriodicExpansion

/-!
# Power-sum structure of length-dependent coefficients, without blocking

This file answers the power-sum coefficient question.  Whenever the periodic
vectors of a tensor lie, at every positive length, in the span of the periodic
vectors of a separated family of normal tensors, the coefficients of that
expansion are the power sums of finite nonzero weight multisets.  The
expansion holds at *every* positive length, with no blocking, and the
coefficients are eventually rigid.  `PowerSumCoefficients.lean` supplies the
normalization and independence steps this argument uses.

Source: `Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/t1_unblocked.tex`
("Power-sum coefficients without blocking").  The
mathematical argument groups the unblocked irreducible composition factors of
the source into gauge-and-scalar equivalence classes, excludes every
genuinely periodic class by a Vandermonde tail argument on a common multiple
of the periods, and reads the canonical weights off the resulting matching.

## Main results

* `MPSTensor.exists_irreducible_expansion` — the trace-reduction step: every
  tensor's periodic vectors are, at every positive length, a power-sum
  combination of periodic representatives of its irreducible composition
  factors.
* `MPSTensor.exists_matching_of_span` — the matching-before-blocking
  exclusion: under the spanning hypothesis, every representative class is
  gauge-phase equivalent to one of the normal targets.
* `MPSTensor.exists_unblocked_powerSum_coeff` — the unblocked theorem:
  existence of a canonical power-sum expansion at every positive length,
  eventual rigidity of arbitrary expansion coefficients, and the dimension bound
  `∑ γ, n γ * DM γ ≤ DB`.
* `MPSTensor.exists_unblocked_powerSum_coeff_unique` — the same, together with
  uniqueness of the finite nonzero weight multisets.
-/

open MPTensor

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **Matching before blocking** (exclusion of unmatched periodic classes).

Under the spanning hypothesis, every representative class `A j` of
`exists_irreducible_expansion` is gauge-phase equivalent, up to a cast along
the equal dimensions, to one of the targets `M γ`.

Source: `t1_unblocked.tex`, Proposition `moa-t1:exclusion`. -/
theorem exists_matching_of_span
    {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ))
    (hspan : ∀ N : ℕ, 0 < N → ∃ c : Γ → ℂ, ∀ σ : Fin N → Fin d,
      mpv B σ = ∑ γ, c γ * mpv (M γ) σ)
    {g : ℕ} {dimRep : Fin g → ℕ} (A : (j : Fin g) → MPSTensor d (dimRep j))
    (per : Fin g → ℕ) (copies : Fin g → ℕ) (α : (j : Fin g) → Fin (copies j) → ℂ)
    (hPer : ∀ j, IsPeriodic (per j) (A j))
    (hCopiesPos : ∀ j, 0 < copies j)
    (hα : ∀ j q, α j q ≠ 0)
    (hRepDistinct : ∀ j k : Fin g, j ≠ k → ∀ h : dimRep j = dimRep k,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k))
    (hBeq : ∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
      mpv B σ = ∑ j : Fin g, (∑ q : Fin (copies j), (α j q) ^ L) * mpv (A j) σ) :
    ∀ j : Fin g, ∃ γ : Γ, ∃ h : dimRep j = DM γ,
      GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (M γ) := by
  classical
  have hDneC : ∀ γ, NeZero (DM γ) := fun γ => ⟨(hD γ).ne'⟩
  choose C τ0 hτ0 hGaugeC hmpvC hLCC hNTC using
    fun γ => letI := hDneC γ; exists_leftCanonical_normalTensor_scale_of_isNormal (hM γ)
  have hPerC : ∀ γ, IsPeriodic 1 (C γ) := fun γ =>
    (IsPeriodic.one_iff_primitive (C γ)).2
      ⟨(hNTC γ).no_invariant_proj, hLCC γ, (hNTC γ).primitive_transfer⟩
  have hdistinctC : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (C γ)) (C δ) := by
    intro γ δ hne h hGPE
    exact hdistinct γ δ hne h
      (gaugePhaseEquiv_of_smul_smul_cast h (hτ0 γ) (hτ0 δ)
        (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast h (hGaugeC γ) hGPE (hGaugeC δ)))
  set lab : Fin g → Option Γ := fun j =>
    if h : ∃ γ : Γ, ∃ hd : dimRep j = DM γ,
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hd) (A j)) (C γ) then
      some (Classical.choose h) else none with hlab_def
  have hUnmatched : ∀ j, lab j = none → ∀ γ : Γ, ∀ h : dimRep j = DM γ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (C γ) := by
    intro j hlabj γ h hGPE
    have hwit : ∃ γ' : Γ, ∃ hd : dimRep j = DM γ',
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hd) (A j)) (C γ') := ⟨γ, h, hGPE⟩
    have hsome : lab j = some (Classical.choose hwit) := by
      simp only [hlab_def, dite_eq_left hwit]
    rw [hlabj] at hsome
    exact Option.some_ne_none _ hsome.symm
  have hMatched : ∀ j γ, lab j = some γ → ∃ h : dimRep j = DM γ,
      GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (C γ) := by
    intro j γ hlabj
    by_cases hex : ∃ γ' : Γ, ∃ hd : dimRep j = DM γ',
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hd) (A j)) (C γ')
    · have hsome : lab j = some (Classical.choose hex) := by simp only [hlab_def, dite_eq_left hex]
      rw [hlabj] at hsome
      have hγeq : γ = Classical.choose hex := Option.some_injective _ hsome
      rw [hγeq]
      exact Classical.choose_spec hex
    · have hnone : lab j = none := by simp only [hlab_def, dite_eq_right hex]
      rw [hlabj] at hnone
      exact absurd hnone (Option.some_ne_none _)
  -- Combined family of unmatched representatives and normal targets.
  set U : Type := {j : Fin g // lab j = none} with hU_def
  set dimF : U ⊕ Γ → ℕ := Sum.elim (fun u => dimRep u.1) DM with hdimF_def
  set F : (x : U ⊕ Γ) → MPSTensor d (dimF x) := Sum.rec (fun u => A u.1) C with hF_def
  set perF : U ⊕ Γ → ℕ := Sum.elim (fun u => per u.1) (fun _ => 1) with hperF_def
  have hPerF : ∀ x, IsPeriodic (perF x) (F x) := by rintro (u | γ); exacts [hPer u.1, hPerC γ]
  set p : ℕ := Finset.univ.lcm per with hp_def
  have hp0 : p ≠ 0 := by
    intro h0
    rw [hp_def, Finset.lcm_eq_zero_iff] at h0
    obtain ⟨j, -, hj0⟩ := h0
    exact (hPer j).period_pos.ne' hj0
  have : NeZero p := ⟨hp0⟩
  have hDivF : ∀ x, perF x ∣ p := by
    rintro (u | γ)
    · exact Finset.dvd_lcm (Finset.mem_univ u.1)
    · exact one_dvd p
  have hNonrepF : ∀ x y : U ⊕ Γ, x ≠ y → ∀ h : dimF x = dimF y,
      ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) h) (F x)) (F y) := by
    rintro (u | γ) (u' | γ') hxy h
    · exact not_repeatedBlocks_of_not_gaugePhaseEquiv
        (hRepDistinct u.1 u'.1 (fun heq => hxy (by rw [Subtype.ext heq])) h)
    · exact not_repeatedBlocks_of_not_gaugePhaseEquiv (hUnmatched u.1 u.2 γ' h)
    · intro hRep
      exact hUnmatched u'.1 u'.2 γ h.symm
        (gaugePhaseEquiv_cast_symm_of_repeatedBlocks h hRep)
    · exact not_repeatedBlocks_of_not_gaugePhaseEquiv
        (hdistinctC γ γ' (fun heq => hxy (by rw [heq])) h)
  obtain ⟨N₀, hLI⟩ :=
    exists_eventually_linearIndependent_of_periodic_blocks_not_repeated F perF hPerF p hDivF
      hNonrepF
  -- Matching scalars: whenever `lab j = some γ`, the periodic vectors of `C γ`
  -- are a power of a fixed nonzero scalar times those of `A j`.
  have hθex : ∀ j : Fin g, ∃ θ : ℂ, θ ≠ 0 ∧
      ∀ γ : Γ, lab j = some γ → ∀ N, 0 < N → ∀ σ : Fin N → Fin d,
        mpv (C γ) σ = θ ^ N * mpv (A j) σ := by
    intro j
    rcases hlj : lab j with _ | γ₀
    · refine ⟨1, one_ne_zero, fun γ hc => ?_⟩
      exact absurd hc (by simp)
    · obtain ⟨h, hGPE⟩ := hMatched j γ₀ hlj
      obtain ⟨θ, hθne, hθmpv⟩ := MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast (A j) (C γ₀) h hGPE
      refine ⟨θ, hθne, fun γ hc N hN σ => ?_⟩
      have hγeq : γ₀ = γ := Option.some_injective _ hc
      subst hγeq
      exact hθmpv N hN σ
  choose θ hθne hθmpv using hθex
  -- Every unmatched class is excluded by the tail power-sum uniqueness lemma.
  have hUEmpty : IsEmpty U := by
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨u⟩ := hne
    have hcontra : ∀ n : ℕ, N₀ ≤ n → 1 ≤ n →
        (∑ q : Fin (copies u.1), (α u.1 q) ^ (p * n)) = 0 := by
      intro n hn hn1
      have hpn_pos : 0 < p * n := Nat.mul_pos (Nat.pos_of_ne_zero hp0) hn1
      obtain ⟨c, hc⟩ := hspan (p * n) hpn_pos
      set gW : U ⊕ Γ → ℂ := Sum.elim
        (fun u' => ∑ q : Fin (copies u'.1), (α u'.1 q) ^ (p * n))
        (fun γ => (∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
            (∑ q : Fin (copies j), (α j q) ^ (p * n)) * (θ j)⁻¹ ^ (p * n))
          - c γ * (τ0 γ)⁻¹ ^ (p * n)) with hgW_def
      have hzero : ∑ x : U ⊕ Γ, gW x • mpvState (α := Fin d) (F x) (p * n) = 0 := by
        apply sum_smul_mpvState_eq_zero
        intro σ
        have hBσ := hBeq (p * n) hpn_pos σ
        have hcσ := hc σ
        have hsplit : ∑ j : Fin g, (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ =
            ∑ u' : U, (∑ q : Fin (copies u'.1), (α u'.1 q) ^ (p * n)) * mpv (A u'.1) σ +
              ∑ γ : Γ, ∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ := by
          have hfw :
              ∑ j : Fin g, (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ =
                ∑ o : Option Γ, ∑ j ∈ Finset.univ.filter (fun j => lab j = o),
                  (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ :=
            (Finset.sum_fiberwise Finset.univ lab
              (fun j => (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ)).symm
          rw [hfw, Fintype.sum_option]
          congr 1
          exact Finset.sum_subtype (Finset.univ.filter (fun j => lab j = none))
            (fun j => by simp)
            (fun j => (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ)
        have hmatchTerm : ∀ γ : Γ,
            ∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ =
              (∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                (∑ q : Fin (copies j), (α j q) ^ (p * n)) * (θ j)⁻¹ ^ (p * n)) *
                mpv (C γ) σ := by
          intro γ
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hlabj : lab j = some γ := (Finset.mem_filter.mp hj).2
          have hθmpvj := hθmpv j γ hlabj (p * n) hpn_pos σ
          have hθLne : (θ j) ^ (p * n) ≠ 0 := pow_ne_zero _ (hθne j)
          have hmulboth := congrArg (fun x => ((θ j) ^ (p * n))⁻¹ * x) hθmpvj
          simp only [← mul_assoc, inv_mul_cancel₀ hθLne, one_mul] at hmulboth
          rw [inv_pow, mul_assoc, hmulboth]
        have hcC : ∀ γ : Γ, c γ * mpv (M γ) σ = c γ * (τ0 γ)⁻¹ ^ (p * n) * mpv (C γ) σ := by
          intro γ
          have hτLne : (τ0 γ) ^ (p * n) ≠ 0 := pow_ne_zero _ (hτ0 γ)
          have hmulboth := congrArg (fun x => ((τ0 γ) ^ (p * n))⁻¹ * x) (hmpvC γ (p * n) σ)
          simp only [← mul_assoc, inv_mul_cancel₀ hτLne, one_mul] at hmulboth
          rw [inv_pow, mul_assoc, hmulboth]
        have hgoal :
            (∑ u' : U, gW (Sum.inl u') * mpv (F (Sum.inl u')) σ) +
              ∑ γ : Γ, gW (Sum.inr γ) * mpv (F (Sum.inr γ)) σ = 0 := by
          have hUeq : ∑ u' : U, gW (Sum.inl u') * mpv (F (Sum.inl u')) σ
              = ∑ u' : U, (∑ q : Fin (copies u'.1), (α u'.1 q) ^ (p * n)) * mpv (A u'.1) σ :=
            Finset.sum_congr rfl fun u' _ => by
              rw [hgW_def, hF_def]; rfl
          have hΓeq : ∑ γ : Γ, gW (Sum.inr γ) * mpv (F (Sum.inr γ)) σ
              = ∑ γ : Γ, ((∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                  (∑ q : Fin (copies j), (α j q) ^ (p * n)) * (θ j)⁻¹ ^ (p * n))
                - c γ * (τ0 γ)⁻¹ ^ (p * n)) * mpv (C γ) σ :=
            Finset.sum_congr rfl fun γ _ => by
              rw [hgW_def, hF_def]; rfl
          rw [hUeq, hΓeq]
          have hexpand :
              ∑ γ : Γ, ((∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                  (∑ q : Fin (copies j), (α j q) ^ (p * n)) * (θ j)⁻¹ ^ (p * n))
                - c γ * (τ0 γ)⁻¹ ^ (p * n)) * mpv (C γ) σ =
              (∑ γ : Γ, ∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ) -
                ∑ γ : Γ, c γ * mpv (M γ) σ := by
            simp only [sub_mul]
            rw [Finset.sum_sub_distrib]
            have e1 : ∑ γ : Γ, (∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                  (∑ q : Fin (copies j), (α j q) ^ (p * n)) * (θ j)⁻¹ ^ (p * n)) * mpv (C γ) σ
                = ∑ γ : Γ, ∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                    (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ :=
              Finset.sum_congr rfl fun γ _ => (hmatchTerm γ).symm
            have e2 : ∑ γ : Γ, c γ * (τ0 γ)⁻¹ ^ (p * n) * mpv (C γ) σ =
                ∑ γ : Γ, c γ * mpv (M γ) σ :=
              Finset.sum_congr rfl fun γ _ => (hcC γ).symm
            rw [e1, e2]
          rw [hexpand]
          rw [show ∑ u' : U, (∑ q : Fin (copies u'.1), (α u'.1 q) ^ (p * n)) * mpv (A u'.1) σ +
                ((∑ γ : Γ, ∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                    (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ) -
                  ∑ γ : Γ, c γ * mpv (M γ) σ)
              = ((∑ u' : U, (∑ q : Fin (copies u'.1), (α u'.1 q) ^ (p * n)) * mpv (A u'.1) σ) +
                  ∑ γ : Γ, ∑ j ∈ Finset.univ.filter (fun j => lab j = some γ),
                    (∑ q : Fin (copies j), (α j q) ^ (p * n)) * mpv (A j) σ) -
                ∑ γ : Γ, c γ * mpv (M γ) σ from by ring]
          rw [← hsplit, ← hBσ, hcσ]
          ring
        simpa [Fintype.sum_sum_type] using hgoal
      have hcoef := Fintype.linearIndependent_iff.1 (hLI n hn) gW hzero (Sum.inl u)
      simpa [hgW_def] using hcoef
    have hΛ : (0 : ℂ) ∉
        (↑(List.ofFn (fun q : Fin (copies u.1) => (α u.1 q) ^ p)) : Multiset ℂ) := by
      rw [Multiset.mem_coe]
      rw [List.mem_ofFn']
      rintro ⟨q, hq⟩
      exact pow_ne_zero p (hα u.1 q) hq
    have hΛzero := Multiset.eq_zero_of_notMem_zero_of_forall_sum_map_pow_eq_zero hΛ
      ⟨max N₀ 1, fun n hn => by
        have hle : N₀ ≤ n := le_trans (le_max_left N₀ 1) hn
        have hge1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hn
        have := hcontra n hle hge1
        rw [Multiset.map_coe, Multiset.sum_coe]
        rw [List.map_ofFn]
        rw [List.sum_ofFn]
        rw [← this]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [Function.comp]
        rw [← pow_mul, Nat.mul_comm]⟩
    have hcard := congrArg Multiset.card hΛzero
    rw [Multiset.coe_card, List.length_ofFn, Multiset.card_zero] at hcard
    exact (hCopiesPos u.1).ne' hcard
  intro j
  by_contra hj
  push Not at hj
  have hlabNone : lab j = none := by
    by_cases hex : ∃ γ' : Γ, ∃ hd : dimRep j = DM γ',
        GaugePhaseEquiv (cast (congr_arg (MPSTensor d) hd) (A j)) (C γ')
    · obtain ⟨γ', h', hGPE'⟩ := hex
      have hGPE'' : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h') (A j))
          (fun i => τ0 γ' • M γ' i) :=
        gaugePhaseEquiv_trans hGPE' (hGaugeC γ').symm.toGaugePhaseEquiv
      exact absurd (gaugePhaseEquiv_of_gaugePhaseEquiv_smul_right (hτ0 γ') hGPE'')
        (hj γ' h')
    · simp only [hlab_def, dite_eq_right hex]
  exact hUEmpty.false ⟨j, hlabNone⟩

/-! ### The canonical expansion at every positive length -/

/-- A finite family of nonzero weights indexed by a fintype is reindexed by `Fin (card ι)`
without changing its power sums. -/
theorem exists_fin_weights_of_sum_pow_card {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : ∀ i, w i ≠ 0) :
    ∃ μ : Fin (Fintype.card ι) → ℂ, (∀ k, μ k ≠ 0) ∧
      ∀ m : ℕ, ∑ k, (μ k) ^ m = ∑ i, (w i) ^ m :=
  ⟨fun k => w ((Fintype.equivFin ι).symm k), fun _ => hw _, fun m =>
    Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (w i) ^ m)⟩

/-- **Unblocked power-sum coefficients** (`t1_unblocked.tex`, Theorem
`moa-t1:theorem`).

If the periodic vectors of `B` lie, at every positive length, in the span of
the periodic vectors of a finite family of pairwise inequivalent normal
tensors `M γ`, then there are finite nonzero weight multisets — one per
target, recorded as `n γ` weights `μ γ k` — whose power sums give the
periodic vectors of `B` at *every* positive length, with no blocking.  Past a
threshold length, the coefficients of any expansion of `B` in the `M γ` are
forced to equal these power sums; the threshold is a positive length.  The
multiplicities satisfy the dimension bound `∑ γ, n γ * DM γ ≤ DB`, because every
composition factor of `B` matched to `M γ` has bond dimension `DM γ`.

Source: `Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/t1_unblocked.tex`,
Theorem `moa-t1:theorem`. -/
theorem exists_unblocked_powerSum_coeff
    {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ))
    (hspan : ∀ N : ℕ, 0 < N → ∃ c : Γ → ℂ, ∀ σ : Fin N → Fin d,
      mpv B σ = ∑ γ, c γ * mpv (M γ) σ) :
    ∃ (n : Γ → ℕ) (μ : ∀ γ, Fin (n γ) → ℂ),
      (∀ γ k, μ γ k ≠ 0) ∧
      (∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
        mpv B σ = ∑ γ, (∑ k, (μ γ k) ^ L) * mpv (M γ) σ) ∧
      (∃ L₀ : ℕ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∀ c : Γ → ℂ,
        (∀ σ : Fin L → Fin d, mpv B σ = ∑ γ, c γ * mpv (M γ) σ) →
        ∀ γ, c γ = ∑ k, (μ γ k) ^ L) ∧
      ∑ γ, n γ * DM γ ≤ DB := by
  classical
  have hDne : ∀ γ, NeZero (DM γ) := fun γ => ⟨(hD γ).ne'⟩
  obtain ⟨g, dimRep, A, per, copies, α, hDimPos, hPerA, hCopiesPos, hαne, hRepDistinct, hBeq,
      hdimSum⟩ :=
    exists_irreducible_expansion B
  have hmatch := exists_matching_of_span B M hM hD hdistinct hspan A per copies α hPerA
    hCopiesPos hαne hRepDistinct hBeq
  choose labFn labH labGPE using hmatch
  choose θ hθne hθmpv using
    fun j => MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast (A j) (M (labFn j)) (labH j) (labGPE j)
  set lamW : (j : Fin g) → Fin (copies j) → ℂ := fun j q => (α j q) * (θ j)⁻¹ with hlamW_def
  have hlamWne : ∀ j q, lamW j q ≠ 0 := fun j q => mul_ne_zero (hαne j q) (inv_ne_zero (hθne j))
  have hAeq : ∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
      mpv B σ = ∑ j : Fin g, (∑ q : Fin (copies j), (lamW j q) ^ L) * mpv (M (labFn j)) σ := by
    intro L hL σ
    rw [hBeq L hL σ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hθL : (θ j) ^ L ≠ 0 := pow_ne_zero L (hθne j)
    have hθmpvj := hθmpv j L hL σ
    have hmulboth := congrArg (fun x => ((θ j) ^ L)⁻¹ * x) hθmpvj
    simp only [← mul_assoc, inv_mul_cancel₀ hθL, one_mul] at hmulboth
    simp only [hlamW_def, mul_pow, inv_pow]
    rw [← Finset.sum_mul, mul_assoc, hmulboth]
  have hpack : ∀ γ : Γ, ∃ (n : ℕ) (μ : Fin n → ℂ),
      n = ∑ j : Fin g, (if labFn j = γ then copies j else 0) ∧ (∀ k, μ k ≠ 0) ∧
      ∀ m : ℕ, ∑ k, (μ k) ^ m = ∑ j : Fin g, (if labFn j = γ then
          ∑ q : Fin (copies j), (lamW j q) ^ m else 0) := by
    intro γ
    obtain ⟨μ, hμne, hμsum⟩ := exists_fin_weights_of_sum_pow_card
      (ι := {x : (Σ j : Fin g, Fin (copies j)) // labFn x.1 = γ})
      (fun x => lamW x.1.1 x.1.2) (fun x => hlamWne x.1.1 x.1.2)
    refine ⟨_, μ, ?_, hμne, fun m => ?_⟩
    · rw [Fintype.card_subtype, Finset.card_filter, ← Finset.univ_sigma_univ,
        Finset.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hlab : labFn j = γ <;> simp [hlab]
    rw [hμsum m]
    rw [← Finset.sum_subtype
      (Finset.univ.filter (fun x : (Σ j : Fin g, Fin (copies j)) => labFn x.1 = γ))
      (fun x => by simp) (fun x => (lamW x.1 x.2) ^ m)]
    rw [Finset.sum_filter, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hlab : labFn j = γ
    · simp [hlab]
    · simp [hlab]
  choose n μ hn hμne hμsum using hpack
  have hCanonical : ∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
      mpv B σ = ∑ γ, (∑ k, (μ γ k) ^ L) * mpv (M γ) σ := by
    intro L hL σ
    rw [hAeq L hL σ]
    have hregroup : ∑ j : Fin g, (∑ q : Fin (copies j), (lamW j q) ^ L) * mpv (M (labFn j)) σ =
        ∑ γ : Γ, ∑ j ∈ Finset.univ.filter (fun j => labFn j = γ),
          (∑ q : Fin (copies j), (lamW j q) ^ L) * mpv (M (labFn j)) σ :=
      (Finset.sum_fiberwise Finset.univ labFn
        (fun j => (∑ q : Fin (copies j), (lamW j q) ^ L) * mpv (M (labFn j)) σ)).symm
    rw [hregroup]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hstep : ∑ j ∈ Finset.univ.filter (fun j => labFn j = γ),
        (∑ q : Fin (copies j), (lamW j q) ^ L) * mpv (M (labFn j)) σ =
        (∑ j ∈ Finset.univ.filter (fun j => labFn j = γ),
          ∑ q : Fin (copies j), (lamW j q) ^ L) * mpv (M γ) σ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hlabj : labFn j = γ := (Finset.mem_filter.mp hj).2
      rw [hlabj]
    rw [hstep, hμsum γ L, Finset.sum_filter]
  have hbound : ∑ γ, n γ * DM γ ≤ DB := by
    calc ∑ γ, n γ * DM γ
        = ∑ γ, (∑ j : Fin g, if labFn j = γ then copies j else 0) * DM γ :=
          Finset.sum_congr rfl fun γ _ => by rw [hn γ]
      _ = ∑ γ, ∑ j : Fin g, if labFn j = γ then copies j * DM γ else 0 := by
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
      _ = ∑ j : Fin g, ∑ γ, if labFn j = γ then copies j * DM γ else 0 := Finset.sum_comm
      _ = ∑ j : Fin g, copies j * dimRep j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [labH j]
      _ ≤ DB := hdimSum
  refine ⟨n, μ, hμne, hCanonical, ?_, hbound⟩
  choose C τ0 hτ0 hGaugeC hmpvC hLCC hNTC using
    fun γ => letI := hDne γ; exists_leftCanonical_normalTensor_scale_of_isNormal (hM γ)
  have hCdist : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (C γ)) (C δ) := by
    intro γ δ hne h hGPE
    exact hdistinct γ δ hne h
      (gaugePhaseEquiv_of_smul_smul_cast h (hτ0 γ) (hτ0 δ)
        (gaugePhaseEquiv_of_gaugeEquiv_left_right_cast h (hGaugeC γ) hGPE (hGaugeC δ)))
  obtain ⟨N₀, hLI⟩ :=
    exists_eventually_linearIndependent_of_normalTensor_distinct C
      (fun γ => (hNTC γ)) hCdist
  refine ⟨N₀ + 1, Nat.succ_pos _, fun L hL c hc γ => ?_⟩
  have hL0 : 0 < L := by omega
  have hzero : ∀ σ : Fin L → Fin d,
      ∑ γ, ((c γ - ∑ k, (μ γ k) ^ L) * ((τ0 γ) ^ L)⁻¹) * mpv (C γ) σ = 0 := by
    intro σ
    have hdiff : ∑ γ, c γ * mpv (M γ) σ = ∑ γ, (∑ k, (μ γ k) ^ L) * mpv (M γ) σ :=
      (hc σ).symm.trans (hCanonical L hL0 σ)
    have hexpand : ∑ γ, (c γ - ∑ k, (μ γ k) ^ L) * mpv (M γ) σ = 0 := by
      have hstep2 : ∑ γ, (c γ - ∑ k, (μ γ k) ^ L) * mpv (M γ) σ
          = ∑ γ, c γ * mpv (M γ) σ - ∑ γ, (∑ k, (μ γ k) ^ L) * mpv (M γ) σ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun γ _ => by ring
      rw [hstep2, hdiff, sub_self]
    rw [← hexpand]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have hτL : (τ0 γ) ^ L ≠ 0 := pow_ne_zero L (hτ0 γ)
    have hmulboth := congrArg (fun x => ((τ0 γ) ^ L)⁻¹ * x) (hmpvC γ L σ)
    simp only [← mul_assoc, inv_mul_cancel₀ hτL, one_mul] at hmulboth
    rw [mul_assoc, hmulboth]
  have hcoef := Fintype.linearIndependent_iff.1 (hLI L (by omega))
    (fun γ => (c γ - ∑ k, (μ γ k) ^ L) * ((τ0 γ) ^ L)⁻¹)
    (sum_smul_mpvState_eq_zero C
      (fun γ => (c γ - ∑ k, (μ γ k) ^ L) * ((τ0 γ) ^ L)⁻¹) hzero) γ
  have hτL : ((τ0 γ) ^ L)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero L (hτ0 γ))
  have hdz : c γ - ∑ k, (μ γ k) ^ L = 0 := by
    rcases mul_eq_zero.mp hcoef with h | h
    · exact h
    · exact absurd h hτL
  exact sub_eq_zero.mp hdz

/-- The power sum of the multiset of a finite weight family is the finite power sum. -/
theorem sum_map_pow_ofFn {n : ℕ} (μ : Fin n → ℂ) (L : ℕ) :
    ((↑(List.ofFn μ) : Multiset ℂ).map (· ^ L)).sum = ∑ k, (μ k) ^ L := by
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
  rfl

/-- **Unblocked power-sum coefficients with unique weight multisets**
(`t1_unblocked.tex`, Theorem `moa-t1:theorem`, uniqueness clause).

In addition to the conclusions of `exists_unblocked_powerSum_coeff`, any other
finite families of nonzero weights whose power sums give an expansion of the
periodic vectors of `B` at all sufficiently large lengths have, target by
target, the same multiset of weights, counting repetitions. -/
private theorem exists_unblocked_powerSum_coeff_unique_fin
    {DB : ℕ} (B : MPSTensor d DB) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPSTensor d (DM γ))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (M γ)) (M δ))
    (hspan : ∀ N : ℕ, 0 < N → ∃ c : Γ → ℂ, ∀ σ : Fin N → Fin d,
      mpv B σ = ∑ γ, c γ * mpv (M γ) σ) :
    ∃ (n : Γ → ℕ) (μ : ∀ γ, Fin (n γ) → ℂ),
      (∀ γ k, μ γ k ≠ 0) ∧
      (∀ L : ℕ, 0 < L → ∀ σ : Fin L → Fin d,
        mpv B σ = ∑ γ, (∑ k, (μ γ k) ^ L) * mpv (M γ) σ) ∧
      (∃ L₀ : ℕ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∀ c : Γ → ℂ,
        (∀ σ : Fin L → Fin d, mpv B σ = ∑ γ, c γ * mpv (M γ) σ) →
        ∀ γ, c γ = ∑ k, (μ γ k) ^ L) ∧
      ∑ γ, n γ * DM γ ≤ DB ∧
      ∀ (n' : Γ → ℕ) (μ' : ∀ γ, Fin (n' γ) → ℂ), (∀ γ k, μ' γ k ≠ 0) →
        (∃ L₁ : ℕ, ∀ L, L₁ ≤ L → ∀ σ : Fin L → Fin d,
          mpv B σ = ∑ γ, (∑ k, (μ' γ k) ^ L) * mpv (M γ) σ) →
        ∀ γ, (↑(List.ofFn (μ' γ)) : Multiset ℂ) = ↑(List.ofFn (μ γ)) := by
  obtain ⟨n, μ, hμne, hexp, ⟨L₀, hL₀, hrig⟩, hbound⟩ :=
    exists_unblocked_powerSum_coeff B M hM hD hdistinct hspan
  refine ⟨n, μ, hμne, hexp, ⟨L₀, hL₀, hrig⟩, hbound, ?_⟩
  intro n' μ' hμ'ne ⟨L₁, hL₁⟩ γ
  have hnz : ∀ (m : ℕ) (w : Fin m → ℂ), (∀ k, w k ≠ 0) →
      (0 : ℂ) ∉ (↑(List.ofFn w) : Multiset ℂ) := by
    intro m w hw h0
    rw [Multiset.mem_coe, List.mem_ofFn'] at h0
    obtain ⟨k, hk⟩ := h0
    exact hw k hk
  refine Multiset.eq_of_notMem_zero_of_forall_sum_map_pow_eq (hnz _ _ (hμ'ne γ))
    (hnz _ _ (hμne γ)) ⟨max L₀ L₁, fun L hL => ?_⟩
  rw [sum_map_pow_ofFn, sum_map_pow_ofFn]
  exact (hrig L (le_trans (le_max_left _ _) hL) (fun γ => ∑ k, (μ' γ k) ^ L)
    (hL₁ L (le_trans (le_max_right _ _) hL)) γ)

/-- **Unblocked power-sum coefficients with unique weight multisets**
(`t1_unblocked.tex`, Theorem `moa-t1:theorem`, uniqueness clause).

In addition to the conclusions of `exists_unblocked_powerSum_coeff`, any other
finite families of nonzero weights whose power sums give an expansion of the
periodic vectors of `B` at all sufficiently large lengths have, target by
target, the same multiset of weights, counting repetitions.  The physical alphabet is
relabelled by `Fin (Fintype.card β)`. -/
theorem exists_unblocked_powerSum_coeff_unique {β : Type*} [Fintype β]
    {DB : ℕ} (B : MPTensor β (Fin DB)) {Γ : Type*} [Fintype Γ] {DM : Γ → ℕ}
    (M : ∀ γ, MPTensor β (Fin (DM γ)))
    (hM : ∀ γ, Kraus.IsNormal (M γ)) (hD : ∀ γ, 0 < DM γ)
    (hdistinct : ∀ γ δ : Γ, γ ≠ δ → ∀ h : DM γ = DM δ,
      ¬ GaugePhaseEquiv (cast (congr_arg (fun n ↦ MPTensor β (Fin n)) h) (M γ)) (M δ))
    (hspan : ∀ N : ℕ, 0 < N → ∃ c : Γ → ℂ, ∀ σ : Fin N → β,
      mpv B σ = ∑ γ, c γ * mpv (M γ) σ) :
    ∃ (n : Γ → ℕ) (μ : ∀ γ, Fin (n γ) → ℂ),
      (∀ γ k, μ γ k ≠ 0) ∧
      (∀ L : ℕ, 0 < L → ∀ σ : Fin L → β,
        mpv B σ = ∑ γ, (∑ k, (μ γ k) ^ L) * mpv (M γ) σ) ∧
      (∃ L₀ : ℕ, 0 < L₀ ∧ ∀ L, L₀ ≤ L → ∀ c : Γ → ℂ,
        (∀ σ : Fin L → β, mpv B σ = ∑ γ, c γ * mpv (M γ) σ) →
        ∀ γ, c γ = ∑ k, (μ γ k) ^ L) ∧
      ∑ γ, n γ * DM γ ≤ DB ∧
      ∀ (n' : Γ → ℕ) (μ' : ∀ γ, Fin (n' γ) → ℂ), (∀ γ k, μ' γ k ≠ 0) →
        (∃ L₁ : ℕ, ∀ L, L₁ ≤ L → ∀ σ : Fin L → β,
          mpv B σ = ∑ γ, (∑ k, (μ' γ k) ^ L) * mpv (M γ) σ) →
        ∀ γ, (↑(List.ofFn (μ' γ)) : Multiset ℂ) = ↑(List.ofFn (μ γ)) := by
  let f : Fin (Fintype.card β) ≃ β := (Fintype.equivFin β).symm
  have hσ : ∀ {L : ℕ} (σ : Fin L → β), (fun n ↦ f (f.symm (σ n))) = σ := fun σ ↦ by
    funext n; exact f.apply_symm_apply (σ n)
  obtain ⟨n, μ, hμne, hexp, ⟨L₀, hL₀, hrig⟩, hbound, huniq⟩ :=
    exists_unblocked_powerSum_coeff_unique_fin (Kraus.reindexPhysical f B)
      (fun γ ↦ Kraus.reindexPhysical f (M γ))
      (fun γ ↦ (isNormal_reindexPhysical_equiv f _).2 (hM γ)) hD
      (fun γ δ hγδ h hG ↦ hdistinct γ δ hγδ h <| (gaugePhaseEquiv_reindexPhysical_equiv f _ _).1
        (by rw [reindexPhysical_cast_dim f h (M γ)]; exact hG))
      (fun N hN ↦ by
        obtain ⟨c, hc⟩ := hspan N hN
        exact ⟨c, fun σ ↦ by simp only [MPTensor.mpv_reindexPhysical]; exact hc _⟩)
  refine ⟨n, μ, hμne, fun L hL σ ↦ ?_, ⟨L₀, hL₀, fun L hL c hc ↦ hrig L hL c fun τ ↦ ?_⟩,
    hbound, fun n' μ' hμ' ⟨L₁, h⟩ ↦ huniq n' μ' hμ' ⟨L₁, fun L hL τ ↦ ?_⟩⟩
  · have h := hexp L hL fun n ↦ f.symm (σ n)
    simpa only [MPTensor.mpv_reindexPhysical, hσ] using h
  · simp only [MPTensor.mpv_reindexPhysical]; exact hc _
  · simp only [MPTensor.mpv_reindexPhysical]; exact h L hL _

end MPSTensor
