/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Entropy.RelativeGeneratorLocalization
import QICLean.ManyBody.Dynamics.SupportedGaussianIntegral
import QICLean.Analysis.Real.ExplicitThresholds

/-!
# Supported Gaussian averaging

A projected relative-evolution equation constructs a unitary path near the
crossing supports. This path is chosen before the observable, Gaussian
variance and time cutoff. Averaging its product with the separately localized
observable gives a supported operator without increasing the observable norm,
together with an explicit approximation bound. The constants depend only on
the interaction range and norm bound.

The construction is carried out once, on a finite graph whose spheres have at most two
sites, from a localization bound for the relative-evolution generator. The contiguous
chain `Fin L` with its path graph and the finite integer domains with their induced path
graphs are the two specializations.

## Main results

* `exists_supported_gaussian_integral_graphNeighborhood`: the supported path and its
  Gaussian averages on a graph, from a generator localization bound.
* `exists_supported_gaussian_integral`: one supported path and its
  Gaussian averages, with constants uniform in all chain and observable data.
* `exists_supported_gaussian_integral_domain`: the same on finite integer domains, with
  natural radii.

**Source convention (contiguous chains):** The note fixes a contiguous chain in
`part1_arealaw.tex`, lines 91–93, before the Part II argument. The chain sites here
are `Fin L`, as in that argument. The finite-domain statement extends it to the domains of
`part0_preamble.tex`, lines 191–215; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 381–402.
No gap, information bound or reset conclusion is assumed or asserted here.
-/

open ManyBody (ChainSupport DomainSupport lineDomainGraph ChainInteraction DomainInteraction)

open MeasureTheory ProbabilityTheory QuantumCircuit
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace TNLean.MPS.AreaLaw

section Graph

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q R : ℕ} {κ : Type*} [Fintype κ]
  {Y : κ → Finset ι}

/-- A single supported unitary path yields the localized truncated Gaussian integrals for
every supported observable, variance and cutoff, on a finite graph whose spheres have at most
two sites. The evolving interaction `Φ` has supports of graph diameter at most `R` and at
most `R + 1` sites and per-site norm budget `b₀`; the generator of the evolution relative to
the Hermitian `K` is localized on the radius-`⌊ℓ⌋` neighborhood of `Z` with error
`d |V| e^{v|s| - ℓ/2}`. TNLean note, `part2a_mps_information.tex`, lines 381–402. -/
theorem exists_supported_gaussian_integral_graphNeighborhood
    (G : SimpleGraph ι)
    (hSphere : ∀ x : ι, ∀ d : ℕ, (Finset.univ.filter fun y ↦ G.edist x y = d).card ≤ 2)
    (Φ : ManyBody.Interaction (fun _ : ι ↦ Fin q) Y)
    (hDiam : ∀ k, ∀ x ∈ Y k, ∀ z ∈ Y k, G.edist x z ≤ R)
    (hCard : ∀ k, (Y k).card ≤ R + 1)
    (hHerm : ∀ k, (Φ.term k).IsHermitian) (b₀ : ℝ)
    (hBudget : ∀ x : ι, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ Y k), ‖Φ.term k‖ ≤ b₀)
    {K : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hK : K.IsHermitian) (Z : Finset ι) (ℓ d : ℝ)
    (hd : 0 ≤ d)
    (hgen : ∀ s : ℝ,
      ‖ManyBody.heisenbergEvolution Φ.hamiltonian s (Φ.hamiltonian - K) -
        ManyBody.regionExpectation (ManyBody.graphNeighborhood G Z ⌊ℓ⌋₊)
          (ManyBody.heisenbergEvolution Φ.hamiltonian s (Φ.hamiltonian - K))‖ ≤
        d * (Fintype.card ι : ℝ) *
          Real.exp ((2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |s| - ℓ / 2)) :
    let n : ℝ := Fintype.card ι
    let K' := Φ.hamiltonian
    let N := fun S : Finset ι ↦ ManyBody.graphNeighborhood G S ⌊ℓ⌋₊
    let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
      (1 - Real.exp (-(1 / 2)))
    let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
    ∃ U : ℝ → Matrix (ι → Fin q) (ι → Fin q) ℂ,
      U 0 = 1 ∧
      (∀ t, HasDerivAt U
        ((Complex.I • ManyBody.regionExpectation (N Z)
          (ManyBody.heisenbergEvolution K' t (K' - K))) * U t) t) ∧
      (∀ t, U t ∈ Matrix.unitaryGroup (ι → Fin q) ℂ) ∧
      (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (N Z : Finset ι)) ∧
      ∀ (Q : Finset ι) (W : Matrix (ι → Fin q) (ι → Fin q) ℂ),
        W ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) Q →
        ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
          let B := N (Q ∪ Z)
          let M := ∫ t : ℝ in Set.Icc (-T) T,
            ManyBody.regionExpectation (N Q) (ManyBody.heisenbergEvolution K' t W) * U t
              ∂gaussianReal 0 η
          M ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) B ∧
          ‖M‖ ≤ ‖W‖ ∧
          ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K W‖ ≤
            ‖W‖ * (a + d) * n ^ 2 * (1 + T) * Real.exp (v * T - ℓ / 2) := by
  classical
  intro n K' N a v
  have ha : 0 < a := by
    have hden : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    exact div_pos (by positivity) hden
  have hv : 0 < v := by positivity
  obtain ⟨U, hU0, hU, hunit, hsupport, haverage⟩ :=
    ManyBody.exists_supported_gaussian_integral_of_projection_bounds
      (ManyBody.Interaction.isHermitian_hamiltonian hHerm) hK (N Z)
  refine ⟨U, hU0, hU, hunit, fun t ↦ (hsupport t), ?_⟩
  intro Q W hW η T hT B M
  have hgenT (s : ℝ) (hs : |s| ≤ T) :
      ‖ManyBody.heisenbergEvolution K' s (K' - K) -
        ManyBody.regionExpectation (N Z) (ManyBody.heisenbergEvolution K' s (K' - K))‖ ≤
          d * n * Real.exp (v * T - ℓ / 2) :=
    (hgen s).trans (mul_le_mul_of_nonneg_left
      (Real.exp_mul_sub_le_exp_mul_sub hv.le hs) (mul_nonneg hd (Nat.cast_nonneg _)))
  have hnear (t : ℝ) (ht : |t| ≤ T) :
      ‖ManyBody.heisenbergEvolution K' t W -
        ManyBody.regionExpectation (N Q) (ManyBody.heisenbergEvolution K' t W)‖ ≤
          ‖W‖ * a * n ^ 2 * Real.exp (v * T - ℓ / 2) := by
    have hloc :=
      ManyBody.norm_heisenberg_sub_regionExpectation_graphNeighborhood_le_of_sphere_le_two
        G Φ hHerm R hDiam hCard hSphere b₀ hBudget Q hW ℓ t
    have hc : (Q.card : ℝ) ≤ n := by
      change (Q.card : ℝ) ≤ (Fintype.card ι : ℝ)
      exact_mod_cast Finset.card_le_univ Q
    calc
      _ ≤ a * (Q.card : ℝ) ^ 2 * ‖W‖ * Real.exp (v * |t| - ℓ / 2) := hloc
      _ ≤ a * (Q.card : ℝ) ^ 2 * ‖W‖ * Real.exp (v * T - ℓ / 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_mul_sub_le_exp_mul_sub hv.le ht) (by positivity)
      _ ≤ a * n ^ 2 * ‖W‖ * Real.exp (v * T - ℓ / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg W)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) ha.le
      _ = _ := by ring
  have hmono {S S' : Finset ι} (hSS' : S ⊆ S') : N S ⊆ N S' :=
    ManyBody.graphNeighborhood_mono_left hSS'
  obtain ⟨hMsupport, hMnorm, hMerror⟩ := haverage (N Q) B
    (hmono (Finset.subset_union_left : Q ⊆ Q ∪ Z))
    (hmono (Finset.subset_union_right : Z ⊆ Q ∪ Z)) W η T hT
    (a * n ^ 2 * Real.exp (v * T - ℓ / 2))
    (d * n * Real.exp (v * T - ℓ / 2)) (by positivity) (by positivity)
    (fun t ht ↦ by simpa only [mul_assoc] using hnear t ht) hgenT
  refine ⟨hMsupport, hMnorm, hMerror.trans ?_⟩
  have hnsq : n ≤ n ^ 2 := by
    change (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2
    exact_mod_cast (show Fintype.card ι ≤ Fintype.card ι ^ 2 by
      simpa only [pow_two] using Nat.le_mul_self (Fintype.card ι))
  have hscaleT : a * n ^ 2 + d * n * T ≤ (a + d) * n ^ 2 * (1 + T) := by
    calc
      _ ≤ a * n ^ 2 + d * n ^ 2 * T :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnsq hd) hT)
      _ ≤ _ := by
        nlinarith [mul_nonneg hd (sq_nonneg n), mul_nonneg (mul_nonneg ha.le (sq_nonneg n)) hT]
  nlinarith only [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscaleT (norm_nonneg W)) (Real.exp_pos (v * T - ℓ / 2)).le]

end Graph

/-- A single supported unitary path yields the localized truncated
Gaussian integrals for every supported observable, variance and cutoff.
Source: TNLean note, `part2a_mps_information.tex`, lines 381–402. -/
theorem exists_supported_gaussian_integral (R : ℕ) (J : ℝ) :
    ∃ C v : ℝ, 0 < C ∧ 0 < v ∧
      ∀ (q : ℕ), 1 ≤ q →
      ∀ (L : ℕ) (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) (D : Finset (Fin L))
        (ℓ : ℝ),
        let K := h.doubledFin.hamiltonian
        let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
        let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
        let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
        let K' := F * K * Fᴴ
        let crossing := ManyBody.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
        let Z := crossing.biUnion (fun X ↦ X.1)
        let N := fun S : Finset (Fin L) ↦
          ManyBody.graphNeighborhood (SimpleGraph.pathGraph L) S ⌊ℓ⌋₊
        ∃ U : ℝ → Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ,
          U 0 = 1 ∧
          (∀ t, HasDerivAt U
            ((Complex.I • ManyBody.regionExpectation (N Z)
              (ManyBody.heisenbergEvolution K' t (K' - K))) * U t) t) ∧
          (∀ t, U t ∈ Matrix.unitaryGroup (Fin L → Fin (q * q)) ℂ) ∧
          (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) (N Z : Finset (Fin L))) ∧
          ∀ (Q : Finset (Fin L))
            (W : Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ),
            W ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q →
            ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
              let B := N (Q ∪ Z)
              let M := ∫ t : ℝ in Set.Icc (-T) T,
                ManyBody.regionExpectation (N Q) (ManyBody.heisenbergEvolution K' t W) * U t
                  ∂gaussianReal 0 η
              M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
              ‖M‖ ≤ ‖W‖ ∧
              ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K W‖ ≤
                ‖W‖ * C * (L : ℝ) ^ 2 * (1 + T) *
                  Real.exp (v * T - ℓ / 2) := by
  classical
  let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
  let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
    (1 - Real.exp (-(1 / 2)))
  let d : ℝ := 4 * |J| * a * (R + 1 : ℝ) ^ 2 * (ManyBody.chainCrossConst R : ℝ)
  have ha : 0 < a := div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
  have hd : 0 ≤ d := by positivity
  refine ⟨a + d, 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1, by positivity, by positivity, ?_⟩
  intro q hq L h hh hhJ D ℓ K pr e F K' crossing Z N
  let Φ : ManyBody.Interaction (fun _ : Fin L ↦ Fin (q * q)) (fun X : ChainSupport L R ↦ X.1) :=
    (h.doubled.conj (ManyBody.pairSwapOp (X := fun _ ↦ Fin q) D) fun X ↦
        ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators D
          (h.doubled.mem X)).relabel (X' := fun _ ↦ Fin (q * q)) (Equiv.refl _)
      (fun _ ↦ finProdFinEquiv) (fun X : ChainSupport L R ↦ X.1) fun _ _ ↦ Iff.rfl
  have hΦ : Φ.hamiltonian = K' :=
    (ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled (X' := fun _ ↦ Fin (q * q))
      h D _ (Equiv.refl _) (fun _ ↦ finProdFinEquiv) _ fun _ _ ↦ Iff.rfl).trans
      (congrArg (fun M ↦ F * M * Fᴴ) h.hamiltonian_doubledFin.symm)
  have hΦh : ∀ X, (Φ.term X).IsHermitian := fun X ↦
    ManyBody.Interaction.isHermitian_relabel_term _ _ _ _
      (ManyBody.Interaction.isHermitian_conj_term _ _
        (ManyBody.Interaction.isHermitian_doubled_term (hh X)))
  have hΦn : ∀ X, ‖Φ.term X‖ ≤ 2 * J := fun X ↦
    ((ManyBody.Interaction.norm_relabel_term _ _ _ _ _ X).trans
      (ManyBody.Interaction.norm_conj_term _ (ManyBody.pairSwapOp_mem_unitaryGroup D) _
        X)).trans_le ((ManyBody.Interaction.norm_doubled_term_le h X).trans
          (by linarith [hhJ X]))
  have hgen := exists_supported_gaussian_integral_graphNeighborhood
    (SimpleGraph.pathGraph L) (SimpleGraph.pathGraph_card_sphere_le_two L) Φ
    (fun X ↦ ManyBody.ChainSupport.edist_le X) (fun X ↦ X.2.card_le) hΦh b₀
    (ManyBody.ChainInteraction.sum_norm_terms_containing_le Φ hΦn)
        (ManyBody.Interaction.isHermitian_hamiltonian (Φ := h.doubledFin) fun X ↦
          (ManyBody.Interaction.isHermitian_doubled_term (hh X)).reindex _) Z ℓ
        d hd (fun s ↦ by
      rw [hΦ, Fintype.card_fin]
      exact h.norm_relativeGenerator_sub_regionExpectation_le hh hhJ D hq ℓ s)
  simp only [hΦ, Fintype.card_fin] at hgen
  exact hgen

/-- One supported unitary path gives the localized truncated Gaussian integrals
for every supported observable, variance and cutoff on an actual finite integer
domain. This extends the chain argument of the TNLean one-dimensional note,
part2a_mps_information.tex, lines 381–402, to the finite domains specified in
part0_preamble.tex, lines 191–215. No gap or information-reset conclusion is asserted. -/
theorem exists_supported_gaussian_integral_domain (R : ℕ) (J : ℝ) :
    ∃ C v : ℝ, 0 < C ∧ 0 < v ∧
      ∀ (q : ℕ), 1 ≤ q →
      ∀ (Λ : Finset ℤ) (h : DomainInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J)
        (D : Finset (Fin Λ.card)) (m : ℕ),
        let K := h.doubledFin.hamiltonian
        let pr := Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q
        let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv)
        let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
        let K' := F * K * Fᴴ
        let crossing := ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
        let Z := crossing.biUnion (fun X ↦ X.1)
        let N := fun S : Finset (Fin Λ.card) ↦
          ManyBody.graphNeighborhood (lineDomainGraph Λ) S m
        ∃ U : ℝ → Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ,
          U 0 = 1 ∧
          (∀ t, HasDerivAt U
            ((Complex.I • ManyBody.regionExpectation (N Z)
              (ManyBody.heisenbergEvolution K' t (K' - K))) * U t) t) ∧
          (∀ t, U t ∈ Matrix.unitaryGroup (Fin Λ.card → Fin (q * q)) ℂ) ∧
          (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q))
              (N Z : Finset (Fin Λ.card))) ∧
          ∀ (Q : Finset (Fin Λ.card))
            (W : Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ),
            W ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q →
            ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
              let B := N (Q ∪ Z)
              let M := ∫ t : ℝ in Set.Icc (-T) T,
                ManyBody.regionExpectation (N Q) (ManyBody.heisenbergEvolution K' t W) * U t
                  ∂gaussianReal 0 η
              M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
              ‖M‖ ≤ ‖W‖ ∧
              ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K W‖ ≤
                ‖W‖ * C * (Λ.card : ℝ) ^ 2 * (1 + T) *
                  Real.exp (v * T - (m : ℝ) / 2) := by
  classical
  let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
  let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
    (1 - Real.exp (-(1 / 2)))
  let d : ℝ := 4 * |J| * a * (R + 1 : ℝ) ^ 2 * (ManyBody.chainCrossConst R : ℝ)
  have ha : 0 < a := div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
  have hd : 0 ≤ d := by positivity
  refine ⟨a + d, 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1, by positivity, by positivity, ?_⟩
  intro q hq Λ h hh hhJ D m K pr e F K' crossing Z N
  let Φ : ManyBody.Interaction (fun _ : Fin Λ.card ↦ Fin (q * q))
      (fun X : DomainSupport Λ R ↦ X.1) :=
    (h.doubled.conj (ManyBody.pairSwapOp (X := fun _ ↦ Fin q) D) fun X ↦
        ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators D
          (h.doubled.mem X)).relabel (X' := fun _ ↦ Fin (q * q)) (Equiv.refl _)
      (fun _ ↦ finProdFinEquiv) (fun X : DomainSupport Λ R ↦ X.1) fun _ _ ↦ Iff.rfl
  have hΦ : Φ.hamiltonian = K' :=
    (ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled (X' := fun _ ↦ Fin (q * q))
      h D _ (Equiv.refl _) (fun _ ↦ finProdFinEquiv) _ fun _ _ ↦ Iff.rfl).trans
      (congrArg (fun M ↦ F * M * Fᴴ) h.hamiltonian_doubledFin.symm)
  have hΦh : ∀ X, (Φ.term X).IsHermitian := fun X ↦
    ManyBody.Interaction.isHermitian_relabel_term _ _ _ _
      (ManyBody.Interaction.isHermitian_conj_term _ _
        (ManyBody.Interaction.isHermitian_doubled_term (hh X)))
  have hΦn : ∀ X, ‖Φ.term X‖ ≤ 2 * J := fun X ↦
    ((ManyBody.Interaction.norm_relabel_term _ _ _ _ _ X).trans
      (ManyBody.Interaction.norm_conj_term _ (ManyBody.pairSwapOp_mem_unitaryGroup D) _
        X)).trans_le ((ManyBody.Interaction.norm_doubled_term_le h X).trans
          (by linarith [hhJ X]))
  have hgen := exists_supported_gaussian_integral_graphNeighborhood
    (lineDomainGraph Λ) (ManyBody.lineDomainGraph_card_sphere_le_two Λ) Φ
    (fun X ↦ X.2.2) (fun X ↦ X.2.isChainSupport.card_le) hΦh b₀
    (ManyBody.DomainInteraction.sum_norm_terms_containing_le Φ hΦn)
        (ManyBody.Interaction.isHermitian_hamiltonian (Φ := h.doubledFin) fun X ↦
          (ManyBody.Interaction.isHermitian_doubled_term (hh X)).reindex _) Z (m : ℝ)
        d hd (fun s ↦ by
      rw [hΦ, Nat.floor_natCast, Fintype.card_fin]
      exact h.norm_relativeGenerator_sub_regionExpectation_le hh hhJ D hq m s)
  simp only [hΦ, Nat.floor_natCast, Fintype.card_fin] at hgen
  exact hgen

end TNLean.MPS.AreaLaw
