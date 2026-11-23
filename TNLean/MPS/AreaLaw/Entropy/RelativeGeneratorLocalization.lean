/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.DoubledHamiltonian
import TNLean.MPS.AreaLaw.Chain.PartialSwap
import TNLean.MPS.AreaLaw.Chain.DomainPartialSwap
import TNLean.MPS.AreaLaw.Chain.LiebRobinson
import TNLean.MPS.AreaLaw.Chain.Counting
import QICLean.ManyBody.Dynamics.SwappedDoubledInteraction

/-!
# Localization of the relative-evolution generator

The relative-evolution generator is localized term by term over crossing
replica differences. Its projection error is bounded by a constant depending
only on the range and interaction bound, times the number of sites and an
exponential in time and distance.

The term-by-term localization is proved once, on a finite graph whose spheres
have at most two sites, for the Heisenberg evolution of any finite sum of local
perturbations. The contiguous chain `Fin L` with its path graph and the finite
integer domains with their induced path graphs are the two specializations. On
the chain the sharper boundary cardinality is retained in the proof; no factor
quadratic in the full crossing zone is used. On a domain, intrinsic graph
neighborhoods retain disconnected components.

## Main results

* `norm_heisenberg_sum_sub_regionExpectation_graphNeighborhood_le`: localization of an
  evolved sum of local perturbations on a graph.
* `ManyBody.ChainInteraction.norm_relativeGenerator_sub_regionExpectation_le`: localization of the
  generator on the chain, with an error linear in `L`.
* `ManyBody.DomainInteraction.norm_relativeGenerator_sub_regionExpectation_le`: the natural-radius
  localization on a finite integer domain, with the same constants.

**Source convention (contiguous chains):** The note fixes a contiguous chain in
`part1_arealaw.tex`, lines 91–93, before the Part II argument. The chain sites here
are `Fin L`, as in that argument. The finite-domain statement extends it to the domains of
`part0_preamble.tex`, lines 191–215; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 380–400.
This estimate does not construct a Gaussian filter or an information reset.
-/

open ManyBody (ChainSupport DomainSupport boundaryEdges lineDomainGraph ChainInteraction
  DomainInteraction)

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

section Graph

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q R : ℕ} [NeZero q] {κ : Type*} [Fintype κ]
  {T : κ → Finset ι}

omit [NeZero q] in
/-- Localization of the Heisenberg evolution of a finite sum of local perturbations, on a
finite graph whose spheres have at most two sites. Each perturbation `P c`, `c ∈ C`, is
supported on a set `U c ⊆ Z` of at most `R + 1` sites and has norm at most `ε`; the
evolving interaction has supports of graph diameter at most `R` and at most `R + 1` sites,
and per-site norm budget `b₀`. Each evolved perturbation is localized onto the balls of
radius `⌊ℓ⌋` about its own support, which lie in those about `Z`. This is the term-by-term
localization of TNLean note, `part2a_mps_information.tex`, lines 380–400. -/
theorem norm_heisenberg_sum_sub_regionExpectation_graphNeighborhood_le
    (G : SimpleGraph ι)
    (hSphere : ∀ x : ι, ∀ d : ℕ, (Finset.univ.filter fun y ↦ G.edist x y = d).card ≤ 2)
    (Φ : ManyBody.Interaction (fun _ : ι ↦ Fin q) T)
    (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (hCard : ∀ k, (T k).card ≤ R + 1)
    (hHerm : ∀ k, (Φ.term k).IsHermitian) (b₀ : ℝ)
    (hBudget : ∀ x : ι, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ T k), ‖Φ.term k‖ ≤ b₀)
    {γ : Type*} (C : Finset γ) (U : γ → Finset ι) (Z : Finset ι)
    (hUZ : ∀ c ∈ C, U c ⊆ Z) (hU : ∀ c ∈ C, (U c).card ≤ R + 1)
    (P : γ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hP : ∀ c ∈ C, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (P c) (U c))
    (ε : ℝ) (hPε : ∀ c ∈ C, ‖P c‖ ≤ ε) (ℓ t : ℝ) :
    let B := ManyBody.graphNeighborhood G Z ⌊ℓ⌋₊
    let E :=ManyBody.heisenbergEvolution Φ.hamiltonian t (∑ c ∈ C, P c)
    let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
      (1 - Real.exp (-(1 / 2)))
    let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
    ‖E - ManyBody.regionExpectation B E‖ ≤
      (C.card : ℝ) * (2 * (a * (R + 1 : ℝ) ^ 2 * ε * Real.exp (v * |t| - ℓ / 2))) := by
  classical
  intro B E a v
  have ha : 0 ≤ a := by
    have hden : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    exact (div_pos (by positivity) hden).le
  -- one evolved perturbation, localized onto the balls about its own support
  have hterm (c : γ) (hc : c ∈ C) :
      ‖ManyBody.heisenbergEvolution Φ.hamiltonian t (P c) - ManyBody.regionExpectation B
        (ManyBody.heisenbergEvolution Φ.hamiltonian t (P c))‖ ≤
          2 * (a * (R + 1 : ℝ) ^ 2 * ε * Real.exp (v * |t| - ℓ / 2)) := by
    let N := ManyBody.graphNeighborhood G (U c) ⌊ℓ⌋₊
    have hNB : N ⊆ B := ManyBody.graphNeighborhood_mono_left (hUZ c hc)
    have hloc :=
      ManyBody.norm_heisenberg_sub_regionExpectation_graphNeighborhood_le_of_sphere_le_two
        G Φ hHerm R hDiam hCard hSphere b₀ hBudget (U c) (hP c hc) ℓ t
    have hcard : ((U c).card : ℝ) ≤ (R + 1 : ℝ) := by exact_mod_cast hU c hc
    refine (ManyBody.norm_sub_regionExpectation_le_two_mul_norm_sub B _
        (ManyBody.regionExpectation N
        (ManyBody.heisenbergEvolution Φ.hamiltonian t (P
            c))) (ManyBody.supportedOperators_mono (Finset.coe_subset.mpr hNB)
        (ManyBody.regionExpectation_mem_supportedOperators N _))).trans
      (mul_le_mul_of_nonneg_left (hloc.trans ?_) (by norm_num))
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) ha)
      (hPε c hc) (norm_nonneg _) (mul_nonneg ha (sq_nonneg _))
  -- the evolution and the error are linear in the observable
  let δ := (LinearMap.id - ManyBody.regionExpectationLM B).comp
    (LinearMap.mulLeftRight ℂ (NormedSpace.exp (t • (Complex.I • Φ.hamiltonian)),
      NormedSpace.exp ((-t) • (Complex.I • Φ.hamiltonian))))
  have hδ (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
      δ A = ManyBody.heisenbergEvolution Φ.hamiltonian t A -
        ManyBody.regionExpectation B (ManyBody.heisenbergEvolution Φ.hamiltonian t A) :=
    rfl
  change ‖δ (∑ c ∈ C, P c)‖ ≤ _
  rw [map_sum]
  calc
    _ ≤ ∑ c ∈ C, ‖δ (P c)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ C, 2 * (a * (R + 1 : ℝ) ^ 2 * ε * Real.exp (v * |t| - ℓ / 2)) :=
      Finset.sum_le_sum fun c hc ↦ (hδ (P c)).symm ▸ hterm c hc
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end Graph

/-- The relative-evolution generator is exponentially close to its
expectation on the neighborhood of the crossing supports, with error linear
in the chain length. Source: TNLean note, `part2a_mps_information.tex`, lines 380–400. -/
theorem _root_.ManyBody.ChainInteraction.norm_relativeGenerator_sub_regionExpectation_le
    {L q R : ℕ} {J : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin L)) (hq : 1 ≤ q) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (t : ℝ) :
    let K := h.doubledFin.hamiltonian
    let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
    let K' := F * K * Fᴴ
    let C := ManyBody.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
    let Z := C.biUnion (fun X ↦ X.1)
    let B := chainNeighborhood Z ℓ
    let G := ManyBody.heisenbergEvolution K' t (K' - K)
    let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
    let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
      (1 - Real.exp (-(1 / 2)))
    let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
    ‖G - ManyBody.regionExpectation B G‖ ≤
      (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
        (L : ℝ) * Real.exp (v * |t| - ℓ / 2) := by
  classical
  intro K pr e F K' C Z B G b₀ a v
  have : NeZero (q * q) := ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos hq hq)⟩
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
  let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  let A (p : ChainSupport L R × Bool) := F * T p.1 p.2 * Fᴴ - T p.1 p.2
  obtain ⟨hsum, hcount⟩ := h.partialSwap_difference_eq_sum_crossing D
  have hdiff : K' - K = ∑ p ∈ C ×ˢ Finset.univ, A p := by
    rw [Finset.sum_product]
    exact hsum
  have hgen := norm_heisenberg_sum_sub_regionExpectation_graphNeighborhood_le
    (SimpleGraph.pathGraph L) (SimpleGraph.pathGraph_card_sphere_le_two L) Φ
    (fun X ↦ ManyBody.ChainSupport.edist_le X) (fun X ↦ X.2.card_le) hΦh b₀
    (ManyBody.ChainInteraction.sum_norm_terms_containing_le Φ hΦn) (C ×ˢ Finset.univ)
        (fun p ↦ p.1.1) Z
    (fun p hp ↦ Finset.subset_biUnion_of_mem (fun X ↦ X.1) (Finset.mem_product.mp hp).1)
    (fun p _ ↦ p.1.2.card_le) A (fun p _ ↦ (h.partialSwap_term_difference_spec hh hhJ D p.1 p.2).1)
    (2 * |J|) (fun p _ ↦ (h.partialSwap_term_difference_spec hh hhJ D p.1 p.2).2.2.trans
      (mul_le_mul_of_nonneg_left (le_abs_self J) (by norm_num))) ℓ t
  dsimp only at hgen
  rw [graphNeighborhood_pathGraph_eq_chainNeighborhood Z hℓ, hΦ, ← hdiff] at hgen
  have hb : (boundaryEdges L D).card ≤ L :=
    (Finset.card_le_card fun p hp ↦ Finset.mem_range.mpr
      (by have := (ManyBody.mem_boundaryEdges.mp hp).1; omega)).trans (Finset.card_range _).le
  have hc : ((C ×ˢ (Finset.univ : Finset Bool)).card : ℝ) ≤ (chainCrossConst R : ℝ) * L := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
    exact_mod_cast hcount.trans (Nat.mul_le_mul_left _ hb)
  have ha : 0 ≤ a := (div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))).le
  calc
    _ ≤ _ := hgen
    _ ≤ ((chainCrossConst R : ℝ) * L) *
        (2 * (a * (R + 1 : ℝ) ^ 2 * (2 * |J|) * Real.exp (v * |t| - ℓ / 2))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

/-- Natural-radius localization of the relative-evolution generator on an
actual finite integer domain. This extends the chain localization argument of
TNLean note, part2a_mps_information.tex, lines 380–400, to the finite domains of
part0_preamble.tex, lines 191–215. No spectral gap or reset conclusion is asserted. -/
theorem _root_.ManyBody.DomainInteraction.norm_relativeGenerator_sub_regionExpectation_le
    {Λ : Finset ℤ} {q R : ℕ} {J : ℝ} (h : DomainInteraction Λ q R)
        (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin Λ.card)) (hq : 1 ≤ q) (m : ℕ) (t : ℝ) :
    let K := h.doubledFin.hamiltonian
    let pr := Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
    let K' := F * K * Fᴴ
    let C := ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
    let Z := C.biUnion (fun X ↦ X.1)
    let B := ManyBody.graphNeighborhood (lineDomainGraph Λ) Z m
    let G := ManyBody.heisenbergEvolution K' t (K' - K)
    let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
    let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
      (1 - Real.exp (-(1 / 2)))
    let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
    ‖G - ManyBody.regionExpectation B G‖ ≤
      (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
        (Λ.card : ℝ) * Real.exp (v * |t| - (m : ℝ) / 2) := by
  classical
  intro K pr e F K' C Z B G b₀ a v
  have : NeZero (q * q) := ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos hq hq)⟩
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
  let T (X : DomainSupport Λ R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
  let A (p : DomainSupport Λ R × Bool) := F * T p.1 p.2 * Fᴴ - T p.1 p.2
  obtain ⟨hsum, hcount⟩ := h.partialSwap_difference_eq_sum_crossing D
  have hdiff : K' - K = ∑ p ∈ C ×ˢ Finset.univ, A p := by
    rw [Finset.sum_product]
    exact hsum
  have hgen := norm_heisenberg_sum_sub_regionExpectation_graphNeighborhood_le
    (lineDomainGraph Λ) (lineDomainGraph_card_sphere_le_two Λ) Φ
    (fun X ↦ X.2.2) (fun X ↦ X.2.isChainSupport.card_le) hΦh b₀
    (ManyBody.DomainInteraction.sum_norm_terms_containing_le Φ hΦn) (C ×ˢ Finset.univ)
        (fun p ↦ p.1.1) Z
    (fun p hp ↦ Finset.subset_biUnion_of_mem (fun X ↦ X.1) (Finset.mem_product.mp hp).1)
    (fun p _ ↦ p.1.2.isChainSupport.card_le) A
    (fun p _ ↦ (h.partialSwap_term_difference_spec hh hhJ D p.1 p.2).1)
    (2 * |J|) (fun p _ ↦ (h.partialSwap_term_difference_spec hh hhJ D p.1 p.2).2.2.trans
      (mul_le_mul_of_nonneg_left (le_abs_self J) (by norm_num))) (m : ℝ) t
  dsimp only at hgen
  rw [Nat.floor_natCast, hΦ, ← hdiff] at hgen
  have hc : ((C ×ˢ (Finset.univ : Finset Bool)).card : ℝ) ≤
      (chainCrossConst R : ℝ) * Λ.card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
    exact_mod_cast hcount
  have ha : 0 ≤ a := (div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))).le
  calc
    _ ≤ _ := hgen
    _ ≤ ((chainCrossConst R : ℝ) * Λ.card) *
        (2 * (a * (R + 1 : ℝ) ^ 2 * (2 * |J|) * Real.exp (v * |t| - (m : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end TNLean.MPS.AreaLaw
