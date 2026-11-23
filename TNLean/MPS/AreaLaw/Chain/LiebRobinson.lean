/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.Hamiltonian
import TNLean.MPS.AreaLaw.Chain.ChainNeighborhood
import TNLean.MPS.AreaLaw.Chain.LineDomainGraphGeometry
import QICLean.ManyBody.Sites.Lattice.PathGraph
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import QICLean.ManyBody.Dynamics.GraphLocalization

/-!
# Lieb–Robinson estimates on one-dimensional graphs

Let a finite labelled family of Hermitian terms on a finite graph have supports of graph
diameter at most `R` and at most `R + 1` sites, and term norms meeting any site summing to at
most `b₀`. Then the Heisenberg evolution of an operator supported on a finite set `S` has a
commutator bound with an on-site operator, linear in `|S|`, and, when every sphere of the graph
has at most two sites, a real-radius conditional-expectation bound quadratic in `|S|`. The
common decay exponent is `1 / 2`, and the constants are
`C = 2 + 4 |b₀| exp(2R)`, `v = 2(R+1)|b₀| exp(2R) + 1`, and
`C' = 2 C exp(1) / (1 - exp(-1/2))`, depending only on the range and the budget. The initial
support may meet several connected components; at infinite distance the commutator vanishes.

Both estimates are proved once, for a general graph, in QICLean's `ManyBody.Dynamics`
(`ManyBody.norm_heisenberg_commutator_le_graphDistance_inf` and
`ManyBody.norm_heisenberg_sub_regionExpectation_graphNeighborhood_le_of_sphere_le_two`). The
contiguous chain `Fin L` with its path graph and the finite integer domains with their induced
path graphs are the two specializations stated here.

## Main results

* `norm_heisenberg_commutator_le_chainDistance`,
  `norm_heisenberg_sub_regionExpectation_chainNeighborhood_le`: the contiguous chain.
* `norm_heisenberg_commutator_le_domainDistance`,
  `norm_heisenberg_sub_regionExpectation_domainNeighborhood_le`: finite integer domains.

**Source convention (contiguous chains):** The note fixes a contiguous chain in
`part1_arealaw.tex`, lines 91–93, before the Part II argument. The chain sites here
are `Fin L`, as in that argument. The finite-domain statements extend it to the domains of
`part0_preamble.tex`, lines 191–215; see
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, Lemma
`lem:LR`, lines 260–309. No ground-state or spectral-gap assumption is needed.
-/

open scoped Matrix.Norms.L2Operator
open ManyBody (ChainSupport DomainSupport lineDomainGraph)

namespace TNLean.MPS.AreaLaw

/-! ### The contiguous chain -/

/-- The real-radius chain neighborhood of `S` is the path-graph neighbourhood of `S` of
radius `⌊ℓ⌋`. -/
theorem graphNeighborhood_pathGraph_eq_chainNeighborhood {L : ℕ} (S : Finset (Fin L))
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    ManyBody.graphNeighborhood (SimpleGraph.pathGraph L) S ⌊ℓ⌋₊ = chainNeighborhood S ℓ := by
  ext y
  simp only [ManyBody.mem_graphNeighborhood,
    SimpleGraph.pathGraph_edist, ENat.natCast_le_natCast, Nat.le_floor_iff hℓ,
    mem_chainNeighborhood]

/-- Contiguous-chain specialization of Lemma lem:LR, first estimate.
TNLean note, part2a_mps_information.tex:260–273. -/
theorem norm_heisenberg_commutator_le_chainDistance
    {L q R : ℕ} {κ : Type*} [Fintype κ]
    (X : κ → ChainSupport L R)
    (h : κ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (h k) (X k).1)
    (b₀ : ℝ)
    (hBudget : ∀ x : Fin L,
      ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ (X k).1), ‖h k‖ ≤ b₀)
    (S : Finset (Fin L)) {A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hA : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) A S) (y : Fin L)
    (hB : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) B {y}) (t : ℝ) :
    let δ : ℕ∞ := S.inf (fun x ↦ (SimpleGraph.pathGraph L).edist x y)
    ‖ManyBody.heisenbergEvolution (∑ k, h k) t A * B -
        B * ManyBody.heisenbergEvolution (∑ k, h k) t A‖ ≤
      (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) * ‖A‖ * ‖B‖ *
        Real.exp ((2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t|) *
        (if δ = ⊤ then 0 else Real.exp (-((δ.toNat : ℝ) / 2))) :=
  ManyBody.norm_heisenberg_commutator_le_graphDistance_inf (SimpleGraph.pathGraph L)
    (⟨h, hSupport⟩ : ManyBody.Interaction (fun _ : Fin L ↦ Fin q) fun k ↦ (X k).1)
    hHerm R (fun k ↦ ManyBody.ChainSupport.edist_le (X k)) (fun k ↦ (X k).2.card_le)
    b₀ hBudget S hA y hB t

/-- Contiguous-chain specialization of Lemma lem:LR, real-radius localization.
TNLean note, part2a_mps_information.tex:274–280. -/
theorem norm_heisenberg_sub_regionExpectation_chainNeighborhood_le
    {L q R : ℕ} {κ : Type*} [Fintype κ]
    (X : κ → ChainSupport L R)
    (h : κ → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (h k) (X k).1)
    (b₀ : ℝ)
    (hBudget : ∀ x : Fin L,
      ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ (X k).1), ‖h k‖ ≤ b₀)
    (S : Finset (Fin L))
    {A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hA : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) A S)
    (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (t : ℝ) :
    ‖ManyBody.heisenbergEvolution (∑ k, h k) t A -
        ManyBody.regionExpectation
          (chainNeighborhood S ℓ)
          (ManyBody.heisenbergEvolution (∑ k, h k) t A)‖ ≤
      (2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
        (1 - Real.exp (-(1 / 2)))) * (S.card : ℝ) ^ 2 * ‖A‖ *
          Real.exp ((2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t| - ℓ / 2) := by
  rw [← graphNeighborhood_pathGraph_eq_chainNeighborhood S hℓ]
  exact ManyBody.norm_heisenberg_sub_regionExpectation_graphNeighborhood_le_of_sphere_le_two
    (SimpleGraph.pathGraph L)
    (⟨h, hSupport⟩ : ManyBody.Interaction (fun _ : Fin L ↦ Fin q) fun k ↦ (X k).1)
    hHerm R (fun k ↦ ManyBody.ChainSupport.edist_le (X k)) (fun k ↦ (X k).2.card_le)
    (SimpleGraph.pathGraph_card_sphere_le_two L) b₀ hBudget S hA ℓ t

/-! ### Finite integer domains -/

/-- The finite-domain commutator estimate, extending the chain estimate of the
TNLean one-dimensional note, `part2a_mps_information.tex`, Lemma `lem:LR`, lines 267–309,
to the induced integer domains of `part0_preamble.tex`, lines 191–215. -/
theorem norm_heisenberg_commutator_le_domainDistance
    {Λ : Finset ℤ} {q R : ℕ} {κ : Type*} [Fintype κ]
    (X : κ → DomainSupport Λ R)
    (h : κ → Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ)
    (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (h k) (X k).1)
    (b₀ : ℝ)
    (hBudget : ∀ x : Fin Λ.card,
      ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ (X k).1), ‖h k‖ ≤ b₀)
    (S : Finset (Fin Λ.card))
    {A B : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ}
    (hA : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) A S) (y : Fin Λ.card)
    (hB : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) B {y}) (t : ℝ) :
    let δ : ℕ∞ := S.inf (fun x ↦ (lineDomainGraph Λ).edist x y)
    ‖ManyBody.heisenbergEvolution (∑ k, h k) t A * B -
        B * ManyBody.heisenbergEvolution (∑ k, h k) t A‖ ≤
      (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) * ‖A‖ * ‖B‖ *
        Real.exp ((2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t|) *
        (if δ = ⊤ then 0 else Real.exp (-((δ.toNat : ℝ) / 2))) :=
  ManyBody.norm_heisenberg_commutator_le_graphDistance_inf (lineDomainGraph Λ)
    (⟨h, hSupport⟩ : ManyBody.Interaction (fun _ : Fin Λ.card ↦ Fin q) fun k ↦ (X k).1)
    hHerm R (fun k ↦ (X k).2.2) (fun k ↦ (X k).2.isChainSupport.card_le)
    b₀ hBudget S hA y hB t

/-- Real-radius localization on a finite induced integer domain, extending the chain
estimate of the TNLean note, `part2a_mps_information.tex`, Lemma `lem:LR`,
lines 274–280, to the finite domains of `part0_preamble.tex`, lines 191–215. -/
theorem norm_heisenberg_sub_regionExpectation_domainNeighborhood_le
    {Λ : Finset ℤ} {q R : ℕ} {κ : Type*} [Fintype κ]
    (X : κ → DomainSupport Λ R)
    (h : κ → Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ)
    (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (h k) (X k).1)
    (b₀ : ℝ)
    (hBudget : ∀ x : Fin Λ.card,
      ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ (X k).1), ‖h k‖ ≤ b₀)
    (S : Finset (Fin Λ.card))
    {A : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ}
    (hA : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) A S)
    (ℓ : ℝ) (t : ℝ) :
    ‖ManyBody.heisenbergEvolution (∑ k, h k) t A -
        ManyBody.regionExpectation
          (ManyBody.graphNeighborhood (lineDomainGraph Λ) S ⌊ℓ⌋₊)
          (ManyBody.heisenbergEvolution (∑ k, h k) t A)‖ ≤
      (2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
        (1 - Real.exp (-(1 / 2)))) * (S.card : ℝ) ^ 2 * ‖A‖ *
          Real.exp ((2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1) * |t| - ℓ / 2) :=
  ManyBody.norm_heisenberg_sub_regionExpectation_graphNeighborhood_le_of_sphere_le_two
    (lineDomainGraph Λ)
    (⟨h, hSupport⟩ : ManyBody.Interaction (fun _ : Fin Λ.card ↦ Fin q) fun k ↦ (X k).1)
    hHerm R (fun k ↦ (X k).2.2) (fun k ↦ (X k).2.isChainSupport.card_le)
    (lineDomainGraph_card_sphere_le_two Λ) b₀ hBudget S hA ℓ t

end TNLean.MPS.AreaLaw
