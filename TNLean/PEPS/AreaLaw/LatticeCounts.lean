/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.LocalHamiltonian
import TNLean.PEPS.AreaLaw.CrossingBudget
import TNLean.PEPS.AreaLaw.GraphInteractionDiamondCounting

/-!
# Counting bounds on an induced square-lattice domain

The graph-theoretic results of Section 4 of the area-law manuscript take as hypotheses the
counts of Section 2: graph balls and spheres of radius `d` have at most a constant times
`(d + 1)²` sites, each support has at most `v_R = 1 + 2 R (R + 1)` sites, at most
`μ_R = 2 ^ (v_R - 1)` supports contain a given site, so at most `μ_R` labels share an
anchor and the norms of the terms meeting a site sum to at most `μ_R J`. This file derives
them on the induced nearest-neighbour graph of an arbitrary finite domain, holes and
disconnected components included, from the ambient diamond count `eq:ball-count`.

## Main results

* `TNLean.PEPS.AreaLaw.card_graphBall_domainGraph_le`: `|N_d(x)| ≤ 2 (d + 1)²`.
* `TNLean.PEPS.AreaLaw.card_sphere_domainGraph_le`: the same bound for spheres.
* `TNLean.PEPS.AreaLaw.IsAdmissibleSupport.edist_le`,
  `TNLean.PEPS.AreaLaw.IsAdmissibleSupport.card_le`: diameter `R` and `|X| ≤ v_R`.
* `TNLean.PEPS.AreaLaw.card_anchor_fiber_le`: at most `μ_R` labels per anchor.
* `TNLean.PEPS.AreaLaw.LocalHamiltonian.sum_norm_term_containing_le`: the site budget
  `b₀ = μ_R J` of `eq:quasilocal-budget`.
* `TNLean.PEPS.AreaLaw.card_cutEdges_le_card_edgeBoundary`: ordered cut edges are counted by
  the unordered edge boundary `∂_Λ X`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `eq:ball-count` and the multiplicity bound after it (`01-preliminaries.tex`, lines 81–95),
  and `eq:quasilocal-budget` (`03-quasilocal.tex`, lines 30–40).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit

variable {Λ : Finset (ℤ × ℤ)}

/-- Adjacent sites of the induced domain graph are at ambient lattice distance one. -/
theorem latticeL1Distance_le_one_of_adj {x y : Site Λ} (h : (domainGraph Λ).Adj x y) :
    latticeL1Distance x.1 y.1 ≤ 1 := by
  simp only [domainGraph] at h
  unfold latticeL1Distance
  omega

/-- **Ball count** (`eq:ball-count`, `01-preliminaries.tex`, lines 81–87): a graph ball of
radius `d` in an induced domain has at most `1 + 2 d (d + 1) ≤ 2 (d + 1)²` sites. -/
theorem card_graphBall_domainGraph_le (x : Site Λ) (d : ℕ) :
    ((graphBall (domainGraph Λ) x d).card : ℝ) ≤ 2 * ((d : ℝ) + 1) ^ 2 := by
  have h := card_le_diamond_of_edist_le (G := domainGraph Λ) Subtype.val
    (graphBall (domainGraph Λ) x d) Subtype.val_injective
    (fun _ _ hxy => latticeL1Distance_le_one_of_adj hxy) x d (fun y hy => mem_graphBall.mp hy)
  have h' : ((graphBall (domainGraph Λ) x d).card : ℝ) ≤ 1 + 2 * d * (d + 1) := by
    exact_mod_cast h
  nlinarith

/-- **Sphere count**: the sites at graph distance exactly `d` from `x` number at most
`2 (d + 1)²`, the sphere-growth hypothesis of Lemma 4.1 with `K_g = k_g = 2`. -/
theorem card_sphere_domainGraph_le (x : Site Λ) (d : ℕ) :
    ((Finset.univ.filter fun y => (domainGraph Λ).edist x y = d).card : ℝ) ≤
      2 * ((d : ℝ) + 1) ^ 2 := by
  refine le_trans ?_ (card_graphBall_domainGraph_le x d)
  exact_mod_cast Finset.card_le_card fun y hy => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact mem_graphBall.mpr hy.le

/-- An admissible support has graph diameter at most `R` (`eq:hamiltonian`). -/
theorem IsAdmissibleSupport.edist_le {R : ℕ} {X : Finset (Site Λ)}
    (hX : IsAdmissibleSupport Λ R X) : ∀ x ∈ X, ∀ z ∈ X, (domainGraph Λ).edist x z ≤ R :=
  fun x hx z hz => (exists_walk_length_le_iff_edist_le Λ R x z).mp (hX.2 x hx z hz)

/-- An admissible support has at most `v_R = 1 + 2 R (R + 1)` sites (`eq:ball-count`). -/
theorem IsAdmissibleSupport.card_le {R : ℕ} {X : Finset (Site Λ)}
    (hX : IsAdmissibleSupport Λ R X) : X.card ≤ 1 + 2 * R * (R + 1) :=
  card_support_le_diamond Subtype.val Subtype.val_injective
    (fun _ _ hxy => latticeL1Distance_le_one_of_adj hxy) X R hX.2

/-- At most `μ_R = 2 ^ (v_R - 1)` admissible supports contain a given site
(`01-preliminaries.tex`, lines 88–95). -/
theorem card_admissibleSupport_containing_le (R : ℕ) (x : Site Λ) :
    (Finset.univ.filter fun X : AdmissibleSupport Λ R => x ∈ X.1).card ≤
      2 ^ ((1 + 2 * R * (R + 1)) - 1) := by
  classical
  set F : Finset (Finset (Site Λ)) :=
    Finset.univ.map (Function.Embedding.subtype (IsAdmissibleSupport Λ R))
  have hF : ∀ Y ∈ F, ∀ a ∈ Y, ∀ z ∈ Y, ∃ p : (domainGraph Λ).Walk a z, p.length ≤ R := by
    intro Y hY
    obtain ⟨X, -, rfl⟩ := Finset.mem_map.mp hY
    exact X.2.2
  have hmap : (Finset.univ.filter fun X : AdmissibleSupport Λ R => x ∈ X.1).map
      (Function.Embedding.subtype _) = F.filter fun Y => x ∈ Y := by
    rw [Finset.filter_map]; rfl
  rw [← Finset.card_map (Function.Embedding.subtype _), hmap]
  exact card_supports_containing_le_diamond Subtype.val Subtype.val_injective
    (fun _ _ hxy => latticeL1Distance_le_one_of_adj hxy) F R hF x

/-- **Anchor multiplicity**: if every label is anchored inside its support, at most `μ_R`
labels share an anchor (`03-quasilocal.tex`, lines 30–33). -/
theorem card_anchor_fiber_le {R : ℕ} (a : AdmissibleSupport Λ R → Site Λ)
    (ha : ∀ X, a X ∈ X.1) (x : Site Λ) :
    (Finset.univ.filter fun X => a X = x).card ≤ 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
  (Finset.card_le_card fun X hX => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
    exact hX ▸ ha X).trans (card_admissibleSupport_containing_le R x)

/-- **Site budget** `b₀ = μ_R J` (`eq:quasilocal-budget`, `03-quasilocal.tex`,
lines 34–40): the norms of the terms whose supports contain a site sum to at most `μ_R J`. -/
theorem LocalHamiltonian.sum_norm_term_containing_le {q R : ℕ} {J : ℝ}
    (h : LocalHamiltonian Λ q R J) (hJ : 0 ≤ J) (x : Site Λ) :
    ∑ X ∈ Finset.univ.filter (fun X : AdmissibleSupport Λ R => x ∈ X.1), ‖h.term X‖ ≤
      ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) * J := by
  calc ∑ X ∈ Finset.univ.filter (fun X : AdmissibleSupport Λ R => x ∈ X.1), ‖h.term X‖
      ≤ ((Finset.univ.filter fun X : AdmissibleSupport Λ R => x ∈ X.1).card : ℝ) * J := by
        simpa using Finset.sum_le_card_nsmul _ _ J fun X _ => h.norm_le X
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_admissibleSupport_containing_le R x) hJ

/-- Ordered cut edges `(u, v)`, `u ∈ X`, `v ∉ X`, are no more numerous than the unordered
edges of `∂_Λ X` (`03-quasilocal.tex`, line 436). -/
theorem card_cutEdges_le_card_edgeBoundary (X : Finset (Site Λ)) :
    (cutEdges (domainGraph Λ) X).card ≤ (edgeBoundary Λ X).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
  · intro p hp
    simp only [cutEdges, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp
    simp only [edgeBoundary, Finset.coe_filter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Set.mem_ofPred_eq]
    exact ⟨hp.1, p.1, hp.2.1, p.2, hp.2.2, rfl⟩
  · intro p hp p' hp' he
    simp only [cutEdges, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ hp.2.1) hp'.2.2

end TNLean.PEPS.AreaLaw
