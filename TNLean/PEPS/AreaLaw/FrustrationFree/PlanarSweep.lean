/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FrustrationFree.LightCone
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.Algebra.GreedyColoring
import QICLean.Algebra.OverlapGraph

/-!
# The colour-ordered sweep on a planar domain and the radius of its light cone

On a finite domain `Λ ⊂ ℤ²`, a support of graph diameter at most `R` meets at most
`d_R = v_R μ_R` other supports, with `v_R = 1 + 2R(R + 1)` and `μ_R = 2^{v_R - 1}`. A greedy
colouring of the overlap graph with `χ = d_R + 1` colours orders the supports colour by colour.
One sweep is then a word of `χ` layers of supports with pairwise disjoint sites, and one layer
moves the region of the light cone by at most `R` in graph distance. So `t` sweeps keep the light
cone of `U` inside the graph neighbourhood `N_{R χ t}(U)`, as in `eq:cone` of the
frustration-free area-law note.

## Main definitions

* `TNLean.PEPS.AreaLaw.FrustrationFree.overlapDegreeBound`: `d_R = v_R μ_R`.
* `TNLean.PEPS.AreaLaw.FrustrationFree.sweepWord`: the supports, colour by colour.

## Main statements

* `degree_overlapGraph_le`: every support meets at most `d_R` others.
* `exists_overlapColoring`: a colouring with `d_R + 1` colours.
* `retainedSet_sweepWord_pow_subset`: the light cone of `t` sweeps lies in `N_{R χ t}(U)`.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  "Setting" (`v_R`, `μ_R`), "Contraction in one sweep" and "Exact localization on the perturbed
  vector".
-/

open ManyBody SimpleGraph TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.FrustrationFree

variable {Λ : Finset (ℤ × ℤ)} {R : ℕ}

/-- The degree bound `d_R = v_R μ_R` of the overlap graph of the supports, with
`v_R = 1 + 2R(R + 1)` and `μ_R = 2^{v_R - 1}`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Contraction in one sweep":
"for example `d = v_R μ_R`". -/
def overlapDegreeBound (R : ℕ) : ℕ := (1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1)

/-- The overlap graph of the supports of range `R`. -/
abbrev supportOverlapGraph (Λ : Finset (ℤ × ℤ)) (R : ℕ) : SimpleGraph (AdmissibleSupport Λ R) :=
  overlapGraph fun X : AdmissibleSupport Λ R ↦ X.1

instance (Λ : Finset (ℤ × ℤ)) (R : ℕ) : DecidableRel (supportOverlapGraph Λ R).Adj :=
  inferInstanceAs (DecidableRel (overlapGraph _).Adj)

/-- **Every support meets at most `d_R` others.** Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Setting" and "Contraction
in one sweep". -/
theorem degree_overlapGraph_le (X : AdmissibleSupport Λ R) :
    (supportOverlapGraph Λ R).degree X ≤ overlapDegreeBound R := by
  rw [← card_neighborFinset_eq_degree]
  refine (card_le_card_mul_of_forall_exists_mem (N := X.1) fun Y hY ↦ ?_).trans
    (Nat.mul_le_mul_right _ X.2.card_le)
  rw [mem_neighborFinset, overlapGraph_adj] at hY
  obtain ⟨v, hv⟩ := hY.2
  exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩

/-- The colourings of the supports with `d_R + 1` colours. -/
abbrev SupportColouring (Λ : Finset (ℤ × ℤ)) (R : ℕ) :=
  (supportOverlapGraph Λ R).Coloring (Fin (overlapDegreeBound R + 1))

/-- **A colouring of the supports with `d_R + 1` colours.** Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Contraction in one sweep":
"Color it in `χ ≤ d + 1` colors and order the terms by color". -/
theorem exists_overlapColoring :
    Nonempty (SupportColouring Λ R) :=
  colorable_succ_of_forall_degree_le _ degree_overlapGraph_le

/-- The supports of one colour. -/
noncomputable def colorLayer (c : SupportColouring Λ R)
    (i : Fin (overlapDegreeBound R + 1)) : List (AdmissibleSupport Λ R) :=
  (Finset.univ.filter fun X ↦ c X = i).toList

/-- The supports, colour by colour: the word of one sweep. -/
noncomputable def sweepWord (c : SupportColouring Λ R) :
    List (AdmissibleSupport Λ R) :=
  (List.ofFn (colorLayer c)).flatten

theorem mem_sweepWord (c : SupportColouring Λ R)
    (X : AdmissibleSupport Λ R) : X ∈ sweepWord c := by
  simp only [sweepWord, List.mem_flatten, List.mem_ofFn]
  exact ⟨colorLayer c (c X), ⟨c X, rfl⟩, by simp [colorLayer]⟩

theorem nodup_sweepWord (c : SupportColouring Λ R) :
    (sweepWord c).Nodup := by
  rw [sweepWord, List.nodup_flatten]
  refine ⟨fun l hl ↦ ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact Finset.nodup_toList _
  · refine List.pairwise_ofFn.mpr fun i j hij ↦ List.disjoint_left.mpr fun X hXi hXj ↦ ?_
    simp only [colorLayer, Finset.mem_toList, Finset.mem_filter] at hXi hXj
    exact hij.ne (hXi.2.symm.trans hXj.2)

/-- The supports of one colour are pairwise disjoint. -/
theorem pairwise_disjoint_colorLayer
    (c : SupportColouring Λ R)
    (i : Fin (overlapDegreeBound R + 1)) :
    (colorLayer c i).Pairwise fun X Y ↦ Disjoint X.1 Y.1 :=
  (Finset.nodup_toList _).pairwise_of_forall_ne fun X hX Y hY hXY ↦ by
    simp only [Finset.mem_toList, Finset.mem_filter] at hX hY
    exact c.disjoint_of_overlapGraph hXY (hX.2.trans hY.2.symm)

/-- One layer of a colour moves the light cone by at most `R`. -/
theorem retainedSet_colorLayer_subset
    (c : SupportColouring Λ R)
    (i : Fin (overlapDegreeBound R + 1)) (U : Finset (Site Λ)) :
    retainedSet (fun X : AdmissibleSupport Λ R ↦ X.1) U (colorLayer c i) ⊆
      graphNeighborhood (planeDomainGraph Λ) U R :=
  retainedSet_subset_of_pairwise_disjoint subset_graphNeighborhood
    (pairwise_disjoint_colorLayer c i) fun X _ hXU ↦
      subset_graphNeighborhood_of_isAdmissibleSupport X.2 hXU

/-- A word of `m` layers moves the light cone by at most `R m`. -/
theorem retainedSet_flatten_subset
    (c : SupportColouring Λ R)
    (Ls : List (Fin (overlapDegreeBound R + 1))) (U : Finset (Site Λ)) :
    retainedSet (fun X : AdmissibleSupport Λ R ↦ X.1) U (Ls.map (colorLayer c)).flatten ⊆
      graphNeighborhood (planeDomainGraph Λ) U (R * Ls.length) := by
  induction Ls generalizing U with
  | nil => exact subset_graphNeighborhood
  | cons i Ls ih =>
    rw [List.map_cons, List.flatten_cons, retainedSet_append]
    refine (ih _).trans ((graphNeighborhood_mono_left (retainedSet_colorLayer_subset c i U)).trans
      (graphNeighborhood_graphNeighborhood_subset.trans ?_))
    exact le_of_eq (by rw [List.length_cons]; congr 1; ring)

/-- **The light cone of one sweep** lies in `N_{R χ}(U)`, `χ = d_R + 1`. -/
theorem retainedSet_sweepWord_subset
    (c : SupportColouring Λ R)
    (U : Finset (Site Λ)) :
    retainedSet (fun X : AdmissibleSupport Λ R ↦ X.1) U (sweepWord c) ⊆
      graphNeighborhood (planeDomainGraph Λ) U (R * (overlapDegreeBound R + 1)) := by
  have h := retainedSet_flatten_subset c (List.ofFn id) U
  rwa [List.map_ofFn, Function.comp_id, List.length_ofFn] at h

/-- **The light cone of `t` sweeps** lies in `N_{R χ t}(U)`, `χ = d_R + 1` (`eq:cone` of the
frustration-free area-law note). Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Exact localization on the
perturbed vector": "a physical product `L_t` supported on `N_{χ R t}(S₀)`". -/
theorem retainedSet_sweepWord_pow_subset
    (c : SupportColouring Λ R)
    (U : Finset (Site Λ)) (t : ℕ) :
    retainedSet (fun X : AdmissibleSupport Λ R ↦ X.1) U (List.replicate t (sweepWord c)).flatten ⊆
      graphNeighborhood (planeDomainGraph Λ) U (R * (overlapDegreeBound R + 1) * t) := by
  induction t generalizing U with
  | zero => exact subset_graphNeighborhood
  | succ t ih =>
    rw [List.replicate_succ, List.flatten_cons, retainedSet_append]
    refine (ih _).trans ((graphNeighborhood_mono_left (retainedSet_sweepWord_subset c U)).trans
      (graphNeighborhood_graphNeighborhood_subset.trans ?_))
    exact le_of_eq (by congr 1; ring)

end TNLean.PEPS.AreaLaw.FrustrationFree
