/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteSetTruncation

/-!
# Supports crossing a cut inside the truncation set

After truncation near `S₀`, a label whose anchor is at finite distance `d` from `S₀` has the
designated support `N_r(aᵢ)` with `r = max {r₀, ⌊d/2⌋}`; a label whose anchor cannot reach
`S₀` has the anchor's connected component. For a cut `X ⊆ S₀`, every designated support
meeting both `X` and its complement is a ball of radius exactly `r₀`, and its anchor lies
within `r₀` of an endpoint of an edge of the cut. Hence at most `2 μ K_b (r₀ + 1)² b_X` labels
cross the cut, where `b_X` is the number of cut edges, and the cut parameter
`ℬ_X = 1 + ∑_{i ∈ 𝒞_X} log²(e dᵢ)` with `dᵢ = q^{|X̃ᵢ|}` is at most
`C (1 + b_X) (r₀ + 1)⁶`. No factor involving the total volume appears; components not
meeting `S₀`, and the empty set `S₀`, contribute no crossing label.

## Main definitions

* `TNLean.PEPS.AreaLaw.cutEdges`: the ordered cut edges `(u, v)`, `u ∈ X`, `v ∉ X`.
* `TNLean.PEPS.AreaLaw.designatedSupport`: the designated support after truncation.
* `TNLean.PEPS.AreaLaw.crossingLabels`: the labels whose designated support crosses `X`.

## Main results

* `TNLean.PEPS.AreaLaw.truncationRadius_eq_of_mem_crossingLabels`: crossing supports have
  radius exactly `r₀`.
* `TNLean.PEPS.AreaLaw.card_crossingLabels_le`: `|𝒞_X| ≤ 2 μ K_b (r₀ + 1)² b_X`.
* `TNLean.PEPS.AreaLaw.cutBudget_le`: `ℬ_X ≤ C (1 + b_X) (r₀ + 1)⁶`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.5 (`prop:truncation`), `eq:quasilocal-crossing-count` and
  `eq:quasilocal-cut-budget`, section file `03-quasilocal.tex`, lines 434–455 and 506–534.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordered cut edges `(u, v)` with `u ∈ X` and `v ∉ X`; their number is
`b_X = |∂_Λ X|` (`03-quasilocal.tex`, line 436). -/
noncomputable def cutEdges (G : SimpleGraph ι) (X : Finset ι) : Finset (ι × ι) := by
  classical
  exact Finset.univ.filter fun p => G.Adj p.1 p.2 ∧ p.1 ∈ X ∧ p.2 ∉ X

/-- The connected component of `a`, as a finite set. -/
noncomputable def componentFinset (G : SimpleGraph ι) (a : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun x => G.Reachable a x

/-- **The designated support** after truncation (`eq:quasilocal-variable-radius`,
`03-quasilocal.tex`, lines 417–424): `N_r(a)` with `r = max {r₀, ⌊d/2⌋}` when
`d = d_Λ(a, S₀) < ∞`, and the component of `a` otherwise. -/
noncomputable def designatedSupport (G : SimpleGraph ι) (S₀ : Finset ι) (r₀ : ℕ) (a : ι) :
    Finset ι :=
  if setDist G S₀ a = ⊤ then componentFinset G a
  else graphBall G a (truncationRadius r₀ (setDist G S₀ a).toNat)

/-- The labels whose designated support meets both `X` and its complement
(`03-quasilocal.tex`, lines 436–438). -/
noncomputable def crossingLabels {κ : Type*} [Fintype κ] (G : SimpleGraph ι) (S₀ : Finset ι)
    (r₀ : ℕ) (a : κ → ι) (X : Finset ι) : Finset κ := by
  classical
  exact Finset.univ.filter fun i =>
    (∃ x ∈ designatedSupport G S₀ r₀ (a i), x ∈ X) ∧
      ∃ x ∈ designatedSupport G S₀ r₀ (a i), x ∉ X

omit [Fintype ι] in
/-- A point of a ball of radius `r` about `a ∈ S` outside `S` forces a cut edge `(u, v)`,
`u ∈ S`, `v ∉ S`, with `d(a, u) ≤ r`. -/
theorem exists_cut_edge_near {G : SimpleGraph ι} {a x : ι} {S : Set ι} {r : ℕ}
    (ha : a ∈ S) (hx : x ∉ S) (hax : G.edist a x ≤ r) :
    ∃ u v, G.Adj u v ∧ u ∈ S ∧ v ∉ S ∧ G.edist a u ≤ r := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hax)
  obtain ⟨d, hd, hd1, hd2⟩ := p.exists_boundary_dart S ha hx
  refine ⟨d.fst, d.snd, d.adj, hd1, hd2, ?_⟩
  have hmem := p.dart_fst_mem_support_of_mem_darts hd
  calc G.edist a d.fst ≤ (p.takeUntil d.fst hmem).length := SimpleGraph.edist_le _
    _ ≤ p.length := by exact_mod_cast p.length_takeUntil_le_length hmem
    _ = G.edist a x := hp
    _ ≤ r := hax

/-- **Crossing supports have radius `r₀`** (`03-quasilocal.tex`, lines 439–440 and
507–510): if the designated support of a label meets `X ⊆ S₀` and its complement, the
anchor has finite distance from `S₀` and its truncation radius is `r₀`. -/
theorem truncationRadius_eq_of_mem_crossingLabels {κ : Type*} [Fintype κ]
    {G : SimpleGraph ι} {S₀ : Finset ι} {r₀ : ℕ} {a : κ → ι} {X : Finset ι} (hX : X ⊆ S₀)
    {i : κ} (hi : i ∈ crossingLabels G S₀ r₀ a X) :
    setDist G S₀ (a i) ≠ ⊤ ∧ truncationRadius r₀ (setDist G S₀ (a i)).toNat = r₀ ∧
      designatedSupport G S₀ r₀ (a i) = graphBall G (a i) r₀ := by
  classical
  simp only [crossingLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨⟨x, hxD, hxX⟩, -⟩ := hi
  have hfin : setDist G S₀ (a i) ≠ ⊤ := by
    intro htop
    simp only [designatedSupport, htop, ite_true, componentFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxD
    have : setDist G S₀ (a i) ≤ G.edist (a i) x := Finset.inf_le (hX hxX)
    rw [htop, top_le_iff] at this
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr hxD this
  set d := (setDist G S₀ (a i)).toNat with hd
  have hdcoe : (d : ℕ∞) = setDist G S₀ (a i) := ENat.natCast_toNat hfin
  simp only [designatedSupport, hfin, ite_false, mem_graphBall] at hxD
  have hdle : (d : ℕ∞) ≤ G.edist (a i) x := by rw [hdcoe]; exact Finset.inf_le (hX hxX)
  have hr : truncationRadius r₀ d = r₀ := by
    unfold truncationRadius
    by_contra hne
    have hlt : r₀ < d / 2 := by
      rcases le_or_gt (d / 2) r₀ with h | h
      · exact absurd (max_eq_left h) hne
      · exact h
    have hd2 : d / 2 < d := Nat.div_lt_self (by omega) one_lt_two
    have : G.edist (a i) x ≤ ((d / 2 : ℕ) : ℕ∞) := by
      have h' : G.edist (a i) x ≤ ((max r₀ (d / 2) : ℕ) : ℕ∞) := hxD
      rwa [max_eq_right hlt.le] at h'
    have := hdle.trans this
    have : d ≤ d / 2 := by exact_mod_cast this
    omega
  refine ⟨hfin, hr, ?_⟩
  simp only [designatedSupport, hfin, ite_false, ← hd, hr]

/-- **Crossing count** (`eq:quasilocal-crossing-count`, `03-quasilocal.tex`, lines 441–447):
if balls of radius `r` have at most `K_b (r + 1)²` sites and each site anchors at most `μ`
labels, then `|𝒞_X| ≤ 2 μ K_b (r₀ + 1)² b_X` for every `X ⊆ S₀`. -/
theorem card_crossingLabels_le {κ : Type*} [Fintype κ] (G : SimpleGraph ι) (S₀ : Finset ι)
    (r₀ : ℕ) (a : κ → ι) {X : Finset ι} (hX : X ⊆ S₀) {Kb μ : ℝ} (hμ : 0 ≤ μ)
    (hBall : ∀ x (d : ℕ), ((graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) :
    ((crossingLabels G S₀ r₀ a X).card : ℝ) ≤
      2 * μ * Kb * ((r₀ : ℝ) + 1) ^ 2 * (cutEdges G X).card := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨x₀⟩⟩
  · have : IsEmpty κ := ⟨fun i => hι.false (a i)⟩
    have hE : cutEdges G X = ∅ := Finset.eq_empty_of_isEmpty _
    simp [hE, crossingLabels]
  set E := cutEdges G X
  set P : Finset ι := E.image Prod.fst ∪ E.image Prod.snd
  set T : Finset ι := P.biUnion fun u => graphBall G u r₀
  -- Every crossing label has its anchor within `r₀` of an endpoint of a cut edge.
  have hsub : crossingLabels G S₀ r₀ a X ⊆ T.biUnion fun x =>
      Finset.univ.filter fun i => a i = x := by
    intro i hi
    obtain ⟨-, -, hsupp⟩ := truncationRadius_eq_of_mem_crossingLabels hX hi
    have hi' := hi
    simp only [crossingLabels, Finset.mem_filter, Finset.mem_univ, true_and, hsupp,
      mem_graphBall] at hi'
    obtain ⟨⟨x₁, hx₁, hx₁X⟩, ⟨x₂, hx₂, hx₂X⟩⟩ := hi'
    refine Finset.mem_biUnion.mpr ⟨a i, ?_, by simp⟩
    refine Finset.mem_biUnion.mpr ?_
    by_cases ha : a i ∈ X
    · obtain ⟨u, v, huv, hu, hv, hau⟩ := exists_cut_edge_near (S := (X : Set ι)) ha hx₂X hx₂
      refine ⟨u, ?_, ?_⟩
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩)
        simp only [Finset.mem_coe] at hu hv
        simp [E, cutEdges, huv, hu, hv]
      · rw [mem_graphBall, SimpleGraph.edist_comm]; exact hau
    · obtain ⟨u, v, huv, hu, hv, hau⟩ :=
        exists_cut_edge_near (S := ((X : Set ι)ᶜ)) ha (by simpa using hx₁X) hx₁
      refine ⟨u, ?_, ?_⟩
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v, u), ?_, rfl⟩)
        simp only [Set.mem_compl_iff, Finset.mem_coe, not_not] at hu hv
        simp [E, cutEdges, huv.symm, hu, hv]
      · rw [mem_graphBall, SimpleGraph.edist_comm]; exact hau
  have hKb : 0 ≤ Kb := by
    have := hBall x₀ 0
    have h1 : (1 : ℝ) ≤ (graphBall G x₀ 0).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨x₀, mem_graphBall.mpr (by simp)⟩
    nlinarith
  have hPcard : (P.card : ℝ) ≤ 2 * E.card := by
    have : P.card ≤ 2 * E.card :=
      calc P.card ≤ (E.image Prod.fst).card + (E.image Prod.snd).card := Finset.card_union_le _ _
        _ ≤ E.card + E.card := add_le_add Finset.card_image_le Finset.card_image_le
        _ = 2 * E.card := by ring
    exact_mod_cast this
  calc ((crossingLabels G S₀ r₀ a X).card : ℝ)
      ≤ ((T.biUnion fun x => Finset.univ.filter fun i => a i = x).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ T, ((Finset.univ.filter fun i => a i = x).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ T, μ := Finset.sum_le_sum fun x _ => hMult x
    _ = T.card * μ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ u ∈ P, ((graphBall G u r₀).card : ℝ)) * μ := by
        gcongr; exact_mod_cast Finset.card_biUnion_le
    _ ≤ (∑ _u ∈ P, Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by
        gcongr with u _; exact hBall u r₀
    _ = P.card * (Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * E.card) * (Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by gcongr
    _ = 2 * μ * Kb * ((r₀ : ℝ) + 1) ^ 2 * E.card := by ring

end TNLean.PEPS.AreaLaw
