/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteSetTruncation
import QICLean.Entropy.SupportedMarginalTails

/-!
# Crossing supports and cut budgets

After truncation near `S₀`, a label whose anchor is at finite distance `d` from `S₀` has the
designated support `N_r(aᵢ)` with `r = max {r₀, ⌊d/2⌋}`; a label whose anchor cannot reach
`S₀` has the anchor's connected component. For a cut `X ⊆ S₀`, every designated support
meeting both `X` and its complement is a ball of radius exactly `r₀`, and its anchor lies
within `r₀` of an endpoint of an edge of the cut. Hence at most `2 μ K_b (r₀ + 1)² b_X` labels
cross the cut, where `b_X` is the number of cut edges, and the cut parameter
`ℬ_X = 1 + ∑_{i ∈ 𝒞_X} log²(e dᵢ)` with `dᵢ = q^{|Sᵢ|}`, `Sᵢ` the designated support, is at
most `C (1 + b_X) (r₀ + 1)⁶`. No factor involving the total volume appears. For cuts
`X ⊆ S₀`, components not meeting `S₀` contribute no crossing label; when `S₀` is empty,
the only such cut is empty. The exact identification with the marginal-tail budget,
complement invariance, and lower bound by one hold for arbitrary cuts and local dimensions.

## Main definitions

* `TNLean.PEPS.AreaLaw.cutEdges`: the ordered cut edges `(u, v)`, `u ∈ X`, `v ∉ X`.
* `TNLean.PEPS.AreaLaw.designatedSupport`: the designated support after truncation.
* `TNLean.PEPS.AreaLaw.crossingLabels`: the labels whose designated support crosses `X`.

## Main results

* `TNLean.PEPS.AreaLaw.truncationRadius_eq_of_mem_crossingLabels`: crossing supports have
  radius exactly `r₀`.
* `TNLean.PEPS.AreaLaw.card_crossingLabels_le`: `|𝒞_X| ≤ 2 μ K_b (r₀ + 1)² b_X`.
* `TNLean.PEPS.AreaLaw.cutBudget_le`: `ℬ_X ≤ C (1 + b_X) (r₀ + 1)⁶`.
* `TNLean.PEPS.AreaLaw.cutBudget_eq_cutLogBudget`: the same budget on the original labels
  and designated support dimensions as in the marginal-tail bound.
* `TNLean.PEPS.AreaLaw.cutBudget_compl`: complementary cuts have the same budget.
* `TNLean.PEPS.AreaLaw.one_le_cutBudget`: the budget is at least one for every cut.

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

/-- Interchanging the sides of a cut preserves each crossing label. This holds for every
cut, whether or not it is contained in the truncation set. -/
@[simp] theorem crossingLabels_compl {κ : Type*} [Fintype κ] (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) (X : Finset ι) :
    crossingLabels G S₀ r₀ a Xᶜ = crossingLabels G S₀ r₀ a X := by
  classical
  ext i
  simp only [crossingLabels, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_compl, not_not]
  exact and_comm

omit [Fintype ι] [DecidableEq ι] in
/-- A point of a ball of radius `r` about `a ∈ S` outside `S` forces a cut edge `(u, v)`,
`u ∈ S`, `v ∉ S`, with `d(a, u) ≤ r`. -/
theorem exists_cut_edge_near {G : SimpleGraph ι} {a x : ι} {S : Set ι} {r : ℕ}
    (ha : a ∈ S) (hx : x ∉ S) (hax : G.edist a x ≤ r) :
    ∃ u v, G.Adj u v ∧ u ∈ S ∧ v ∉ S ∧ G.edist a u ≤ r := by
  classical
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

/-- **The cut parameter** `ℬ_X = 1 + ∑_{i ∈ 𝒞_X} log²(e dᵢ)` with `dᵢ = q^{|Sᵢ|}` for the
designated support `Sᵢ` (`eq:quasilocal-cut-budget`, `03-quasilocal.tex`, lines 448–451). -/
noncomputable def cutBudget {κ : Type*} [Fintype κ] (q : ℕ) (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) (X : Finset ι) : ℝ :=
  1 + ∑ i ∈ crossingLabels G S₀ r₀ a X,
    Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ^ 2

/-- The geometric cut budget is exactly the designated-support budget of the marginal-tail
bound (Lemma 3.1, `02-initial.tex`, lines 47–55). The original label family is unchanged,
including repeated supports and labels whose operators vanish. No positivity of `q` or
containment of the cut in the truncation set is required for this identity. -/
theorem cutBudget_eq_cutLogBudget {κ : Type*} [Fintype κ] (q : ℕ) (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) (X : Finset ι) :
    cutBudget q G S₀ r₀ a X =
      Entropy.cutLogBudget
        (Entropy.crossingTerms (fun i => designatedSupport G S₀ r₀ (a i)) X)
        (Entropy.supportDim (fun _ : ι => q) ∘
          (fun i => designatedSupport G S₀ r₀ (a i))) := by
  classical
  simp only [cutBudget, crossingLabels, Entropy.cutLogBudget, Entropy.crossingTerms,
    Function.comp_apply, Entropy.supportDim, Finset.prod_const, Nat.cast_pow]

/-- The cut budget is invariant under exchanging the two sides of any cut. -/
@[simp] theorem cutBudget_compl {κ : Type*} [Fintype κ] (q : ℕ) (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) (X : Finset ι) :
    cutBudget q G S₀ r₀ a Xᶜ = cutBudget q G S₀ r₀ a X := by
  simp only [cutBudget, crossingLabels_compl]

/-- The constant term in the cut budget is retained even when no label crosses the cut. -/
theorem one_le_cutBudget {κ : Type*} [Fintype κ] (q : ℕ) (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) (X : Finset ι) :
    1 ≤ cutBudget q G S₀ r₀ a X := by
  rw [cutBudget_eq_cutLogBudget]
  exact Entropy.one_le_cutLogBudget _ _

/-- **Support dimensions of crossing labels** (`eq:quasilocal-crossing-count`,
`03-quasilocal.tex`, lines 447–448): `log dᵢ = |Sᵢ| log q ≤ K_b (r₀ + 1)² log q`. -/
theorem log_dim_le_of_mem_crossingLabels {κ : Type*} [Fintype κ] {q : ℕ} (hq : 1 ≤ q)
    {G : SimpleGraph ι} {S₀ : Finset ι} {r₀ : ℕ} {a : κ → ι} {X : Finset ι} (hX : X ⊆ S₀)
    {Kb : ℝ} (hBall : ∀ x (d : ℕ), ((graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    {i : κ} (hi : i ∈ crossingLabels G S₀ r₀ a X) :
    Real.log ((q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ≤
      Kb * Real.log q * ((r₀ : ℝ) + 1) ^ 2 := by
  obtain ⟨-, -, hsupp⟩ := truncationRadius_eq_of_mem_crossingLabels hX hi
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  rw [Real.log_pow, hsupp]
  calc ((graphBall G (a i) r₀).card : ℝ) * Real.log q ≤
        Kb * ((r₀ : ℝ) + 1) ^ 2 * Real.log q :=
      mul_le_mul_of_nonneg_right (hBall _ _) hlq
    _ = Kb * Real.log q * ((r₀ : ℝ) + 1) ^ 2 := by ring

/-- **Cut budget** (`eq:quasilocal-cut-budget`, `03-quasilocal.tex`, lines 448–451 and
526–528): `ℬ_X ≤ C (1 + b_X) (r₀ + 1)⁶` with
`C = max {1, 2 μ K_b (1 + K_b log q)²}`, independent of the total volume. -/
theorem cutBudget_le {κ : Type*} [Fintype κ] {q : ℕ} (hq : 1 ≤ q) (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) {X : Finset ι} (hX : X ⊆ S₀) {Kb μ : ℝ}
    (hKb : 0 ≤ Kb) (hμ : 0 ≤ μ)
    (hBall : ∀ x (d : ℕ), ((graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) :
    cutBudget q G S₀ r₀ a X ≤
      max 1 (2 * μ * Kb * (1 + Kb * Real.log q) ^ 2) * (1 + (cutEdges G X).card) *
        ((r₀ : ℝ) + 1) ^ 6 := by
  set L := Real.log q
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hq)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set R := (r₀ : ℝ) + 1
  have hR : 1 ≤ R := by simp only [R]; linarith [(Nat.cast_nonneg r₀ : (0 : ℝ) ≤ r₀)]
  set b : ℝ := ((cutEdges G X).card : ℝ)
  have hb : 0 ≤ b := Nat.cast_nonneg _
  -- Each crossing term is at most `(1 + K_b L)² R⁴`.
  have hterm : ∀ i ∈ crossingLabels G S₀ r₀ a X,
      Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ^ 2 ≤
        (1 + Kb * L) ^ 2 * R ^ 4 := by
    intro i hi
    have hlog := log_dim_le_of_mem_crossingLabels hq hX hBall hi
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    have h0 : 0 ≤ Real.log ((q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) := by
      rw [Real.log_pow]; positivity
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
    have h1 : 1 + Real.log ((q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ≤
        (1 + Kb * L) * R ^ 2 := by
      have : Kb * L * R ^ 2 = Kb * L * ((r₀ : ℝ) + 1) ^ 2 := rfl
      nlinarith [mul_nonneg hKb hL]
    calc (1 + Real.log ((q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card)) ^ 2
        ≤ ((1 + Kb * L) * R ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = (1 + Kb * L) ^ 2 * R ^ 4 := by ring
  have hcard := card_crossingLabels_le G S₀ r₀ a hX hμ hBall hMult
  set K := 2 * μ * Kb * (1 + Kb * L) ^ 2
  have hsum : ∑ i ∈ crossingLabels G S₀ r₀ a X,
      Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ^ 2 ≤
        K * b * R ^ 6 := by
    calc _ ≤ ∑ _i ∈ crossingLabels G S₀ r₀ a X, (1 + Kb * L) ^ 2 * R ^ 4 :=
          Finset.sum_le_sum hterm
      _ = (crossingLabels G S₀ r₀ a X).card * ((1 + Kb * L) ^ 2 * R ^ 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * μ * Kb * R ^ 2 * b) * ((1 + Kb * L) ^ 2 * R ^ 4) := by gcongr
      _ = K * b * R ^ 6 := by simp only [K]; ring
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have hM1 : 1 ≤ max 1 K := le_max_left _ _
  have hMK : K ≤ max 1 K := le_max_right _ _
  unfold cutBudget
  calc 1 + ∑ i ∈ crossingLabels G S₀ r₀ a X,
        Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ^ 2
      ≤ 1 + K * b * R ^ 6 := by linarith
    _ ≤ max 1 K * R ^ 6 + max 1 K * b * R ^ 6 := by
        have : (1 : ℝ) ≤ max 1 K * R ^ 6 := by nlinarith
        have : K * b * R ^ 6 ≤ max 1 K * b * R ^ 6 := by gcongr
        linarith
    _ = max 1 K * (1 + b) * R ^ 6 := by ring

/-- **The cut budget in terms of `n`** (`03-quasilocal.tex`, lines 452–455 and 528–529):
with `r₀ = ⌈C₁ (log n)²⌉`, `n ≥ 2`, `D ≥ 1` and `b_X ≤ C₂ n D`, a bound
`ℬ_X ≤ C (1 + b_X) (r₀ + 1)⁶` gives `ℬ_X ≤ C (1 + C₂) (C₁ + 2 / (log 2)²)⁶ n D (log n)¹²`. -/
theorem le_of_cutBudget_le {C C₁ C₂ B n D b : ℝ} (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hn : 2 ≤ n) (hD : 1 ≤ D) (hbX : b ≤ C₂ * n * D)
    (hB : B ≤ C * (1 + b) * (((⌈C₁ * Real.log n ^ 2⌉₊ : ℕ) : ℝ) + 1) ^ 6) :
    B ≤ C * (1 + C₂) * (C₁ + 2 / Real.log 2 ^ 2) ^ 6 * (n * D * Real.log n ^ 12) := by
  set L := Real.log n
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL2 : Real.log 2 ≤ L := Real.log_le_log two_pos hn
  have hL : 0 < L := hl2.trans_le hL2
  have hr : ((⌈C₁ * L ^ 2⌉₊ : ℕ) : ℝ) + 1 ≤ (C₁ + 2 / Real.log 2 ^ 2) * L ^ 2 := by
    have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ C₁ * L ^ 2)
    have h2 : 2 ≤ 2 / Real.log 2 ^ 2 * L ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [pow_le_pow_left₀ hl2.le hL2 2]
    nlinarith
  have hnD : 1 ≤ n * D := by nlinarith
  have hb' : 1 + b ≤ (1 + C₂) * (n * D) := by nlinarith
  refine hB.trans ?_
  calc C * (1 + b) * (((⌈C₁ * L ^ 2⌉₊ : ℕ) : ℝ) + 1) ^ 6
      ≤ C * ((1 + C₂) * (n * D)) * ((C₁ + 2 / Real.log 2 ^ 2) * L ^ 2) ^ 6 := by
        gcongr
    _ = C * (1 + C₂) * (C₁ + 2 / Real.log 2 ^ 2) ^ 6 * (n * D * L ^ 12) := by ring

/-- **Empty truncation set** (`03-quasilocal.tex`, lines 530–532): with `S₀ = ∅` every
constraint is retained exactly and no label crosses any cut `X ⊆ S₀`. -/
theorem truncatedConstraint_empty {q : ℕ} (G : SimpleGraph ι) (r₀ : ℕ) (a : ι)
    (k : Matrix (ι → Fin q) (ι → Fin q) ℂ) : truncatedConstraint q G ∅ r₀ a k = k := by
  simp [truncatedConstraint, setDist]

@[simp] theorem crossingLabels_empty {κ : Type*} [Fintype κ] (G : SimpleGraph ι) (S₀ : Finset ι)
    (r₀ : ℕ) (a : κ → ι) : crossingLabels G S₀ r₀ a ∅ = ∅ := by
  simp [crossingLabels]

/-- No designated support crosses the full cut. -/
@[simp] theorem crossingLabels_univ {κ : Type*} [Fintype κ] (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) :
    crossingLabels G S₀ r₀ a Finset.univ = ∅ := by
  simp [crossingLabels]

/-- The empty cut has budget one, for every truncation set and local dimension. -/
@[simp] theorem cutBudget_empty {κ : Type*} [Fintype κ] (q : ℕ) (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) : cutBudget q G S₀ r₀ a ∅ = 1 := by
  simp [cutBudget]

/-- The full cut has budget one, for every truncation set and local dimension. -/
@[simp] theorem cutBudget_univ {κ : Type*} [Fintype κ] (q : ℕ) (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) : cutBudget q G S₀ r₀ a Finset.univ = 1 := by
  simp [cutBudget]

/-- **Components away from `S₀` are retained exactly** (`03-quasilocal.tex`, lines
532–533): a label whose anchor cannot reach `S₀` keeps its constraint. -/
theorem truncatedConstraint_of_setDist_eq_top {q : ℕ} {G : SimpleGraph ι} {S₀ : Finset ι}
    (r₀ : ℕ) {a : ι} (ha : setDist G S₀ a = ⊤) (k : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    truncatedConstraint q G S₀ r₀ a k = k := by
  simp [truncatedConstraint, ha]

/-- **The truncated constraint acts on its designated support** (`03-quasilocal.tex`,
lines 419–424): the ball expectation acts on the ball, and a retained constraint acting on
the component of its anchor acts on the designated component. -/
theorem truncatedConstraint_mem_supportedOperators {q : ℕ} [NeZero q] (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ supportedOperators q {x | G.Reachable a x}) :
    truncatedConstraint q G S₀ r₀ a k ∈
      supportedOperators q (designatedSupport G S₀ r₀ a : Set ι) := by
  classical
  unfold truncatedConstraint designatedSupport
  split_ifs with h
  · have hc : ((componentFinset G a : Finset ι) : Set ι) = {x | G.Reachable a x} := by
      ext x; simp [componentFinset]
    rw [hc]; exact hk
  · exact siteExpectation_mem_supportedOperators _ k

end TNLean.PEPS.AreaLaw
