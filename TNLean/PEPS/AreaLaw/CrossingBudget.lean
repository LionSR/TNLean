/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteSetTruncation
import QICLean.Entropy.SupportedMarginalTails
import QICLean.ManyBody.Sites.GraphBoundary
import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# Crossing supports and cut budgets

After truncation near `S₀`, a label whose anchor is at finite distance `d` from `S₀` has the
designated support `N_r(aᵢ)` with `r = max {r₀, ⌊d/2⌋}`; a label whose anchor cannot reach
`S₀` has the anchor's connected component. For a cut `X ⊆ S₀`, every designated support
meeting both `X` and its complement is a ball of radius exactly `r₀`, and its anchor lies
within `r₀` of an endpoint of an edge of the cut. Hence at most `2 μ K_b (r₀ + 1)² b_X` labels
cross the cut, where `b_X` is the number of ordered cut edges `(u, v)`, `u ∈ X`, `v ∉ X`, and
the cut parameter `ℬ_X = 1 + ∑_{i ∈ 𝒞_X} log²(e dᵢ)` with `dᵢ = q^{|Sᵢ|}`, `Sᵢ` the designated
support, is at most `C (1 + b_X) (r₀ + 1)⁶`. No factor involving the total volume appears. For
cuts `X ⊆ S₀`, components not meeting `S₀` contribute no crossing label; when `S₀` is empty,
the only such cut is empty.

The crossing labels, the cut parameter and the ordered cut edges are not defined here: they
are QICLean's crossing terms `ManyBody.crossingTerms` and cut budget `ManyBody.cutLogBudget`
of the family of designated supports, the same budget as in the marginal-tail bound, and
Mathlib's `SimpleGraph.interedges G X Xᶜ`. Complement invariance and the lower bound by one
are QICLean's `ManyBody.cutLogBudget_compl` and `Entropy.one_le_cutLogBudget`.

## Main definitions

* `TNLean.PEPS.AreaLaw.designatedSupport`: the designated support after truncation.

## Main results

* `TNLean.PEPS.AreaLaw.truncationRadius_eq_of_mem_crossingTerms`: crossing supports have
  radius exactly `r₀`.
* `TNLean.PEPS.AreaLaw.card_crossingTerms_designatedSupport_le`:
  `|𝒞_X| ≤ 2 μ K_b (r₀ + 1)² b_X`.
* `TNLean.PEPS.AreaLaw.cutLogBudget_designatedSupport_le`: `ℬ_X ≤ C (1 + b_X) (r₀ + 1)⁶`.

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

/-- The connected component of `a`, as a finite set. -/
noncomputable def componentFinset (G : SimpleGraph ι) (a : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun x => G.Reachable a x

/-- **The designated support** after truncation (`eq:quasilocal-variable-radius`,
`03-quasilocal.tex`, lines 417–424): `N_r(a)` with `r = max {r₀, ⌊d/2⌋}` when
`d = d_Λ(a, S₀) < ∞`, and the component of `a` otherwise. -/
noncomputable def designatedSupport (G : SimpleGraph ι) (S₀ : Finset ι) (r₀ : ℕ) (a : ι) :
    Finset ι :=
  if ManyBody.setEdist G S₀ a = ⊤ then componentFinset G a
  else ManyBody.graphBall G a (truncationRadius r₀ (ManyBody.setEdist G S₀ a).toNat)

omit [DecidableEq ι] in
/-- **Crossing supports have radius `r₀`** (`03-quasilocal.tex`, lines 439–440 and
507–510): if the designated support of a label meets `X ⊆ S₀` and its complement, the
anchor has finite distance from `S₀` and its truncation radius is `r₀`. -/
theorem truncationRadius_eq_of_mem_crossingTerms {κ : Type*} [Fintype κ]
    {G : SimpleGraph ι} {S₀ : Finset ι} {r₀ : ℕ} {a : κ → ι} {X : Finset ι} (hX : X ⊆ S₀)
    {i : κ} (hi : i ∈ ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X) :
    ManyBody.setEdist G S₀ (a i) ≠ ⊤ ∧
      truncationRadius r₀ (ManyBody.setEdist G S₀ (a i)).toNat = r₀ ∧
      designatedSupport G S₀ r₀ (a i) = ManyBody.graphBall G (a i) r₀ := by
  classical
  obtain ⟨⟨x, hxD, hxX⟩, -⟩ := ManyBody.mem_crossingTerms.mp hi
  have hfin : ManyBody.setEdist G S₀ (a i) ≠ ⊤ := by
    intro htop
    simp only [designatedSupport, htop, ite_true, componentFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxD
    have : ManyBody.setEdist G S₀ (a i) ≤ G.edist (a i) x := ManyBody.setEdist_le_edist (hX hxX)
    rw [htop, top_le_iff] at this
    exact SimpleGraph.edist_ne_top_iff_reachable.mpr hxD this
  set d := (ManyBody.setEdist G S₀ (a i)).toNat with hd
  have hdcoe : (d : ℕ∞) = ManyBody.setEdist G S₀ (a i) := ENat.natCast_toNat hfin
  simp only [designatedSupport, hfin, ite_false, ManyBody.mem_graphBall] at hxD
  have hdle : (d : ℕ∞) ≤ G.edist (a i) x := by
    rw [hdcoe]; exact ManyBody.setEdist_le_edist (hX hxX)
  have hr : truncationRadius r₀ d = r₀ := by
    refine max_eq_left (not_lt.mp fun hlt ↦ ?_)
    have h' : G.edist (a i) x ≤ ((max r₀ (d / 2) : ℕ) : ℕ∞) := hxD
    rw [max_eq_right hlt.le] at h'
    have : d ≤ d / 2 := by exact_mod_cast hdle.trans h'
    omega
  refine ⟨hfin, hr, ?_⟩
  simp only [designatedSupport, hfin, ite_false, ← hd, hr]

/-- **Crossing count** (`eq:quasilocal-crossing-count`, `03-quasilocal.tex`, lines 441–447):
if balls of radius `r` have at most `K_b (r + 1)²` sites and each site anchors at most `μ`
labels, then `|𝒞_X| ≤ 2 μ K_b (r₀ + 1)² b_X` for every `X ⊆ S₀`, where `𝒞_X` is the set of
crossing terms of the designated supports and `b_X` the number of ordered cut edges. -/
theorem card_crossingTerms_designatedSupport_le {κ : Type*} [Fintype κ] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (S₀ : Finset ι)
    (r₀ : ℕ) (a : κ → ι) {X : Finset ι} (hX : X ⊆ S₀) {Kb μ : ℝ} (hμ : 0 ≤ μ)
    (hBall : ∀ x (d : ℕ), ((ManyBody.graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) :
    ((ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X).card : ℝ) ≤
      2 * μ * Kb * ((r₀ : ℝ) + 1) ^ 2 * (G.interedges X Xᶜ).card := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨x₀⟩⟩
  · have : IsEmpty κ := ⟨fun i => hι.false (a i)⟩
    have hE : G.interedges X Xᶜ = ∅ := Finset.eq_empty_of_isEmpty _
    have hC : ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X = ∅ :=
      Finset.eq_empty_of_isEmpty _
    simp [hE, hC]
  set E := G.interedges X Xᶜ
  set P : Finset ι := E.image Prod.fst ∪ E.image Prod.snd
  set T : Finset ι := P.biUnion fun u => ManyBody.graphBall G u r₀
  -- Every crossing label has its anchor within `r₀` of an endpoint of a cut edge.
  have hsub : ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X ⊆
      T.biUnion fun x => Finset.univ.filter fun i => a i = x := by
    intro i hi
    obtain ⟨-, -, hsupp⟩ := truncationRadius_eq_of_mem_crossingTerms hX hi
    have hi' := hi
    simp only [ManyBody.mem_crossingTerms, hsupp, ManyBody.mem_graphBall] at hi'
    obtain ⟨⟨x₁, hx₁, hx₁X⟩, ⟨x₂, hx₂, hx₂X⟩⟩ := hi'
    refine Finset.mem_biUnion.mpr ⟨a i, ?_, by simp⟩
    refine Finset.mem_biUnion.mpr ?_
    by_cases ha : a i ∈ X
    · obtain ⟨u, v, hu, hv, he, hau⟩ := ManyBody.exists_edgeBoundary_near ha hx₂X hx₂
      have huv : G.Adj u v := (ManyBody.mk_mem_edgeBoundary_iff.mp he).1
      refine ⟨u, ?_, ?_⟩
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩)
        simp [E, SimpleGraph.mk_mem_interedges_iff, huv, hu, hv]
      · rw [ManyBody.mem_graphBall, SimpleGraph.edist_comm]; exact hau
    · obtain ⟨u, v, hu, hv, he, hau⟩ := ManyBody.exists_edgeBoundary_near
        (A := Xᶜ) (Finset.mem_compl.mpr ha) (by simpa using hx₁X) hx₁
      have huv : G.Adj u v := (ManyBody.mk_mem_edgeBoundary_iff.mp he).1
      refine ⟨u, ?_, ?_⟩
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v, u), ?_, rfl⟩)
        simp only [Finset.mem_compl, not_not] at hu hv
        simp [E, SimpleGraph.mk_mem_interedges_iff, huv.symm, hu, hv]
      · rw [ManyBody.mem_graphBall, SimpleGraph.edist_comm]; exact hau
  have hKb : 0 ≤ Kb := by
    have := hBall x₀ 0
    have h1 : (1 : ℝ) ≤ (ManyBody.graphBall G x₀ 0).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨x₀, ManyBody.mem_graphBall.mpr (by simp)⟩
    nlinarith
  have hPcard : (P.card : ℝ) ≤ 2 * E.card := by
    rw [two_mul]
    exact_mod_cast (Finset.card_union_le _ _).trans
      (add_le_add Finset.card_image_le Finset.card_image_le)
  calc ((ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X).card : ℝ)
      ≤ ((T.biUnion fun x => Finset.univ.filter fun i => a i = x).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ T, ((Finset.univ.filter fun i => a i = x).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ T, μ := Finset.sum_le_sum fun x _ => hMult x
    _ = T.card * μ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ u ∈ P, ((ManyBody.graphBall G u r₀).card : ℝ)) * μ := by
        gcongr; exact_mod_cast Finset.card_biUnion_le
    _ ≤ (∑ _u ∈ P, Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by
        gcongr with u _; exact hBall u r₀
    _ = P.card * (Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * E.card) * (Kb * ((r₀ : ℝ) + 1) ^ 2) * μ := by gcongr
    _ = 2 * μ * Kb * ((r₀ : ℝ) + 1) ^ 2 * E.card := by ring

omit [DecidableEq ι] in
/-- **Support dimensions of crossing labels** (`eq:quasilocal-crossing-count`,
`03-quasilocal.tex`, lines 447–448): `log dᵢ = |Sᵢ| log q ≤ K_b (r₀ + 1)² log q`. -/
theorem log_dim_le_of_mem_crossingTerms {κ : Type*} [Fintype κ] {q : ℕ} (hq : 1 ≤ q)
    {G : SimpleGraph ι} {S₀ : Finset ι} {r₀ : ℕ} {a : κ → ι} {X : Finset ι} (hX : X ⊆ S₀)
    {Kb : ℝ} (hBall : ∀ x (d : ℕ), ((ManyBody.graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    {i : κ} (hi : i ∈ ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X) :
    Real.log ((q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ≤
      Kb * Real.log q * ((r₀ : ℝ) + 1) ^ 2 := by
  obtain ⟨-, -, hsupp⟩ := truncationRadius_eq_of_mem_crossingTerms hX hi
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  rw [Real.log_pow, hsupp]
  calc ((ManyBody.graphBall G (a i) r₀).card : ℝ) * Real.log q ≤
        Kb * ((r₀ : ℝ) + 1) ^ 2 * Real.log q :=
      mul_le_mul_of_nonneg_right (hBall _ _) hlq
    _ = Kb * Real.log q * ((r₀ : ℝ) + 1) ^ 2 := by ring

/-- **Cut budget** (`eq:quasilocal-cut-budget`, `03-quasilocal.tex`, lines 448–451 and
526–528): the cut parameter `ℬ_X = 1 + ∑_{i ∈ 𝒞_X} log²(e dᵢ)`, with `dᵢ = q^{|Sᵢ|}` for the
designated support `Sᵢ`, satisfies `ℬ_X ≤ C (1 + b_X) (r₀ + 1)⁶` with
`C = max {1, 2 μ K_b (1 + K_b log q)²}`, independent of the total volume. -/
theorem cutLogBudget_designatedSupport_le {κ : Type*} [Fintype κ] {q : ℕ} (hq : 1 ≤ q)
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    (S₀ : Finset ι) (r₀ : ℕ) (a : κ → ι) {X : Finset ι} (hX : X ⊆ S₀) {Kb μ : ℝ}
    (hKb : 0 ≤ Kb) (hμ : 0 ≤ μ)
    (hBall : ∀ x (d : ℕ), ((ManyBody.graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) :
    ManyBody.cutLogBudget (fun i ↦ designatedSupport G S₀ r₀ (a i)) (fun _ ↦ q) X ≤
      max 1 (2 * μ * Kb * (1 + Kb * Real.log q) ^ 2) * (1 + (G.interedges X Xᶜ).card) *
        ((r₀ : ℝ) + 1) ^ 6 := by
  have hB : ManyBody.cutLogBudget (fun i ↦ designatedSupport G S₀ r₀ (a i)) (fun _ ↦ q) X =
      1 + ∑ i ∈ ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X,
        Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ^ 2 := by
    simp only [ManyBody.cutLogBudget, Entropy.cutLogBudget, Function.comp_apply,
      Entropy.supportDim, Finset.prod_const, Nat.cast_pow]
  set L := Real.log q
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hq)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set R := (r₀ : ℝ) + 1
  have hR : 1 ≤ R := by simp only [R]; linarith [(Nat.cast_nonneg r₀ : (0 : ℝ) ≤ r₀)]
  set b : ℝ := ((G.interedges X Xᶜ).card : ℝ)
  have hb : 0 ≤ b := Nat.cast_nonneg _
  -- Each crossing term is at most `(1 + K_b L)² R⁴`.
  have hterm : ∀ i ∈ ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X,
      Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ^ 2 ≤
        (1 + Kb * L) ^ 2 * R ^ 4 := by
    intro i hi
    have hlog := log_dim_le_of_mem_crossingTerms hq hX hBall hi
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
  have hcard := card_crossingTerms_designatedSupport_le G S₀ r₀ a hX hμ hBall hMult
  set K := 2 * μ * Kb * (1 + Kb * L) ^ 2
  have hsum : ∑ i ∈ ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X,
      Real.log (Real.exp 1 * (q : ℝ) ^ (designatedSupport G S₀ r₀ (a i)).card) ^ 2 ≤
        K * b * R ^ 6 := by
    calc _ ≤ ∑ _i ∈ ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X,
          (1 + Kb * L) ^ 2 * R ^ 4 :=
          Finset.sum_le_sum hterm
      _ = (ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X).card *
          ((1 + Kb * L) ^ 2 * R ^ 4) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * μ * Kb * R ^ 2 * b) * ((1 + Kb * L) ^ 2 * R ^ 4) := by gcongr
      _ = K * b * R ^ 6 := by simp only [K]; ring
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have hM1 : 1 ≤ max 1 K := le_max_left _ _
  have hMK : K ≤ max 1 K := le_max_right _ _
  rw [hB]
  calc 1 + ∑ i ∈ ManyBody.crossingTerms (fun i ↦ designatedSupport G S₀ r₀ (a i)) X,
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
  simp [truncatedConstraint, ManyBody.setEdist_empty]

/-- **Components away from `S₀` are retained exactly** (`03-quasilocal.tex`, lines
532–533): a label whose anchor cannot reach `S₀` keeps its constraint. -/
theorem truncatedConstraint_of_setEdist_eq_top {q : ℕ} {G : SimpleGraph ι} {S₀ : Finset ι}
    (r₀ : ℕ) {a : ι} (ha : ManyBody.setEdist G S₀ a = ⊤)
    (k : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    truncatedConstraint q G S₀ r₀ a k = k := by
  simp [truncatedConstraint, ha]

open Classical in
/-- **The truncated constraint acts on its designated support** (`03-quasilocal.tex`,
lines 419–424): the ball expectation acts on the ball, and a retained constraint acting on
the component of its anchor acts on the designated component. -/
theorem truncatedConstraint_mem_supportedOperators {q : ℕ} (G : SimpleGraph ι)
    (S₀ : Finset ι) (r₀ : ℕ) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
        (Finset.univ.filter fun x ↦ G.Reachable a x)) :
    truncatedConstraint q G S₀ r₀ a k ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q) (designatedSupport G S₀ r₀ a : Finset ι) := by
  classical
  unfold truncatedConstraint designatedSupport
  split_ifs with h
  · exact hk
  · exact (ManyBody.regionExpectation_mem_supportedOperators _ k)

end TNLean.PEPS.AreaLaw
