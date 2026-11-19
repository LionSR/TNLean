/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import TNLean.Algebra.KroneckerLocalSection

/-!
# Lifting paths that are continuous modulo local unitaries

Let `u : [0, 1] → U(ℓ r)` be continuous modulo the local unitaries: for every `p`
and `ε > 0` there is `δ > 0` such that for `|q - p| < δ` some product `x ⊗ y` of
unitaries gives `‖u(q) - (x ⊗ y) u(p)‖ < ε`. Then there is a continuous
`û : [0, 1] → U(ℓ r)` with `û(p)` in the orbit of `u(p)` for every `p`.

The proof uses the local sections of `TNLean/Algebra/KroneckerLocalSection.lean`:
near each `p`, the map `q ↦ σ_p(u(q))` is a continuous lift, because `σ_p` is
invariant under the local unitaries. A Lebesgue number for the cover of `[0, 1]`
by these neighbourhoods divides `[0, 1]` into finitely many intervals, each
carrying a local lift, and neighbouring lifts are matched at the junctions by
constant local unitaries. No continuity of `u` itself is used.

This is step 4 of the cross-section construction that replaces the slice theorem
of Montgomery and Yang in arXiv:1703.09188, proof of Corollary `coruvSF`,
lines 942--947; see `docs/paper-gaps/mpu_standard_form_path_cross_section.tex`.

## Main statements

* `exists_continuousOn_Icc_lift`: local lifts on `[0, 1]`, matched by constant
  group elements, glue to a lift on `[0, 1]`, for any group action by
  homeomorphisms.
* `Matrix.exists_continuous_lift_of_continuous_mod_localUnitary`: the path
  lifting theorem.
-/

open Set Filter Topology Metric

/-! ### Gluing local lifts along `[0, 1]` -/

section Gluing

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- Gluing a lift on `[0, t]` to a lift on `[t, t']` by a constant group element. -/
private theorem glue_lift {f : ℝ → X} {t t' : ℝ} (htt' : t ≤ t') {L L' : ℝ → X}
    (hL : ContinuousOn L (Icc 0 t)) (hLf : ∀ q ∈ Icc 0 t, ∃ g : G, L q = g • f q)
    (hL' : ContinuousOn L' (Icc t t')) (hL'f : ∀ q ∈ Icc t t', ∃ g : G, L' q = g • f q)
    (ht : 0 ≤ t) :
    ∃ L'' : ℝ → X, ContinuousOn L'' (Icc 0 t') ∧ ∀ q ∈ Icc 0 t', ∃ g : G, L'' q = g • f q := by
  obtain ⟨g₁, hg₁⟩ := hLf t ⟨ht, le_rfl⟩
  obtain ⟨g₂, hg₂⟩ := hL'f t ⟨le_rfl, htt'⟩
  set c : G := g₁ * g₂⁻¹
  have hc : L t = c • L' t := by rw [hg₁, hg₂, smul_smul, mul_assoc, inv_mul_cancel, mul_one]
  classical
  refine ⟨fun q ↦ if q ≤ t then L q else c • L' q, ?_, fun q hq ↦ ?_⟩
  · have hunion : Icc 0 t' = Icc 0 t ∪ Icc t t' := (Icc_union_Icc_eq_Icc ht htt').symm
    rw [hunion]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hL.congr fun q hq ↦ by simp only [hq.2, ↓reduceIte]
    · refine ((continuous_const_smul c).comp_continuousOn hL').congr fun q hq ↦ ?_
      rcases hq.1.lt_or_eq with h | h
      · simp only [not_le.mpr h, ↓reduceIte, Function.comp_apply]
      · simp only [← h, le_refl, ↓reduceIte, hc, Function.comp_apply]
  · by_cases hqt : q ≤ t
    · simp only [hqt, ↓reduceIte]
      exact hLf q ⟨hq.1, hqt⟩
    · simp only [hqt, ↓reduceIte]
      obtain ⟨g, hg⟩ := hL'f q ⟨(not_le.mp hqt).le, hq.2⟩
      exact ⟨c * g, by rw [hg, smul_smul]⟩

/-- **Gluing local lifts.** Suppose every point of `[0, 1]` has a neighbourhood
carrying a continuous map `L` with `L q` in the orbit of `f q`. Then there is a
map, continuous on `[0, 1]`, whose value at every `q ∈ [0, 1]` lies in the orbit
of `f q`. The function `f` itself need not be continuous.

Source: the Lebesgue number argument of step 4 of the cross-section construction
for arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
theorem exists_continuousOn_Icc_lift {f : ℝ → X}
    (hloc : ∀ p ∈ Icc (0 : ℝ) 1, ∃ U ∈ 𝓝 p, ∃ L : ℝ → X,
      ContinuousOn L U ∧ ∀ q ∈ U, ∃ g : G, L q = g • f q) :
    ∃ L : ℝ → X, ContinuousOn L (Icc 0 1) ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∃ g : G, L q = g • f q := by
  choose! U hU L hL hLf using hloc
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (c := fun p : Icc (0 : ℝ) 1 ↦
      interior (U p)) isCompact_Icc (fun _ ↦ isOpen_interior)
    (fun p hp ↦ mem_iUnion.mpr ⟨⟨p, hp⟩, mem_interior_iff_mem_nhds.mpr (hU p hp)⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  -- Every interval `[k/(n+1), (k+1)/(n+1)]` with `k ≤ n` lies in some `U p`.
  have hstep : ∀ k : ℕ, k ≤ n → ∃ p ∈ Icc (0 : ℝ) 1,
      Icc ((k : ℝ) / (n + 1)) ((k + 1 : ℝ) / (n + 1)) ⊆ U p := by
    intro k hk
    have hk0 : (k : ℝ) / (n + 1) ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, (div_le_one hn0).mpr ?_⟩
      exact_mod_cast hk.trans (Nat.le_succ n)
    obtain ⟨⟨p, hp⟩, hp'⟩ := hball _ hk0
    refine ⟨p, hp, fun q hq ↦ interior_subset (hp' ?_)⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have h1 : q - (k : ℝ) / (n + 1) ≤ 1 / (n + 1) := by
      have := hq.2
      rw [add_div] at this
      linarith
    constructor <;> linarith [hq.1]
  -- Induction on the number of intervals.
  have hind : ∀ k : ℕ, k ≤ n + 1 → ∃ L : ℝ → X, ContinuousOn L (Icc 0 ((k : ℝ) / (n + 1))) ∧
      ∀ q ∈ Icc (0 : ℝ) ((k : ℝ) / (n + 1)), ∃ g : G, L q = g • f q := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ ↦ f 0, continuousOn_const, fun q hq ↦ ⟨1, ?_⟩⟩
      have : q = 0 := by simp only [Nat.cast_zero, zero_div] at hq; exact le_antisymm hq.2 hq.1
      rw [this, one_smul]
    | succ k ih =>
      intro hk
      obtain ⟨L₀, hL₀, hL₀f⟩ := ih (by omega)
      obtain ⟨p, hp, hsub⟩ := hstep k (by omega)
      have htt' : (k : ℝ) / (n + 1) ≤ (k + 1 : ℝ) / (n + 1) :=
        div_le_div_of_nonneg_right (by linarith) hn0.le
      have := glue_lift (G := G) htt' hL₀ hL₀f ((hL p hp).mono hsub)
        (fun q hq ↦ hLf p hp q (hsub hq)) (by positivity)
      simpa only [Nat.cast_succ] using this
  obtain ⟨L₀, hL₀, hL₀f⟩ := hind (n + 1) le_rfl
  have : ((n + 1 : ℕ) : ℝ) / (n + 1) = 1 := by push_cast; exact div_self hn0.ne'
  rw [this] at hL₀ hL₀f
  exact ⟨L₀, hL₀, hL₀f⟩

end Gluing

/-! ### Lifting paths of unitaries -/

namespace Matrix

open scoped Matrix.Norms.L2Operator Kronecker

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The local unitaries `x ⊗ y` acting by left multiplication. -/
@[reducible] private noncomputable def localUnitaryAction :
    MulAction (unitary (Matrix m m ℂ) × unitary (Matrix n n ℂ)) (Matrix (m × n) (m × n) ℂ) where
  smul g v := ((g.1 : Matrix m m ℂ) ⊗ₖ (g.2 : Matrix n n ℂ)) * v
  one_smul v := by
    change ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ)) * v = v
    rw [one_kronecker_one, Matrix.one_mul]
  mul_smul g h v := by
    change (((g.1 : Matrix m m ℂ) * (h.1 : Matrix m m ℂ)) ⊗ₖ
      ((g.2 : Matrix n n ℂ) * (h.2 : Matrix n n ℂ))) * v = _
    rw [mul_kronecker_mul, Matrix.mul_assoc]
    rfl

variable {a b : ℝ} (hapos : 0 < a) (hab : a < b) (hbc : b < Fintype.card m * Fintype.card n)
include hapos hab hbc

omit hapos hab hbc in
/-- **The local section is continuous along a path continuous modulo local
unitaries.** If `f(q₀)` lies in the domain of the local section `σ`, then `f(q)`
lies in the domain for `q` near `q₀`, and `q ↦ σ(f(q))` is continuous at `q₀`. -/
private theorem eventually_mem_and_continuousAt {u₀ : Matrix (m × n) (m × n) ℂ}
    {f : ℝ → Matrix (m × n) (m × n) ℂ}
    (hf : ∀ t, ∀ ε > 0, ∃ δ > 0, ∀ s, dist s t < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖f s - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * f t‖ < ε)
    {q₀ : ℝ} (hq₀ : f q₀ ∈ localSectionDomain a b u₀) :
    (∀ᶠ q in 𝓝 q₀, f q ∈ localSectionDomain a b u₀) ∧
      ContinuousAt (fun q ↦ localSection a b u₀ (f q)) q₀ := by
  have hopen := isOpen_localSectionDomain a b u₀
  have hσ : ContinuousAt (localSection a b u₀) (f q₀) :=
    (continuousOn_localSection a b u₀).continuousAt (hopen.mem_nhds hq₀)
  -- Moving `f s` back by the inverse local unitary lands near `f q₀`.
  have hback : ∀ η > 0, ∃ δ > 0, ∀ s, dist s q₀ < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        dist (((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * f s) (f q₀) < η := by
    intro η hη
    obtain ⟨δ, hδ, hfδ⟩ := hf q₀ η hη
    refine ⟨δ, hδ, fun s hs ↦ ?_⟩
    obtain ⟨x, y, hxy⟩ := hfδ s hs
    have hV := kronecker_mem_unitary x.2 y.2
    have hstar : ((star x : unitary (Matrix m m ℂ)) ⊗ₖ (star y : unitary (Matrix n n ℂ)) :
        Matrix (m × n) (m × n) ℂ) = star ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) := by
      rw [star_eq_conjTranspose, conjTranspose_kronecker]
      rfl
    refine ⟨star x, star y, ?_⟩
    have hk : ((star x : unitary (Matrix m m ℂ)) ⊗ₖ (star y : unitary (Matrix n n ℂ)) :
        Matrix (m × n) (m × n) ℂ) * f s - f q₀ =
        star ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) *
          (f s - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * f q₀) := by
      rw [hstar, Matrix.mul_sub, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hV,
        Matrix.one_mul]
    rw [dist_eq_norm, hk]
    exact lt_of_eq_of_lt (CStarRing.norm_coe_unitary_mul ⟨_, Unitary.star_mem hV⟩ _) hxy
  constructor
  · obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen _ hq₀
    obtain ⟨δ, hδ, hδ'⟩ := hback η hη
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun s hs ↦ ?_⟩
    obtain ⟨x, y, hxy⟩ := hδ' s hs
    exact (kronecker_mul_mem_localSectionDomain_iff a b u₀ x y (f s)).mp (hball hxy)
  · refine Metric.continuousAt_iff.mpr fun ε hε ↦ ?_
    obtain ⟨η, hη, hση⟩ := Metric.continuousAt_iff.mp hσ ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hback η hη
    refine ⟨δ, hδ, fun s hs ↦ ?_⟩
    obtain ⟨x, y, hxy⟩ := hδ' s hs
    have := hση hxy
    rwa [localSection_kronecker_mul] at this

omit hapos hab hbc in
/-- A path continuous modulo local unitaries on `[0, 1]`, extended to `ℝ` by
projection, stays continuous modulo local unitaries. -/
private theorem continuous_mod_projIcc {u : unitInterval → Matrix (m × n) (m × n) ℂ}
    (hcont : ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, dist q p < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖u q - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p‖ < ε) :
    ∀ t, ∀ ε > 0, ∃ δ > 0, ∀ s, dist s t < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖u (projIcc 0 1 zero_le_one s) -
          ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u (projIcc 0 1 zero_le_one t)‖ < ε := by
  intro t ε hε
  obtain ⟨δ, hδ, h⟩ := hcont (projIcc 0 1 zero_le_one t) ε hε
  refine ⟨δ, hδ, fun s hs ↦ h _ ?_⟩
  have := (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul s t
  simp only [NNReal.coe_one, one_mul] at this
  exact this.trans_lt hs

/-- The path lifting theorem for fixed cutoffs `0 < a < b < |m| |n|`. -/
private theorem exists_continuous_lift_aux
    (u : unitInterval → Matrix (m × n) (m × n) ℂ) (hu : ∀ p, u p ∈ unitaryGroup (m × n) ℂ)
    (hcont : ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, dist q p < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖u q - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p‖ < ε) :
    ∃ û : unitInterval → Matrix (m × n) (m × n) ℂ, Continuous û ∧
      ∀ p, ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        û p = ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p := by
  let := localUnitaryAction (m := m) (n := n)
  have : ContinuousConstSMul (unitary (Matrix m m ℂ) × unitary (Matrix n n ℂ))
      (Matrix (m × n) (m × n) ℂ) := ⟨fun g ↦ continuous_const.mul continuous_id⟩
  set f : ℝ → Matrix (m × n) (m × n) ℂ := fun t ↦ u (projIcc 0 1 zero_le_one t) with hfdef
  have hf := continuous_mod_projIcc hcont
  have hloc : ∀ p ∈ Icc (0 : ℝ) 1, ∃ U ∈ 𝓝 p, ∃ L : ℝ → Matrix (m × n) (m × n) ℂ,
      ContinuousOn L U ∧ ∀ q ∈ U, ∃ g : unitary (Matrix m m ℂ) × unitary (Matrix n n ℂ),
        L q = g • f q := by
    intro p _
    have hp : f p ∈ localSectionDomain a b (f p) := by
      have := kronecker_mul_mem_localSectionDomain (u₀ := f p) 1 1 hapos hab hbc (hu _)
      simpa only [OneMemClass.coe_one, one_kronecker_one, Matrix.one_mul] using this
    let U := {q | f q ∈ localSectionDomain a b (f p)}
    have hUopen : IsOpen U := isOpen_iff_mem_nhds.mpr fun q hq ↦
      (eventually_mem_and_continuousAt hf hq).1
    refine ⟨U, hUopen.mem_nhds hp, fun q ↦ localSection a b (f p) (f q), fun q hq ↦
      (eventually_mem_and_continuousAt hf hq).2.continuousWithinAt,
      fun q hq ↦ ?_⟩
    obtain ⟨x, y, hxy⟩ := exists_localSection_eq_kronecker_mul a b (f p) hapos hab hq
    exact ⟨(x, y), hxy⟩
  obtain ⟨L, hL, hLf⟩ := exists_continuousOn_Icc_lift hloc
  refine ⟨fun p ↦ L p, hL.comp_continuous continuous_subtype_val fun p ↦ p.2, fun p ↦ ?_⟩
  obtain ⟨g, hg⟩ := hLf p p.2
  refine ⟨g.1, g.2, ?_⟩
  change L p = ((g.1 : Matrix m m ℂ) ⊗ₖ (g.2 : Matrix n n ℂ)) * u p
  rw [hg]
  change ((g.1 : Matrix m m ℂ) ⊗ₖ (g.2 : Matrix n n ℂ)) *
    u (projIcc 0 1 zero_le_one (p : ℝ)) = _
  rw [projIcc_val]

omit hapos hab hbc in
/-- **Lifting paths continuous modulo local unitaries.** Let `u : [0, 1] → U(ℓ r)`
be continuous modulo the local unitaries: for every `p` and `ε > 0` there is
`δ > 0` such that for `|q - p| < δ` some unitaries `x` and `y` give
`‖u(q) - (x ⊗ y) u(p)‖ < ε`. Then some continuous `û` on `[0, 1]` has
`û(p) = (x ⊗ y) u(p)` for unitaries `x`, `y` depending on `p`. Nothing is assumed
about the regularity of `u` itself.

Source: arXiv:1703.09188, proof of Corollary `coruvSF`, lines 942--947, where this
step is obtained from the slice theorem of Montgomery and Yang; here it follows
from the direct cross-section construction recorded in
`docs/paper-gaps/mpu_standard_form_path_cross_section.tex`. -/
theorem exists_continuous_lift_of_continuous_mod_localUnitary
    (u : unitInterval → Matrix (m × n) (m × n) ℂ) (hu : ∀ p, u p ∈ unitaryGroup (m × n) ℂ)
    (hcont : ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, dist q p < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖u q - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p‖ < ε) :
    ∃ û : unitInterval → Matrix (m × n) (m × n) ℂ, Continuous û ∧
      ∀ p, ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        û p = ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p := by
  rcases isEmpty_or_nonempty (m × n) with hmn | hmn
  · exact ⟨u, continuous_of_const fun _ _ ↦ Subsingleton.elim _ _,
      fun p ↦ ⟨1, 1, Subsingleton.elim _ _⟩⟩
  have hc : (0 : ℝ) < Fintype.card m * Fintype.card n := by
    have := Fintype.card_pos (α := m × n)
    rw [Fintype.card_prod] at this
    exact_mod_cast this
  exact exists_continuous_lift_aux (a := (Fintype.card m * Fintype.card n : ℝ) / 3)
    (b := 2 * (Fintype.card m * Fintype.card n : ℝ) / 3) (by positivity) (by linarith)
    (by linarith) u hu hcont

end Matrix
