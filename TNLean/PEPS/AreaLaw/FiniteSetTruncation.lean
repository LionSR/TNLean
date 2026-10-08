/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.PositiveConstraints
import TNLean.PEPS.AreaLaw.TruncationSeries
import QICLean.Analysis.GapPerturbation

/-!
# Truncation of the positive constraints near a finite set

Fix a finite set `S₀` of sites and a base radius `r₀`. A constraint whose anchor has finite
graph distance `d` from `S₀` is replaced by its expectation onto the graph ball of radius
`max {r₀, ⌊d/2⌋}`; a constraint whose anchor cannot reach `S₀` is kept. Shells at distance
`d` contain at most `μ |S₀| K_b (d + 1)²` labels, so the total truncation error is at most
a constant times `|S₀| e^{-(c/2) r₀^α}`, with no factor involving the total volume. Components
not meeting `S₀` contribute exactly zero error.

## Main definitions

* `TNLean.PEPS.AreaLaw.setDist`: the graph distance from a site to `S₀`.
* `TNLean.PEPS.AreaLaw.truncationRadius`: `max {r₀, ⌊d/2⌋}`.
* `TNLean.PEPS.AreaLaw.truncatedConstraint`: the variable-radius truncation.

## Main results

* `TNLean.PEPS.AreaLaw.card_label_shell_le`: the shell count.
* `TNLean.PEPS.AreaLaw.exists_norm_sum_truncatedConstraint_sub_le`: the volume-free
  truncation error `eq:quasilocal-volume-free`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 4.5 (`prop:truncation`), section file `03-quasilocal.tex`, lines 405–478.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The graph distance `d_Λ(x, S₀) = min_{y ∈ S₀} d_Λ(x, y)`, infinite when `x` cannot reach
`S₀` (`03-quasilocal.tex`, line 418). -/
noncomputable def setDist (G : SimpleGraph ι) (S₀ : Finset ι) (x : ι) : ℕ∞ :=
  S₀.inf fun y => G.edist x y

omit [Fintype ι] [DecidableEq ι] in
/-- A finite distance to `S₀` is attained at a point of `S₀`. -/
theorem exists_mem_edist_eq_setDist {G : SimpleGraph ι} {S₀ : Finset ι} {x : ι}
    (hx : setDist G S₀ x ≠ ⊤) : ∃ y ∈ S₀, G.edist x y = setDist G S₀ x := by
  have hne : S₀.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [setDist, h] at hx
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_inf S₀ hne fun y => G.edist x y
  exact ⟨y, hy, he.symm⟩

/-- The truncation radius `r = max {r₀, ⌊d/2⌋}` (`eq:quasilocal-variable-radius`). -/
def truncationRadius (r₀ d : ℕ) : ℕ := max r₀ (d / 2)

/-- **The variable-radius truncation** (`eq:quasilocal-variable-radius`,
`03-quasilocal.tex`, lines 417–424): the expectation of `k` onto the graph ball of radius
`max {r₀, ⌊d/2⌋}` about the anchor `a` when `d = d_Λ(a, S₀) < ∞`, and `k` itself when the
anchor cannot reach `S₀`. -/
noncomputable def truncatedConstraint (q : ℕ) (G : SimpleGraph ι) (S₀ : Finset ι) (r₀ : ℕ)
    (a : ι) (k : Matrix (ι → Fin q) (ι → Fin q) ℂ) : Matrix (ι → Fin q) (ι → Fin q) ℂ :=
  if setDist G S₀ a = ⊤ then k
  else siteExpectation q (graphBall G a (truncationRadius r₀ (setDist G S₀ a).toNat)) k

/-- **Shell count** (`03-quasilocal.tex`, lines 460–463): if every graph ball of radius `d`
has at most `K_b (d + 1)²` sites and every site anchors at most `μ` labels, then at most
`μ |S₀| K_b (d + 1)²` labels have anchors at distance `d` from `S₀`. -/
theorem card_label_shell_le {κ : Type*} [Fintype κ] (G : SimpleGraph ι) (S₀ : Finset ι)
    (a : κ → ι) {Kb μ : ℝ}
    (hBall : ∀ x (d : ℕ), ((graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ) (d : ℕ) :
    ((Finset.univ.filter fun i => setDist G S₀ (a i) = d).card : ℝ) ≤
      μ * (S₀.card * (Kb * ((d : ℝ) + 1) ^ 2)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨x₀⟩⟩
  · have : IsEmpty κ := ⟨fun i => hι.false (a i)⟩
    simp [Finset.univ_eq_empty, Finset.eq_empty_of_isEmpty S₀]
  have hμ : 0 ≤ μ := (Nat.cast_nonneg _).trans (hMult x₀)
  set T := Finset.univ.filter fun x => setDist G S₀ x = d
  -- Sites at distance `d` lie in the balls of radius `d` about the points of `S₀`.
  have hT : T ⊆ S₀.biUnion fun y => graphBall G y d := by
    intro x hx
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨y, hy, he⟩ := exists_mem_edist_eq_setDist (x := x) (G := G) (S₀ := S₀)
      (by rw [hx]; exact ENat.natCast_ne_top d)
    refine Finset.mem_biUnion.mpr ⟨y, hy, mem_graphBall.mpr ?_⟩
    rw [SimpleGraph.edist_comm, he, hx]
  have hTcard : (T.card : ℝ) ≤ S₀.card * (Kb * ((d : ℝ) + 1) ^ 2) := by
    calc (T.card : ℝ) ≤ ((S₀.biUnion fun y => graphBall G y d).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hT
      _ ≤ ∑ y ∈ S₀, ((graphBall G y d).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ S₀, Kb * ((d : ℝ) + 1) ^ 2 := Finset.sum_le_sum fun y _ => hBall y d
      _ = S₀.card * (Kb * ((d : ℝ) + 1) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Each site anchors at most `μ` labels.
  have hlab : (Finset.univ.filter fun i => setDist G S₀ (a i) = d) =
      T.biUnion fun x => Finset.univ.filter fun i => a i = x := by
    ext i; simp [T]
  rw [hlab]
  calc ((T.biUnion fun x => Finset.univ.filter fun i => a i = x).card : ℝ)
      ≤ ∑ x ∈ T, ((Finset.univ.filter fun i => a i = x).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ T, μ := Finset.sum_le_sum fun x _ => hMult x
    _ = T.card * μ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S₀.card * (Kb * ((d : ℝ) + 1) ^ 2)) * μ := mul_le_mul_of_nonneg_right hTcard hμ
    _ = μ * (S₀.card * (Kb * ((d : ℝ) + 1) ^ 2)) := by ring

/-- **Volume-free truncation error** (`eq:quasilocal-volume-free`, `03-quasilocal.tex`,
lines 457–478). Suppose the constraints satisfy `‖kᵢ - E_{N_l(aᵢ)} kᵢ‖ ≤ C e^{-c l^α}`, every
graph ball of radius `d` has at most `K_b (d + 1)²` sites, every site anchors at most `μ`
labels, and the shell series is bounded by `A e^{-(c/2) r₀^α}`. Then the truncated sum
differs from `∑ᵢ kᵢ` by at most `C μ K_b |S₀| A e^{-(c/2) r₀^α}`. -/
theorem norm_sum_truncatedConstraint_sub_le {q : ℕ} [NeZero q] {κ : Type*} [Fintype κ]
    (G : SimpleGraph ι) (S₀ : Finset ι) (a : κ → ι)
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) {C c α Kb μ A : ℝ} (hC : 0 ≤ C)
    (hKb : 0 ≤ Kb) (hμ : 0 ≤ μ)
    (htail : ∀ i (l : ℕ), ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (hBall : ∀ x (d : ℕ), ((graphBall G x d).card : ℝ) ≤ Kb * ((d : ℝ) + 1) ^ 2)
    (hMult : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ)
    (hA : ∀ r₀ N : ℕ, ∑ d ∈ Finset.range N, ((d : ℝ) + 1) ^ 2 *
        Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α)) ≤
      A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α))) (r₀ : ℕ) :
    ‖∑ i, truncatedConstraint q G S₀ r₀ (a i) (k i) - ∑ i, k i‖ ≤
      C * μ * Kb * S₀.card * A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by
  classical
  set D : κ → ℕ := fun i => (setDist G S₀ (a i)).toNat
  set F := Finset.univ.filter fun i => setDist G S₀ (a i) ≠ ⊤
  set f : ℕ → ℝ := fun d => C * Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α))
  have hterm : ∀ i, ‖truncatedConstraint q G S₀ r₀ (a i) (k i) - k i‖ ≤
      if setDist G S₀ (a i) ≠ ⊤ then f (D i) else 0 := by
    intro i
    by_cases hi : setDist G S₀ (a i) = ⊤
    · simp [truncatedConstraint, hi]
    · simp only [truncatedConstraint, hi, ite_false, ne_eq, not_false_eq_true, ite_true]
      rw [norm_sub_rev]
      exact htail i _
  calc ‖∑ i, truncatedConstraint q G S₀ r₀ (a i) (k i) - ∑ i, k i‖
      = ‖∑ i, (truncatedConstraint q G S₀ r₀ (a i) (k i) - k i)‖ := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖truncatedConstraint q G S₀ r₀ (a i) (k i) - k i‖ := norm_sum_le _ _
    _ ≤ ∑ i, if setDist G S₀ (a i) ≠ ⊤ then f (D i) else 0 := Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ i ∈ F, f (D i) := by rw [Finset.sum_filter]
    _ = ∑ d ∈ F.image D, ((F.filter fun i => D i = d).card : ℝ) * f d := by
        rw [Finset.sum_comp]; simp [nsmul_eq_mul]
    _ ≤ ∑ d ∈ Finset.range ((F.image D).sup id + 1),
          (μ * (S₀.card * (Kb * ((d : ℝ) + 1) ^ 2))) * f d := by
        refine (Finset.sum_le_sum fun d _ => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
          (fun d hd => ?_) fun d _ _ => ?_)
        · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine le_trans ?_ (card_label_shell_le G S₀ a hBall hMult d)
          exact_mod_cast Finset.card_le_card fun i hi => by
            simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            rw [← hi.2]; exact (ENat.natCast_toNat hi.1).symm
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hd))
        · positivity
    _ = C * μ * Kb * S₀.card * ∑ d ∈ Finset.range ((F.image D).sup id + 1),
          ((d : ℝ) + 1) ^ 2 * Real.exp (-(c * ((max r₀ (d / 2) : ℕ) : ℝ) ^ α)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => ?_; simp only [f]; ring
    _ ≤ C * μ * Kb * S₀.card * (A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α))) := by
        gcongr; exact hA r₀ _
    _ = C * μ * Kb * S₀.card * A * Real.exp (-(c / 2 * (r₀ : ℝ) ^ α)) := by ring

end TNLean.PEPS.AreaLaw
