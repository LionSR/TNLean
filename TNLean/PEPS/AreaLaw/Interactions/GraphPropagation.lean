/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Config
import QICLean.ManyBody.Sites.Lattice.SupportCounting
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import QICLean.ManyBody.Dynamics.GraphLocalization
import QICLean.ManyBody.Hamiltonian.Models

/-!
# Graph-distance propagation for finite-domain Hamiltonians

Let `h` be a finite-range Hamiltonian on a finite induced domain `Λ ⊆ ℤ²`, with one
Hermitian term of norm at most `J` for each nonempty support of induced-graph diameter at
most `R`. For an original support `X` with anchor `a ∈ X`, an operator `A` acting on `X`,
a site `y` and an on-site operator `B` at `y`,
`‖[τ_t(A), B]‖ ≤ C ‖A‖ ‖B‖ e^{v|t| - c d_Λ(a, y)}`, the commutator vanishes when
`d_Λ(a, y) = ∞`, and the normalized partial-trace expectation onto the graph ball
`N_l(a)` satisfies `‖τ_t(A) - E_{N_l(a)}(τ_t(A))‖ ≤ ‖A‖ min(2, C e^{v|t| - c l})`. The
constants `C, v, c` are chosen from `R` and `J` alone, before the domain and the
interaction; the source allows dependence on `q, R, J`.

The proof instantiates the general graph estimates of `QuantumCircuit` on the induced
nearest-neighbor graph `planeDomainGraph Λ`. The support diameter comes from the walk condition
in `IsAdmissibleSupport`, the support size `v_R = 1 + 2R(R + 1)` and the per-site budget
`b₀ = μ_R J` with `μ_R = 2^{v_R - 1}` come from the exact lattice diamond counts, and the
sphere growth `|{y : d_Λ(x, y) = d}| ≤ 2 (d + 1)²` comes from the same count, since graph
distance dominates ambient lattice distance. Distances are always measured in the induced
graph; sites joined only through a hole are far apart.

## Main results

* `ManyBody.PlaneInteraction.norm_commutator_le_graphDistance`: the explicit
  commutator bound.
* `ManyBody.PlaneInteraction.commutator_eq_zero_of_edist_eq_top`: exact vanishing
  between different connected components of the domain.
* `ManyBody.PlaneInteraction.norm_sub_regionExpectation_graphBall_le`: the explicit
  graph-ball localization bound.
* `TNLean.PEPS.AreaLaw.exists_quasilocal_lieb_robinson`: Lemma 4.1 of the source, with
  constants depending only on `R` and `J`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 4.1 (`lem:quasilocal-lr`), `03-quasilocal.tex`, lines 52–128, with the budget
  `eq:quasilocal-budget` (lines 31–39) and the counts of `01-preliminaries.tex`,
  lines 81–102. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix.Norms.L2Operator Nat

open ManyBody (AdmissibleSupport IsAdmissibleSupport card_le_diamond_of_edist_le
  exists_walk_length_le_iff_edist_le latticeL1Distance_le_one_of_planeDomainGraph_adj
  planeDomainGraph PlaneInteraction)

open ManyBody (card_supports_containing_le_diamond)

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit

/-! ### Geometry of the induced domain graph -/

/-- The sites at induced-graph distance exactly `d` from a site number at most
`2 (d + 1)²`. Source: area law, `03-quasilocal.tex`, lines 124–126, using the diamond
count `eq:ball-count`. -/
theorem card_domainGraph_sphere_le (Λ : Finset (ℤ × ℤ)) (x : ↥Λ) (d : ℕ) :
    ((Finset.univ.filter fun y => (planeDomainGraph Λ).edist x y = d).card : ℝ) ≤
      2 * ((d : ℝ) + 1) ^ 2 := by
  have hcard := card_le_diamond_of_edist_le Subtype.val
    (Finset.univ.filter fun y => (planeDomainGraph Λ).edist x y = d) Subtype.val_injective
    (fun _ _ => latticeL1Distance_le_one_of_planeDomainGraph_adj) x d
    (fun y hy => (Finset.mem_filter.mp hy).2.le)
  have hreal : ((Finset.univ.filter fun y => (planeDomainGraph Λ).edist x y = d).card : ℝ) ≤
      ((1 + 2 * d * (d + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
  push_cast at hreal
  nlinarith

end TNLean.PEPS.AreaLaw

/-! ### The interaction budget -/

namespace ManyBody.PlaneInteraction

open TNLean.PEPS.AreaLaw QuantumCircuit

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- The term-norm bound `J` is nonnegative as soon as one support exists, since the term at
that support has norm at most `J`. Source: area law, `eq:hamiltonian`
(`00-introduction.tex`, lines 19–25). -/
theorem normBound_nonneg (h : PlaneInteraction Λ q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (X : AdmissibleSupport Λ R) :
    0 ≤ J :=
  (norm_nonneg _).trans (hhJ X)

/-- The norms of the terms whose support contains a site sum to at most `μ_R J`, with
`μ_R = 2^{v_R - 1}`. Source: area law, `eq:quasilocal-budget`
(`03-quasilocal.tex`, lines 31–39) and `01-preliminaries.tex`, lines 95–102. -/
theorem sum_norm_term_containing_le (h : PlaneInteraction Λ q R)
    (hhJ : ∀ X, ‖h.term X‖ ≤ J) (hJ : 0 ≤ J)
    (x : ↥Λ) :
    ∑ X ∈ Finset.univ.filter (fun X : AdmissibleSupport Λ R => x ∈ X.1), ‖h.term X‖ ≤
      (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J := by
  classical
  have hcard := card_supports_containing_le_diamond Subtype.val Subtype.val_injective
    (fun _ _ => latticeL1Distance_le_one_of_planeDomainGraph_adj)
    ((Finset.univ : Finset (AdmissibleSupport Λ R)).map (Function.Embedding.subtype _)) R
    (fun Y hY => by
      obtain ⟨Z, -, rfl⟩ := Finset.mem_map.mp hY
      exact Z.2.2) x
  rw [Finset.filter_map, Finset.card_map] at hcard
  calc
    _ ≤ ((Finset.univ.filter (fun X : AdmissibleSupport Λ R => x ∈ X.1)).card : ℝ) * J := by
      simpa using Finset.sum_le_card_nsmul _ (fun X => ‖h.term X‖) J
        (fun X _ => hhJ X)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hJ

/-- The terms of `h` as an interaction on the sites of `Λ`, with Hamiltonian `h.hamiltonian`. -/
private noncomputable def interaction (h : PlaneInteraction Λ q R) :
    ManyBody.Interaction (fun _ : ↥Λ ↦ Fin q) (fun X : AdmissibleSupport Λ R ↦ X.1) :=
  ⟨h.term, fun X ↦ (h.mem X)⟩

/-- An anchor family that takes the prescribed value `a` at `X` and an arbitrary site of
every other support. -/
private noncomputable def anchors (X : AdmissibleSupport Λ R) (a : ↥Λ) :
    AdmissibleSupport Λ R → ↥Λ := by
  classical
  exact Function.update (fun Y => Y.2.1.choose) X a

private theorem anchors_mem {X : AdmissibleSupport Λ R} {a : ↥Λ} (ha : a ∈ X.1)
    (Y : AdmissibleSupport Λ R) : anchors X a Y ∈ Y.1 := by
  classical
  unfold anchors
  by_cases hY : Y = X
  · subst hY
    convert ha
    exact Function.update_self ..
  · convert Y.2.1.choose_spec
    exact Function.update_of_ne hY ..

private theorem anchors_self (X : AdmissibleSupport Λ R) (a : ↥Λ) :
    anchors X a X = a := by
  classical
  unfold anchors
  convert Function.update_self ..

/-! ### Propagation estimates -/

/-- **Graph-distance propagation**, explicit form, for the finite-domain Hamiltonian.
With `v_R = 1 + 2R(R + 1)` and `μ_R = 2^{v_R - 1}`, for every `μ ≥ 0` and every integer
`n ≤ d_Λ(a, y)`,
`‖[τ_t(A), B]‖ ≤ 2 e^{μR} ‖A‖ ‖B‖ exp(2 v_R μ_R J e^{2μR} |t| - μ n)`.
The velocity factor `e^{2μR}` is coarser than the factor `e^{μR}` of the source's chain
bound; only the existence of uniform constants is used downstream.

Source: OpenAI area law, Lemma 4.1, `eq:quasilocal-lr` (`03-quasilocal.tex`,
lines 52–64 and 70–112), with the budget `eq:quasilocal-budget` (lines 31–39). -/
theorem norm_commutator_le_graphDistance (h : PlaneInteraction Λ q R)
    (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (X : AdmissibleSupport Λ R) {a : ↥Λ} (ha : a ∈ X.1)
    {A B : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) X.1) (y : ↥Λ)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ({y} : Finset ↥Λ))
    (μ : ℝ) (hμ : 0 ≤ μ) (n : ℕ) (hn : (n : ℕ∞) ≤ (planeDomainGraph Λ).edist a y) (t : ℝ) :
    ‖ManyBody.heisenbergEvolution h.hamiltonian t A * B - B *
        ManyBody.heisenbergEvolution h.hamiltonian
        t A‖ ≤
      2 * Real.exp (μ * R) * ‖A‖ * ‖B‖ *
        Real.exp (2 * (1 + 2 * R * (R + 1) : ℕ) *
          ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J) * Real.exp (2 * μ * R) * |t| - μ * n) :=
  ManyBody.norm_heisenberg_commutator_le_graphDistance (planeDomainGraph Λ) h.interaction
    (anchors X a) (anchors_mem ha) hh R
    (fun Y => Y.2.edist_le) _ (fun Y => Y.2.card_le) _
    (h.sum_norm_term_containing_le hhJ (h.normBound_nonneg hhJ X)) X
    hA y
    (by assumption) μ hμ n
    (by rwa [anchors_self]) t

/-- **Exact vanishing between components.** If the anchor `a` and the site `y` lie in
different connected components of the induced domain graph, then `τ_t(A)` commutes with
every on-site operator at `y`.

Source: OpenAI area law, Lemma 4.1: "The commutator is zero when `d_Λ(a_i, y) = ∞`"
(`03-quasilocal.tex`, lines 63 and 113–114). -/
theorem commutator_eq_zero_of_edist_eq_top (h : PlaneInteraction Λ q R)
    (X : AdmissibleSupport Λ R) {a : ↥Λ} (ha : a ∈ X.1)
    {A B : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) X.1) (y : ↥Λ)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ({y} : Finset ↥Λ))
    (hy : (planeDomainGraph Λ).edist a y = ⊤) (t : ℝ) :
    ManyBody.heisenbergEvolution h.hamiltonian t A * B - B * ManyBody.heisenbergEvolution
        h.hamiltonian t
        A = 0 :=
  ManyBody.heisenberg_commutator_eq_zero_of_edist_eq_top (planeDomainGraph Λ) h.interaction
    (anchors X a) (anchors_mem ha) R (fun Y => Y.2.edist_le) X
    hA y
    (by assumption)
    (by rwa [anchors_self]) t

/-- **Localization onto graph balls**, explicit form, for the finite-domain Hamiltonian.
With `v_R = 1 + 2R(R + 1)`, `μ_R = 2^{v_R - 1}` and the sphere growth constant `2` in
degree `2`,
`‖τ_t(A) - E_{N_l(a)}(τ_t(A))‖ ≤ ‖A‖ min(2, C₀ exp(2 v_R μ_R J e^{2R} |t| - l/2))`
with `C₀ = 2 e^R · 2 · 2² 2! e^{1/2} / (1 - e^{-1/2})`.

Source: OpenAI area law, Lemma 4.1, `eq:quasilocal-lr-ce` (`03-quasilocal.tex`,
lines 65–68 and 117–128), with `E_{i,l}` from `eq:quasilocal-ce` (lines 17–29). -/
theorem norm_sub_regionExpectation_graphBall_le (h : PlaneInteraction Λ q R)
    (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (X : AdmissibleSupport Λ R) {a : ↥Λ} (ha : a ∈ X.1)
    {A : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) X.1) (l : ℕ) (t : ℝ) :
    ‖ManyBody.heisenbergEvolution h.hamiltonian t A -
        ManyBody.regionExpectation (ManyBody.graphBall (planeDomainGraph Λ) a l)
          (ManyBody.heisenbergEvolution h.hamiltonian t A)‖ ≤
      ‖A‖ * min 2
        (2 * Real.exp R * 2 * (2 ^ 2 * 2 ! * Real.exp (1 / 2) /
            (1 - Real.exp (-(1 / 2)))) *
          Real.exp (2 * (1 + 2 * R * (R + 1) : ℕ) *
            ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * J) * Real.exp (2 * R) * |t| - l / 2)) := by
  have hBound := ManyBody.norm_heisenberg_sub_regionExpectation_graphBall_le
    (planeDomainGraph Λ) h.interaction (anchors X a) (anchors_mem ha) hh
    R (fun Y => Y.2.edist_le) _ (fun Y => Y.2.card_le) _
    (h.sum_norm_term_containing_le hhJ (h.normBound_nonneg hhJ X)) 2 2
    (fun x d => card_domainGraph_sphere_le Λ x d) X
    hA l t
  rwa [anchors_self] at hBound

end ManyBody.PlaneInteraction

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit

/-- **Graph-distance propagation** (OpenAI area law, Lemma 4.1, `lem:quasilocal-lr`). For
local dimension `q ≥ 1`, range `R` and term-norm bound `J`, there are positive constants
`C, v, c`, depending only on `q, R, J`, such that for every finite domain `Λ`, every
finite-range Hamiltonian `h` on `Λ`, every original support `X` with anchor `a ∈ X`, every
operator `A` acting on `X` and every time `t`:

* for every site `y` and every on-site operator `B` at `y`,
  `‖[τ_t(A), B]‖ ≤ C ‖A‖ ‖B‖ e^{v|t| - c d_Λ(a, y)}` when `d_Λ(a, y)` is finite, and the
  commutator is zero when `d_Λ(a, y) = ∞`;
* for every integer `l ≥ 0`,
  `‖τ_t(A) - E_{N_l(a)}(τ_t(A))‖ ≤ ‖A‖ min(2, C e^{v|t| - c l})`.

Source: OpenAI area law, `03-quasilocal.tex`, lines 52–68 (statement), 70–128 (proof),
with the constants independent of `Λ` as stated at lines 40–41 and `q ≥ 1` from
`00-introduction.tex`, line 25. -/
lemma exists_quasilocal_lieb_robinson (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J : ℝ) :
    ∃ C v c : ℝ, 0 < C ∧ 0 < v ∧ 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) (X : AdmissibleSupport Λ R)
        (a : ↥Λ), a ∈ X.1 →
        ∀ A : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ,
        A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) X.1 → ∀ t : ℝ,
        (∀ (y : ↥Λ) (B : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ),
          B ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) ({y} : Finset ↥Λ) →
          (∀ d : ℕ, (planeDomainGraph Λ).edist a y = d →
            ‖ManyBody.heisenbergEvolution h.hamiltonian t A * B -
                B * ManyBody.heisenbergEvolution h.hamiltonian t A‖ ≤
              C * ‖A‖ * ‖B‖ * Real.exp (v * |t| - c * d)) ∧
          ((planeDomainGraph Λ).edist a y = ⊤ →
            ManyBody.heisenbergEvolution h.hamiltonian t A * B -
              B * ManyBody.heisenbergEvolution h.hamiltonian t A = 0)) ∧
        ∀ l : ℕ,
          ‖ManyBody.heisenbergEvolution h.hamiltonian t A -
              ManyBody.regionExpectation (ManyBody.graphBall (planeDomainGraph Λ) a l)
                (ManyBody.heisenbergEvolution h.hamiltonian t A)‖ ≤
            ‖A‖ * min 2 (C * Real.exp (v * |t| - c * l)) := by
  have : NeZero q := ⟨by omega⟩
  set vR : ℕ := 1 + 2 * R * (R + 1)
  set b₀ : ℝ := ((2 ^ (vR - 1) : ℕ) : ℝ) * J
  obtain ⟨C₁, v₁, c₁, hC₁, hv₁, hc₁, hLR⟩ := ManyBody.exists_graph_lieb_robinson R vR b₀
  set C₂ : ℝ := 2 * Real.exp R * 2 *
    (2 ^ 2 * 2 ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2))))
  set v₂ : ℝ := 2 * vR * b₀ * Real.exp (2 * R)
  refine ⟨max C₁ C₂, max v₁ v₂, min c₁ (1 / 2), lt_max_of_lt_left hC₁,
    lt_max_of_lt_left hv₁, lt_min hc₁ one_half_pos, ?_⟩
  intro Λ h hh hhJ X a ha A hA t
  have hJ := h.normBound_nonneg hhJ X
  refine ⟨fun y B hB => ?_, fun l => ?_⟩
  · have hXY := hLR (planeDomainGraph Λ) h.interaction (ManyBody.PlaneInteraction.anchors X a)
      (ManyBody.PlaneInteraction.anchors_mem ha) hh
      (fun Y => Y.2.edist_le) (fun Y => Y.2.card_le)
      (h.sum_norm_term_containing_le hhJ hJ) X A B hA y
      (by assumption) t
    rw [ManyBody.PlaneInteraction.anchors_self] at hXY
    refine ⟨fun d hd => (hXY.1 d hd.symm.le).trans ?_, hXY.2⟩
    gcongr
    · exact le_max_left _ _
    · exact le_max_left _ _
    · exact min_le_left _ _
  · refine (h.norm_sub_regionExpectation_graphBall_le hh hhJ X ha hA l t).trans ?_
    gcongr ‖A‖ * min 2 ?_
    have hc : min c₁ (1 / 2) * (l : ℝ) ≤ (l : ℝ) / 2 := by
      have := mul_le_mul_of_nonneg_right (min_le_right c₁ (1 / 2 : ℝ)) (Nat.cast_nonneg l)
      linarith
    gcongr
    · exact le_max_right _ _
    · exact le_max_right _ _

end TNLean.PEPS.AreaLaw
