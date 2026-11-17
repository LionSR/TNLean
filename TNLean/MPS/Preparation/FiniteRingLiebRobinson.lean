/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Dynamics.GraphPropagation
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import TNLean.Circuit.SiteEmbedding
import TNLean.Circuit.SupportedMatrixElements
import QICLean.Entropy.RegionUnion
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Preparation.CyclicOperatorSupport
import TNLean.MPS.Preparation.EmbedLocalOperatorNorm
import TNLean.MPS.Symmetry.GappedInteractionPath
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Ring
import TNLean.Circuit.LocalCircuit
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lieb–Robinson estimate on finite periodic chains

For Hermitian nearest-neighbor terms of operator norm at most one, the
commutator of observables supported on disjoint sets satisfies an exponential
propagation estimate. The velocity is at most `8 exp a` for any nonnegative
spatial weight `a`. All constants are independent of the chain length and the
local Hilbert-space dimension. Distinct oriented bonds are counted separately,
including on a two-site ring. The ground energy is unrestricted.

This is the finite-periodic nearest-neighbor specialization of Hastings–Koma,
arXiv:math-ph/0507008, Appendix A, Theorem A.2: it is the cycle-graph case of
the graph estimate `ManyBody.norm_heisenberg_commutator_le_graphDistance_of_disjoint`,
whose site budget `∑_{j ∋ x} |T_j| ‖h_j‖ e^{a diam T_j}` is at most `4 e^a` here
(two bonds of at most two sites meet each site, each of diameter one). The ring
support distance is at most the cycle-graph distance between the supports. No
spectral-gap or frustration-free hypothesis is used. Exponential clustering is a
separate step.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Set NormedSpace


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

namespace MPSPreparation

open QuantumCircuit

open Fin.CommRing

variable {N : ℕ} [NeZero N]

private def reaches (X Y : Set (Fin N)) (r : ℕ) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, ∃ m : ℤ, |m| ≤ r ∧ y = x + (m : Fin N)

private theorem exists_reaches (X Y : Set (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∃ r, reaches X Y r := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  refine ⟨(y - x).val, x, hx, y, hy, (y - x).val, by simp, ?_⟩
  simp only [Int.cast_natCast, Fin.cast_val_eq_self]
  ring

open Classical in
/-- Shortest-path separation of two nonempty supports on the periodic chain,
expressed through integer displacements modulo the ring length. -/
noncomputable def ringSupportDistance (X Y : Set (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) : ℕ :=
  Nat.find (exists_reaches X Y hX hY)

private theorem reaches_ringSupportDistance (X Y : Set (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    reaches X Y (ringSupportDistance X Y hX hY) := by
  classical
  exact Nat.find_spec (exists_reaches X Y hX hY)

/-- The displacement-based separation predicate agrees with the strict
shortest-path distance inequality. -/
theorem isSeparatedBy_iff_lt_ringSupportDistance
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty) (r : ℕ) :
    IsSeparatedBy X Y r ↔ r < ringSupportDistance X Y hX hY := by
  classical
  constructor
  · intro h
    by_contra hlt
    have hle := Nat.le_of_not_gt hlt
    obtain ⟨x, hx, y, hy, m, hm, heq⟩ := reaches_ringSupportDistance X Y hX hY
    exact h x hx y hy m (hm.trans (by exact_mod_cast hle)) heq
  · intro hr x hx y hy m hm heq
    have hReach : reaches X Y r := ⟨x, hx, y, hy, m, hm, heq⟩
    have hle : ringSupportDistance X Y hX hY ≤ r :=
      Nat.find_min' (exists_reaches X Y hX hY) hReach
    exact (Nat.not_lt_of_ge hle) hr


/-- Each step of a walk in the cycle graph moves by one site, so the endpoint of a
walk is reached from its start by an integer displacement of absolute value at most
the walk length. -/
private theorem exists_int_eq_add_of_walk {x y : Fin N}
    (p : (SimpleGraph.cycleGraph N).Walk x y) :
    ∃ m : ℤ, |m| ≤ p.length ∧ y = x + (m : Fin N) := by
  induction p with
  | nil => exact ⟨0, by simp, by simp⟩
  | @cons u z w hadj q ih =>
    obtain ⟨m, hm, rfl⟩ := ih
    have hstep : z = u + ((1 : ℤ) : Fin N) ∨ z = u + ((-1 : ℤ) : Fin N) := by
      rcases SimpleGraph.cycleGraph_adj'.mp hadj with h | h
      · right
        have : u - z = 1 := by rw [← Fin.cast_val_eq_self (u - z), h, Nat.cast_one]
        push_cast
        linear_combination (-1 : Fin N) * this
      · left
        have : z - u = 1 := by rw [← Fin.cast_val_eq_self (z - u), h, Nat.cast_one]
        push_cast
        linear_combination this
    rcases hstep with rfl | rfl
    · refine ⟨1 + m, ?_, by push_cast; ring⟩
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith [abs_add_le (1 : ℤ) m, abs_one (α := ℤ)]
    · refine ⟨-1 + m, ?_, by push_cast; ring⟩
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith [abs_add_le (-1 : ℤ) m, abs_neg (1 : ℤ), abs_one (α := ℤ)]

/-- The ring support distance is at most the cycle-graph distance between any two
sites of the supports. -/
theorem ringSupportDistance_le_edist (X Y : Set (Fin N))
    (hX : X.Nonempty) (hY : Y.Nonempty) {x y : Fin N} (hx : x ∈ X) (hy : y ∈ Y) :
    (ringSupportDistance X Y hX hY : ℕ∞) ≤ (SimpleGraph.cycleGraph N).edist x y := by
  classical
  by_cases htop : (SimpleGraph.cycleGraph N).edist x y = ⊤
  · simp [htop]
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
  obtain ⟨m, hm, heq⟩ := exists_int_eq_add_of_walk p
  rw [← hp]
  exact_mod_cast Nat.find_min' (exists_reaches X Y hX hY) ⟨x, hx, y, hy, m, hm, heq⟩

end MPSPreparation

namespace MPSPreparation

open QuantumCircuit
open Fin.CommRing
open scoped Matrix.Norms.L2Operator

/-- A bond `{j, j + 1}` has cycle-graph diameter at most one. -/
private theorem edist_le_one_of_mem_bond {N : ℕ} [NeZero N] (j : Fin N) :
    ∀ x ∈ ({j, j + 1} : Finset (Fin N)), ∀ z ∈ ({j, j + 1} : Finset (Fin N)),
      (SimpleGraph.cycleGraph N).edist x z ≤ ((1 : ℕ) : ℕ∞) := by
  have hj : (SimpleGraph.cycleGraph N).edist j (j + 1) ≤ 1 := by
    by_cases hjj : j = j + 1
    · rw [← hjj, SimpleGraph.edist_self]
      exact zero_le_one
    · refine (SimpleGraph.edist_eq_one_iff_adj.mpr ?_).le
      refine SimpleGraph.cycleGraph_adj'.mpr (Or.inr ?_)
      have hN : 1 < N := by
        by_contra hN
        exact hjj (Subsingleton.elim (h := Fin.subsingleton_iff_le_one.mpr (by omega)) _ _)
      simp [Nat.mod_eq_of_lt hN]
  intro x hx z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hz
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
  · simp
  · simpa using hj
  · simpa [SimpleGraph.edist_comm] using hj
  · simp

/-- Hastings–Koma's site budget on the ring: at most two bonds of at most two sites meet a
site, each of norm at most one, and every bond has diameter one. -/
private theorem sum_bond_budget_le {N : ℕ} [NeZero N] (k : Fin N → ℝ) (hk0 : ∀ j, 0 ≤ k j)
    (hk : ∀ j, k j ≤ 1) (a : ℝ) (x : Fin N) :
    ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ ({j, j + 1} : Finset (Fin N))),
        (({j, j + 1} : Finset (Fin N)).card : ℝ) * k j * Real.exp (a * ((1 : ℕ) : ℝ)) ≤
      4 * Real.exp a := by
  classical
  have hsub : Finset.univ.filter (fun j ↦ x ∈ ({j, j + 1} : Finset (Fin N))) ⊆ {x, x - 1} := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hj ⊢
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by ring)
  have hterm : ∀ j, (({j, j + 1} : Finset (Fin N)).card : ℝ) * k j *
      Real.exp (a * ((1 : ℕ) : ℝ)) ≤ 2 * Real.exp a := by
    intro j
    have hcard : (({j, j + 1} : Finset (Fin N)).card : ℝ) ≤ 2 := by
      exact_mod_cast Finset.card_le_two
    simp only [Nat.cast_one, mul_one]
    have := mul_le_mul hcard (hk j) (hk0 j) (by norm_num)
    nlinarith [Real.exp_pos a]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ ({j, j + 1} : Finset (Fin N))),
          2 * Real.exp a := Finset.sum_le_sum fun j _ ↦ hterm j
    _ = (Finset.univ.filter (fun j ↦ x ∈ ({j, j + 1} : Finset (Fin N)))).card *
          (2 * Real.exp a) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) * (2 * Real.exp a) := by
      gcongr
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_le_two
    _ = 4 * Real.exp a := by ring

/-- A local observable satisfies the same propagation estimate, with its
operator norm multiplying the restricted commutator norm. -/
theorem norm_heisenberg_commutator_le_exp_abs_of_disjoint
    {d N : ℕ} [NeZero N]
    (h : Fin N → Matrix (MPSTensor.Cfg d N) (MPSTensor.Cfg d N) ℂ)
    (hHerm : ∀ j, (h j).IsHermitian)
    (hSupport : ∀ j, h j ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (ringBond j))
    (hNorm : ∀ j, ‖h j‖ ≤ 1)
    (A B : Matrix (MPSTensor.Cfg d N) (MPSTensor.Cfg d N) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X) (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ‖(exp (t • (Complex.I • ∑ j, h j)) * A *
        exp ((-t) • (Complex.I • ∑ j, h j))) * B -
      B * (exp (t • (Complex.I • ∑ j, h j)) * A *
        exp ((-t) • (Complex.I • ∑ j, h j)))‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * |t|) - 1) := by
  classical
  let Φ : ManyBody.Interaction (fun _ : Fin N ↦ Fin d) (fun j : Fin N ↦ ({j, j + 1} : Finset _)) :=
    ⟨h, fun j ↦ (by simpa only [Finset.coe_pair, ringBond] using hSupport j)⟩
  have hBound := ManyBody.norm_heisenberg_commutator_le_graphDistance_of_disjoint
    (SimpleGraph.cycleGraph N) Φ hHerm (fun _ ↦ 1) (fun j ↦ edist_le_one_of_mem_bond j)
    a ha (4 * Real.exp a)
    (sum_bond_budget_le (fun j ↦ ‖h j‖) (fun j ↦ norm_nonneg _) hNorm a) X
    hA Y hB
    (Finset.disjoint_coe.mp hXY) (ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)
    (fun x hx y hy ↦ ringSupportDistance_le_edist _ _ hX hY hx hy) t
  refine hBound.trans_eq ?_
  rw [show 2 * (4 * Real.exp a) = 8 * Real.exp a by ring]
  ring_nf

end MPSPreparation

namespace MPSTensor
open MPSPreparation NormedSpace QuantumCircuit
open scoped Matrix.Norms.L2Operator

/-- A bounded Hermitian two-site interaction satisfies the finite-ring
Lieb–Robinson estimate after cyclic embedding. The estimate is uniform in
the ring length and local Hilbert-space dimension, and allows arbitrary ground
energy. Source context: Hastings–Koma, arXiv:math-ph/0507008, Appendix A. -/
theorem norm_interactionHamiltonian_commutator_le_exp_abs_of_disjoint
    {d N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (h : MPOTensor.ChainOperator d 2) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : MPOTensor.ChainOperator d N)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X) (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ‖(exp (t • (Complex.I • interactionHamiltonian h hN)) * A *
        exp ((-t) • (Complex.I • interactionHamiltonian h hN))) * B -
      B * (exp (t • (Complex.I • interactionHamiltonian h hN)) * A *
        exp ((-t) • (Complex.I • interactionHamiltonian h hN)))‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * |t|) - 1) := by
  apply norm_heisenberg_commutator_le_exp_abs_of_disjoint
    (fun j => MPOTensor.embedLocalOperator 2 N hN j h)
    (fun j => MPOTensor.embedLocalOperator_isHermitian 2 N hN j hHerm)
    (fun j => embedLocalOperator_twoSite_mem_supportedOperators hN j h)
    (fun j => (MPOTensor.norm_embedLocalOperator_le 2 N hN j h).trans hNorm)
    A B X Y hX hY hA hB hXY a ha t

end MPSTensor
