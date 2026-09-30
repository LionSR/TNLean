/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.Cluster

/-!
# Stabilizers of graph-state circuits

The controlled-Z circuit description in arXiv:2011.12127, Appendix A,
"The cluster state" (two dimensions), applies to arbitrary graphs. We index
bonds by their two endpoints, so parallel bonds retain their multiplicity.
We derive the stabilizer action and its common eigenspace from this circuit.
The stabilizer at a vertex flips its qubit and applies Z at the other endpoint
of every incident bond.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V E : Type*} [DecidableEq V] [Fintype E]

/-- The diagonal coefficient of the product of controlled-Z gates on the bonds.
Source: arXiv:2011.12127, Appendix A, two-dimensional cluster state. -/
def graphCircuitSign (a b : E → V) (s : V → Fin 2) : ℂ :=
  ∏ e, (-1 : ℂ) ^ ((s (a e)).val * (s (b e)).val)

/-- Flip one qubit in the computational basis. -/
def graphFlip (v : V) (s : V → Fin 2) : V → Fin 2 :=
  Function.update s v (s v + 1)

/-- The Z factors in the graph-state stabilizer at a vertex, one per incident bond. -/
def graphNeighborSign (a b : E → V) (v : V) (s : V → Fin 2) : ℂ :=
  ∏ e, if a e = v then (-1 : ℂ) ^ (s (b e)).val
    else if b e = v then (-1 : ℂ) ^ (s (a e)).val else 1

private lemma graphCircuitSign_flip (a b : E → V) (h : ∀ e, a e ≠ b e)
    (v : V) (s : V → Fin 2) :
    graphCircuitSign a b (graphFlip v s) =
      graphNeighborSign a b v s * graphCircuitSign a b s := by
  simp only [graphCircuitSign, graphNeighborSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases ha : a e = v <;> by_cases hb : b e = v
  all_goals simp_all only [graphFlip, Function.update_apply, ite_true, ite_false]
  · exact (h e (ha.trans hb.symm)).elim
  · generalize s v = x, s (b e) = y
    fin_cases x <;> fin_cases y <;> norm_num
  · generalize s (a e) = x, s v = y
    fin_cases x <;> fin_cases y <;> norm_num
  · simp

private lemma graphNeighborSign_sq (a b : E → V) (v : V) (s : V → Fin 2) :
    graphNeighborSign a b v s * graphNeighborSign a b v s = 1 := by
  simp only [graphNeighborSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun e _ => ?_
  split_ifs <;> simp [← mul_pow]

/-- The graph-state stabilizer X at v times Z at the opposite endpoint of each incident
bond. -/
def graphStabilizer (a b : E → V) (v : V) (ψ : (V → Fin 2) → ℂ)
    (s : V → Fin 2) : ℂ :=
  graphNeighborSign a b v s * ψ (graphFlip v s)

/-- The controlled-Z circuit state is fixed by every graph stabilizer, as follows
by comparing its coefficients before and after a single-site flip. -/
theorem graphStabilizer_graphCircuitSign (a b : E → V) (h : ∀ e, a e ≠ b e)
    (v : V) : graphStabilizer a b v (graphCircuitSign a b) = graphCircuitSign a b := by
  funext s
  simp only [graphStabilizer, graphCircuitSign_flip a b h, ← mul_assoc,
    graphNeighborSign_sq, one_mul]

private lemma eq_zeroConfig_of_flip_invariant [Finite V]
    (f : (V → Fin 2) → ℂ) (hf : ∀ v s, f (graphFlip v s) = f s)
    (s : V → Fin 2) : f s = f (fun _ => 0) := by
  haveI := Fintype.ofFinite V
  have hu (v : V) (t : V → Fin 2) (x : Fin 2) : f (Function.update t v x) = f t := by
    by_cases hx : x = t v
    · simp [hx]
    · have hx' : x = t v + 1 := by
        generalize t v = y at *
        fin_cases x <;> fin_cases y <;> norm_num at *
      simpa [hx', graphFlip] using hf v t
  have hi (u : Finset V) : ∀ t : V → Fin 2,
      (∀ v, v ∉ u → t v = 0) → f t = f (fun _ => 0) := by
    induction u using Finset.induction_on with
    | empty =>
      intro t ht
      have he : t = fun _ => 0 := funext fun v => ht v (by simp)
      rw [he]
    | @insert v u hv ih =>
      intro t ht
      rw [← hu v t 0]
      apply ih
      intro w hw
      by_cases hwv : w = v
      · simp [hwv]
      · simp [Function.update_of_ne hwv, ht w (by simp [hw, hwv])]
  exact hi Finset.univ s (by simp)

omit [DecidableEq V] in
private lemma graphCircuitSign_sq (a b : E → V) (s : V → Fin 2) :
    graphCircuitSign a b s * graphCircuitSign a b s = 1 := by
  simp [graphCircuitSign, ← Finset.prod_mul_distrib, ← mul_pow]

/-- The common positive stabilizer eigenspace consists exactly of scalar multiples of the
controlled-Z circuit state. Multiplication by the circuit sign reduces the
stabilizer equations to invariance under every single-site flip. -/
theorem graphStabilizer_fixed_iff [Finite V] (a b : E → V) (h : ∀ e, a e ≠ b e)
    (ψ : (V → Fin 2) → ℂ) :
    (∀ v, graphStabilizer a b v ψ = ψ) ↔
      ∃ c : ℂ, ψ = c • graphCircuitSign a b := by
  constructor
  · intro hψ
    have hinv : ∀ v s, graphCircuitSign a b (graphFlip v s) * ψ (graphFlip v s) =
        graphCircuitSign a b s * ψ s := by
      intro v s
      rw [graphCircuitSign_flip a b h]
      have he := congrFun (hψ v) s
      change graphNeighborSign a b v s * ψ (graphFlip v s) = ψ s at he
      calc
        _ = graphCircuitSign a b s *
            (graphNeighborSign a b v s * ψ (graphFlip v s)) := by ring
        _ = _ := by rw [he]
    refine ⟨ψ (fun _ => 0), ?_⟩
    funext s
    have he := eq_zeroConfig_of_flip_invariant
      (fun t => graphCircuitSign a b t * ψ t) hinv s
    simp only [graphCircuitSign, Fin.val_zero, zero_mul, pow_zero,
      Finset.prod_const_one, one_mul] at he
    change graphCircuitSign a b s * ψ s = ψ (fun _ => 0) at he
    change ψ s = ψ (fun _ => 0) * graphCircuitSign a b s
    calc
      ψ s = ψ s * (graphCircuitSign a b s * graphCircuitSign a b s) := by
        rw [graphCircuitSign_sq, mul_one]
      _ = (graphCircuitSign a b s * ψ s) * graphCircuitSign a b s := by ring
      _ = _ := by rw [he]
  · rintro ⟨c, rfl⟩ v
    funext s
    have he := congrFun (graphStabilizer_graphCircuitSign a b h v) s
    simp only [graphStabilizer, Pi.smul_apply, smul_eq_mul] at he ⊢
    rw [← mul_assoc, mul_comm _ c, mul_assoc, he]

private lemma graphNeighborSign_eq_prod (a b : E → V) (h : ∀ e, a e ≠ b e)
    (v : V) (s : V → Fin 2) :
    graphNeighborSign a b v s =
      (∏ e, if a e = v then (-1 : ℂ) ^ (s (b e)).val else 1) *
      ∏ e, if b e = v then (-1 : ℂ) ^ (s (a e)).val else 1 := by
  rw [graphNeighborSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hn : ¬(a e = v ∧ b e = v) := fun he => h e (he.1.trans he.2.symm)
  split_ifs <;> simp_all

section Torus

variable (width height : ℕ) [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- Target of a horizontal or vertical positively oriented torus bond. -/
def clusterBondTarget : TorusVertex width height ⊕ TorusVertex width height →
    TorusVertex width height :=
  Sum.elim (fun v => (v.1 + 1, v.2)) (fun v => (v.1, v.2 + 1))

/-- X at the indicated site and Z at each of its four neighbours. -/
def clusterStabilizer (v : TorusVertex width height)
    (ψ : (TorusVertex width height → Fin 2) → ℂ) :
    (TorusVertex width height → Fin 2) → ℂ :=
  graphStabilizer (Sum.elim id id) (clusterBondTarget width height) v ψ

omit [NeZero width] [NeZero height] in
private lemma clusterBondTarget_ne (e : TorusVertex width height ⊕
    TorusVertex width height) : Sum.elim id id e ≠ clusterBondTarget width height e := by
  rcases e with ⟨x, y⟩ | ⟨x, y⟩ <;> simp [clusterBondTarget]

/-- Coefficient formula for the four-neighbour Pauli stabilizer. -/
theorem clusterStabilizer_apply (v : TorusVertex width height)
    (ψ : (TorusVertex width height → Fin 2) → ℂ) (s : TorusVertex width height → Fin 2) :
    clusterStabilizer width height v ψ s =
      (-1 : ℂ) ^ ((s (v.1 + 1, v.2)).val + (s (v.1, v.2 + 1)).val +
        (s (v.1 - 1, v.2)).val + (s (v.1, v.2 - 1)).val) * ψ (graphFlip v s) := by
  rw [clusterStabilizer, graphStabilizer,
    graphNeighborSign_eq_prod _ _ (clusterBondTarget_ne width height)]
  simp only [Fintype.prod_sum_type]
  dsimp +instances only [clusterBondTarget, Sum.elim_inl, Sum.elim_inr, id_eq]
  have hx (u : TorusVertex width height) : (u.1 + 1, u.2) = v ↔
      u = (v.1 - 1, v.2) := by simp only [Prod.ext_iff, ← eq_sub_iff_add_eq]
  have hy (u : TorusVertex width height) : (u.1, u.2 + 1) = v ↔
      u = (v.1, v.2 - 1) := by simp only [Prod.ext_iff, ← eq_sub_iff_add_eq]
  simp [hx, hy, pow_add, mul_assoc]

/-- The normalized product of plus states after the nearest-neighbour controlled-Z gates.
Source: arXiv:2011.12127, Appendix A, two-dimensional cluster-state preparation. -/
noncomputable def clusterCircuitState : (TorusVertex width height → Fin 2) → ℂ :=
  Complex.invSqrtTwo ^ (width * height) •
    graphCircuitSign (Sum.elim id id) (clusterBondTarget width height)

variable [Fact (2 < width)] [Fact (2 < height)]

/-- Exact circuit coefficient, including the normalization of the printed virtual legs.
Source: arXiv:2011.12127, Appendix A, lines 2424–2429. -/
theorem stateCoeff_clusterPEPS_eq_smul_graphCircuitSign :
    stateCoeff (clusterPEPS width height) = (2⁻¹ : ℂ) ^ (width * height) •
      graphCircuitSign (Sum.elim id id) (clusterBondTarget width height) := by
  funext s
  simp only [stateCoeff_clusterPEPS, Pi.smul_apply, smul_eq_mul,
    graphCircuitSign, Fintype.prod_sum_type, clusterBondTarget, Sum.elim_inl,
    Sum.elim_inr, id_eq, pow_add, Finset.prod_mul_distrib]

/-- The printed PEPS is a nonzero scalar multiple of the normalized circuit state.
Source: arXiv:2011.12127, Appendix A, lines 2424–2429. -/
theorem stateCoeff_clusterPEPS_eq_smul_clusterCircuitState :
    stateCoeff (clusterPEPS width height) =
      Complex.invSqrtTwo ^ (width * height) • clusterCircuitState width height := by
  rw [stateCoeff_clusterPEPS_eq_smul_graphCircuitSign, clusterCircuitState,
    smul_smul, ← mul_pow, Complex.invSqrtTwo_mul_self]

/-- The common +1 eigenspace of the square-torus cluster stabilizers is exactly the line
spanned by the printed cluster PEPS. This follows from the graph-state
eigenspace theorem and the PEPS-to-circuit coefficient identity. -/
theorem clusterStabilizer_fixed_iff (ψ : (TorusVertex width height → Fin 2) → ℂ) :
    (∀ v, clusterStabilizer width height v ψ = ψ) ↔
      ∃ c : ℂ, ψ = c • stateCoeff (clusterPEPS width height) := by
  change (∀ v, graphStabilizer (Sum.elim id id) (clusterBondTarget width height) v ψ = ψ) ↔ _
  rw [graphStabilizer_fixed_iff _ _ (clusterBondTarget_ne width height),
    stateCoeff_clusterPEPS_eq_smul_graphCircuitSign]
  have hc : (2⁻¹ : ℂ) ^ (width * height) ≠ 0 := pow_ne_zero _ (inv_ne_zero (by norm_num))
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c / (2⁻¹ : ℂ) ^ (width * height), by rw [smul_smul, div_mul_cancel₀ _ hc]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c * (2⁻¹ : ℂ) ^ (width * height), smul_smul _ _ _⟩

/-- The printed square-torus cluster PEPS is nonzero.
Source: arXiv:2011.12127, Appendix A, two-dimensional cluster state. -/
theorem stateCoeff_clusterPEPS_ne_zero : stateCoeff (clusterPEPS width height) ≠ 0 := by
  intro hzero
  have h := congrFun hzero (fun _ => 0)
  simp [stateCoeff_clusterPEPS] at h

end Torus

end TNLean.PEPS
