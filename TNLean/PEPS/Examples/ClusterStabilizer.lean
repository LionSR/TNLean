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
## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*, Appendix A
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
  have := Fintype.ofFinite V
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

section Hamiltonian

/-- A single-site flip is an involution. -/
theorem graphFlip_graphFlip (v : V) (s : V → Fin 2) : graphFlip v (graphFlip v s) = s := by
  funext u
  by_cases hu : u = v
  · subst hu
    simp only [graphFlip, Function.update_self]
    generalize s u = x
    fin_cases x <;> rfl
  · simp [graphFlip, Function.update_of_ne hu]

/-- Flips at two sites commute. -/
theorem graphFlip_comm (v w : V) (s : V → Fin 2) :
    graphFlip v (graphFlip w s) = graphFlip w (graphFlip v s) := by
  by_cases hvw : v = w
  · rw [hvw]
  · funext u
    by_cases hu : u = v
    · subst hu
      simp [graphFlip, Function.update_apply, hvw]
    · by_cases hu' : u = w
      · subst hu'
        simp [graphFlip, Function.update_apply, Ne.symm hvw]
      · simp [graphFlip, Function.update_apply, hu, hu']

/-- A graph stabilizer is the single-site flip conjugated by the controlled-Z
circuit sign. -/
theorem graphStabilizer_apply_eq (a b : E → V) (h : ∀ e, a e ≠ b e) (v : V)
    (ψ : (V → Fin 2) → ℂ) (s : V → Fin 2) :
    graphStabilizer a b v ψ s =
      graphCircuitSign a b s * graphCircuitSign a b (graphFlip v s) * ψ (graphFlip v s) := by
  rw [graphStabilizer, graphCircuitSign_flip a b h]
  calc graphNeighborSign a b v s * ψ (graphFlip v s) =
      graphNeighborSign a b v s * (graphCircuitSign a b s * graphCircuitSign a b s) *
        ψ (graphFlip v s) := by rw [graphCircuitSign_sq, mul_one]
    _ = _ := by ring

/-- The graph stabilizers commute pairwise. Source: arXiv:2011.12127, line 1445,
"the commuting parent Hamiltonian". -/
theorem graphStabilizer_comm (a b : E → V) (h : ∀ e, a e ≠ b e) (v w : V)
    (ψ : (V → Fin 2) → ℂ) :
    graphStabilizer a b v (graphStabilizer a b w ψ) =
      graphStabilizer a b w (graphStabilizer a b v ψ) := by
  funext s
  simp only [graphStabilizer_apply_eq a b h, graphFlip_comm w v]
  have hv := graphCircuitSign_sq a b (graphFlip v s)
  have hw := graphCircuitSign_sq a b (graphFlip w s)
  calc _ = graphCircuitSign a b s *
        (graphCircuitSign a b (graphFlip v s) * graphCircuitSign a b (graphFlip v s)) *
        graphCircuitSign a b (graphFlip v (graphFlip w s)) *
        ψ (graphFlip v (graphFlip w s)) := by ring
    _ = graphCircuitSign a b s *
        (graphCircuitSign a b (graphFlip w s) * graphCircuitSign a b (graphFlip w s)) *
        graphCircuitSign a b (graphFlip v (graphFlip w s)) *
        ψ (graphFlip v (graphFlip w s)) := by rw [hv, hw]
    _ = _ := by ring

/-- A graph stabilizer squares to the identity. -/
theorem graphStabilizer_graphStabilizer (a b : E → V) (h : ∀ e, a e ≠ b e) (v : V)
    (ψ : (V → Fin 2) → ℂ) : graphStabilizer a b v (graphStabilizer a b v ψ) = ψ := by
  funext s
  simp only [graphStabilizer_apply_eq a b h, graphFlip_graphFlip]
  have hs := graphCircuitSign_sq a b s
  have hf := graphCircuitSign_sq a b (graphFlip v s)
  calc _ = (graphCircuitSign a b s * graphCircuitSign a b s) *
      (graphCircuitSign a b (graphFlip v s) * graphCircuitSign a b (graphFlip v s)) * ψ s := by
        ring
    _ = ψ s := by rw [hs, hf, one_mul, one_mul]

omit [DecidableEq V] in
private lemma star_graphCircuitSign (a b : E → V) (s : V → Fin 2) :
    star (graphCircuitSign a b s) = graphCircuitSign a b s := by
  change (starRingEnd ℂ) _ = _
  simp [graphCircuitSign, map_prod]

variable [Fintype V]

/-- A graph stabilizer is symmetric for the coefficient inner product. -/
theorem sum_star_mul_graphStabilizer (a b : E → V) (h : ∀ e, a e ≠ b e) (v : V)
    (φ ψ : (V → Fin 2) → ℂ) :
    ∑ s, star (φ s) * graphStabilizer a b v ψ s =
      ∑ s, star (graphStabilizer a b v φ s) * ψ s := by
  let f : (V → Fin 2) ≃ (V → Fin 2) :=
    ⟨graphFlip v, graphFlip v, graphFlip_graphFlip v, graphFlip_graphFlip v⟩
  rw [← f.sum_comp]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [f, Equiv.coe_fn_mk, graphStabilizer_apply_eq a b h, graphFlip_graphFlip,
    star_mul, star_graphCircuitSign]
  ring

/-- The stabilizer Hamiltonian `-∑ᵥ Kᵥ` of a graph, with `Kᵥ` the stabilizer
`X` at `v` times `Z` at its neighbours. Source: arXiv:2011.12127, line 1445,
with the sign of the printed `∑ X Z Z Z` reversed; see the honeycomb example. -/
def graphHamiltonian (a b : E → V) (ψ : (V → Fin 2) → ℂ) : (V → Fin 2) → ℂ :=
  -∑ v, graphStabilizer a b v ψ

/-- Energy identity of the stabilizer Hamiltonian: its expectation exceeds
`-|V|` by half the summed squared defects `|ψ - Kᵥ ψ|²`. -/
theorem sum_star_mul_graphHamiltonian (a b : E → V) (h : ∀ e, a e ≠ b e)
    (ψ : (V → Fin 2) → ℂ) :
    ∑ s, star (ψ s) * graphHamiltonian a b ψ s =
      -(Fintype.card V : ℂ) * ∑ s, star (ψ s) * ψ s +
        2⁻¹ * ∑ v, ∑ s, star (ψ s - graphStabilizer a b v ψ s) *
          (ψ s - graphStabilizer a b v ψ s) := by
  have hv (v : V) : ∑ s, star (ψ s - graphStabilizer a b v ψ s) *
      (ψ s - graphStabilizer a b v ψ s) =
      2 * (∑ s, star (ψ s) * ψ s - ∑ s, star (ψ s) * graphStabilizer a b v ψ s) := by
    have h1 := sum_star_mul_graphStabilizer a b h v ψ ψ
    have h2 := sum_star_mul_graphStabilizer a b h v (graphStabilizer a b v ψ) ψ
    rw [graphStabilizer_graphStabilizer a b h] at h2
    simp only [star_sub, sub_mul, mul_sub, Finset.sum_sub_distrib]
    rw [← h1, h2]
    ring
  have hsum : ∑ s, star (ψ s) * graphHamiltonian a b ψ s =
      -∑ v, ∑ s, star (ψ s) * graphStabilizer a b v ψ s := by
    simp only [graphHamiltonian, Pi.neg_apply, Finset.sum_apply, mul_neg, Finset.mul_sum,
      Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  rw [hsum, Finset.sum_congr rfl fun v _ => hv v, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [DecidableEq V] in
private lemma star_mul_self_eq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) :=
  Complex.normSq_eq_conj_mul_self.symm

private lemma re_energy (c : ℝ) (f : V → (V → Fin 2) → ℂ) (ψ : (V → Fin 2) → ℂ) :
    (-(c : ℂ) * ∑ s, star (ψ s) * ψ s + 2⁻¹ * ∑ v, ∑ s, star (f v s) * f v s).re =
      -c * ∑ s, Complex.normSq (ψ s) + 2⁻¹ * ∑ v, ∑ s, Complex.normSq (f v s) := by
  simp only [star_mul_self_eq, ← Complex.ofReal_sum, ← Complex.ofReal_neg, ← Complex.ofReal_mul]
  norm_num [Complex.add_re, Complex.mul_re]

/-- The stabilizer Hamiltonian is bounded below by `-|V|`. -/
theorem neg_card_mul_le_re_sum_star_mul_graphHamiltonian (a b : E → V)
    (h : ∀ e, a e ≠ b e) (ψ : (V → Fin 2) → ℂ) :
    -(Fintype.card V : ℝ) * ∑ s, Complex.normSq (ψ s) ≤
      (∑ s, star (ψ s) * graphHamiltonian a b ψ s).re := by
  rw [sum_star_mul_graphHamiltonian a b h, ← Complex.ofReal_natCast, re_energy]
  have : 0 ≤ (2 : ℝ)⁻¹ * ∑ v, ∑ s, Complex.normSq (ψ s - graphStabilizer a b v ψ s) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  linarith

/-- The eigenvalue `-|V|` of the stabilizer Hamiltonian is attained exactly on
the common fixed space of the stabilizers. -/
theorem graphHamiltonian_eq_neg_card_smul_iff (a b : E → V) (h : ∀ e, a e ≠ b e)
    (ψ : (V → Fin 2) → ℂ) :
    graphHamiltonian a b ψ = -(Fintype.card V : ℂ) • ψ ↔ ∀ v, graphStabilizer a b v ψ = ψ := by
  constructor
  · intro hψ v
    have he := sum_star_mul_graphHamiltonian a b h ψ
    rw [hψ] at he
    have he' : ∑ v, ∑ s, star (ψ s - graphStabilizer a b v ψ s) *
        (ψ s - graphStabilizer a b v ψ s) = 0 := by
      simp only [Pi.smul_apply, smul_eq_mul] at he
      have : ∑ s, star (ψ s) * (-(Fintype.card V : ℂ) * ψ s) =
          -(Fintype.card V : ℂ) * ∑ s, star (ψ s) * ψ s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this] at he
      have h2 : (2⁻¹ : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp (left_eq_add.mp he)).resolve_left h2
    simp only [star_mul_self_eq, ← Complex.ofReal_sum, Complex.ofReal_eq_zero] at he'
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)).1 he' v (Finset.mem_univ _)
    funext s
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).1
      hzero s (Finset.mem_univ _)
    rw [Complex.normSq_eq_zero, sub_eq_zero] at this
    exact this.symm
  · intro hψ
    funext s
    simp [graphHamiltonian, hψ, Finset.sum_const, Finset.card_univ]

end Hamiltonian

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

/-- The printed square-torus cluster PEPS is nonzero. This is derived here from its explicit
coefficient formula, whose all-zero coefficient is `2^(-N)`; the cited passage does not state
nonvanishing. -/
theorem stateCoeff_clusterPEPS_ne_zero : stateCoeff (clusterPEPS width height) ≠ 0 := by
  intro hzero
  have h := congrFun hzero (fun _ => 0)
  simp [stateCoeff_clusterPEPS] at h

end Torus

end TNLean.PEPS
