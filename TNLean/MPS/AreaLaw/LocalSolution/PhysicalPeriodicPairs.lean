/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.PeriodicCoarsening
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.GaussianFilterTruncation
import QICLean.ManyBody.Hamiltonian.Translation
import QICLean.Algebra.ZModDisplacement
import QICLean.ManyBody.Sites.GraphBall
import TNLean.Algebra.MatrixHermitianSum

/-!
# Periodic neighbouring-block operators from local Gaussian filters

The periodic grouping of Hastings, arXiv:cond-mat/0508554v3, lines 609–639,
is applied to the actual truncated Gaussian filters of lines 285–320.
The local terms, rather than approximating operators or residual estimates,
are the input.
-/

open Matrix QuantumCircuit ManyBody
open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexOrder MatrixOrder

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw.LocalSolution

/-- The nearest-neighbour physical ring on the blocked coordinates.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628. -/
def periodicPhysicalGraph (N ℓ : ℕ) : SimpleGraph (Fin N × Fin (2 * ℓ)) :=
  (SimpleGraph.cycleGraph (N * (2 * ℓ))).comap finProdFinEquiv

private theorem periodicPhysicalCoordinate_eq {N ℓ : ℕ} (i : Fin N × Fin (2 * ℓ)) :
    (finProdFinEquiv i : ℕ) = periodicPhysicalCoordinate i := by
  change i.2.val + (2 * ℓ) * i.1.val = i.1.val * (2 * ℓ) + i.2.val
  ring

private theorem cyclic_natAbs_eq {n : ℕ} [NeZero n] (x y : Fin n) :
    (((y : ℕ) : ZMod n) - ((x : ℕ) : ZMod n)).valMinAbs.natAbs =
      min (Nat.dist x.val y.val) (n - Nat.dist x.val y.val) := by
  wlog h : x.val ≤ y.val generalizing x y
  · rw [← neg_sub, ZMod.natAbs_valMinAbs_neg, this y x (by omega), Nat.dist_comm]
  have hv : (((y : ℕ) : ZMod n) - ((x : ℕ) : ZMod n)).val = y.val - x.val := by
    rw [← Nat.cast_sub h, ZMod.val_natCast, Nat.mod_eq_of_lt]
    omega
  rw [ZMod.valMinAbs_natAbs_eq_min, hv, Nat.dist_eq_sub_of_le h]

private theorem ring_step_le_one {n : ℕ} [NeZero n] (x y : Fin n)
    (h : (SimpleGraph.cycleGraph n).Adj x y) :
    (((y : ℕ) : ZMod n) - ((x : ℕ) : ZMod n)).valMinAbs.natAbs ≤ 1 := by
  have hcast (u v : Fin n) :
      (((v - u : Fin n) : ℕ) : ZMod n) = ((v : ℕ) : ZMod n) - ((u : ℕ) : ZMod n) := by
    rw [Fin.val_sub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub u.isLt.le,
      ZMod.natCast_self]
    ring
  have hone : (1 : ZMod n).valMinAbs.natAbs ≤ 1 := by
    rw [ZMod.valMinAbs_natAbs_eq_min]
    exact (min_le_left _ _).trans (by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le 1 n)
  rcases SimpleGraph.cycleGraph_adj'.mp h with h | h
  · rw [← neg_sub, ZMod.natAbs_valMinAbs_neg, ← hcast, h, Nat.cast_one]
    exact hone
  · rw [← hcast, h, Nat.cast_one]
    exact hone

/-- Graph distance dominates the actual cyclic physical distance.
Hastings, arXiv:cond-mat/0508554v3, lines 609–628. -/
theorem periodicPhysicalDistance_le_edist {N ℓ : ℕ} (hN : 0 < N) (hℓ : 0 < ℓ)
    (i v : Fin N × Fin (2 * ℓ)) :
    (periodicPhysicalDistance i v : ℕ∞) ≤ (periodicPhysicalGraph N ℓ).edist i v := by
  let : NeZero (N * (2 * ℓ)) := ⟨by positivity⟩
  have hb := SimpleGraph.natAbs_valMinAbs_sub_le_edist
    (Γ := periodicPhysicalGraph N ℓ) (R := 1) (by omega)
    (fun i ↦ ((finProdFinEquiv i : ℕ) : ZMod (N * (2 * ℓ))))
    (fun u v h ↦ ring_step_le_one _ _ h) i v
  rw [cyclic_natAbs_eq (finProdFinEquiv i) (finProdFinEquiv v)] at hb
  simpa only [periodicPhysicalCoordinate_eq, periodicPhysicalDistance,
    Nat.cast_one, one_mul] using hb

section Truncation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem radius_support_diameter (G : SimpleGraph ι) (R : ℕ)
    (i : ι) {x y : ι} (hx : x ∈ ManyBody.graphBall G i R) (hy : y ∈ ManyBody.graphBall G i R) :
    G.edist x y ≤ (2 * R : ℕ) := by
  have hx' : G.edist x i ≤ (R : ℕ∞) := by
    simpa only [SimpleGraph.edist_comm] using ManyBody.mem_graphBall.mp hx
  calc G.edist x y ≤ G.edist x i + G.edist i y := G.edist_triangle
    _ ≤ (R : ℕ∞) + R := add_le_add hx' (ManyBody.mem_graphBall.mp hy)
    _ = (2 * R : ℕ) := by push_cast; ring

omit [DecidableEq ι] in
private theorem truncated_centres_supported (G : SimpleGraph ι) {R ℓ : ℕ}
    (hR : R ≤ ℓ) (i k : ι) (hk : k ∈ ManyBody.graphBall G i (ℓ - R)) :
    ManyBody.graphBall G k R ⊆ ManyBody.graphBall G i ℓ := by
  intro x hx
  apply ManyBody.mem_graphBall.mpr
  calc G.edist i x ≤ G.edist i k + G.edist k x := G.edist_triangle
    _ ≤ ((ℓ - R : ℕ) : ℕ∞) + R := add_le_add (ManyBody.mem_graphBall.mp hk)
        (ManyBody.mem_graphBall.mp hx)
    _ = (ℓ : ℕ∞) := by rw [← Nat.cast_add, Nat.sub_add_cancel hR]

omit [DecidableEq ι] in
private theorem omitted_centres_separated (G : SimpleGraph ι) {R ℓ m : ℕ}
    (hm : m + 3 * R ≤ ℓ) (i k : ι) (hk : k ∉ ManyBody.graphBall G i (ℓ - R))
    {x y : ι} (hx : x ∈ ManyBody.graphBall G i R) (hy : y ∈ ManyBody.graphBall G k R) :
    (m : ℕ∞) ≤ G.edist x y := by
  by_contra h
  have hxy : G.edist x y ≤ (m : ℕ∞) := (lt_of_not_ge h).le
  have hy' : G.edist y k ≤ (R : ℕ∞) := by
    simpa only [SimpleGraph.edist_comm] using ManyBody.mem_graphBall.mp hy
  apply hk
  apply ManyBody.mem_graphBall.mpr
  calc G.edist i k ≤ G.edist i x + G.edist x y + G.edist y k :=
      (G.edist_triangle (u := i) (v := y) (w := k)).trans
        (add_le_add (G.edist_triangle (u := i) (v := x) (w := y)) le_rfl)
    _ ≤ (R : ℕ∞) + m + R := add_le_add (add_le_add (ManyBody.mem_graphBall.mp hx) hxy) hy'
    _ ≤ ((ℓ - R : ℕ) : ℕ∞) := by exact_mod_cast (by omega : R + m + R ≤ ℓ - R)

private theorem radius_interaction_budget (G : SimpleGraph ι) {d R S : ℕ}
    (h : ι → Matrix (ι → Fin d) (ι → Fin d) ℂ) {J : ℝ}
    (hJ0 : 0 ≤ J) (hJ : ∀ i, ‖h i‖ ≤ J)
    (hS : ∀ i, (ManyBody.graphBall G i R).card ≤ S) (x : ι) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ x ∈ ManyBody.graphBall G i R), ‖h i‖ ≤ S * J := by
  have he : Finset.univ.filter (fun i ↦ x ∈ ManyBody.graphBall G i R) = ManyBody.graphBall G x R :=
      by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ManyBody.mem_graphBall,
      SimpleGraph.edist_comm]
  rw [he]
  calc ∑ i ∈ ManyBody.graphBall G x R, ‖h i‖ ≤ ∑ _i ∈ ManyBody.graphBall G x R, J :=
      Finset.sum_le_sum fun i _ ↦ hJ i
    _ = (ManyBody.graphBall G x R).card * J := by simp
    _ ≤ S * J := mul_le_mul_of_nonneg_right (by exact_mod_cast hS x) hJ0

end Truncation

/-- The actual local Gaussian filter uses the Hamiltonian terms with centres
within distance `ℓ - R`. Hastings, arXiv:cond-mat/0508554v3, eqs. `mid`,
`odef`, `hpdef`, lines 285–307. -/
noncomputable def periodicLocalFilter {N ℓ d : ℕ} (R : ℕ) (θ Δ : ℝ)
    (h : (Fin N × Fin (2 * ℓ)) → Matrix ((Fin N × Fin (2 * ℓ)) → Fin d)
      ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ) (i : Fin N × Fin (2 * ℓ)) :=
  ManyBody.gaussianFilteredTerm θ Δ
    (∑ k ∈ ManyBody.graphBall (periodicPhysicalGraph N ℓ) i (ℓ - R), h k) (h i)

/-- The neighbouring-supersite family constructed from the original local terms.
Hastings, arXiv:cond-mat/0508554v3, lines 609–639. -/
noncomputable def periodicFilteredPair {N ℓ d : ℕ} (R : ℕ) (θ Δ : ℝ)
    (h : (Fin N × Fin (2 * ℓ)) → Matrix ((Fin N × Fin (2 * ℓ)) → Fin d)
      ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ) :=
  periodicCoarseOperator (periodicLocalFilter R θ Δ h)

/-- The largest actual omitted shell of the local truncations. The count is
constructed from the interaction radius and the physical ring, rather than
supplied as approximation data. Hastings, arXiv:cond-mat/0508554v3, lines 309–320. -/
noncomputable def periodicTruncationShell (N ℓ R : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup fun i : Fin N × Fin (2 * ℓ) ↦
    ((ManyBody.graphBall (periodicPhysicalGraph N ℓ) i (ℓ - R))ᶜ.filter fun k ↦
      ¬Disjoint (ManyBody.graphBall (periodicPhysicalGraph N ℓ) k R)
        (ManyBody.graphBall (periodicPhysicalGraph N ℓ) i ℓ)).card

/-- The explicit uniform local-filter error, with the actual omitted-shell count.
The interaction-ball count `S` is the finite-range hypothesis of Hastings,
arXiv:cond-mat/0508554v3, lines 180–185; the error is eq. `apb`, lines 309–320,
with the time-window comparison of `GaussianFilteredTruncationGround`. -/
noncomputable def periodicFilterError (N ℓ R S m : ℕ) (J θ Δ μ : ℝ) : ℝ :=
  2 * S * (2 + 4 * |(S : ℝ) * J| * Real.exp (2 * μ * (2 * R))) * S * J * J *
    periodicTruncationShell N ℓ R * (θ / Δ) *
    Real.exp ((2 * S * |(S : ℝ) * J| * Real.exp (2 * μ * (2 * R)) + 1) * (θ / Δ) - μ * m) +
      2 * J * Real.exp (-θ / 2)

private theorem periodic_local_filter_data {N ℓ d R S m : ℕ} [NeZero d]
    (hm : m + 3 * R ≤ ℓ) (θ Δ μ J : ℝ) (hθ : 0 ≤ θ) (hΔ : 0 < Δ)
    (hμ : 0 ≤ μ) (hJ0 : 0 ≤ J)
    (h : (Fin N × Fin (2 * ℓ)) → Matrix ((Fin N × Fin (2 * ℓ)) → Fin d)
      ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    (hherm : ∀ i, (h i).IsHermitian)
    (hsupp : ∀ i, h i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (ManyBody.graphBall (periodicPhysicalGraph N ℓ) i R : Finset (Fin N × Fin (2 * ℓ))))
    (hJ : ∀ i, ‖h i‖ ≤ J)
    (hS : ∀ i, (ManyBody.graphBall (periodicPhysicalGraph N ℓ) i R).card ≤ S)
    (i : Fin N × Fin (2 * ℓ)) :
    periodicLocalFilter R θ Δ h i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (ManyBody.graphBall (periodicPhysicalGraph N ℓ) i ℓ : Finset (Fin N × Fin (2 * ℓ))) ∧
    ‖periodicLocalFilter R θ Δ h i‖ ≤ J ∧
    (periodicLocalFilter R θ Δ h i).IsHermitian ∧
    ‖ManyBody.gaussianFilteredTerm θ Δ (∑ k, h k) (h i) - periodicLocalFilter R θ Δ h i‖ ≤
      periodicFilterError N ℓ R S m J θ Δ μ := by
  let G := periodicPhysicalGraph N ℓ
  let X := fun i ↦ ManyBody.graphBall G i R
  have hR : R ≤ ℓ := by omega
  have hdiam : ∀ i, ∀ x ∈ X i, ∀ y ∈ X i, G.edist x y ≤ (2 * R : ℕ) :=
    fun i _ hx _ hy ↦ radius_support_diameter G R i hx hy
  have hbudget := radius_interaction_budget G h hJ0 hJ hS
  have hsK := truncated_centres_supported G hR i
  have hXi : X i ⊆ ManyBody.graphBall G i ℓ := by
    intro x hx
    apply ManyBody.mem_graphBall.mpr
    exact (ManyBody.mem_graphBall.mp hx).trans (by exact_mod_cast hR)
  have hsep : ∀ k ∉ ManyBody.graphBall G i (ℓ - R),
      ¬Disjoint (X k) (ManyBody.graphBall G i ℓ) → ∀ x ∈ X i, ∀ y ∈ X k,
        (m : ℕ∞) ≤ G.edist x y :=
    fun k hk _ _ hx _ hy ↦ omitted_centres_separated G hm i k hk hx hy
  have hdata := ManyBody.truncated_approx_gaussianFilteredTerm G
    (⟨h, hsupp⟩ : ManyBody.Interaction (fun _ ↦ Fin d) X) hherm
    (2 * R) hdiam S hS (S * J) hbudget (ΔE := Δ) hθ
    (ManyBody.graphBall G i (ℓ - R)) (ManyBody.graphBall G i ℓ) hsK (X i) hXi (hsupp i) J hJ μ hμ m
        hsep
    (τ := θ / Δ) (div_nonneg hθ hΔ.le)
  rw [ManyBody.exp_neg_sq_div_eq_of_time_eq hΔ.ne'] at hdata
  refine ⟨hdata.1, hdata.2.1.trans (hJ i), hdata.2.2.1 (hherm i), hdata.2.2.2.trans ?_⟩
  have hcount : ((ManyBody.graphBall G i (ℓ - R))ᶜ.filter
      (fun k ↦ ¬Disjoint (X k) (ManyBody.graphBall G i ℓ))).card ≤ periodicTruncationShell N ℓ R :=
          by
    classical
    exact Finset.le_sup (f := fun i : Fin N × Fin (2 * ℓ) ↦
      ((ManyBody.graphBall G i (ℓ - R))ᶜ.filter fun k ↦
        ¬Disjoint (X k) (ManyBody.graphBall G i ℓ)).card) (Finset.mem_univ i)
  unfold periodicFilterError
  push_cast
  gcongr
  · exact_mod_cast hS i
  · exact hJ i
  · exact hJ i

private theorem norm_error_gap_transfer {α : Type*} [Fintype α] [DecidableEq α]
    {H M : Matrix α α ℂ} (hH : H.IsHermitian) (hM : M.IsHermitian)
    {E₀ Δ ε : ℝ} {Ω : EuclideanSpace ℂ α}
    (hgap : (H - (E₀ : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (herr : ‖M - H‖ ≤ ε) :
    (M - ((E₀ - ε : ℝ) : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
  have hlo : -((‖M - H‖ : ℝ) • (1 : Matrix α α ℂ)) ≤ M - H := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (hM.sub hH).isSelfAdjoint.neg_algebraMap_norm_le_self
  have hnorm : (M - H + ((‖M - H‖ : ℝ) : ℂ) • 1).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    simpa only [Complex.coe_smul] using (neg_le_iff_add_nonneg.mp hlo)
  have hscalar : (((ε - ‖M - H‖ : ℝ) : ℂ) • (1 : Matrix α α ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr herr)
  convert (hgap.add hnorm).add hscalar using 1
  push_cast
  module

/-- Construct the periodic pair family from the original finite-range Hamiltonian.
The pair at edge `j` acts only on blocks `j - 1` and `j`, including the closing
edge. Its residual follows from the actual local filters; the total error
also transfers the original ground-projector lower bound to the pair sum.

**Scope restriction (unique ground vector and regular blocking):** this
auxiliary treats a nonempty physical ring partitioned into blocks of exactly
`2ℓ` sites and a unique gapped ground vector. It does not construct the
basis of a degenerate ground space, the subsequent hierarchy, or a tensor
representation of its final space. Hastings, arXiv:cond-mat/0508554v3,
lines 285–387 and 609–639; see
`docs/paper-gaps/hastings05_physical_periodic_pairs.tex`. -/
theorem periodicFilteredPair_properties {N ℓ d R S m : ℕ} [NeZero d]
    (hN : 0 < N) (hℓ : 0 < ℓ) (hm : m + 3 * R ≤ ℓ)
    (θ Δ μ J : ℝ) (hθ : 0 ≤ θ) (hΔ : 0 < Δ) (hμ : 0 ≤ μ)
    (h : (Fin N × Fin (2 * ℓ)) → Matrix ((Fin N × Fin (2 * ℓ)) → Fin d)
      ((Fin N × Fin (2 * ℓ)) → Fin d) ℂ)
    (hherm : ∀ i, (h i).IsHermitian)
    (hsupp : ∀ i, h i ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (ManyBody.graphBall (periodicPhysicalGraph N ℓ) i R : Finset (Fin N × Fin (2 * ℓ))))
    (hJ : ∀ i, ‖h i‖ ≤ J)
    (hS : ∀ i, (ManyBody.graphBall (periodicPhysicalGraph N ℓ) i R).card ≤ S)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ ((Fin N × Fin (2 * ℓ)) → Fin d)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped (∑ i, h i) E₀ Δ)
    (hspan : groundSpace (∑ i, h i) E₀ = Submodule.span ℂ {Ω}) :
    let M := periodicFilteredPair R θ Δ h
    let ε := periodicFilterError N ℓ R S m J θ Δ μ
    (∀ j, (M j).IsHermitian ∧
      M j ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (Finset.univ.filter fun v ↦ v.1 = j ∨
          finRotate N v.1 = j) ∧
      ‖M j‖ ≤ (2 * ℓ : ℕ) * J ∧
      ‖M j - ((⟪Ω, toEuclideanLin (M j) Ω⟫_ℂ).re : ℂ) • 1‖ ≤ 4 * (ℓ : ℝ) * J ∧
      ‖toEuclideanLin (M j - ((⟪Ω, toEuclideanLin (M j) Ω⟫_ℂ).re : ℂ) • 1) Ω‖ ≤
        (2 * ℓ : ℕ) * (J * Real.exp (-θ / 2) + ε)) ∧
    ‖∑ j, M j - ∑ i, h i‖ ≤ (N * (2 * ℓ) : ℕ) * ε ∧
    (∑ j, M j - ((E₀ - (N * (2 * ℓ) : ℕ) * ε : ℝ) : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
  intro M ε
  let a := periodicLocalFilter R θ Δ h
  have hJ0 : 0 ≤ J := (norm_nonneg (h (⟨0, hN⟩, ⟨0, by omega⟩))).trans (hJ _)
  have hd := periodic_local_filter_data hm θ Δ μ J hθ hΔ hμ hJ0 h hherm hsupp hJ hS
  have hε : 0 ≤ ε := by dsimp [ε, periodicFilterError]; positivity
  have haH : ∀ i, (a i).IsHermitian := fun i ↦ (hd i).2.2.1
  have haJ : ∀ i, ‖a i‖ ≤ J := fun i ↦ (hd i).2.1
  have hares : ∀ i, ‖toEuclideanLin
      (a i - ((⟪Ω, toEuclideanLin (a i) Ω⟫_ℂ).re : ℂ) • 1) Ω‖ ≤
        J * Real.exp (-θ / 2) + ε := by
    intro i
    have hb := ManyBody.norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm hθ hΔ
      (Matrix.isHermitian_sum _ fun i _ ↦ hherm i) hΩ hgap hspan (h i) (a i)
    have hreal : ((⟪Ω, toEuclideanLin (a i) Ω⟫_ℂ).re : ℂ) =
        ⟪Ω, toEuclideanLin (a i) Ω⟫_ℂ :=
      (isSymmetric_toEuclideanLin_iff.mpr (haH i)).coe_re_inner_self_apply Ω
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      toLpLin_one, LinearMap.id_apply, hreal]
    exact hb.trans (add_le_add
      (mul_le_mul_of_nonneg_right (hJ i) (Real.exp_pos _).le) ((hd i).2.2.2))
  have hMherm : ∀ j, (M j).IsHermitian := isHermitian_periodicCoarseOperator a haH
  have herr : ‖∑ j, M j - ∑ i, h i‖ ≤ (N * (2 * ℓ) : ℕ) * ε := by
    change ‖∑ j, periodicCoarseOperator a j - ∑ i, h i‖ ≤ _
    rw [sum_periodicCoarseOperator]
    refine (ManyBody.norm_sum_sub_le_of_sum_eq Finset.univ θ Δ
      (Matrix.isHermitian_sum _ fun i _ ↦ hherm i) (W := h) rfl).trans ?_
    calc ∑ i : Fin N × Fin (2 * ℓ),
        ‖ManyBody.gaussianFilteredTerm θ Δ (∑ i, h i) (h i) - a i‖ ≤ ∑ _i, ε :=
          Finset.sum_le_sum fun i _ ↦ (hd i).2.2.2
      _ = _ := by simp
  refine ⟨fun j ↦ ⟨hMherm j, ?_, ?_, ?_, ?_⟩, herr, ?_⟩
  · apply edgePartition_mem_supportedOperators
    intro i hi
    apply ManyBody.supportedOperators_mono _ ((hd i).1)
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact periodicCoarseEdge_support_all hℓ i v hi
      (by
        have hdv := (periodicPhysicalDistance_le_edist hN hℓ i v).trans (ManyBody.mem_graphBall.mp
            hv)
        exact_mod_cast hdv)
  · exact norm_edgePartition_le_of_fibre_card periodicCoarseEdge a hJ0 haJ j
      (card_periodicCoarseEdge_fibre j).le
  · exact centeredNorm_periodicCoarseOperator_le a hΩ hJ0 haJ j
  · exact residual_periodicCoarseOperator_le a Ω (by positivity) hares j
  · exact norm_error_gap_transfer (Matrix.isHermitian_sum _ fun i _ ↦ hherm i)
      (Matrix.isHermitian_sum _ fun j _ ↦ hMherm j) (hgap.posSemidef_sub_smul_one
        (Matrix.isHermitian_sum _ fun i _ ↦ hherm i) hΩ hspan) herr

end TNLean.MPS.AreaLaw.LocalSolution
