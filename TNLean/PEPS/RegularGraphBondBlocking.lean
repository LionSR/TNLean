/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RegularRepresentationBlocking
import TNLean.PEPS.GraphAveragingBondState
import TNLean.PEPS.RegularTorusSite
import QICLean.Channel.MaximallyEntangled

/-!
# Physical separation of regular bond bundles on a finite graph

The actual contraction of regular averaging tensors with a bundle of regular
bonds on every edge separates into the single-bond contraction and independent
Bell pairs. The operation is the relative-coordinate permutation on each
physical half-edge, hence a product of local physical unitaries, followed only
by regrouping the physical indices. No global equality is assumed.

Source: SCP10, arXiv:1001.3807, Observations 6.5–6.6,
`Papers/1001.3807/paper_v3.tex`, lines 1830–1909, and figures
`renorm-gg-sym`, `renorm-g-id-and-split`.

**Scope restriction (bond separation):** This is the finite-graph network step
of Observation 6.5 for canonical accessible averaging tensors. It does not
identify a tiled 2×2 fine lattice with this bundled network. The full fixed-point
statement of Observation 6.6 remains separate. See
`docs/paper-gaps/scp10_general_group_physical_blocking.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (K : Type*) [Fintype K] [DecidableEq K]

/-- Simultaneous regular translation on one distinguished bond and a finite
family of additional bonds. Source: SCP10, lines 1830–1848. -/
def regularBundleMatrix : G →* Matrix (G × (K → G)) (G × (K → G)) ℂ :=
  Matrix.permMatrixHom.comp (MulAction.toPermHom G (G × (K → G)))

/-- The explicit physical relative coordinates separate the matrix element
into one regular factor and an identity factor. Source: SCP10, lines 1840–1873. -/
theorem regularBundleMatrix_blocking (g : G) (x y : G × (K → G)) :
    regularBundleMatrix K g (RegularRepresentation.blockingFamilyEquiv K x)
        (RegularRepresentation.blockingFamilyEquiv K y) =
      leftRegularMatrix G g x.1 y.1 * (if x.2 = y.2 then 1 else 0) := by
  have h (u v : G × (K → G)) : regularBundleMatrix K g u v =
      if u = g • v then 1 else 0 := by
    simp [regularBundleMatrix, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, MulAction.toPerm_symm_apply, eq_inv_smul_iff, eq_comm]
  rw [h, leftRegularMatrix_apply]
  have he : RegularRepresentation.blockingFamilyEquiv K x =
      g • RegularRepresentation.blockingFamilyEquiv K y ↔ x.1 = g * y.1 ∧ x.2 = y.2 := by
    rw [← RegularRepresentation.blockingFamilyEquiv_smul,
      Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  simp only [he, ite_zero_mul_ite_zero, mul_one]

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- Local relative coordinates, with the distinguished and residual physical
registers displayed separately. Source: SCP10, lines 1851–1873. -/
def regularGraphBlockingEquiv :
    ((v : V) → IncidentEdge Γ v → G × (K → G)) ≃
      (((v : V) → IncidentEdge Γ v → G) ×
        ((v : V) → IncidentEdge Γ v → (K → G))) where
  toFun σ := (fun v f => (σ v f).1, fun v f => (σ v f).1⁻¹ • (σ v f).2)
  invFun σ v f := RegularRepresentation.blockingFamilyEquiv K (σ.1 v f, σ.2 v f)
  left_inv σ := by
    funext v f
    simp [RegularRepresentation.blockingFamilyEquiv]
  right_inv σ := by
    apply Prod.ext
    · rfl
    · funext v f k
      simp [RegularRepresentation.blockingFamilyEquiv, Pi.smul_apply, smul_eq_mul]

/-- The coordinate change is an isometry of the entire physical Hilbert space,
not just a virtual similarity. It acts independently at every vertex.
Source: SCP10, physical operation in lines 1851–1864. -/
def regularGraphBlockingIsometry :
    EuclideanSpace ℂ ((v : V) → IncidentEdge Γ v → G × (K → G)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (((v : V) → IncidentEdge Γ v → G) ×
        ((v : V) → IncidentEdge Γ v → (K → G))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regularGraphBlockingEquiv K)

/-- The same physical isometry on coefficient functions. Source: SCP10,
lines 1851–1873. -/
def regularGraphBlocking :
    (((v : V) → IncidentEdge Γ v → G × (K → G)) → ℂ) ≃ₗ[ℂ]
      ((((v : V) → IncidentEdge Γ v → G) ×
        ((v : V) → IncidentEdge Γ v → (K → G))) → ℂ) :=
  LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) (regularGraphBlockingEquiv K)

omit [DecidableEq G] in
/-- The Hilbert-space isometry and the coefficient operation are the same
physical map. Source: SCP10, lines 1851–1864. -/
theorem regularGraphBlockingIsometry_apply
    (ψ : EuclideanSpace ℂ ((v : V) → IncidentEdge Γ v → G × (K → G)))
    (σ : ((v : V) → IncidentEdge Γ v → G) ×
      ((v : V) → IncidentEdge Γ v → (K → G))) :
    regularGraphBlockingIsometry K ψ σ = regularGraphBlocking K (fun x => ψ x) σ := rfl

/-- Independent, unnormalized Bell vectors on the residual physical registers.
All endpoint indices are retained. Source: SCP10, lines 1865–1874. -/
def regularGraphResidualBell
    (τ : (v : V) → IncidentEdge Γ v → (K → G)) : ℂ :=
  ∏ e : Edge Γ,
    if τ e.1.2 (edgeRightIncident e) = τ e.1.1 (edgeLeftIncident e) then 1 else 0

/-- Physical bond separation of the actual graph tensor-network state, with
one normalized group average per original vertex and no omitted scalar.
Source: SCP10, Observation 6.5, lines 1851–1880. -/
theorem regularGraphBlocking_averagingSite :
    regularGraphBlocking (Γ := Γ) (G := G) K
        (graphBondNetwork (graphAveragingSite (regularBundleMatrix K))) =
      fun σ => graphBondNetwork (graphAveragingSite (leftRegularMatrix G)) σ.1 *
        regularGraphResidualBell K σ.2 := by
  funext σ
  let β : Edge Γ → (G × (K → G)) × (G × (K → G)) :=
    graphSiteBondEndpointEquiv ((regularGraphBlockingEquiv K).symm σ)
  have h := congrFun (graphBondRegrouping_averagingSite_coherent
    (Γ := Γ) (regularBundleMatrix (G := G) K)) β
  have hc := congrFun (graphBondRegrouping_averagingSite_coherent
    (Γ := Γ) (leftRegularMatrix G)) (graphSiteBondEndpointEquiv σ.1)
  simp only [β, graphBondRegrouping_apply, Equiv.symm_apply_apply] at h hc
  change graphBondNetwork (graphAveragingSite (regularBundleMatrix K))
    ((regularGraphBlockingEquiv K).symm σ) = _
  rw [h, hc]
  simp only [graphSiteBondEndpointEquiv, regularGraphBlockingEquiv,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, regularBundleMatrix_blocking, Finset.prod_mul_distrib,
    regularGraphResidualBell, ← mul_assoc, Finset.sum_mul]

omit [DecidableEq G] in
/-- The physical operation preserves every overlap, including normalization.
Source: SCP10, the local unitary operation in lines 1851–1864. -/
theorem regularGraphBlocking_dotProduct
    (ψ φ : ((v : V) → IncidentEdge Γ v → G × (K → G)) → ℂ) :
    star (regularGraphBlocking K ψ) ⬝ᵥ regularGraphBlocking K φ = star ψ ⬝ᵥ φ :=
  (regularGraphBlockingEquiv K).symm.sum_comp (fun σ => star (ψ σ) * φ σ)

omit [Group G] [Fintype G] [DecidableEq K] in
/-- Every surplus regular bond supplies a separate Bell factor, before
normalization. Source: SCP10, lines 1865–1874. -/
theorem regularGraphResidualBell_eq_prod
    (τ : (v : V) → IncidentEdge Γ v → (K → G)) :
    regularGraphResidualBell K τ = ∏ e : Edge Γ, ∏ k : K,
      if τ e.1.2 (edgeRightIncident e) k = τ e.1.1 (edgeLeftIncident e) k
        then 1 else 0 := by
  simp only [regularGraphResidualBell, Fintype.prod_boole, ← funext_iff]

omit [Group G] in
/-- The Bell product has one factor of its local dimension for every edge.
Source: SCP10, maximally entangled factors in lines 1865–1874. -/
theorem regularGraphResidualBell_dotProduct :
    star (regularGraphResidualBell (Γ := Γ) (G := G) K) ⬝ᵥ
        regularGraphResidualBell K =
      (Fintype.card (K → G) : ℂ) ^ Fintype.card (Edge Γ) := by
  classical
  let E := graphSiteBondEndpointEquiv (Γ := Γ) (X := K → G)
  change (∑ τ, star (regularGraphResidualBell K τ) * regularGraphResidualBell K τ) = _
  rw [← E.symm.sum_comp]
  simp only [regularGraphResidualBell, graphSiteBondEndpointEquiv_symm_head,
    graphSiteBondEndpointEquiv_symm_tail, E, star_prod, ← Finset.prod_mul_distrib]
  have h (p : (K → G) × (K → G)) :
      star (if p.1 = p.2 then (1 : ℂ) else 0) *
        (if p.1 = p.2 then (1 : ℂ) else 0) = if p.1 = p.2 then 1 else 0 := by
    split_ifs <;> simp
  simp_rw [h]
  rw [← Fintype.prod_sum (fun (_ : Edge Γ) (p : (K → G) × (K → G)) =>
    if p.1 = p.2 then (1 : ℂ) else 0)]
  have hs : (∑ p : (K → G) × (K → G),
      if p.1 = p.2 then (1 : ℂ) else 0) = Fintype.card (K → G) := by
    rw [Fintype.sum_prod_type]
    simp
  simp only [hs, Finset.prod_const, Finset.card_univ]

/-- The residual product with every Bell pair normalized to unit norm.
Source: SCP10, lines 1865–1874; the normalization is retained explicitly. -/
def regularGraphNormalizedBell
    (τ : (v : V) → IncidentEdge Γ v → (K → G)) : ℂ :=
  (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ)⁻¹ ^ Fintype.card (Edge Γ) *
    regularGraphResidualBell K τ

/-- The discarded state is a unit vector, for every finite group and graph.
Source: SCP10, independent maximally entangled pairs in lines 1865–1874. -/
theorem regularGraphNormalizedBell_dotProduct :
    star (regularGraphNormalizedBell (Γ := Γ) (G := G) K) ⬝ᵥ
        regularGraphNormalizedBell K = 1 := by
  let r : ℂ := (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ)⁻¹
  have hr : star r = r := by simp [r]
  have hrr : r * r = (Fintype.card (K → G) : ℂ)⁻¹ := by
    simpa only [r, Complex.ofReal_natCast] using
      Complex.ofReal_sqrt_inv_mul_self (Fintype.card (K → G) : ℝ) (by positivity)
  change star (r ^ Fintype.card (Edge Γ) • regularGraphResidualBell K) ⬝ᵥ
    (r ^ Fintype.card (Edge Γ) • regularGraphResidualBell K) = 1
  rw [star_smul, smul_dotProduct, dotProduct_smul, regularGraphResidualBell_dotProduct]
  simp only [smul_eq_mul, star_pow, hr]
  rw [← mul_assoc, ← mul_pow, hrr, ← mul_pow, inv_mul_cancel₀, one_pow]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

omit [Group G] in
/-- Each residual edge factor is exactly the standard normalized maximally
entangled vector, with its two endpoint registers retained.
Source: SCP10, lines 1865–1874. -/
theorem regularGraphNormalizedBell_eq_prod_omegaVec
    (τ : (v : V) → IncidentEdge Γ v → (K → G)) :
    regularGraphNormalizedBell K τ = ∏ e : Edge Γ,
      Matrix.omegaVec (Fintype.card (K → G))
        (Fintype.equivFin (K → G) (τ e.1.2 (edgeRightIncident e)),
          Fintype.equivFin (K → G) (τ e.1.1 (edgeLeftIncident e))) := by
  simp only [Matrix.omegaVec_apply, Equiv.apply_eq_iff_eq, one_div]
  have h (a b : K → G) :
      (if a = b then (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ)⁻¹ else 0) =
        (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ)⁻¹ *
          (if a = b then 1 else 0) := by
    split_ifs <;> simp
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp [regularGraphNormalizedBell, regularGraphResidualBell]

/-- The actual transformed state is the coarse regular network tensored with
unit-normalized Bell pairs. Its explicit scalar is one square root of the
residual bond dimension per edge. No normalization is silently discarded.
Source: SCP10, Observation 6.5, lines 1851–1880. -/
theorem regularGraphBlocking_averagingSite_normalized :
    regularGraphBlocking (Γ := Γ) (G := G) K
        (graphBondNetwork (graphAveragingSite (regularBundleMatrix K))) =
      fun σ => (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ) ^ Fintype.card (Edge Γ) *
        graphBondNetwork (graphAveragingSite (leftRegularMatrix G)) σ.1 *
          regularGraphNormalizedBell K σ.2 := by
  rw [regularGraphBlocking_averagingSite]
  funext σ
  have hr : (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  simp only [regularGraphNormalizedBell, ← mul_assoc]
  rw [mul_right_comm _ (graphBondNetwork _ σ.1), ← mul_pow, mul_inv_cancel₀ hr,
    one_pow, one_mul]

end TNLean.PEPS
