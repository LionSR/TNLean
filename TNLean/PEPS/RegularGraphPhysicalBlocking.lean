/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphPhysicalMap
import TNLean.PEPS.GIsometricSupportCoordinates
import TNLean.PEPS.GraphAveragingGInjective
import TNLean.PEPS.RegularGraphBondBlocking

/-!
# Physical support transport followed by regular bond separation

The physical maps in Observation 6.4 are derived from local G-isometry and
then composed with the actual-network Bell-pair separation. Arbitrary local
physical spaces and arbitrary local positive isometry factors are retained.
Source: SCP10, arXiv:1001.3807, Observations 6.4–6.5, lines 1765–1880.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (K : Type*) [Fintype K] [DecidableEq K]
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The bundled representation is simultaneous translation in the physical
coordinate basis. Source: SCP10, lines 1830–1848. -/
theorem regularBundleMatrix_apply (g : G) (x y : G × (K → G)) :
    regularBundleMatrix K g x y = if x = g • y then 1 else 0 := by
  simp [regularBundleMatrix, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, MulAction.toPerm_symm_apply, eq_inv_smul_iff, eq_comm]

/-- Both orientations of a regular bundled leg have the same simultaneous
translation action on their coordinate labels. Source: SCP10, lines 1830–1864. -/
theorem graphIncidentMatrix_regularBundle_apply (v : V) (g : G)
    (σ η : IncidentEdge Γ v → G × (K → G)) :
    graphIncidentMatrix (regularBundleMatrix K) v g σ η =
      if σ = g • η then 1 else 0 := by
  have h (f : IncidentEdge Γ v) :
      (if f.1.1.1 = v then regularBundleMatrix K g⁻¹ (η f) (σ f)
        else regularBundleMatrix K g (σ f) (η f)) =
          if σ f = g • η f then 1 else 0 := by
    rw [regularBundleMatrix_apply, regularBundleMatrix_apply]
    simp only [eq_inv_smul_iff, eq_comm (a := g • η f), ite_self]
  simp only [graphIncidentMatrix, h, Fintype.prod_boole, ← funext_iff]
  rfl

/-- The incident bundled action permutes the full virtual basis.
Source: SCP10, regular symmetry in lines 1830–1864. -/
theorem graphIncidentRepresentation_regularBundle_apply (v : V) (g : G)
    (x : (IncidentEdge Γ v → G × (K → G)) → ℂ)
    (σ : IncidentEdge Γ v → G × (K → G)) :
    graphIncidentRepresentation (regularBundleMatrix K) v g x σ = x (g⁻¹ • σ) := by
  rw [graphIncidentRepresentation_apply]
  have he (η : IncidentEdge Γ v → G × (K → G)) :
      σ = g • η ↔ η = g⁻¹ • σ := by rw [eq_inv_smul_iff, eq_comm]
  simp [Matrix.mulVec, dotProduct, graphIncidentMatrix_regularBundle_apply, he]

/-- Unitarity of the bundled incident symmetry is derived from its coordinate
permutation, not assumed of the physical site. Source: SCP10, lines 1830–1864. -/
theorem graphIncidentRepresentation_regularBundle_unitary (v : V) (g : G)
    (x y : (IncidentEdge Γ v → G × (K → G)) → ℂ) :
    star (graphIncidentRepresentation (regularBundleMatrix K) v g x) ⬝ᵥ
        graphIncidentRepresentation (regularBundleMatrix K) v g y = star x ⬝ᵥ y := by
  simp only [dotProduct, Pi.star_apply, graphIncidentRepresentation_regularBundle_apply]
  exact Equiv.sum_comp (MulAction.toPermHom G (IncidentEdge Γ v → G × (K → G)) g⁻¹)
    (fun σ => star (x σ) * y σ)

variable {P : V → Type*} [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

/-- The explicit normalized physical adjoint at each original vertex.
Source: SCP10, Observation 6.4, lines 1765–1820. -/
def regularGraphSupportMatrix
    (a : (v : V) → (IncidentEdge Γ v → G × (K → G)) → P v → ℂ)
    (c : V → ℝ) (v : V) : Matrix (IncidentEdge Γ v → G × (K → G)) (P v) ℂ :=
  LinearMap.toMatrix' ((Real.sqrt (c v) : ℂ)⁻¹ • coordinateAdjoint (regularSiteMap (a v)))

omit [Group G] in
/-- The physical inverse is the literal normalized conjugate of the original
site coefficient. Source: SCP10, Observation 6.4, lines 1770–1788. -/
theorem regularGraphSupportMatrix_apply
    (a : (v : V) → (IncidentEdge Γ v → G × (K → G)) → P v → ℂ)
    (c : V → ℝ) (v : V) (α : IncidentEdge Γ v → G × (K → G)) (s : P v) :
    regularGraphSupportMatrix K a c v α s =
      (Real.sqrt (c v) : ℂ)⁻¹ * star (a v α s) := by
  simp only [regularGraphSupportMatrix, map_smul, coordinateAdjoint,
    toMatrix_regularSiteMap, LinearMap.toMatrix'_toLin', Matrix.smul_apply, smul_eq_mul]
  rfl

/-- First expose the actual local physical supports, then apply the local
relative-coordinate unitaries that separate the Bell pairs.
Source: SCP10, Observations 6.4–6.5, lines 1765–1880. -/
def regularGraphPhysicalDisentangler
    (a : (v : V) → (IncidentEdge Γ v → G × (K → G)) → P v → ℂ)
    (c : V → ℝ) : (((v : V) → P v) → ℂ) →ₗ[ℂ]
      ((((v : V) → IncidentEdge Γ v → G) ×
        ((v : V) → IncidentEdge Γ v → (K → G))) → ℂ) :=
  (regularGraphBlocking K).toLinearMap ∘ₗ
    graphPhysicalProductMap (regularGraphSupportMatrix K a c)

/-- Local G-isometry alone gives the physical disentangler and its exact
Bell-pair factorization on the original graph state. The normalized adjoints
are isometries on the derived local physical ranges; their product followed by
the relative-coordinate unitary is isometric on the product range. The actual
state lies in that range by its contraction formula. All positive local
normalization factors and all physical indices are retained.
Source: SCP10, Observations 6.4–6.5, lines 1765–1880.

**Scope restriction (bundled graph):** The finite graph already carries the
uniform bundle alphabet. Identification with a tiled 2×2 fine lattice remains
separate; see `docs/paper-gaps/scp10_general_group_physical_blocking.tex`. -/
theorem exists_regularGraphPhysicalDisentangler
    (a : (v : V) → (IncidentEdge Γ v → G × (K → G)) → P v → ℂ)
    (ha : ∀ v, IsGIsometric (graphIncidentRepresentation (regularBundleMatrix K) v)
      (regularSiteMap (a v))) :
    ∃ c : V → ℝ, (∀ v, 0 < c v) ∧
      (∀ v, ∀ x ∈ (regularSiteMap (a v)).range, ∀ y ∈ (regularSiteMap (a v)).range,
        star (regularGraphSupportMatrix K a c v *ᵥ x) ⬝ᵥ
          (regularGraphSupportMatrix K a c v *ᵥ y) = star x ⬝ᵥ y) ∧
      (∀ ψ ∈ LinearMap.range (graphPhysicalProductMap (fun v s η => a v η s)),
        ∀ φ ∈ LinearMap.range (graphPhysicalProductMap (fun v s η => a v η s)),
        star (regularGraphPhysicalDisentangler K a c ψ) ⬝ᵥ
          regularGraphPhysicalDisentangler K a c φ = star ψ ⬝ᵥ φ) ∧
      (star (regularGraphPhysicalDisentangler K a c (graphBondNetwork a)) ⬝ᵥ
          regularGraphPhysicalDisentangler K a c (graphBondNetwork a) =
        star (graphBondNetwork a) ⬝ᵥ graphBondNetwork a) ∧
      regularGraphPhysicalDisentangler K a c (graphBondNetwork a) =
        fun σ => (∏ v, (Real.sqrt (c v) : ℂ)) *
          (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ) ^ Fintype.card (Edge Γ) *
            graphBondNetwork (graphAveragingSite (leftRegularMatrix G)) σ.1 *
              regularGraphNormalizedBell K σ.2 := by
  classical
  choose c hc h using fun v => (ha v).exists_accessibleCoordinates
    (graphIncidentRepresentation_regularBundle_unitary K v)
  have hlocal (v : V) (x) (hx : x ∈ (regularSiteMap (a v)).range)
      (y) (hy : y ∈ (regularSiteMap (a v)).range) :
      star (regularGraphSupportMatrix K a c v *ᵥ x) ⬝ᵥ
        (regularGraphSupportMatrix K a c v *ᵥ y) = star x ⬝ᵥ y := by
    simpa only [regularGraphSupportMatrix, LinearMap.toMatrix'_mulVec] using (h v).2 x hx y hy
  have hGram (v : V) :
      (regularGraphSupportMatrix K a c v * (Matrix.of fun s η => a v η s)).conjTranspose *
          (regularGraphSupportMatrix K a c v * (Matrix.of fun s η => a v η s)) =
        (Matrix.of fun s η => a v η s).conjTranspose * (Matrix.of fun s η => a v η s) := by
    ext η ξ
    let T := Matrix.of fun s α => a v α s
    have hη : T.col η ∈ (regularSiteMap (a v)).range :=
      ⟨Pi.single η 1, Matrix.mulVec_single_one T η⟩
    have hξ : T.col ξ ∈ (regularSiteMap (a v)).range :=
      ⟨Pi.single ξ 1, Matrix.mulVec_single_one T ξ⟩
    change star ((regularGraphSupportMatrix K a c v * T).col η) ⬝ᵥ
      (regularGraphSupportMatrix K a c v * T).col ξ = star (T.col η) ⬝ᵥ T.col ξ
    rw [Matrix.col_mul_eq_mulVec_col, Matrix.col_mul_eq_mulVec_col]
    exact hlocal v _ hη _ hξ
  have hglobal (ψ) (hψ : ψ ∈ LinearMap.range
      (graphPhysicalProductMap (fun v s η => a v η s)))
      (φ) (hφ : φ ∈ LinearMap.range
      (graphPhysicalProductMap (fun v s η => a v η s))) :
      star (regularGraphPhysicalDisentangler K a c ψ) ⬝ᵥ
        regularGraphPhysicalDisentangler K a c φ = star ψ ⬝ᵥ φ := by
    simp only [regularGraphPhysicalDisentangler, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, regularGraphBlocking_dotProduct]
    exact graphPhysicalProductMap_dotProduct_on_range _ _ hGram ψ φ hψ hφ
  refine ⟨c, hc, hlocal, hglobal,
    hglobal _ (graphBondNetwork_mem_range_productSiteMap a)
      _ (graphBondNetwork_mem_range_productSiteMap a), ?_⟩
  have hcoeff (v : V) (α η : IncidentEdge Γ v → G × (K → G)) :
      (∑ s : P v, regularGraphSupportMatrix K a c v α s * a v η s) =
        (Real.sqrt (c v) : ℂ) * graphAveragingSite (regularBundleMatrix K) v η α := by
    let J := (Real.sqrt (c v) : ℂ)⁻¹ • coordinateAdjoint (regularSiteMap (a v))
    calc
      _ = (LinearMap.toMatrix' J * LinearMap.toMatrix' (regularSiteMap (a v))) α η := by
        rw [toMatrix_regularSiteMap]
        rfl
      _ = LinearMap.toMatrix' (J ∘ₗ regularSiteMap (a v)) α η := by
        rw [LinearMap.toMatrix'_comp]
      _ = _ := by
        rw [(h v).1, ← regularSiteMap_graphAveragingSite]
        simp only [map_smul, toMatrix_regularSiteMap]
        rfl
  have hnet : graphPhysicalProductMap (regularGraphSupportMatrix K a c) (graphBondNetwork a) =
      (∏ v, (Real.sqrt (c v) : ℂ)) •
        graphBondNetwork (graphAveragingSite (regularBundleMatrix K)) := by
    rw [graphPhysicalProductMap_graphBondNetwork]
    simp_rw [hcoeff]
    ext σ
    simp only [graphBondNetwork, Finset.prod_mul_distrib, ← Finset.mul_sum,
      Pi.smul_apply, smul_eq_mul]
  simp only [regularGraphPhysicalDisentangler, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, hnet, map_smul, regularGraphBlocking_averagingSite_normalized]
  ext σ
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The physical disentangler is an actual Hilbert-space isometry on the
product of the original site ranges, with the same explicit coordinate action
and the same scalar-correct state factorization.
Source: SCP10, Observations 6.4–6.5, lines 1765–1880.

**Scope restriction (bundled graph):** This statement does not identify a
2×2 fine lattice with the bundled graph; see
`docs/paper-gaps/scp10_general_group_physical_blocking.tex`. -/
theorem exists_regularGraphPhysicalSupportIsometry
    (a : (v : V) → (IncidentEdge Γ v → G × (K → G)) → P v → ℂ)
    (ha : ∀ v, IsGIsometric (graphIncidentRepresentation (regularBundleMatrix K) v)
      (regularSiteMap (a v))) :
    ∃ c : V → ℝ, (∀ v, 0 < c v) ∧
      ∃ I : (Matrix.toEuclideanLin (LinearMap.toMatrix'
          (graphPhysicalProductMap (fun v s η => a v η s)))).range →ₗᵢ[ℂ]
        EuclideanSpace ℂ (((v : V) → IncidentEdge Γ v → G) ×
          ((v : V) → IncidentEdge Γ v → (K → G))),
        (∀ x, (I x).ofLp = regularGraphPhysicalDisentangler K a c x.val.ofLp) ∧
        I ⟨WithLp.toLp 2 (graphBondNetwork a),
            graphBondNetwork_mem_euclideanRange_productSiteMap a⟩ =
          WithLp.toLp 2 (fun σ => (∏ v, (Real.sqrt (c v) : ℂ)) *
            (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ) ^ Fintype.card (Edge Γ) *
              graphBondNetwork (graphAveragingSite (leftRegularMatrix G)) σ.1 *
                regularGraphNormalizedBell K σ.2) := by
  obtain ⟨c, hc, _, hglobal, _, hfactor⟩ := exists_regularGraphPhysicalDisentangler K a ha
  refine ⟨c, hc, coordinateSupportIsometry _ _ hglobal,
    coordinateSupportIsometry_apply _ _ hglobal, ?_⟩
  apply WithLp.ofLp_injective 2
  rw [coordinateSupportIsometry_apply]
  exact hfactor

end TNLean.PEPS
