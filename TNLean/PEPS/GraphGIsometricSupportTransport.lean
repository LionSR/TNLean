/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphPhysicalMap
import TNLean.PEPS.RegularSiteGram
import TNLean.PEPS.GIsometricCanonicalSupport

/-!
# Physical support transport between G-isometric graph tensors

Two physical realizations of the same unitary virtual symmetry have isometric
physical supports after retaining their positive normalization factors.
Applying the derived local maps to an actual graph contraction gives the
actual other graph contraction. Source: SCP10, arXiv:1001.3807,
Observations 6.4–6.6, lines 1765–1915.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

section Local
variable {G ι κ ν : Type*} [Group G] [Finite G] [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
attribute [local instance] Representation.invertibleFintypeCardComplex

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] in
/-- The normalized second tensor composed with the normalized adjoint of the
first transports their physical supports isometrically. Both positive factors
remain explicit. Source: SCP10, Observations 6.4 and 6.6. -/
theorem IsGIsometric.exists_physicalSupportTransport
    {ρ : Representation ℂ G (ι → ℂ)}
    {A : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)} {B : (ι → ℂ) →ₗ[ℂ] (ν → ℂ)}
    (hA : IsGIsometric ρ A) (hB : IsGIsometric ρ B)
    (hU : ∀ g x y, star (ρ g x) ⬝ᵥ ρ g y = star x ⬝ᵥ y) :
    ∃ ca cb : ℝ, 0 < ca ∧ 0 < cb ∧
      ∃ F : (κ → ℂ) →ₗ[ℂ] (ν → ℂ),
        F ∘ₗ A = ((Real.sqrt ca : ℂ) / (Real.sqrt cb : ℂ)) • B ∧
        ∀ x ∈ A.range, ∀ y ∈ A.range, star (F x) ⬝ᵥ F y = star x ⬝ᵥ y := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨ca, hca, hJA, hJ⟩ := hA.exists_accessibleCoordinates hU
  obtain ⟨cb, hcb, hBinner⟩ := hB.exists_inner_eq
  let J := (Real.sqrt ca : ℂ)⁻¹ • coordinateAdjoint A
  let F := (Real.sqrt cb : ℂ)⁻¹ • B ∘ₗ J
  have hBP : B ∘ₗ ρ.averageMap = B := by
    apply LinearMap.ext
    intro u
    exact apply_averageMap_of_forall_comp_eq hB.invariant u
  change J ∘ₗ A = (Real.sqrt ca : ℂ) • ρ.averageMap at hJA
  have hFA : F ∘ₗ A = ((Real.sqrt ca : ℂ) / (Real.sqrt cb : ℂ)) • B := by
    simp only [F, LinearMap.comp_assoc, hJA, LinearMap.comp_smul, LinearMap.smul_comp,
      hBP, smul_smul, div_eq_mul_inv, mul_comm]
  have hmem (x : κ → ℂ) (hx : x ∈ A.range) : J x ∈ ρ.invariants := by
    obtain ⟨u, rfl⟩ := hx
    have h := LinearMap.congr_fun hJA u
    change J (A u) = _ at h
    rw [h]
    exact ρ.invariants.smul_mem _ (ρ.averageMap_invariant u)
  have hs : (Real.sqrt cb : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hcb)
  refine ⟨ca, cb, hca, hcb, F, hFA, ?_⟩
  intro x hx y hy
  change star ((Real.sqrt cb : ℂ)⁻¹ • B (J x)) ⬝ᵥ
    ((Real.sqrt cb : ℂ)⁻¹ • B (J y)) = _
  rw [star_smul, smul_dotProduct, dotProduct_smul, hBinner _ (hmem x hx) _ (hmem y hy)]
  simp only [smul_eq_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← Complex.ofReal_sqrt_sq cb hcb.le, pow_two]
  have hscalar : (Real.sqrt cb : ℂ)⁻¹ *
      ((Real.sqrt cb : ℂ)⁻¹ * ((Real.sqrt cb : ℂ) * (Real.sqrt cb : ℂ) *
        (star (J x) ⬝ᵥ J y))) = star (J x) ⬝ᵥ J y := by field_simp
  rw [hscalar]
  exact hJ x hx y hy

end Local

section Graph
variable {G X V : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X]
  [Fintype V] [LinearOrder V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {P Q : V → Type*} [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]
  [∀ v, Fintype (Q v)] [∀ v, DecidableEq (Q v)]

omit [∀ v, DecidableEq (P v)] [∀ v, DecidableEq (Q v)] in
/-- Local G-isometry alone supplies a global Hilbert-space isometry on the
actual product physical range, carrying one actual graph state to the other
with all positive site factors retained. Source: SCP10, Observations 6.4–6.6. -/
theorem exists_graphGIsometricPhysicalSupportTransport
    (ρ : (v : V) → Representation ℂ G ((IncidentEdge Γ v → X) → ℂ))
    (a : (v : V) → (IncidentEdge Γ v → X) → P v → ℂ)
    (b : (v : V) → (IncidentEdge Γ v → X) → Q v → ℂ)
    (ha : ∀ v, IsGIsometric (ρ v) (regularSiteMap (a v)))
    (hb : ∀ v, IsGIsometric (ρ v) (regularSiteMap (b v)))
    (hU : ∀ v g x y, star (ρ v g x) ⬝ᵥ ρ v g y = star x ⬝ᵥ y) :
    ∃ ca cb : V → ℝ, (∀ v, 0 < ca v) ∧ (∀ v, 0 < cb v) ∧
      ∃ F : (v : V) → Matrix (Q v) (P v) ℂ,
        ∃ I : (Matrix.toEuclideanLin (LinearMap.toMatrix'
            (graphPhysicalProductMap (fun v s η => a v η s)))).range →ₗᵢ[ℂ]
          EuclideanSpace ℂ ((v : V) → Q v),
          (∀ x, (I x).ofLp = graphPhysicalProductMap F x.val.ofLp) ∧
          I ⟨WithLp.toLp 2 (graphBondNetwork a),
              graphBondNetwork_mem_euclideanRange_productSiteMap a⟩ =
            WithLp.toLp 2 ((∏ v, (Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) •
              graphBondNetwork b) := by
  classical
  choose ca cb hca hcb F hFA hF using fun v =>
    (ha v).exists_physicalSupportTransport (hb v) (hU v)
  let M := fun v => LinearMap.toMatrix' (F v)
  have hgram (v : V) :
      (M v * (Matrix.of fun s η => a v η s)).conjTranspose *
          (M v * (Matrix.of fun s η => a v η s)) =
        (Matrix.of fun s η => a v η s).conjTranspose * (Matrix.of fun s η => a v η s) := by
    ext η ξ
    let T := Matrix.of fun s α => a v α s
    have hη : T.col η ∈ (regularSiteMap (a v)).range :=
      ⟨Pi.single η 1, Matrix.mulVec_single_one T η⟩
    have hξ : T.col ξ ∈ (regularSiteMap (a v)).range :=
      ⟨Pi.single ξ 1, Matrix.mulVec_single_one T ξ⟩
    change star ((M v * T).col η) ⬝ᵥ (M v * T).col ξ = star (T.col η) ⬝ᵥ T.col ξ
    rw [Matrix.col_mul_eq_mulVec_col, Matrix.col_mul_eq_mulVec_col]
    simpa only [M, LinearMap.toMatrix'_mulVec] using hF v _ hη _ hξ
  have hglobal (ψ) (hψ : ψ ∈ (graphPhysicalProductMap (fun v s η => a v η s)).range)
      (φ) (hφ : φ ∈ (graphPhysicalProductMap (fun v s η => a v η s)).range) :=
    graphPhysicalProductMap_dotProduct_on_range M
      (fun v s η => a v η s) hgram ψ φ hψ hφ
  refine ⟨ca, cb, hca, hcb, M, coordinateSupportIsometry _ _ hglobal,
    coordinateSupportIsometry_apply _ _ hglobal, ?_⟩
  apply WithLp.ofLp_injective 2
  rw [coordinateSupportIsometry_apply, graphPhysicalProductMap_graphBondNetwork]
  have hcoeff (v : V) (η : IncidentEdge Γ v → X) (s : Q v) :
      (∑ t : P v, M v s t * a v η t) =
        ((Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) * b v η s := by
    have h := congrArg (fun T => LinearMap.toMatrix' T s η) (hFA v)
    simp only [LinearMap.toMatrix'_comp, map_smul, toMatrix_regularSiteMap] at h
    exact h
  simp_rw [hcoeff]
  ext σ
  simp only [graphBondNetwork, Finset.prod_mul_distrib, ← Finset.mul_sum,
    Pi.smul_apply, smul_eq_mul]

end Graph
end TNLean.PEPS
