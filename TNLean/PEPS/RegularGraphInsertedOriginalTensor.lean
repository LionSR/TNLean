/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphInsertedPhysicalSupport
import TNLean.PEPS.RegularGraphInsertedSurplus
import TNLean.PEPS.RegularTwoByTwoOriginalTensor

/-!
# Uniform physical transport of inserted states to the original tensor

One local support isometry, chosen before the edge labels, transports every
bundled regular inserted state to the original single-regular-bond tensor and
the same unit Bell product. Source: SCP10, arXiv:1001.3807, Observations 6.5–6.6,
lines 1840–1909. This graph statement is separate from geometric reblocking.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (K : Type*) [Fintype K] [DecidableEq K]
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {P Q : V → Type*} [∀ v, Fintype (P v)] [∀ v, Fintype (Q v)]

/-- Regroup the complete original physical registers and the complete surplus
half-edge registers as two factors. Source: SCP10, Observation 6.6. -/
def regularGraphOriginalOutputRegrouping :
    EuclideanSpace ℂ ((v : V) → P v × (IncidentEdge Γ v → K → G)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (((v : V) → P v) × ((v : V) → IncidentEdge Γ v → K → G)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.arrowProdEquivProdArrow V P (fun v => IncidentEdge Γ v → K → G))

/-- All inserted sectors share one physical-support isometry and exactly the
same positive site and Bell factors. The original tensor is retained literally.
Source: SCP10, Observations 6.5–6.6, lines 1840–1909. -/
theorem exists_regularGraphInsertedOriginalTensorIsometry
    (a : (v : V) → (IncidentEdge Γ v → G) → P v → ℂ)
    (b : (v : V) → (IncidentEdge Γ v → G × (K → G)) → Q v → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hb : ∀ v, IsGIsometric (graphIncidentRepresentation (regularBundleMatrix K) v)
      (regularSiteMap (b v))) :
    ∃ ca cb : V → ℝ, (∀ v, 0 < ca v) ∧ (∀ v, 0 < cb v) ∧
      ∃ F : (v : V) → Matrix (P v × (IncidentEdge Γ v → K → G)) (Q v) ℂ,
      ∃ I : (Matrix.toEuclideanLin (LinearMap.toMatrix'
          (graphPhysicalProductMap (fun v s η => b v η s)))).range →ₗᵢ[ℂ]
        EuclideanSpace ℂ (((v : V) → P v) × ((v : V) → IncidentEdge Γ v → K → G)),
        (∀ x σ, I x σ = graphPhysicalProductMap F x.val.ofLp
          (fun v => (σ.1 v, σ.2 v))) ∧
        ∀ u : Edge Γ → G,
          I ⟨WithLp.toLp 2 (graphInsertedBondNetwork (fun e => regularBundleMatrix K (u e)) b),
              graphInsertedBondNetwork_mem_euclideanRange_productSiteMap _ b⟩ =
            (((∏ v, Real.sqrt (ca v) / Real.sqrt (cb v)) *
                Real.sqrt (Fintype.card (K → G) : ℝ) ^ Fintype.card (Edge Γ) : ℝ) : ℂ) •
              physicalStateProduct
                (WithLp.toLp 2 (graphInsertedBondNetwork (fun e => leftRegularMatrix G (u e)) a))
                (WithLp.toLp 2 (regularGraphNormalizedBell (Γ := Γ) (G := G) K)) := by
  classical
  let c := regularGraphSurplusSite K a
  obtain ⟨ca, cb, hca, hcb, F, J, hJ, hstate⟩ :=
    exists_graphGIsometricInsertedPhysicalSupportTransport
      (graphIncidentRepresentation (regularBundleMatrix K)) b c hb
      (isGIsometric_regularGraphSurplusSite K a ha)
      (graphIncidentRepresentation_regularBundle_unitary K)
  let I := (regularGraphOriginalOutputRegrouping K).toLinearIsometry.comp J
  refine ⟨ca, cb, hca, hcb, F, I, ?_, ?_⟩
  · intro x σ
    exact congrFun (hJ x) (fun v => (σ.1 v, σ.2 v))
  · intro u
    change regularGraphOriginalOutputRegrouping K (J _) = _
    rw [hstate]
    apply WithLp.ofLp_injective 2
    funext σ
    change (∏ v, (Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) *
      graphInsertedBondNetwork (fun e => regularBundleMatrix K (u e)) c
        (fun v => (σ.1 v, σ.2 v)) = _
    rw [graphInsertedBondNetwork_regularGraphSurplusSite]
    simp only [physicalStateProduct, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, regularGraphNormalizedBell, Complex.ofReal_mul,
      Complex.ofReal_prod, Complex.ofReal_div, Complex.ofReal_pow]
    have hs : (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr Fintype.card_pos))
    have hcancel : (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ) ^
        Fintype.card (Edge Γ) * (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ)⁻¹ ^
          Fintype.card (Edge Γ) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hs, one_pow]
    calc
      _ = ((∏ v, (Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) *
          graphInsertedBondNetwork (fun e => leftRegularMatrix G (u e)) a σ.1 *
            regularGraphResidualBell K σ.2) *
        ((Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ) ^ Fintype.card (Edge Γ) *
          (Real.sqrt (Fintype.card (K → G) : ℝ) : ℂ)⁻¹ ^ Fintype.card (Edge Γ)) := by
            rw [hcancel, mul_one, mul_assoc]
      _ = _ := by ring

end TNLean.PEPS
