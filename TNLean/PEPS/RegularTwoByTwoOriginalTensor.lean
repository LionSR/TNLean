/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphGIsometricSupportTransport
import TNLean.PEPS.RegularGraphSurplusSite
import TNLean.PEPS.RegularTwoByTwoNonzero
import TNLean.PEPS.PhysicalStateNormalization

/-!
# Normalized renormalization with the original coarse tensor

The target tensor is the original homogeneous four-leg tensor together with
physical surplus registers carrying independent Bell pairs. Its G-isometry
and its actual graph contraction are derived, and both original fine and
coarse states are proved nonzero. Positive normalization factors are retained
before the final unit-state comparison.

Source: SCP10, arXiv:1001.3807, Observation 6.6, lines 1888–1909.
Scope: untwisted torus with both coarse periods at least three.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The surplus Bell product has unit Hilbert norm. -/
theorem norm_regularGraphNormalizedBell
    (K : Type*) [Fintype K] [DecidableEq K]
    {V : Type*} [Fintype V] [LinearOrder V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj] :
    ‖WithLp.toLp 2 (regularGraphNormalizedBell (Γ := Γ) (G := G) K)‖ = 1 := by
  have h : ‖WithLp.toLp 2 (regularGraphNormalizedBell (Γ := Γ) (G := G) K)‖ ^ 2 = 1 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm,
      WithLp.ofLp_toLp, regularGraphNormalizedBell_dotProduct]
    rfl
  nlinarith [norm_nonneg (WithLp.toLp 2 (regularGraphNormalizedBell (Γ := Γ) (G := G) K))]

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)
local notation "TG" => torusGraph width height
variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Regroup the complete coarse original physical registers and surplus
half-edge registers as the two tensor-product factors. -/
def twoByTwoOriginalOutputRegrouping :
    EuclideanSpace ℂ ((v : TV) → P × (IncidentEdge TG v → Unit → G)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((TV → P) × ((v : TV) → IncidentEdge TG v → Unit → G)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.arrowProdEquivProdArrow TV (fun _ => P) (fun v => IncidentEdge TG v → Unit → G))

/-- The complete positive scalar before state normalization, with one ratio
of site factors per block and one Bell normalization per coarse edge. -/
def twoByTwoOriginalScale (ca cb : TV → ℝ) : ℝ :=
  (∏ v, Real.sqrt (ca v) / Real.sqrt (cb v)) *
    Real.sqrt (Fintype.card (Unit → G) : ℝ) ^ Fintype.card (Edge TG)

omit [DecidableEq G] in
/-- All block and Bell normalization factors are strictly positive. -/
theorem twoByTwoOriginalScale_pos (ca cb : TV → ℝ)
    (ha : ∀ v, 0 < ca v) (hb : ∀ v, 0 < cb v) :
    0 < twoByTwoOriginalScale (G := G) ca cb := by
  apply mul_pos
  · exact Finset.prod_pos fun v _ => div_pos (Real.sqrt_pos.mpr (ha v)) (Real.sqrt_pos.mpr (hb v))
  · exact pow_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) _

omit [DecidableEq P] in
/-- Physical renormalization with the original homogeneous tensor on the
coarse lattice. The genuine fine support isometry is derived from the local
fine tensors and the original coarse tensor with surplus registers; neither
state nonvanishing nor any global factorization is assumed. The unnormalized
identity retains every positive scalar. After normalization it gives exactly
the normalized original coarse state tensored with unit Bell pairs.
Source: SCP10, Observation 6.6, lines 1888–1909.
Scope: identity bonds and coarse periods at least three. -/
theorem exists_regularTwoByTwoOriginalTensorIsometry
    (a : (Fin 4 → G) → P → ℂ)
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) :
    let ψ := WithLp.toLp 2 (twoByTwoFineState (width := width) (height := height) (fun _ => a))
    let χ := WithLp.toLp 2 (graphBondNetwork (torusIncidentFamily (fun _ : TV => a)))
    let ω := WithLp.toLp 2 (regularGraphNormalizedBell (Γ := TG) (G := G) Unit)
    ψ ≠ 0 ∧ χ ≠ 0 ∧ ‖ω‖ = 1 ∧
      ∃ ca cb : TV → ℝ, (∀ v, 0 < ca v) ∧ (∀ v, 0 < cb v) ∧
        ∃ F : (v : TV) → Matrix (P × (IncidentEdge TG v → Unit → G)) (Fin 4 → P) ℂ,
        ∃ I : twoByTwoFinePhysicalSupport (fun _ : FV => a) →ₗᵢ[ℂ]
          EuclideanSpace ℂ ((TV → P) × ((v : TV) → IncidentEdge TG v → Unit → G)),
          (∀ x σ, I x σ = graphPhysicalProductMap F
            (fun τ => x.val (twoByTwoPhysicalEquiv.symm τ)) (fun v => (σ.1 v, σ.2 v))) ∧
          I ⟨ψ, twoByTwoFineState_mem_physicalSupport (fun _ => a)⟩ =
            (twoByTwoOriginalScale (G := G) ca cb : ℂ) • physicalStateProduct χ ω ∧
          I ((‖ψ‖ : ℂ)⁻¹ • ⟨ψ, twoByTwoFineState_mem_physicalSupport (fun _ => a)⟩) =
            physicalStateProduct ((‖χ‖ : ℂ)⁻¹ • χ) ω := by
  classical
  dsimp only
  let A := torusIncidentFamily (fun _ : TV => a)
  let B := twoByTwoBundledGraphSite (fun _ : FV => a)
  let C := regularGraphSurplusSite Unit A
  have hA (v : TV) : IsGIsometric (regularLegRepresentation (IncidentEdge TG v))
      (regularSiteMap (A v)) := by
    rw [← graphIncidentRepresentation_leftRegularMatrix]
    exact ha.isGIsometric_torusIncidentFamily v
  obtain ⟨ca, cb, hca, hcb, F, J, hJ, hstate⟩ :=
    exists_graphGIsometricPhysicalSupportTransport
      (graphIncidentRepresentation (regularBundleMatrix Unit)) B C
      (isGIsometric_twoByTwoBundledGraphSite (fun _ => a) (fun _ => ha))
      (isGIsometric_regularGraphSurplusSite Unit A hA)
      (graphIncidentRepresentation_regularBundle_unitary Unit)
  let I := twoByTwoOriginalOutputRegrouping.toLinearIsometry.comp
    (J.comp (twoByTwoPhysicalSupportRegrouping (fun _ : FV => a)).toLinearIsometry)
  have hψ : WithLp.toLp 2 (twoByTwoFineState (width := width) (height := height)
      (fun _ => a)) ≠ 0 := by
    intro h
    apply ha.twoByTwoFineState_ne_zero (width := width) (height := height)
    exact congrArg WithLp.ofLp h
  have hχ : WithLp.toLp 2 (graphBondNetwork A) ≠ 0 := by
    intro h
    apply ha.graphBondNetwork_torusIncidentFamily_ne_zero (width := width) (height := height)
    exact congrArg WithLp.ofLp h
  have hω := norm_regularGraphNormalizedBell (Γ := TG) (G := G) Unit
  have hfactor : I ⟨WithLp.toLp 2 (twoByTwoFineState (fun _ : FV => a)),
        twoByTwoFineState_mem_physicalSupport (fun _ => a)⟩ =
      (twoByTwoOriginalScale (G := G) ca cb : ℂ) •
        physicalStateProduct (WithLp.toLp 2 (graphBondNetwork A))
          (WithLp.toLp 2 (regularGraphNormalizedBell (Γ := TG) (G := G) Unit)) := by
    have hgroup : twoByTwoPhysicalSupportRegrouping (fun _ : FV => a)
        ⟨WithLp.toLp 2 (twoByTwoFineState (fun _ => a)),
          twoByTwoFineState_mem_physicalSupport (fun _ => a)⟩ =
        ⟨WithLp.toLp 2 (graphBondNetwork B),
          graphBondNetwork_mem_euclideanRange_productSiteMap B⟩ := by
      apply Subtype.ext
      exact twoByTwoPhysicalRegroupingIsometry_fineState _
    change twoByTwoOriginalOutputRegrouping (J
      (twoByTwoPhysicalSupportRegrouping (fun _ : FV => a)
        ⟨WithLp.toLp 2 (twoByTwoFineState (fun _ => a)),
          twoByTwoFineState_mem_physicalSupport (fun _ => a)⟩)) = _
    rw [hgroup, hstate]
    apply WithLp.ofLp_injective 2
    funext σ
    change (∏ v, (Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) *
      graphBondNetwork C (fun v => (σ.1 v, σ.2 v)) = _
    rw [graphBondNetwork_regularGraphSurplusSite]
    simp only [physicalStateProduct, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, regularGraphNormalizedBell, twoByTwoOriginalScale,
      Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_div, Complex.ofReal_pow]
    have hs : (Real.sqrt (Fintype.card (Unit → G) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr Fintype.card_pos))
    have hcancel : (Real.sqrt (Fintype.card (Unit → G) : ℝ) : ℂ) ^
        Fintype.card (Edge TG) * (Real.sqrt (Fintype.card (Unit → G) : ℝ) : ℂ)⁻¹ ^
          Fintype.card (Edge TG) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hs, one_pow]
    calc
      _ = ((∏ v, (Real.sqrt (ca v) : ℂ) / (Real.sqrt (cb v) : ℂ)) *
          graphBondNetwork A σ.1 * regularGraphResidualBell Unit σ.2) *
        ((Real.sqrt (Fintype.card (Unit → G) : ℝ) : ℂ) ^ Fintype.card (Edge TG) *
          (Real.sqrt (Fintype.card (Unit → G) : ℝ) : ℂ)⁻¹ ^ Fintype.card (Edge TG)) := by
            rw [hcancel, mul_one, mul_assoc]
      _ = _ := by ring
  refine ⟨hψ, hχ, hω, ca, cb, hca, hcb, F, I, ?_, hfactor, ?_⟩
  · intro x σ
    exact congrFun (hJ (twoByTwoPhysicalSupportRegrouping (fun _ : FV => a) x))
      (fun v => (σ.1 v, σ.2 v))
  · exact LinearIsometry.normalized_physicalStateProduct I
      ⟨WithLp.toLp 2 (twoByTwoFineState (fun _ : FV => a)),
        twoByTwoFineState_mem_physicalSupport (fun _ => a)⟩
      (WithLp.toLp 2 (graphBondNetwork A))
      (WithLp.toLp 2 (regularGraphNormalizedBell (Γ := TG) (G := G) Unit))
      (twoByTwoOriginalScale_pos ca cb hca hcb) hω hfactor

end TNLean.PEPS
