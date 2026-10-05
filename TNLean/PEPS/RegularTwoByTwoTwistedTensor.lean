/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusInsertedRegularBundles
import TNLean.PEPS.RegularGraphInsertedOriginalTensor
import TNLean.PEPS.RegularFourLegClosure
import TNLean.PEPS.PhysicalStateCoherentNormalization

/-!
# One two-by-two physical isometry for all native torus closures

The original fine and coarse native closure states are related by one
block-local isometry on the complete physical support, chosen independently
of the closure labels. Every positive normalization factor is retained, and
the surplus state is the same unit Bell product for every closure. Thus the
same map transports arbitrary coherent sums, with their relative phases.

Source: SCP10, arXiv:1001.3807, Definition 5.6, Theorem 5.9 and Observation 6.6,
lines 1515–1525, 1582–1621 and 1888–1909. The geometric/support identity holds
for all closure pairs; its ground-state interpretation uses commuting pairs.
Both coarse periods are at least three. Small-period physical separation,
other boundary conditions and ambient-space unitary extension remain separate.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G P : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype P]
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)
local notation "TG" => torusGraph width height

/-- Every native fine closure lies in the same complete block physical support.
No closure-dependent restriction of that support is used.
Source: SCP10, Observations 6.4–6.6 and Definition 5.6. -/
theorem twoByTwoFineClosure_mem_physicalSupport
    (a : (Fin 4 → G) → P → ℂ) (g h : G) :
    WithLp.toLp 2 (torusGClosure (width := width * 2) (height := height * 2)
      (leftRegularMatrix G) (fun t r d l => a ![t, r, d, l]) g h) ∈
        twoByTwoFinePhysicalSupport (fun _ : FV => a) := by
  classical
  change twoByTwoPhysicalRegroupingIsometry (width := width) (height := height)
      (WithLp.toLp 2 (torusGClosure (width := width * 2) (height := height * 2)
        (leftRegularMatrix G) (fun t r d l => a ![t, r, d, l]) g h)) ∈
    (Matrix.toEuclideanLin (LinearMap.toMatrix' (graphPhysicalProductMap
      (fun v s η => twoByTwoBundledGraphSite (fun _ : FV => a) v η s)))).range
  have heq : twoByTwoPhysicalRegroupingIsometry (width := width) (height := height)
      (WithLp.toLp 2 (torusGClosure (width := width * 2) (height := height * 2)
        (leftRegularMatrix G) (fun t r d l => a ![t, r, d, l]) g h)) =
      WithLp.toLp 2 (graphInsertedBondNetwork
        (fun e => regularBundleMatrix Unit (torusClosureRegularLabels g h e))
        (twoByTwoBundledGraphSite (fun _ : FV => a))) := by
    apply WithLp.ofLp_injective 2
    funext τ
    change torusGClosure (width := width * 2) (height := height * 2)
      (leftRegularMatrix G) (fun t r d l => a ![t, r, d, l]) g h (twoByTwoPhysicalEquiv.symm τ) = _
    rw [torusGClosure_leftRegular_eq_twoByTwoBundledGraphSite, Equiv.apply_symm_apply]
  rw [heq]
  exact graphInsertedBondNetwork_mem_euclideanRange_productSiteMap _ _

/-- The actual fine native closure, as an element of its fixed full physical
support. Source: SCP10, Definition 5.6 and Observation 6.6. -/
def twoByTwoSupportedClosure (a : (Fin 4 → G) → P → ℂ) (g h : G) :
    twoByTwoFinePhysicalSupport (fun _ : FV => a) :=
  ⟨WithLp.toLp 2 (torusGClosure (leftRegularMatrix G)
      (fun t r d l => a ![t, r, d, l]) g h),
    twoByTwoFineClosure_mem_physicalSupport a g h⟩

/-- Exact twisted fixed-point identity with one physical support map uniform
in the native closure labels. The map acts by physical grouping and local
matrices on every supported vector. Individual closure states are proved
nonzero. The same map and positive scale also transport all coherent sums;
restricting coefficients to commuting pairs gives their ground-state span.
Source: SCP10, Theorem 5.9 and Observation 6.6.
**Scope restriction (native periodic support):** regular homogeneous tensors,
native periodic seams, and coarse periods at least three. See
`docs/paper-gaps/scp10_twisted_two_by_two_regular_fixed_point.tex`. -/
theorem exists_regularTwoByTwoTwistedTensorIsometry
    (a : (Fin 4 → G) → P → ℂ)
    (ha : IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap a)) :
    let χ := fun g h => WithLp.toLp 2 (torusGClosure (width := width) (height := height)
      (leftRegularMatrix G) (fun t r d l => a ![t, r, d, l]) g h)
    let ω := WithLp.toLp 2 (regularGraphNormalizedBell (Γ := TG) (G := G) Unit)
    ‖ω‖ = 1 ∧
      ∃ ca cb : TV → ℝ, (∀ v, 0 < ca v) ∧ (∀ v, 0 < cb v) ∧
        ∃ F : (v : TV) → Matrix (P × (IncidentEdge TG v → Unit → G)) (Fin 4 → P) ℂ,
        ∃ I : twoByTwoFinePhysicalSupport (fun _ : FV => a) →ₗᵢ[ℂ]
          EuclideanSpace ℂ ((TV → P) × ((v : TV) → IncidentEdge TG v → Unit → G)),
          (∀ x σ, I x σ = graphPhysicalProductMap F
            (fun τ => x.val (twoByTwoPhysicalEquiv.symm τ)) (fun v => (σ.1 v, σ.2 v))) ∧
          (∀ g h, twoByTwoSupportedClosure (width := width) (height := height) a g h ≠ 0 ∧
            χ g h ≠ 0 ∧
            I (twoByTwoSupportedClosure (width := width) (height := height) a g h) =
              (twoByTwoOriginalScale (G := G) ca cb : ℂ) • physicalStateProduct (χ g h) ω ∧
            I ((‖twoByTwoSupportedClosure (width := width) (height := height) a g h‖ : ℂ)⁻¹ •
                twoByTwoSupportedClosure (width := width) (height := height) a g h) =
              physicalStateProduct ((‖χ g h‖ : ℂ)⁻¹ • χ g h) ω) ∧
          ∀ c : G × G → ℂ,
            let x := ∑ p, c p •
              twoByTwoSupportedClosure (width := width) (height := height) a p.1 p.2
            let y := ∑ p, c p • χ p.1 p.2
            I x = (twoByTwoOriginalScale (G := G) ca cb : ℂ) • physicalStateProduct y ω ∧
              (x ≠ 0 ↔ y ≠ 0) ∧
              I ((‖x‖ : ℂ)⁻¹ • x) = physicalStateProduct ((‖y‖ : ℂ)⁻¹ • y) ω := by
  classical
  dsimp only
  let A := torusIncidentFamily (fun _ : TV => a)
  let B := twoByTwoBundledGraphSite (fun _ : FV => a)
  have hA (v : TV) : IsGIsometric (regularLegRepresentation (IncidentEdge TG v))
      (regularSiteMap (A v)) := by
    rw [← graphIncidentRepresentation_leftRegularMatrix]
    exact ha.isGIsometric_torusIncidentFamily v
  obtain ⟨ca, cb, hca, hcb, F, J, hJ, hstate⟩ :=
    exists_regularGraphInsertedOriginalTensorIsometry Unit A B hA
      (isGIsometric_twoByTwoBundledGraphSite (fun _ => a) (fun _ => ha))
  let I := J.comp (twoByTwoPhysicalSupportRegrouping (fun _ : FV => a)).toLinearIsometry
  have hfactor (g h : G) : I (twoByTwoSupportedClosure (width := width) (height := height) a g h) =
      (twoByTwoOriginalScale (G := G) ca cb : ℂ) • physicalStateProduct
        (WithLp.toLp 2 (torusGClosure (width := width) (height := height)
          (leftRegularMatrix G) (fun t r d l => a ![t, r, d, l]) g h))
        (WithLp.toLp 2 (regularGraphNormalizedBell (Γ := TG) (G := G) Unit)) := by
    have hgroup : twoByTwoPhysicalSupportRegrouping (fun _ : FV => a)
        (twoByTwoSupportedClosure (width := width) (height := height) a g h) =
        ⟨WithLp.toLp 2 (graphInsertedBondNetwork
            (fun e => regularBundleMatrix Unit (torusClosureRegularLabels g h e)) B),
          graphInsertedBondNetwork_mem_euclideanRange_productSiteMap _ B⟩ := by
      apply Subtype.ext
      apply WithLp.ofLp_injective 2
      funext τ
      change torusGClosure (width := width * 2) (height := height * 2)
        (leftRegularMatrix G) (fun t r d l => a ![t, r, d, l]) g h
          (twoByTwoPhysicalEquiv.symm τ) = _
      rw [torusGClosure_leftRegular_eq_twoByTwoBundledGraphSite, Equiv.apply_symm_apply]
    change J (twoByTwoPhysicalSupportRegrouping _ _) = _
    rw [hgroup, hstate]
    congr 2
    apply WithLp.ofLp_injective 2
    funext σ
    exact graphInsertedBondNetwork_torusClosureRegularLabels a g h σ
  have hω := norm_regularGraphNormalizedBell (Γ := TG) (G := G) Unit
  refine ⟨hω, ca, cb, hca, hcb, F, I, ?_, ?_, ?_⟩
  · intro x σ
    exact hJ (twoByTwoPhysicalSupportRegrouping (fun _ : FV => a) x) σ
  · intro g h
    have hfine : twoByTwoSupportedClosure (width := width) (height := height) a g h ≠ 0 := by
      intro hz
      apply ha.regularFourLegClosure_ne_zero (width := width * 2) (height := height * 2) g h
      exact congrArg (fun x => WithLp.ofLp x.val) hz
    have hcoarse : WithLp.toLp 2 (torusGClosure (width := width) (height := height)
        (leftRegularMatrix G) (fun t r d l => a ![t, r, d, l]) g h) ≠ 0 := by
      intro hz
      exact ha.regularFourLegClosure_ne_zero g h (congrArg WithLp.ofLp hz)
    exact ⟨hfine, hcoarse, hfactor g h,
      LinearIsometry.normalized_physicalStateProduct I _ _ _
        (twoByTwoOriginalScale_pos ca cb hca hcb) hω (hfactor g h)⟩
  · intro c
    exact LinearIsometry.coherent_physicalStateProduct I
      (fun p : G × G => twoByTwoSupportedClosure (width := width) (height := height) a p.1 p.2) _ _
      (twoByTwoOriginalScale_pos ca cb hca hcb) hω (fun p => hfactor p.1 p.2) c

end TNLean.PEPS
