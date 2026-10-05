/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoByTwoGraphCoordinates
import TNLean.PEPS.TwoByTwoTensorIsometry

/-!
# Physical two-by-two regular PEPS reblocking on the actual torus

Fine-site G-isometry implies G-isometry of the literal four-site contraction.
The actual fine bond sum becomes the paired coarse graph contraction by the
proved geometric bijections. Its physical support isometry then separates the
single-regular-bond coarse PEPS and one normalized Bell pair per coarse edge.
The original four physical registers are retained throughout, and physical
support membership is derived from the actual contraction.

Source: SCP10, arXiv:1001.3807, Observations 6.5–6.6, lines 1818–1915.
The factorization here uses a coarse simple graph, so both coarse periods are
at least three. The geometric reblocking itself applies to all positive
periods, but the physical Bell separation at periods one and two requires
extending the graph support argument to a bond-indexed model.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "FV" => TorusVertex (width * 2) (height * 2)
local notation "TG" => torusGraph width height
variable {G P : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype P] [DecidableEq P]

omit [DecidableEq P] in
/-- G-isometry of the actual bundled coarse graph tensor follows only from
fine-site G-isometry. Source: SCP10, Observations 6.5–6.6, lines 1875–1906. -/
theorem isGIsometric_twoByTwoBundledGraphSite
    (a : FV → (Fin 4 → G) → P → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap (a v)))
    (v : TV) :
    IsGIsometric (graphIncidentRepresentation (regularBundleMatrix Unit) v)
      (regularSiteMap (twoByTwoBundledGraphSite a v)) := by
  have h := isGIsometric_twoByTwoSeparatedTensor
    (fun i => a (kitaevPeriodicTilingEquiv (v, i)))
    (fun i => ha (kitaevPeriodicTilingEquiv (v, i)))
  refine h.of_coordinateEquiv (twoByTwoIncidentBoundaryEquiv v)
    (Equiv.refl (Fin 4 → P)) (twoByTwoIncidentBoundaryEquiv_rep v) ?_
  intro x
  exact regularSiteMap_twoByTwoBundledGraphSite a v x

/-- The physical regrouping as a full Hilbert-space unitary.
Source: SCP10, two-by-two physical grouping in lines 1888–1906. -/
def twoByTwoPhysicalRegroupingIsometry :
    EuclideanSpace ℂ (FV → P) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (TV → Fin 4 → P) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ twoByTwoPhysicalEquiv

omit [Fact (2 < width)] [Fact (2 < height)] [DecidableEq P] in
/-- The physical regrouping merely reads the original coefficient under the
inverse physical label bijection. Source: SCP10, lines 1888–1906. -/
theorem twoByTwoPhysicalRegroupingIsometry_apply
    (ψ : EuclideanSpace ℂ (FV → P)) (τ : TV → Fin 4 → P) :
    twoByTwoPhysicalRegroupingIsometry ψ τ = ψ (twoByTwoPhysicalEquiv.symm τ) := rfl

/-- The original fine PEPS, defined by its full native torus contraction.
Source: SCP10, the original state in Observation 6.6, lines 1888–1906. -/
def twoByTwoFineState (a : FV → (Fin 4 → G) → P → ℂ) : (FV → P) → ℂ :=
  fun σ => torusBondNetwork (fun v c => a v ![c.1, c.2.1, c.2.2.1, c.2.2.2] (σ v)) 1 1

omit [Group G] [DecidableEq P] in
/-- The full physical unitary gives exactly the actual bundled coarse state.
Source: SCP10, geometric step of Observation 6.6. -/
theorem twoByTwoPhysicalRegroupingIsometry_fineState
    (a : FV → (Fin 4 → G) → P → ℂ) :
    twoByTwoPhysicalRegroupingIsometry (WithLp.toLp 2 (twoByTwoFineState a)) =
      WithLp.toLp 2 (graphBondNetwork (twoByTwoBundledGraphSite a)) := by
  apply WithLp.ofLp_injective 2
  funext τ
  change twoByTwoFineState a (twoByTwoPhysicalEquiv.symm τ) = _
  rw [twoByTwoFineState, torusBondNetwork_eq_twoByTwoBundledGraphSite,
    Equiv.apply_symm_apply]

/-- The product of actual four-site physical ranges, expressed back on the
fine Hilbert space by the inverse physical grouping. It retains all support
directions and makes no assertion about unused ambient directions.
Source: SCP10, physical support restriction in Observations 6.4–6.6. -/
def twoByTwoFinePhysicalSupport (a : FV → (Fin 4 → G) → P → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (FV → P)) :=
  (Matrix.toEuclideanLin (LinearMap.toMatrix' (graphPhysicalProductMap
    (fun v s η => twoByTwoBundledGraphSite a v η s)))).range.comap
      twoByTwoPhysicalRegroupingIsometry.toLinearEquiv.toLinearMap

omit [Group G] [DecidableEq P] in
/-- The actual fine state belongs to the derived physical support.
Source: SCP10, Observations 6.4–6.6. -/
theorem twoByTwoFineState_mem_physicalSupport (a : FV → (Fin 4 → G) → P → ℂ) :
    WithLp.toLp 2 (twoByTwoFineState a) ∈ twoByTwoFinePhysicalSupport a := by
  change twoByTwoPhysicalRegroupingIsometry (WithLp.toLp 2 (twoByTwoFineState a)) ∈
    (Matrix.toEuclideanLin (LinearMap.toMatrix' (graphPhysicalProductMap
      (fun v s η => twoByTwoBundledGraphSite a v η s)))).range
  rw [twoByTwoPhysicalRegroupingIsometry_fineState]
  exact graphBondNetwork_mem_euclideanRange_productSiteMap _

/-- Grouping the physical registers restricts to an isometric equivalence of
the fine support and the actual product block support. -/
def twoByTwoPhysicalSupportRegrouping (a : FV → (Fin 4 → G) → P → ℂ) :
    twoByTwoFinePhysicalSupport a ≃ₗᵢ[ℂ]
      (Matrix.toEuclideanLin (LinearMap.toMatrix' (graphPhysicalProductMap
        (fun v s η => twoByTwoBundledGraphSite a v η s)))).range :=
  { twoByTwoPhysicalRegroupingIsometry.toLinearEquiv.ofSubmodule' _ with
    norm_map' x := twoByTwoPhysicalRegroupingIsometry.norm_map x.val }

/-- The actual fine PEPS is mapped, by a derived Hilbert-space isometry on
its physical support, to the canonical coarse regular PEPS times one normalized
Bell pair per coarse edge. The isometry acts by physical grouping followed by
local normalized block adjoints and local relative-coordinate permutations.
Every positive block factor and Bell normalization is explicit. No global
factorization, block Gram identity, or state-support premise is supplied.
Source: SCP10, Observations 6.5–6.6, lines 1875–1909.

The coarse canonical site is support-isometrically equivalent to any original
four-leg regular G-isometric site by `IsGIsometric.exists_torusCanonicalSupportEquiv`.
Both coarse periods are at least three. -/
theorem exists_regularTwoByTwoPhysicalSupportIsometry
    (a : FV → (Fin 4 → G) → P → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap (a v))) :
    ∃ c : TV → ℝ, (∀ v, 0 < c v) ∧
      ∃ I : twoByTwoFinePhysicalSupport a →ₗᵢ[ℂ]
        EuclideanSpace ℂ (((v : TV) → IncidentEdge TG v → G) ×
          ((v : TV) → IncidentEdge TG v → (Unit → G))),
        (∀ x, (I x).ofLp = regularGraphPhysicalDisentangler Unit
          (twoByTwoBundledGraphSite a) c
            (fun τ => x.val (twoByTwoPhysicalEquiv.symm τ))) ∧
        I ⟨WithLp.toLp 2 (twoByTwoFineState a), twoByTwoFineState_mem_physicalSupport a⟩ =
          WithLp.toLp 2 (fun σ => (∏ v, (Real.sqrt (c v) : ℂ)) *
            (Real.sqrt (Fintype.card (Unit → G) : ℝ) : ℂ) ^ Fintype.card (Edge TG) *
              graphBondNetwork (graphAveragingSite (leftRegularMatrix G)) σ.1 *
                regularGraphNormalizedBell Unit σ.2) := by
  obtain ⟨c, hc, I, hI, hstate⟩ := exists_regularGraphPhysicalSupportIsometry Unit
    (twoByTwoBundledGraphSite a) (isGIsometric_twoByTwoBundledGraphSite a ha)
  refine ⟨c, hc, I.comp (twoByTwoPhysicalSupportRegrouping a).toLinearIsometry, ?_, ?_⟩
  · intro x
    exact hI (twoByTwoPhysicalSupportRegrouping a x)
  · change I (twoByTwoPhysicalSupportRegrouping a
      ⟨WithLp.toLp 2 (twoByTwoFineState a), twoByTwoFineState_mem_physicalSupport a⟩) = _
    rw [← hstate]
    congr 1
    apply Subtype.ext
    exact twoByTwoPhysicalRegroupingIsometry_fineState a

end TNLean.PEPS
