/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTwoByTwoTwistedGeometry
import TNLean.PEPS.TorusInsertedRegularBundles
import TNLean.PEPS.RegularFourLegClosure
import TNLean.PEPS.RegularGraphInsertedOriginalTensor
import TNLean.PEPS.PhysicalStateCoherentNormalization
import TNLean.PEPS.RegularProjectorOpenRegion
import TNLean.PEPS.GInjectivePhysicalMap
import TNLean.PEPS.RegularTwoByTwoTwistedTensor

/-!
# Twisted two-by-two blocking with nonabelian, padded physical spaces

The regression uses permutations of three letters with genuinely distinct
inverse and product-order conventions. Native geometric blocking includes
positive periods one and two; graph support statements retain periods at least
three. Unused physical coordinates prevent accidental ambient surjectivity.
-/

noncomputable section
open TNLean.PEPS
open scoped BigOperators Matrix

namespace RegularTwoByTwoTwistedTensorTest

private abbrev S3 := Equiv.Perm (Fin 3)
private def swap01 : S3 := Equiv.swap 0 1
private def swap12 : S3 := Equiv.swap 1 2
private def cycle : S3 := swap01 * swap12
private abbrev PaddedS3 := (Fin 4 → S3) ⊕ Unit

-- These labels genuinely test noncommutative multiplication and inversion.
example : ¬ Commute swap01 swap12 := by
  change ¬ swap01 * swap12 = swap12 * swap01
  decide
example : cycle ≠ cycle⁻¹ := by decide
example : cycle⁻¹ = swap12 * swap01 := by decide

example : leftRegularMatrix S3 cycle cycle 1 = 1 := by
  simp [leftRegularMatrix_apply]

example : (leftRegularMatrix S3 cycle).transpose cycle 1 = 0 := by
  rw [Matrix.transpose_apply, leftRegularMatrix_apply, ite_eq_right]
  decide

-- Both paired labels carry the same left insertion, rather than its inverse.
example : pairedLeftRegularMatrix S3 cycle
    (cycle * swap01, cycle * swap12) (swap01, swap12) = 1 := by
  simp [pairedLeftRegularMatrix_apply]

example : pairedLeftRegularMatrix S3 cycle
    (cycle⁻¹ * swap01, cycle⁻¹ * swap12) (swap01, swap12) = 0 := by
  rw [pairedLeftRegularMatrix_apply, ite_eq_right]
  decide

-- Reversing endpoints really changes an order-three bundled insertion.
example : (regularBundleMatrix (G := S3) Unit cycle).transpose =
    regularBundleMatrix Unit (swap12 * swap01) := by
  rw [regularBundleMatrix_transpose]
  congr 1

-- Left-relative coordinates cancel the same arbitrary noncommuting translation.
example :
    (regularSurplusCoordinates Unit (Fin 4)
      (fun _ => (cycle * swap01, fun _ => cycle * swap12))).2 0 () =
        swap01⁻¹ * swap12 := by
  simp [regularSurplusCoordinates, mul_inv_rev, mul_assoc]

example : swap01⁻¹ * swap12 ≠ swap12 * swap01⁻¹ := by decide

private def extraPhysical {Y : Type*} [DecidableEq Y] : Matrix (Y ⊕ Unit) Y ℂ :=
  fun s η => match s with
    | Sum.inl σ => if σ = η then 1 else 0
    | Sum.inr _ => 0

private theorem extraPhysical_isIsometry {Y : Type*} [Fintype Y] [DecidableEq Y] :
    (extraPhysical (Y := Y)).IsIsometry := by
  ext η ξ
  simp [extraPhysical, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

private def paddedSite : (Fin 4 → S3) → PaddedS3 → ℂ :=
  regularPhysicalMapSite extraPhysical
    (fun η θ => regularLegProjector (Fin 4) θ η)

private theorem paddedSite_isGIsometric :
    IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap paddedSite) := by
  rw [paddedSite, regularSiteMap_regularPhysicalMapSite]
  exact isGIsometric_regularLegProjector.comp_isometry _ extraPhysical_isIsometry

example (η : Fin 4 → S3) : paddedSite η (Sum.inr ()) = 0 := by
  simp [paddedSite, regularPhysicalMapSite, extraPhysical]

example (α : Fin 4 → S3 × S3) :
    twoByTwoTensor (fun _ => paddedSite) α (fun _ => Sum.inr ()) = 0 := by
  simp [twoByTwoTensor, paddedSite, regularPhysicalMapSite, extraPhysical]

-- Native geometric regrouping covers a fine 2×2 torus and a fine 4×4 torus.
-- Neither statement may acquire the graph layer's period-at-least-three premise.
example (a : S3 → S3 → S3 → S3 → PaddedS3 → ℂ)
    (σ : TorusVertex 2 2 → PaddedS3) :
    torusGClosure (leftRegularMatrix S3) a swap01 swap12 σ =
      torusGClosure (pairedLeftRegularMatrix S3)
        (fun t r b l => twoByTwoTensor (fun _ α => a (α 0) (α 1) (α 2) (α 3))
          ![t, r, b, l]) swap01 swap12 (twoByTwoPhysicalEquiv (width := 1) (height := 1) σ) :=
  torusGClosure_leftRegular_eq_twoByTwoBlocked (width := 1) (height := 1) a _ _ σ

example (a : S3 → S3 → S3 → S3 → PaddedS3 → ℂ)
    (σ : TorusVertex 4 4 → PaddedS3) :
    torusGClosure (leftRegularMatrix S3) a cycle swap01 σ =
      torusGClosure (pairedLeftRegularMatrix S3)
        (fun t r b l => twoByTwoTensor (fun _ α => a (α 0) (α 1) (α 2) (α 3))
          ![t, r, b, l]) cycle swap01 (twoByTwoPhysicalEquiv (width := 2) (height := 2) σ) :=
  torusGClosure_leftRegular_eq_twoByTwoBlocked (width := 2) (height := 2) a _ _ σ

-- Even noncommuting closures of the padded native tensor are nonzero.
example : torusGClosure (width := 1) (height := 2) (leftRegularMatrix S3)
    (fun t r b l => paddedSite ![t, r, b, l]) swap01 swap12 ≠ 0 :=
  paddedSite_isGIsometric.regularFourLegClosure_ne_zero _ _

local instance : Fact (2 < 3) := ⟨by decide⟩
local instance : Fact (1 < 3) := ⟨by decide⟩

-- Periodic horizontal seams reverse the lexicographic graph orientation.
example : torusGraphRegularLabels
    (fun _ : TorusVertex 3 3 => cycle) (fun _ => swap01)
      (torusRightEdge (2, 0)) = cycle⁻¹ := by
  unfold torusGraphRegularLabels
  rw [show torusEdgeEquiv.symm (torusRightEdge (2, 0) : Edge (torusGraph 3 3)) =
    Sum.inl (2, 0) from torusEdgeEquiv.symm_apply_apply (Sum.inl (2, 0))]
  dsimp only
  rw [ite_eq_right]
  decide

-- The downward native vertical arrow reverses on ordinary, nonseam edges.
example : torusGraphRegularLabels
    (fun _ : TorusVertex 3 3 => swap01) (fun _ => cycle)
      (torusUpEdge (0, 0)) = cycle⁻¹ := by
  unfold torusGraphRegularLabels
  rw [show torusEdgeEquiv.symm (torusUpEdge (0, 0) : Edge (torusGraph 3 3)) =
    Sum.inr (0, 0) from torusEdgeEquiv.symm_apply_apply (Sum.inr (0, 0))]
  dsimp only
  rw [ite_eq_left]
  decide

-- At the periodic vertical seam that orientation reversal disappears.
example : torusGraphRegularLabels
    (fun _ : TorusVertex 3 3 => swap01) (fun _ => cycle)
      (torusUpEdge (0, 2)) = cycle := by
  unfold torusGraphRegularLabels
  rw [show torusEdgeEquiv.symm (torusUpEdge (0, 2) : Edge (torusGraph 3 3)) =
    Sum.inr (0, 2) from torusEdgeEquiv.symm_apply_apply (Sum.inr (0, 2))]
  dsimp only
  rw [ite_eq_right]
  decide

-- Every ordered insertion retains the original padded physical tensor.
example (u : Edge (torusGraph 3 3) → S3) (σ : TorusVertex 3 3 → PaddedS3)
    (τ : (v : TorusVertex 3 3) → IncidentEdge (torusGraph 3 3) v → Unit → S3) :
    graphInsertedBondNetwork (fun e => regularBundleMatrix Unit (u e))
        (regularGraphSurplusSite Unit
          (torusIncidentFamily (fun _ : TorusVertex 3 3 => paddedSite)))
          (fun v => (σ v, τ v)) =
      graphInsertedBondNetwork (fun e => leftRegularMatrix S3 (u e))
          (torusIncidentFamily (fun _ : TorusVertex 3 3 => paddedSite)) σ *
        regularGraphResidualBell Unit τ :=
  graphInsertedBondNetwork_regularGraphSurplusSite Unit _ u σ τ

private def fineClosure (g h : S3) :=
  twoByTwoSupportedClosure (width := 3) (height := 3) paddedSite g h

private def coarseClosure (g h : S3) :=
  WithLp.toLp 2 (torusGClosure (width := 3) (height := 3)
    (leftRegularMatrix S3) (fun t r b l => paddedSite ![t, r, b, l]) g h)

private def bell :=
  WithLp.toLp 2 (regularGraphNormalizedBell (Γ := torusGraph 3 3) (G := S3) Unit)

-- One choice of block matrices, positive factors, and support isometry works
-- simultaneously for every S₃ closure and every coherent superposition.
example :
    ‖bell‖ = 1 ∧
      ∃ ca cb : TorusVertex 3 3 → ℝ, (∀ v, 0 < ca v) ∧ (∀ v, 0 < cb v) ∧
        ∃ F : (v : TorusVertex 3 3) →
          Matrix (PaddedS3 × (IncidentEdge (torusGraph 3 3) v → Unit → S3))
            (Fin 4 → PaddedS3) ℂ,
        ∃ I : twoByTwoFinePhysicalSupport (width := 3) (height := 3)
          (fun _ : TorusVertex 6 6 => paddedSite) →ₗᵢ[ℂ]
          EuclideanSpace ℂ ((TorusVertex 3 3 → PaddedS3) ×
            ((v : TorusVertex 3 3) → IncidentEdge (torusGraph 3 3) v → Unit → S3)),
          (∀ x σ, I x σ = graphPhysicalProductMap F
            (fun τ => x.val (twoByTwoPhysicalEquiv.symm τ))
              (fun v => (σ.1 v, σ.2 v))) ∧
          (∀ g h, fineClosure g h ≠ 0 ∧ coarseClosure g h ≠ 0 ∧
            I (fineClosure g h) =
              (twoByTwoOriginalScale (G := S3) ca cb : ℂ) •
                physicalStateProduct (coarseClosure g h) bell ∧
            I ((‖fineClosure g h‖ : ℂ)⁻¹ • fineClosure g h) =
              physicalStateProduct ((‖coarseClosure g h‖ : ℂ)⁻¹ • coarseClosure g h) bell) ∧
          ∀ c : S3 × S3 → ℂ,
            let x := ∑ p, c p • fineClosure p.1 p.2
            let y := ∑ p, c p • coarseClosure p.1 p.2
            I x = (twoByTwoOriginalScale (G := S3) ca cb : ℂ) • physicalStateProduct y bell ∧
              (x ≠ 0 ↔ y ≠ 0) ∧
              I ((‖x‖ : ℂ)⁻¹ • x) = physicalStateProduct ((‖y‖ : ℂ)⁻¹ • y) bell :=
  exists_regularTwoByTwoTwistedTensorIsometry (width := 3) (height := 3)
    paddedSite paddedSite_isGIsometric

-- No ambient surjectivity assumption is needed for any twisted supported state.
example (g h : S3) :
    WithLp.toLp 2 (torusGClosure (width := 6) (height := 6) (leftRegularMatrix S3)
      (fun t r b l => paddedSite ![t, r, b, l]) g h) ∈
        twoByTwoFinePhysicalSupport (width := 3) (height := 3)
          (fun _ : TorusVertex 6 6 => paddedSite) :=
  twoByTwoFineClosure_mem_physicalSupport paddedSite g h

-- A genuinely non-real local phase, with the padded physical space retained.
private def phasePhysical : Matrix PaddedS3 PaddedS3 ℂ := Complex.I • 1

private theorem phasePhysical_isIsometry : phasePhysical.IsIsometry := by
  change phasePhysical.conjTranspose * phasePhysical = 1
  simp [phasePhysical, Matrix.conjTranspose_smul, smul_smul]

private def phaseSite : (Fin 4 → S3) → PaddedS3 → ℂ :=
  regularPhysicalMapSite phasePhysical paddedSite

private theorem phaseSite_isGIsometric :
    IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap phaseSite) := by
  rw [phaseSite, regularSiteMap_regularPhysicalMapSite]
  exact paddedSite_isGIsometric.comp_isometry _ phasePhysical_isIsometry

example (η : Fin 4 → S3) (s : PaddedS3) :
    phaseSite η s = Complex.I * paddedSite η s := by
  simp [phaseSite, regularPhysicalMapSite, phasePhysical, Matrix.one_apply]

example :
    ∃ I : twoByTwoFinePhysicalSupport (width := 3) (height := 3)
        (fun _ : TorusVertex 6 6 => phaseSite) →ₗᵢ[ℂ]
      EuclideanSpace ℂ ((TorusVertex 3 3 → PaddedS3) ×
        ((v : TorusVertex 3 3) → IncidentEdge (torusGraph 3 3) v → Unit → S3)),
      ∀ g h : S3,
        I ((‖twoByTwoSupportedClosure (width := 3) (height := 3) phaseSite g h‖ : ℂ)⁻¹ •
            twoByTwoSupportedClosure (width := 3) (height := 3) phaseSite g h) =
          physicalStateProduct
            ((‖WithLp.toLp 2 (torusGClosure (width := 3) (height := 3)
                (leftRegularMatrix S3) (fun t r b l => phaseSite ![t, r, b, l]) g h)‖ : ℂ)⁻¹ •
              WithLp.toLp 2 (torusGClosure (width := 3) (height := 3)
                (leftRegularMatrix S3) (fun t r b l => phaseSite ![t, r, b, l]) g h)) bell := by
  obtain ⟨_, _, _, _, _, _, I, _, hstates, _⟩ :=
    exists_regularTwoByTwoTwistedTensorIsometry (width := 3) (height := 3)
      phaseSite phaseSite_isGIsometric
  exact ⟨I, fun g h => (hstates g h).2.2.2⟩

-- Distinct commuting labels can represent the same sector; a coherent sum
-- with nonzero imaginary coefficients must cancel, on both actual tori.
private theorem native_conjugate_swap {w h : ℕ} [NeZero w] [NeZero h] :
    torusGClosure (width := w) (height := h) (leftRegularMatrix S3)
        (fun t r b l => paddedSite ![t, r, b, l]) swap12 1 =
      torusGClosure (leftRegularMatrix S3)
        (fun t r b l => paddedSite ![t, r, b, l]) swap01 1 := by
  have he : cycle * swap01 * cycle⁻¹ = swap12 := by decide
  funext σ
  simpa only [he, mul_one, mul_inv_cancel] using
    torusGClosure_conjugate (leftRegularMatrix S3)
      (fun t r b l => paddedSite ![t, r, b, l])
      paddedSite_isGIsometric.torusLegRep_of_regularFourLeg.invariant σ cycle swap01 1

private def cancellationCoefficients : S3 × S3 → ℂ :=
  Pi.single (swap01, 1) Complex.I - Pi.single (swap12, 1) Complex.I

example : cancellationCoefficients ≠ 0 := by
  intro hz
  have h := congrFun hz (swap01, 1)
  have hp : (swap01, (1 : S3)) ≠ (swap12, 1) := by decide
  simp [cancellationCoefficients, hp] at h

example : Commute swap01 (1 : S3) ∧ Commute swap12 (1 : S3) :=
  ⟨Commute.one_right _, Commute.one_right _⟩

example : (swap01, (1 : S3)) ≠ (swap12, 1) := by decide

example : (∑ p : S3 × S3, cancellationCoefficients p • fineClosure p.1 p.2) = 0 ∧
    (∑ p : S3 × S3, cancellationCoefficients p • coarseClosure p.1 p.2) = 0 := by
  have hf : fineClosure swap12 1 = fineClosure swap01 1 := by
    apply Subtype.ext
    exact congrArg (WithLp.toLp 2) native_conjugate_swap
  have hc : coarseClosure swap12 1 = coarseClosure swap01 1 :=
    congrArg (WithLp.toLp 2) native_conjugate_swap
  constructor
  · simp [cancellationCoefficients, Pi.single_apply, sub_smul, ite_smul,
      Finset.sum_sub_distrib, hf]
  · simp [cancellationCoefficients, Pi.single_apply, sub_smul, ite_smul,
      Finset.sum_sub_distrib, hc]

end RegularTwoByTwoTwistedTensorTest

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.torusBondNetwork_perm_eq_twoByTwoBlocked'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.torusBondNetwork_perm_eq_twoByTwoBlocked

/--
info: 'TNLean.PEPS.torusGClosure_leftRegular_eq_twoByTwoBlocked'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.torusGClosure_leftRegular_eq_twoByTwoBlocked

/--
info: 'TNLean.PEPS.graphInsertedBondNetwork_torusClosureRegularLabels'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.graphInsertedBondNetwork_torusClosureRegularLabels

/--
info: 'TNLean.PEPS.torusGClosure_leftRegular_eq_twoByTwoBundledGraphSite'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.torusGClosure_leftRegular_eq_twoByTwoBundledGraphSite

/--
info: 'TNLean.PEPS.graphInsertedBondNetwork_mem_euclideanRange_productSiteMap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.graphInsertedBondNetwork_mem_euclideanRange_productSiteMap

/--
info: 'TNLean.PEPS.exists_graphGIsometricInsertedPhysicalSupportTransport'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_graphGIsometricInsertedPhysicalSupportTransport

/--
info: 'TNLean.PEPS.graphInsertedBondNetwork_regularGraphSurplusSite'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.graphInsertedBondNetwork_regularGraphSurplusSite

/--
info: 'TNLean.PEPS.exists_regularGraphInsertedOriginalTensorIsometry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_regularGraphInsertedOriginalTensorIsometry

/--
info: 'TNLean.PEPS.IsGIsometric.regularFourLegClosure_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.regularFourLegClosure_ne_zero

/--
info: 'TNLean.PEPS.LinearIsometry.coherent_physicalStateProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.LinearIsometry.coherent_physicalStateProduct

/--
info: 'TNLean.PEPS.twoByTwoFineClosure_mem_physicalSupport'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.twoByTwoFineClosure_mem_physicalSupport

/--
info: 'TNLean.PEPS.exists_regularTwoByTwoTwistedTensorIsometry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_regularTwoByTwoTwistedTensorIsometry
