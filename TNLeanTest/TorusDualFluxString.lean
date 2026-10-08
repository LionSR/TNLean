/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualFluxString
import TNLean.PEPS.TorusDualWinding
import TNLean.PEPS.TorusDualFluxDetection
import TNLean.PEPS.RegularFourLegClosure
import TNLean.PEPS.RegularProjectorOpenRegion

/-!
# Regression checks for actual dual flux strings

These tests retain native bond labels at seams and on width-two tori. The
nonabelian examples use a three-cycle in S₃ together with a noncommuting
transposition. The C₃ example distinguishes inverse conjugacy classes, hence
checks the clockwise source convention against the counterclockwise detector.
The physical homotopy is instantiated with the canonical regular projector.
-/

namespace TNLeanTest.TorusDualFluxString

open TNLean.PEPS
open scoped BigOperators Matrix ComplexOrder

local instance : Quiver (TorusVertex 3 3) := torusDualQuiver 3 3
local instance : Fact (2 < 3) := ⟨by decide⟩

/-- An order-three permutation, so inverse labels cannot disappear as involutions. -/
def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- A second label which does not commute with the flux generator. -/
def transposition : Equiv.Perm (Fin 3) := Equiv.swap 0 1

example : cycle ^ 3 = 1 := by decide
example : cycle ≠ 1 := by decide
example : cycle ≠ cycle⁻¹ := by decide
example : cycle * transposition ≠ transposition * cycle := by decide

/-- An eastward dual segment crosses the downward bond on its right. -/
def eastPath : TorusDualPath ((0, 0) : TorusVertex 3 3) (1, 0) :=
  Quiver.Path.nil.cons (TorusDualStep.east 0 0)

/-- The reverse segment retains that same bond, with opposite exponent. -/
def westPath : TorusDualPath ((1, 0) : TorusVertex 3 3) (0, 0) :=
  Quiver.Path.nil.cons (TorusDualStep.west 0 0)

/-- A northward segment crosses the rightward bond above it. -/
def northPath : TorusDualPath ((0, 0) : TorusVertex 3 3) (0, 1) :=
  Quiver.Path.nil.cons (TorusDualStep.north 0 0)

/-- A southward segment has an inverse rightward-native insertion. -/
def southPath : TorusDualPath ((0, 1) : TorusVertex 3 3) (0, 0) :=
  Quiver.Path.nil.cons (TorusDualStep.south 0 0)

example : (torusDualFluxLabels cycle eastPath).2 (1, 0) = cycle := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, eastPath, TorusDualStep.crossings,
    torusPointMass]

example : (torusDualFluxLabels cycle westPath).2 (1, 0) = cycle⁻¹ := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, westPath, TorusDualStep.crossings,
    torusPointMass]

example : (torusDualFluxLabels cycle northPath).1 (0, 1) = cycle := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, northPath, TorusDualStep.crossings,
    torusPointMass]

example : (torusDualFluxLabels cycle southPath).1 (0, 1) = cycle⁻¹ := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, southPath, TorusDualStep.crossings,
    torusPointMass]

example : (torusDualFluxLabels cycle eastPath).1 = 1 ∧
    (torusDualFluxLabels cycle northPath).2 = 1 := by
  constructor <;> funext v <;>
    simp [torusDualFluxLabels, torusFluxPowerLabels, eastPath, northPath,
      TorusDualStep.crossings]

/-- The periodic seam is a real bond labelled at its native base vertex. -/
def seamPrefix : TorusDualPath ((2, 0) : TorusVertex 3 3) (0, 0) :=
  Quiver.Path.nil.cons (TorusDualStep.east 2 0)

example : (torusDualFluxLabels cycle seamPrefix).2 (0, 0) = cycle := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, seamPrefix, TorusDualStep.crossings,
    torusPointMass, show (2 : ZMod 3) + 1 = 0 by decide]

example : (torusDualFluxLabels cycle seamPrefix).2 (2, 0) = 1 := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, seamPrefix, TorusDualStep.crossings,
    torusPointMass]

/-- Upward seam crossing inserts on the native rightward bond at height zero. -/
def northSeam : TorusDualPath ((0, 2) : TorusVertex 3 3) (0, 0) :=
  Quiver.Path.nil.cons (TorusDualStep.north 0 2)

example : (torusDualFluxLabels cycle northSeam).1 (0, 0) = cycle := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, northSeam, TorusDualStep.crossings,
    torusPointMass, show (2 : ZMod 3) + 1 = 0 by decide]

/-- The crossed vertical native bond wraps from the last row to the first. -/
def verticalSeamInsertion : TorusDualPath ((0, 2) : TorusVertex 3 3) (1, 2) :=
  Quiver.Path.nil.cons (TorusDualStep.east 0 2)

/-- The ordered graph encoding still transports the inverse downward label upward. -/
example : torusNativeUpTransport
      (torusGraphRegularLabels (torusDualFluxLabels cycle verticalSeamInsertion).1
        (torusDualFluxLabels cycle verticalSeamInsertion).2) (1, 2) = cycle⁻¹ := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, verticalSeamInsertion,
    TorusDualStep.crossings, torusPointMass]

/-- The crossed horizontal native bond wraps from the last column to the first. -/
def horizontalSeamInsertion : TorusDualPath ((2, 0) : TorusVertex 3 3) (2, 1) :=
  Quiver.Path.nil.cons (TorusDualStep.north 2 0)

example : torusNativeRightTransport
      (torusGraphRegularLabels (torusDualFluxLabels cycle horizontalSeamInsertion).1
        (torusDualFluxLabels cycle horizontalSeamInsertion).2) (2, 1) = cycle := by
  simp [torusDualFluxLabels, torusFluxPowerLabels, horizontalSeamInsertion,
    TorusDualStep.crossings, torusPointMass]

/-- A nonempty suffix makes the square move genuinely internal to a longer string. -/
def northSuffix : TorusDualPath ((1, 1) : TorusVertex 3 3) (1, 2) :=
  Quiver.Path.nil.cons (TorusDualStep.north 1 1)

/-- Seam crossing, the east-north corner, and a further northward step. -/
def detourEN : TorusDualPath ((2, 0) : TorusVertex 3 3) (1, 2) :=
  (seamPrefix.comp (torusDualEastNorth 0 0)).comp northSuffix

/-- The same longer string with only its internal corner changed. -/
def detourNE : TorusDualPath ((2, 0) : TorusVertex 3 3) (1, 2) :=
  (seamPrefix.comp (torusDualNorthEast 0 0)).comp northSuffix

/-- Both untouched parts survive a square move supported at one primal vertex. -/
theorem detour_homotopy :
    TorusDualHomotopy {(1, 1)} detourEN detourNE :=
  .comp (.comp (.refl seamPrefix) (.square 0 0 (by simp))) (.refl northSuffix)

/-- Only the endpoints of the longer nonabelian string have clockwise flux. -/
theorem s3_detour_endpoint_holonomies :
    torusBondPlaquetteHolonomy (torusDualFluxLabels cycle detourEN) (2, 0) = cycle ∧
    torusBondPlaquetteHolonomy (torusDualFluxLabels cycle detourEN) (1, 2) = cycle⁻¹ ∧
    torusBondPlaquetteHolonomy (torusDualFluxLabels cycle detourEN) (0, 0) = 1 := by
  refine ⟨torusBondPlaquetteHolonomy_torusDualFluxLabels_source cycle detourEN (by decide),
    torusBondPlaquetteHolonomy_torusDualFluxLabels_target cycle detourEN (by decide), ?_⟩
  exact torusBondPlaquetteHolonomy_torusDualFluxLabels_of_ne cycle detourEN _
    (by decide) (by decide)

example : torusDualPathCrossings detourNE = torusDualPathCrossings detourEN +
    torusFluxGradient (torusPointMass (1, 1)) := by
  simp only [detourNE, detourEN, TorusDualPath.crossings_comp,
    torusDualSquare_crossings]
  abel_nf

example : torusDualFluxLabels cycle (eastPath.comp westPath) = (1, 1) := by
  ext v <;>
    simp [torusDualFluxLabels, torusFluxPowerLabels, eastPath, westPath,
      TorusDualStep.crossings]

example : torusDualFluxLabels cycle (northPath.comp southPath) = (1, 1) := by
  ext v <;>
    simp [torusDualFluxLabels, torusFluxPowerLabels, northPath, southPath,
      TorusDualStep.crossings]

/-- Closed strings have no endpoint curl, including strings with torus winding. -/
example {w h : ℕ} {v : TorusVertex w h} (p : TorusDualPath v v)
    (q : TorusVertex w h) : torusFluxCurl (torusDualPathCrossings p) q = 0 := by
  rw [p.fluxCurl, sub_self]

/-- A full eastward winding closes on the torus but moves three units in the cover. -/
def eastWinding : TorusDualPath ((0, 0) : TorusVertex 3 3) (0, 0) :=
  ((Quiver.Path.nil.cons (TorusDualStep.east 0 0)).cons
    (TorusDualStep.east 1 0)).cons (TorusDualStep.east 2 0)

example : torusDualPathDisplacement eastWinding = (3, 0) := by decide

example (q : TorusVertex 3 3) :
    torusBondPlaquetteHolonomy (torusDualFluxLabels cycle eastWinding) q = 1 :=
  torusBondPlaquetteHolonomy_torusDualFluxLabels_loop cycle eastWinding q

/-- Equal torus endpoints alone do not give a permitted string deformation. -/
theorem eastWinding_not_homotopic_nil (R : Set (TorusVertex 3 3)) :
    ¬ TorusDualHomotopy R eastWinding .nil := by
  intro h
  have hbad : (3 : ℤ) = 0 := by
    simpa [eastWinding, torusDualPathDisplacement, TorusDualStep.displacement] using
      congrArg Prod.fst h.displacement_eq
  omega

example : TorusDualHomotopy {(1, 1)} detourEN.reverse detourNE.reverse :=
  detour_homotopy.reverse

example : TorusDualHomotopy {(1, 1)}
    (torusDualSquareLoop (0 : ZMod 3) (0 : ZMod 3)) .nil :=
  .squareLoop _ 0 0 (by simp)

section WidthTwo

local instance : Quiver (TorusVertex 2 3) := torusDualQuiver 2 3

/-- Going twice east on a width-two torus crosses two different parallel bonds. -/
def widthTwoWinding : TorusDualPath ((0, 0) : TorusVertex 2 3) (0, 0) :=
  (Quiver.Path.nil.cons (TorusDualStep.east 0 0)).cons (TorusDualStep.east 1 0)

example : (torusDualPathCrossings widthTwoWinding).2 (0, 0) = 1 ∧
    (torusDualPathCrossings widthTwoWinding).2 (1, 0) = 1 := by decide

example : (torusDualPathCrossings (widthTwoWinding.comp widthTwoWinding)).2 (0, 0) = 2 ∧
    (torusDualPathCrossings (widthTwoWinding.comp widthTwoWinding)).2 (1, 0) = 2 := by decide

example : (torusDualFluxLabels cycle widthTwoWinding).2 (0, 0) = cycle ∧
    (torusDualFluxLabels cycle widthTwoWinding).2 (1, 0) = cycle := by
  constructor <;> change cycle ^ (1 : ℤ) = cycle <;> simp

example (q : TorusVertex 2 3) :
    torusFluxCurl (torusDualPathCrossings widthTwoWinding) q = 0 := by
  rw [widthTwoWinding.fluxCurl, sub_self]

end WidthTwo

/-- The abelian order-three generator has a genuinely different inverse class. -/
def c3Generator : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1

example : c3Generator ^ 3 = 1 := by decide
example : c3Generator ≠ c3Generator⁻¹ := by decide

/-- S₃ alone cannot catch an inverse-class error, because it is ambivalent. -/
theorem c3_inverse_class_ne :
    ConjClasses.mk c3Generator ≠ ConjClasses.mk c3Generator⁻¹ := by
  rw [ne_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq]
  decide

/-- The source clockwise holonomy is the generator, not its inverse. -/
theorem c3_clockwise_source :
    torusBondPlaquetteHolonomy (torusDualFluxLabels c3Generator eastPath) (0, 0) =
      c3Generator := by
  simp [torusBondPlaquetteHolonomy, torusDualFluxLabels, torusFluxPowerLabels,
    eastPath, TorusDualStep.crossings, torusPointMass]

/-- The detector's counterclockwise walk therefore has the inverse class. -/
theorem c3_detector_source :
    regularWalkHolonomy
      (torusGraphRegularLabels (torusDualFluxLabels c3Generator eastPath).1
        (torusDualFluxLabels c3Generator eastPath).2)
      (torusPlaquetteWalk ((0, 0) : TorusVertex 3 3)) = c3Generator⁻¹ := by
  rw [regularWalkHolonomy_torusGraphRegularLabels, c3_clockwise_source]

example : ConjClasses.mk (regularWalkHolonomy
      (torusGraphRegularLabels (torusDualFluxLabels c3Generator eastPath).1
        (torusDualFluxLabels c3Generator eastPath).2)
      (torusPlaquetteWalk ((0, 0) : TorusVertex 3 3))) ≠
    ConjClasses.mk c3Generator := by
  rw [c3_detector_source]
  exact c3_inverse_class_ne.symm

noncomputable section

/-- An actual regular G-isometric tensor, in native top-right-down-left coordinates. -/
def projectorSite (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (t r b l : G) (s : Fin 4 → G) : ℂ :=
  regularLegProjector (Fin 4) s ![t, r, b, l]

/-- The physical test uses the existing canonical projector, with no tensor assumption. -/
theorem projectorSite_isGIsometric (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap (projectorSite G)) :=
  isGIsometric_regularLegProjector.torusLegRep_of_regularFourLeg

/-- The same concrete tensor with its finite physical alphabet enumerated. -/
def projectorSiteFin (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (t r b l : G) (s : Fin (Fintype.card (Fin 4 → G))) : ℂ :=
  projectorSite G t r b l ((Fintype.equivFin (Fin 4 → G)).symm s)

/-- Physical basis enumeration preserves the established regular isometry. -/
theorem projectorSiteFin_isGIsometric (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap (projectorSiteFin G)) := by
  refine (projectorSite_isGIsometric G).of_coordinateEquiv (Equiv.refl _)
    (Fintype.equivFin (Fin 4 → G)).symm (fun _ _ => rfl) ?_
  intro x
  funext s
  simp [siteMap_apply, projectorSiteFin]

/-- The actual C₃ inserted-state cut seen by the four-spin source detector. -/
def c3SourceCut :=
  torusBondRegularPhysicalCutMatrix (projectorSiteFin (Multiplicative (ZMod 3)))
    (torusDualFluxLabels c3Generator eastPath)
    (torusPlaquetteRegion ((0, 0) : TorusVertex 3 3))

/-- The concrete C₃ detector test acts on a nonzero physical state cut. -/
theorem c3SourceCut_ne_zero : c3SourceCut ≠ 0 := by
  have hA := projectorSiteFin_isGIsometric (Multiplicative (ZMod 3))
  exact hA.torusDualFlux_cutMatrix_ne_zero c3Generator eastPath _

/-- The counterclockwise detector selects the inverse class and rejects the clockwise
class on an actual C₃ projector PEPS. Inverse classes must not be identified. -/
theorem c3_counterclockwise_detector : ∃ Q : Option (ConjClasses (Multiplicative (ZMod 3))) →
      Matrix (RegionPhysicalConfig (d := Fintype.card (Fin 4 → Multiplicative (ZMod 3)))
        (torusPlaquetteRegion ((0, 0) : TorusVertex 3 3)))
        (RegionPhysicalConfig (d := Fintype.card (Fin 4 → Multiplicative (ZMod 3)))
          (torusPlaquetteRegion ((0, 0) : TorusVertex 3 3))) ℂ,
    (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
    (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
    (∑ C, Q C = 1) ∧
    Q (some (ConjClasses.mk c3Generator⁻¹)) * c3SourceCut = c3SourceCut ∧
    Q (some (ConjClasses.mk c3Generator)) * c3SourceCut = 0 := by
  have hA := projectorSiteFin_isGIsometric (Multiplicative (ZMod 3))
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ :=
    hA.exists_torusDualFlux_counterclockwise_cutMeasurement
      ((0, 0) : TorusVertex 3 3)
  refine ⟨Q, hQh, hQm, hQsum, ?_, ?_⟩
  · simpa [c3SourceCut, torusPointMass] using
      hQact c3Generator (0, 0) (1, 0) eastPath (some (ConjClasses.mk c3Generator⁻¹))
  · simpa [c3SourceCut, torusPointMass, c3_inverse_class_ne] using
      hQact c3Generator (0, 0) (1, 0) eastPath (some (ConjClasses.mk c3Generator))

/-- Relabelling the same physical measurement reverses the selected and rejected
C₃ outcomes, with no ambivalence assumption. -/
theorem c3_clockwise_detector : ∃ Q : Option (ConjClasses (Multiplicative (ZMod 3))) →
      Matrix (RegionPhysicalConfig (d := Fintype.card (Fin 4 → Multiplicative (ZMod 3)))
        (torusPlaquetteRegion ((0, 0) : TorusVertex 3 3)))
        (RegionPhysicalConfig (d := Fintype.card (Fin 4 → Multiplicative (ZMod 3)))
          (torusPlaquetteRegion ((0, 0) : TorusVertex 3 3))) ℂ,
    (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
    (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
    (∑ C, Q C = 1) ∧
    Q (some (ConjClasses.mk c3Generator)) * c3SourceCut = c3SourceCut ∧
    Q (some (ConjClasses.mk c3Generator⁻¹)) * c3SourceCut = 0 := by
  have hA := projectorSiteFin_isGIsometric (Multiplicative (ZMod 3))
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ :=
    hA.exists_torusDualFlux_clockwise_cutMeasurement
      ((0, 0) : TorusVertex 3 3)
  refine ⟨Q, hQh, hQm, hQsum, ?_, ?_⟩
  · simpa [c3SourceCut, torusPointMass] using
      hQact c3Generator (0, 0) (1, 0) eastPath (some (ConjClasses.mk c3Generator))
  · simpa [c3SourceCut, torusPointMass, c3_inverse_class_ne.symm] using
      hQact c3Generator (0, 0) (1, 0) eastPath (some (ConjClasses.mk c3Generator⁻¹))

example : conjClassesInvEquiv (Multiplicative (ZMod 3)) (ConjClasses.mk c3Generator) ≠
    ConjClasses.mk c3Generator := by
  simpa using c3_inverse_class_ne.symm

/-- An actual S₃ regular PEPS has identical coefficients after an internal square move. -/
theorem s3_detour_physical_eq (σ : TorusVertex 3 3 → Fin 4 → Equiv.Perm (Fin 3)) :
    torusBondNetwork
        (fun v c => projectorSite (Equiv.Perm (Fin 3)) c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v => leftRegularMatrix _ ((torusDualFluxLabels cycle detourNE).1 v))
        (fun v => leftRegularMatrix _ ((torusDualFluxLabels cycle detourNE).2 v)) =
      torusBondNetwork
        (fun v c => projectorSite (Equiv.Perm (Fin 3)) c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (fun v => leftRegularMatrix _ ((torusDualFluxLabels cycle detourEN).1 v))
        (fun v => leftRegularMatrix _ ((torusDualFluxLabels cycle detourEN).2 v)) := by
  exact detour_homotopy.torusBondNetwork_eq (leftRegularMatrix _)
    (fun _ => projectorSite _) (fun _ _ => (projectorSite_isGIsometric _).invariant) σ cycle

/-- A noncommuting fixed exterior insertion remains exactly the supplied matrix. -/
example : (torusFluxMatricesWithExterior (leftRegularMatrix (Equiv.Perm (Fin 3)))
      {(1, 1)} (fun _ => leftRegularMatrix _ transposition,
        fun _ => leftRegularMatrix _ transposition)
      (torusDualFluxLabels cycle detourEN)).1 (2, 2) = leftRegularMatrix _ transposition := by
  simp [torusFluxMatricesWithExterior, show (2 : ZMod 3) ≠ 1 by decide]

/-- A fixed noncommuting exterior can be carried through the actual S₃ contraction. -/
theorem s3_detour_with_exterior_physical_eq
    (σ : TorusVertex 3 3 → Fin 4 → Equiv.Perm (Fin 3)) :
    let U := leftRegularMatrix (Equiv.Perm (Fin 3))
    let E := (fun _ : TorusVertex 3 3 => U transposition,
      fun _ : TorusVertex 3 3 => U transposition)
    torusBondNetwork
        (fun v c => projectorSite (Equiv.Perm (Fin 3)) c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusFluxMatricesWithExterior U {(1, 1)} E (torusDualFluxLabels cycle detourNE)).1
        (torusFluxMatricesWithExterior U {(1, 1)} E (torusDualFluxLabels cycle detourNE)).2 =
      torusBondNetwork
        (fun v c => projectorSite (Equiv.Perm (Fin 3)) c.1 c.2.1 c.2.2.1 c.2.2.2 (σ v))
        (torusFluxMatricesWithExterior U {(1, 1)} E (torusDualFluxLabels cycle detourEN)).1
        (torusFluxMatricesWithExterior U {(1, 1)} E (torusDualFluxLabels cycle detourEN)).2 := by
  exact detour_homotopy.torusBondNetwork_eq_with_exterior (leftRegularMatrix _)
    (fun _ => projectorSite _) (fun _ _ => (projectorSite_isGIsometric _).invariant) σ cycle _

end

end TNLeanTest.TorusDualFluxString
