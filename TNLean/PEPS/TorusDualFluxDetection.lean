/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusNativeFluxHolonomy
import TNLean.PEPS.TorusDualFluxString
import TNLean.PEPS.RegularTwistedStateNonzero
import Mathlib.Logic.Equiv.Option

/-!
# Detecting the endpoints of arbitrary native flux paths

An arbitrary finite oriented dual path has clockwise native holonomy `g` at
its source, `g⁻¹` at its target, and identity elsewhere. Repeated crossings
cancel with their signs. A closed dual loop is locally flux-free, without any
claim that its global torus state equals the state with no inserted string.

The existing four-spin detector follows the counterclockwise primal walk and
therefore reports the inverse classes. Relabelling its outcomes by the
canonical inverse equivalence of conjugacy classes gives the source's
clockwise convention, with the same physical projectors and the same complete
measurement. The inverse classes are not assumed equal.

Source: SCP10, arXiv:1001.3807, Definition 6.13, Lemma 6.14, and Theorem 6.15,
local source lines 2174–2267. Holonomy statements use actual native bond
labels; graph measurement statements require both torus periods at least three.

**Scope restriction (regular insertions and simple-graph tori):** See
`docs/paper-gaps/scp10_dual_flux_string_deformation.tex` for the distinction
from unrestricted source wording and arbitrary open-boundary geometries.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS

variable {width height : ℕ} {G : Type*} [Group G]
local notation "X" => TorusVertex width height

/-- The clockwise flux of any finite native dual string is the signed pair
of endpoint labels. Source: SCP10, Definition 6.13 and Lemma 6.14. -/
theorem torusBondPlaquetteHolonomy_torusDualFluxLabels
    (g : G) {a b : X} (p : TorusDualPath a b) (q : X) :
    torusBondPlaquetteHolonomy (torusDualFluxLabels g p) q =
      g ^ (torusPointMass a q - torusPointMass b q) := by
  rw [torusDualFluxLabels, torusFluxPowerLabels, torusBondPlaquetteHolonomy_zpow]
  change g ^ torusFluxCurl (torusDualPathCrossings p) q = _
  rw [p.fluxCurl]

/-- In the clockwise native convention the source of an open string carries
`g`, as specified by SCP10, Definition 6.13. -/
theorem torusBondPlaquetteHolonomy_torusDualFluxLabels_source
    (g : G) {a b : X} (p : TorusDualPath a b) (hab : a ≠ b) :
    torusBondPlaquetteHolonomy (torusDualFluxLabels g p) a = g := by
  simp [torusBondPlaquetteHolonomy_torusDualFluxLabels, torusPointMass, hab]

/-- The target of an open string carries the inverse clockwise label.
Source: SCP10, Definition 6.13. -/
theorem torusBondPlaquetteHolonomy_torusDualFluxLabels_target
    (g : G) {a b : X} (p : TorusDualPath a b) (hab : a ≠ b) :
    torusBondPlaquetteHolonomy (torusDualFluxLabels g p) b = g⁻¹ := by
  simp [torusBondPlaquetteHolonomy_torusDualFluxLabels, torusPointMass, hab.symm]

/-- Every plaquette away from both string endpoints has trivial holonomy.
Source: SCP10, Lemma 6.14 and Theorem 6.15. -/
theorem torusBondPlaquetteHolonomy_torusDualFluxLabels_of_ne
    (g : G) {a b : X} (p : TorusDualPath a b) (q : X) (hqa : q ≠ a) (hqb : q ≠ b) :
    torusBondPlaquetteHolonomy (torusDualFluxLabels g p) q = 1 := by
  simp [torusBondPlaquetteHolonomy_torusDualFluxLabels, torusPointMass, hqa, hqb]

/-- Closed dual loops are locally flux-free, including winding loops. This
assertion does not identify their global physical states with the vacuum.
Source: SCP10, Definition 6.13 and the torus closures in Definition 5.6. -/
theorem torusBondPlaquetteHolonomy_torusDualFluxLabels_loop
    (g : G) {a : X} (p : TorusDualPath a a) (q : X) :
    torusBondPlaquetteHolonomy (torusDualFluxLabels g p) q = 1 := by
  simp [torusBondPlaquetteHolonomy_torusDualFluxLabels]

/-- Inversion canonically permutes conjugacy classes; it need not fix them.
This relabels clockwise and counterclockwise flux outcomes in SCP10,
Definition 6.13 and Theorem 6.15. -/
def conjClassesInvEquiv (G : Type*) [Group G] : ConjClasses G ≃ ConjClasses G :=
  Quotient.congr (Equiv.inv G) fun a b => by
    change IsConj a b ↔ IsConj a⁻¹ b⁻¹
    rw [isConj_iff, isConj_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by simpa only [conj_inv] using congrArg Inv.inv hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by simpa only [conj_inv, inv_inv] using congrArg Inv.inv hc⟩

/-- Inverse-class relabelling sends the class of `g` to that of `g⁻¹`. -/
@[simp]
theorem conjClassesInvEquiv_mk (g : G) :
    conjClassesInvEquiv G (ConjClasses.mk g) = ConjClasses.mk g⁻¹ := rfl

variable [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

/-- The clockwise graph walk reads the native endpoint labels of every dual
path. Source: SCP10, Definition 6.13 and Theorem 6.15. -/
theorem regularWalkHolonomy_torusDualFluxLabels_reverse
    (g : G) {a b : X} (p : TorusDualPath a b) (q : X) :
    regularWalkHolonomy
        (torusGraphRegularLabels (torusDualFluxLabels g p).1 (torusDualFluxLabels g p).2)
        (torusPlaquetteWalk q).reverse =
      g ^ (torusPointMass a q - torusPointMass b q) := by
  rw [regularWalkHolonomy_torusGraphRegularLabels_reverse,
    torusBondPlaquetteHolonomy_torusDualFluxLabels]

/-- The counterclockwise detector walk reads the inverse native endpoint
labels. Source: SCP10, Definition 6.13 and Theorem 6.15. -/
theorem regularWalkHolonomy_torusDualFluxLabels
    (g : G) {a b : X} (p : TorusDualPath a b) (q : X) :
    regularWalkHolonomy
        (torusGraphRegularLabels (torusDualFluxLabels g p).1 (torusDualFluxLabels g p).2)
        (torusPlaquetteWalk q) =
      g ^ (torusPointMass b q - torusPointMass a q) := by
  rw [regularWalkHolonomy_torusGraphRegularLabels,
    torusBondPlaquetteHolonomy_torusDualFluxLabels, ← zpow_neg, neg_sub]

variable [Fintype G] [DecidableEq G] {d : ℕ}

/-- Every finite native dual string gives a nonzero actual physical state for
regular G-isometric sites. This proves the endpoint detector acts on a genuine
state, rather than a zero coefficient family. Source: SCP10, Definition 6.13
and Theorem 6.15, using regular injectivity for nonvanishing. -/
theorem IsGIsometric.torusDualFlux_state_ne_zero
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (g : G) {a b : X} (p : TorusDualPath a b) :
    (fun σ : X → Fin d =>
      torusBondNetwork (fun x c => A c.1 c.2.1 c.2.2.1 c.2.2.2 (σ x))
        (fun x => leftRegularMatrix G ((torusDualFluxLabels g p).1 x))
        (fun x => leftRegularMatrix G ((torusDualFluxLabels g p).2 x))) ≠ 0 := by
  simpa only [torusBondNetwork_leftRegular_eq_stateCoeff] using
    hA.stateCoeff_torusRegularTwistedSite_ne_zero
      (torusGraphRegularLabels (torusDualFluxLabels g p).1 (torusDualFluxLabels g p).2)

/-- Every physical cut of the actual native dual-string state is nonzero.
In particular, the four-site endpoint measurements below have a nonzero
input. Source: SCP10, Definition 6.13 and Theorem 6.15. -/
theorem IsGIsometric.torusDualFlux_cutMatrix_ne_zero
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A))
    (g : G) {a b : X} (p : TorusDualPath a b) (R : Finset X) :
    torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p) R ≠ 0 := by
  intro hz
  apply hA.torusDualFlux_state_ne_zero g p
  funext σ
  have h := congrFun (congrFun hz (fun w => σ w.1)) (fun w => σ w.1)
  simpa only [torusBondRegularPhysicalCutMatrix, assembleRegionσ_restrict,
    Matrix.zero_apply, Pi.zero_apply] using h

/-- One fixed complete measurement detects all finite native dual-path
endpoints on the actual contracted PEPS. In the existing counterclockwise
convention it reports `C[g⁻¹]` at the source and `C[g]` at the target.
Source: SCP10, Definition 6.13 and Theorem 6.15, lines 2174–2267. -/
theorem IsGIsometric.exists_torusDualFlux_counterclockwise_cutMeasurement
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A)) (q : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion q))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion q)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (g : G) (a b : X) (p : TorusDualPath a b) (C : Option (ConjClasses G)),
        Q C * torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p)
            (torusPlaquetteRegion q) =
          if C = some (ConjClasses.mk (g ^ (torusPointMass b q - torusPointMass a q)))
          then torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p)
            (torusPlaquetteRegion q) else 0 := by
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ := hA.exists_torusNative_plaquette_cutMeasurement q
  refine ⟨Q, hQh, hQm, hQsum, ?_⟩
  intro g a b p C
  simpa only [torusBondPlaquetteHolonomy_torusDualFluxLabels, ← zpow_neg, neg_sub] using
    hQact (torusDualFluxLabels g p) C

/-- Canonical inverse-class relabelling gives a single complete four-spin
measurement with the source's clockwise labels `C[g]` and `C[g⁻¹]` for every
finite native dual path. Only outcome names change; no equality between a
class and its inverse is assumed. Source: SCP10, Definition 6.13 and
Theorem 6.15, lines 2174–2267. -/
theorem IsGIsometric.exists_torusDualFlux_clockwise_cutMeasurement
    {A : G → G → G → G → Fin d → ℂ}
    (hA : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap A)) (q : X) :
    ∃ Q : Option (ConjClasses G) →
        Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion q))
          (RegionPhysicalConfig (d := d) (torusPlaquetteRegion q)) ℂ,
      (∀ C, (Q C).IsHermitian ∧ (Q C).PosSemidef) ∧
      (∀ C D, Q C * Q D = if C = D then Q C else 0) ∧
      (∑ C, Q C = 1) ∧
      ∀ (g : G) (a b : X) (p : TorusDualPath a b) (C : Option (ConjClasses G)),
        Q C * torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p)
            (torusPlaquetteRegion q) =
          if C = some (ConjClasses.mk (g ^ (torusPointMass a q - torusPointMass b q)))
          then torusBondRegularPhysicalCutMatrix A (torusDualFluxLabels g p)
            (torusPlaquetteRegion q) else 0 := by
  obtain ⟨Q, hQh, hQm, hQsum, hQact⟩ := hA.exists_torusNative_plaquette_cutMeasurement q
  let E : Option (ConjClasses G) ≃ Option (ConjClasses G) :=
    (conjClassesInvEquiv G).optionCongr
  refine ⟨fun C => Q (E C), fun C => hQh (E C), ?_, ?_, ?_⟩
  · intro C D
    simpa only [E.injective.eq_iff] using hQm (E C) (E D)
  · rw [E.sum_comp, hQsum]
  · intro g a b p C
    have he : E C = some (ConjClasses.mk
        (g ^ (torusPointMass a q - torusPointMass b q))⁻¹) ↔
        C = some (ConjClasses.mk (g ^ (torusPointMass a q - torusPointMass b q))) := by
      change E C = E (some (ConjClasses.mk
        (g ^ (torusPointMass a q - torusPointMass b q)))) ↔ _
      exact E.injective.eq_iff
    simpa only [torusBondPlaquetteHolonomy_torusDualFluxLabels, he] using
      hQact (torusDualFluxLabels g p) (E C)

end TNLean.PEPS
