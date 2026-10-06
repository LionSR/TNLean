/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentTorusClosureExtraction

/-!
# Independent closure classes for four separately chosen G-injective blocks

The source's simultaneous-conjugacy quotient is well-defined for the literal
network with eight independently typed virtual bonds and four independent
physical tensors. Their class-labelled closure states are independent. The
proof uses the eight actual trace-dual pairings after the product of four
genuine G-injective left inverses; no regular-representation or uniform-bond
replacement, isometric hypothesis, or independence assumption is used.

Source: SCP10, arXiv:1001.3807, Definition 5.8 and the independence part of
Theorem 5.9, lines 1560–1610. The all-pair result is an algebraic extension;
only the commuting restriction is used in the four-cut dimension theorem.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.DependentTorus

local notation "tail" => (torusLabelledBondTail (width := 2) (height := 2))
local notation "head" => (torusLabelledBondHead (width := 2) (height := 2))

variable {G : Type*} [Group G] [Finite G]
variable (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : Vertex → Type*}

/-- Simultaneous conjugation preserves the actual independently represented
closure. Local invariance alone suffices; no injectivity is used here. -/
theorem closure_conjugate
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v g, DependentBondNetwork.localSiteMap tail head D A v ∘ₗ
      DependentBondNetwork.incidentRepresentation tail head D U v g =
        DependentBondNetwork.localSiteMap tail head D A v)
    (x g h : G) :
    closure D U A (x * g * x⁻¹) (x * h * x⁻¹) = closure D U A g h := by
  let := Fintype.ofFinite G
  have hc : closure D U (canonicalSites D U) (x * g * x⁻¹) (x * h * x⁻¹) =
      closure D U (canonicalSites D U) g h := by
    funext σ
    simp only [closure, closureLabels_conjugate]
    exact DependentBondNetwork.network_averagingSite_vertexGauge tail head D U
      (torusLabelledClosure g h) (fun _ => x) σ
  let R := dependentPhysicalProductFamilyMap (fun v ↦ LinearMap.toMatrix'
    (DependentBondNetwork.localSiteMap tail head D A v))
  have hR (g h : G) : R (closure D U (canonicalSites D U) g h) = closure D U A g h := by
    rw [physicalMap_closure]
    rw [show DependentBondNetwork.physicalMapSite tail head D
        (fun v ↦ LinearMap.toMatrix' (DependentBondNetwork.localSiteMap tail head D A v))
        (canonicalSites D U) = A from
      DependentBondNetwork.physicalMap_recover_representationAveragingSite
        tail head D _ A hA]
  rw [← hR, ← hR, hc]

/-- Equivalent pair representatives have equal actual closure vectors.
Source: SCP10, Definition 5.8, lines 1560–1580. -/
theorem closure_eq_of_pairConjugacyClass_eq
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v g, DependentBondNetwork.localSiteMap tail head D A v ∘ₗ
      DependentBondNetwork.incidentRepresentation tail head D U v g =
        DependentBondNetwork.localSiteMap tail head D A v)
    {p r : G × G} (hpr : pairConjugacyClass G p = pairConjugacyClass G r) :
    closure D U A p.1 p.2 = closure D U A r.1 r.2 := by
  obtain ⟨x, hg, hh⟩ := (pairConjugacyClass_eq_iff p r).mp hpr
  rw [hg, hh]
  exact closure_conjugate D U A hA x r.1 r.2

/-- The actual closure vector associated to a simultaneous-conjugacy class.
The invariant tensors and independent bond dimensions are retained. -/
def closureClass
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v g, DependentBondNetwork.localSiteMap tail head D A v ∘ₗ
      DependentBondNetwork.incidentRepresentation tail head D U v g =
        DependentBondNetwork.localSiteMap tail head D A v)
    (C : PairConjugacyClass G) : ((v : Vertex) → Phys v) → ℂ :=
  Quotient.lift (fun p : G × G => closure D U A p.1 p.2)
    (fun _ _ h => closure_eq_of_pairConjugacyClass_eq D U A hA (Quotient.sound h)) C

/-- Evaluation of the well-defined closure class on any representative. -/
@[simp]
theorem closureClass_pairConjugacyClass
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v g, DependentBondNetwork.localSiteMap tail head D A v ∘ₗ
      DependentBondNetwork.incidentRepresentation tail head D U v g =
        DependentBondNetwork.localSiteMap tail head D A v)
    (p : G × G) :
    closureClass D U A hA (pairConjugacyClass G p) = closure D U A p.1 p.2 := rfl

/-- The canonical closure classes are separated by actual bond trace-dual
functionals, whose nonzero diagonal is calculated explicitly. -/
theorem linearIndependent_closureClass_canonical [Fintype G]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e))) :
    LinearIndependent ℂ (closureClass D U (canonicalSites D U)
      (fun v => (DependentBondNetwork.isGInjective_averagingSite tail head D U v).invariant)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro μ hμ C₀
  let p : G × G := C₀.out
  have hp : pairConjugacyClass G p = C₀ := Quotient.out_eq C₀
  let E := DependentBondNetwork.bondCoefficientExtraction tail head D U
    (torusLabelledClosure p.1 p.2)
  have hinv := fun v =>
    (DependentBondNetwork.isGInjective_averagingSite tail head D U v).invariant
  have hrep (C : PairConjugacyClass G) :
      closureClass D U (canonicalSites D U) hinv C =
        closure D U (canonicalSites D U) C.out.1 C.out.2 := by
    have hout : pairConjugacyClass G C.out = C := Quotient.out_eq C
    exact (congrArg (closureClass D U (canonicalSites D U) hinv) hout).symm
  have hzero (C : PairConjugacyClass G) (hC : C ≠ C₀) :
      E (closureClass D U (canonicalSites D U) hinv C) = 0 := by
    rw [hrep]
    apply bondCoefficientExtraction_closure_eq_zero_of_class_ne D U hU
    rw [hp, show pairConjugacyClass G C.out = C from Quotient.out_eq C]
    exact Ne.symm hC
  have h := congrArg E hμ
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
  rw [Finset.sum_eq_single C₀ (fun C _ hC => by rw [hzero C hC, mul_zero])
    (fun hC => absurd (Finset.mem_univ C₀) hC)] at h
  have hn : E (closureClass D U (canonicalSites D U) hinv C₀) ≠ 0 := by
    rw [← hp, closureClass_pairConjugacyClass]
    exact bondCoefficientExtraction_closure_self_ne_zero D U hU p
  exact (mul_eq_zero.mp h).resolve_right hn

/-- One product of genuine local G-injective inverses transfers independence
from the canonical closures to four independently chosen physical tensors.
Source: SCP10, the independence proof of Theorem 5.9, lines 1582–1610.
The conclusion for all pair classes is an auxiliary algebraic extension. -/
theorem linearIndependent_closureClass [∀ v, Finite (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (DependentBondNetwork.incidentRepresentation tail head D U v)
      (DependentBondNetwork.localSiteMap tail head D A v)) :
    LinearIndependent ℂ (closureClass D U A (fun v => (hA v).invariant)) := by
  classical
  let := Fintype.ofFinite G
  let (v : Vertex) := Fintype.ofFinite (Phys v)
  obtain ⟨F, hF⟩ := DependentBondNetwork.exists_physicalMap_to_representationAveragingSite
    tail head D (DependentBondNetwork.incidentRepresentation tail head D U) A hA
  apply LinearIndependent.of_comp (dependentPhysicalProductFamilyMap F)
  have hc : dependentPhysicalProductFamilyMap F ∘
      closureClass D U A (fun v => (hA v).invariant) =
        closureClass D U (canonicalSites D U)
          (fun v =>
            (DependentBondNetwork.isGInjective_averagingSite tail head D U v).invariant) := by
    funext C
    refine Quotient.inductionOn C (fun p => ?_)
    change dependentPhysicalProductFamilyMap F (closure D U A p.1 p.2) = _
    rw [physicalMap_closure, hF]
    rfl
  rw [hc]
  exact linearIndependent_closureClass_canonical D U hU

/-- The commuting simultaneous-conjugacy classes index independent actual
four-block closures, with separately sized semi-regular bonds and physical sites.
This is the closure independence component of SCP10 Theorem 5.9. -/
theorem linearIndependent_closureClass_commuting [∀ v, Finite (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (A : (v : Vertex) → LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (DependentBondNetwork.incidentRepresentation tail head D U v)
      (DependentBondNetwork.localSiteMap tail head D A v)) :
    LinearIndependent ℂ (fun C : CommutingPairConjugacyClass G =>
      closureClass D U A (fun v => (hA v).invariant) C.1) :=
  (linearIndependent_closureClass D U hU A hA).comp Subtype.val Subtype.val_injective

end TNLean.PEPS.DependentTorus
