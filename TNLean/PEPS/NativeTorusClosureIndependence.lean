/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.NativeTorusClosures
import TNLean.PEPS.DependentCutBondSupport
import TNLean.PEPS.TorusFlatConnectionGauge
import TNLean.PEPS.PairConjugacy

/-!
# Independent closure classes on the actual nonuniform torus

Trace-dual extraction on the separately represented native bonds forces every
surviving vertex gauge to be constant. Its diagonal value is the common
centralizer cardinality divided by the group cardinality raised to the number
of vertices. Genuine local G-injective inverses transfer this separation to
unrelated physical tensors and finite physical alphabets.

Source: SCP10, arXiv:1001.3807, Definition 5.8 and the independence argument of
Theorem 5.9. No independence, blocking, or uniform-representation premise is used.
-/

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.NativeTorus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]

local notation "Vertex" => TorusVertex width height
local notation "Bond" => Edge (torusGraph width height)
local notation "tail" => (graphEdgeTail (Γ := torusGraph width height))
local notation "head" => (graphEdgeHead (Γ := torusGraph width height))

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩

variable {G : Type*} [Group G]

/-- Constant conjugation acts on both native seam labels, including the inverse
horizontal seam required by the ordered graph orientation. -/
theorem closureLabels_conjugate (x g h : G) (e : Bond) :
    torusClosureEdgeAssignment (x * g * x⁻¹) (x * h * x⁻¹) e =
      x * torusClosureEdgeAssignment g h e * x⁻¹ := by
  unfold torusClosureEdgeAssignment
  cases torusEdgeEquiv.symm e with
  | inl v =>
    simp only [torusHorizontalClosureElement]
    split_ifs <;> group
  | inr v =>
    simp only [torusVerticalClosureElement]
    split_ifs <;> group

/-- Equality of gauged native closure labels is exactly a constant vertex
conjugation of the two seam elements. This also holds for noncommuting pairs. -/
theorem closureLabels_eq_iff (p r : G × G) (q : Vertex → G) :
    (∀ e, torusClosureEdgeAssignment p.1 p.2 e =
      q (head e) * torusClosureEdgeAssignment r.1 r.2 e * (q (tail e))⁻¹) ↔
      IsTorusNonseamCompatible q ∧
        p.1 = q (0, 0) * r.1 * (q (0, 0))⁻¹ ∧
        p.2 = q (0, 0) * r.2 * (q (0, 0))⁻¹ := by
  constructor
  · intro hq
    have heq : regularVertexGaugeOperators (fun v => (q v)⁻¹)
        (torusClosureEdgeAssignment r.1 r.2) = torusClosureEdgeAssignment p.1 p.2 := by
      funext e
      simpa only [regularVertexGaugeOperators, inv_inv, graphEdgeHead, graphEdgeTail]
        using (hq e).symm
    have hr (v : Vertex) :
        (if v.1 + 1 = 0 then p.2 else 1) =
          q (v.1 + 1, v.2) * (if v.1 + 1 = 0 then r.2 else 1) * (q v)⁻¹ := by
      have h := regularDirectedTransport_gauge (torusClosureEdgeAssignment r.1 r.2)
        (fun v => (q v)⁻¹) (torusGraph_adj_right v.1 v.2)
      rw [heq] at h
      change torusNativeRightTransport (torusClosureEdgeAssignment p.1 p.2) v =
        ((q (v.1 + 1, v.2))⁻¹)⁻¹ *
          torusNativeRightTransport (torusClosureEdgeAssignment r.1 r.2) v * (q v)⁻¹ at h
      simpa only [torusNativeRightTransport_closure, inv_inv] using h
    have hu (v : Vertex) :
        (if v.2 + 1 = 0 then p.1⁻¹ else 1) =
          q (v.1, v.2 + 1) * (if v.2 + 1 = 0 then r.1⁻¹ else 1) * (q v)⁻¹ := by
      have h := regularDirectedTransport_gauge (torusClosureEdgeAssignment r.1 r.2)
        (fun v => (q v)⁻¹) (torusGraph_adj_up v.1 v.2)
      rw [heq] at h
      change torusNativeUpTransport (torusClosureEdgeAssignment p.1 p.2) v =
        ((q (v.1, v.2 + 1))⁻¹)⁻¹ *
          torusNativeUpTransport (torusClosureEdgeAssignment r.1 r.2) v * (q v)⁻¹ at h
      simpa only [torusNativeUpTransport_closure, inv_inv] using h
    have hc : IsTorusNonseamCompatible q := by
      intro v
      constructor
      · intro hv
        simpa only [hv, ↓reduceIte, mul_one, mul_inv_eq_one] using (hr v).symm
      · intro hv
        apply Eq.symm
        simpa only [hv, ↓reduceIte, mul_one, mul_inv_eq_one] using (hu v).symm
    refine ⟨hc, ?_, ?_⟩
    · have h := congrArg Inv.inv (hu (0, -1))
      simpa only [neg_add_cancel, ↓reduceIte, inv_inv, mul_inv_rev, hc.eq_origin,
        mul_assoc] using h
    · simpa only [neg_add_cancel, ↓reduceIte, hc.eq_origin] using hr (-1, 0)
  · rintro ⟨hc, hg, hh⟩ e
    simp only [hc.eq_origin, hg, hh]
    exact closureLabels_conjugate _ _ _ e

section Extraction

variable [Fintype G]
variable (D : Edge (torusGraph width height) → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

open Classical in
/-- The actual bond trace-dual extraction counts simultaneous conjugations,
with one averaging normalization for every native vertex. -/
theorem bondCoefficientExtraction_closure
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p r : G × G) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U
        (torusClosureEdgeAssignment p.1 p.2)
        (closure D U (canonicalSites D U) r.1 r.2) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex *
        ∑ x : G, if p.1 = x * r.1 * x⁻¹ ∧ p.2 = x * r.2 * x⁻¹ then 1 else 0 := by
  classical
  rw [closure, DependentBondNetwork.bondCoefficientExtraction_network_averagingSite]
  simp only [← map_mul, torusDeltaPairing_apply_rep _ (hU _), Fintype.prod_boole,
    closureLabels_eq_iff]
  congr 1
  refine (Fintype.sum_of_injective (fun x : G => fun _ : Vertex => x)
    (fun x y hxy => congrFun hxy (0, 0)) _ _ ?_ ?_).symm
  · intro q hq
    apply ite_eq_right
    rintro ⟨hc, _⟩
    exact hq ⟨q (0, 0), (funext hc.eq_origin).symm⟩
  · intro x
    have hc : IsTorusNonseamCompatible (fun _ : Vertex => x) :=
      fun _ => ⟨fun _ => rfl, fun _ => rfl⟩
    simp only [hc, true_and]

/-- Distinct simultaneous-conjugacy classes are separated by native bond
trace-dual extraction. -/
theorem bondCoefficientExtraction_closure_eq_zero_of_class_ne
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    {p r : G × G} (hpr : pairConjugacyClass G p ≠ pairConjugacyClass G r) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U
        (torusClosureEdgeAssignment p.1 p.2)
        (closure D U (canonicalSites D U) r.1 r.2) = 0 := by
  classical
  rw [bondCoefficientExtraction_closure D U hU]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x _
  apply ite_eq_right
  intro hx
  exact hpr ((pairConjugacyClass_eq_iff p r).mpr ⟨x, hx⟩)

/-- The diagonal extracted scalar is exactly the common-centralizer cardinality
with the normalization from all native local invariant projectors. -/
theorem bondCoefficientExtraction_closure_self
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p : G × G) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U
        (torusClosureEdgeAssignment p.1 p.2)
        (closure D U (canonicalSites D U) p.1 p.2) =
      (Fintype.card G : ℂ)⁻¹ ^ Fintype.card Vertex *
        (Nat.card (Subgroup.centralizer ({p.1, p.2} : Set G)) : ℂ) := by
  classical
  rw [bondCoefficientExtraction_closure D U hU]
  have hm (x : G) : (p.1 = x * p.1 * x⁻¹ ∧ p.2 = x * p.2 * x⁻¹) ↔
      x ∈ Subgroup.centralizer ({p.1, p.2} : Set G) := by
    simp only [eq_mul_inv_iff_mul_eq, Subgroup.mem_centralizer_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  simp only [hm, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

/-- The diagonal extracted scalar is nonzero since the centralizer contains
identity and the finite group has nonzero complex cardinality. -/
theorem bondCoefficientExtraction_closure_self_ne_zero
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)))
    (p : G × G) :
    DependentBondNetwork.bondCoefficientExtraction tail head D U
        (torusClosureEdgeAssignment p.1 p.2)
        (closure D U (canonicalSites D U) p.1 p.2) ≠ 0 := by
  rw [bondCoefficientExtraction_closure_self D U hU]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end Extraction

variable [Finite G]
variable (D : Edge (torusGraph width height) → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
variable {Phys : TorusVertex width height → Type*}

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
      (torusClosureEdgeAssignment g h) (fun _ => x) σ
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
    (torusClosureEdgeAssignment p.1 p.2)
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
from the canonical closures to independently chosen physical tensors at all vertices.
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
native torus closures, with separately sized semi-regular bonds and physical sites.
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

end TNLean.PEPS.NativeTorus
