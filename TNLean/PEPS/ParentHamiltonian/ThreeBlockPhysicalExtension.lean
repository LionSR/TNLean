/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockDependentCutIntersection
import TNLean.PEPS.GInjectivePhysicalMap

/-!
# Identity exterior endpoints for three independent physical tensors

The eight exterior endpoints carry identity tensors. This adds only freely
variable spectator coordinates; the three physical tensors and all ten virtual
alphabets retain their own dimensions. Semi-regularity supplies nonempty virtual
alphabets when an exterior coordinate is selected.

Source: SCP10, arXiv:1001.3807, Theorem 5.4.
-/

universe u

noncomputable section
open scoped BigOperators
namespace TNLean.PEPS.ThreeBlockDependent
open DependentBondNetwork

/-- The three actual physical sites, with no exterior endpoint among them. -/
abbrev Core := {v : Vertex // v ∈ coreVertices}

variable (D : Bond → Type u) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- Add virtual-coordinate physical alphabets only at the eight exterior endpoints. -/
def ExtendedPhys (Phys : Core → Type u) (v : Vertex) : Type u :=
  if h : v ∈ coreVertices then Phys ⟨v, h⟩ else LocalConfig D v

instance (Phys : Core → Type u) [∀ v, Fintype (Phys v)] (v : Vertex) :
    Fintype (ExtendedPhys D Phys v) := by
  unfold ExtendedPhys
  split <;> infer_instance

instance (Phys : Core → Type u) [∀ v, DecidableEq (Phys v)] (v : Vertex) :
    DecidableEq (ExtendedPhys D Phys v) := by
  unfold ExtendedPhys
  split <;> infer_instance

/-- Original core tensor coefficients and identity tensors at exterior endpoints. -/
def extendedTensor {Phys : Core → Type u}
    (A : (v : Core) → LocalConfig D v.1 → Phys v → ℂ)
    (v : Vertex) (η : LocalConfig D v) (s : ExtendedPhys D Phys v) : ℂ := by
  by_cases h : v ∈ coreVertices
  · exact A ⟨v, h⟩ η (cast (by simp [ExtendedPhys, h]) s)
  · exact if η = cast (by simp [ExtendedPhys, h]) s then 1 else 0

/-- The core coordinate identification introduced by the physical extension. -/
def coreOutputEquiv (Phys : Core → Type u) (v : Core) :
    ExtendedPhys D Phys v.1 ≃ Phys v :=
  Equiv.cast (by simp [ExtendedPhys, v.2])

/-- An exterior physical coordinate is exactly its incident virtual coordinate. -/
def exteriorOutputEquiv (Phys : Core → Type u) (v : Vertex) (hv : v ∉ coreVertices) :
    ExtendedPhys D Phys v ≃ LocalConfig D v :=
  Equiv.cast (by simp [ExtendedPhys, hv])

/-- At a core site the extension merely changes the coordinate type by equality. -/
theorem localSiteMap_extendedTensor_core {Phys : Core → Type u}
    (A : (v : Core) → LocalConfig D v.1 → Phys v → ℂ) (v : Core) :
    localSiteMap tail head D (extendedTensor D A) v.1 =
      (LinearEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ) (coreOutputEquiv D Phys v).symm).toLinearMap ∘ₗ
        Matrix.mulVecLin (fun s η ↦ A v η s) := by
  apply LinearMap.ext
  intro x
  funext s
  simp [localSiteMap_apply, extendedTensor, v.2, coreOutputEquiv,
    LinearEquiv.piCongrLeft']
  rfl

/-- At an exterior endpoint the extended map is an invertible coordinate identification. -/
theorem localSiteMap_extendedTensor_exterior {Phys : Core → Type u}
    (A : (v : Core) → LocalConfig D v.1 → Phys v → ℂ)
    (v : Vertex) (hv : v ∉ coreVertices) :
    localSiteMap tail head D (extendedTensor D A) v =
      (LinearEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ)
        (exteriorOutputEquiv D Phys v hv).symm).toLinearMap := by
  classical
  apply LinearMap.ext
  intro x
  funext s
  simp [localSiteMap_apply, extendedTensor, hv, exteriorOutputEquiv,
    LinearEquiv.piCongrLeft']

/-- Identity exterior tensors impose no restriction on their spectator physical factors. -/
theorem localSiteMap_extendedTensor_exterior_range {Phys : Core → Type u}
    (A : (v : Core) → LocalConfig D v.1 → Phys v → ℂ)
    (v : Vertex) (hv : v ∉ coreVertices) :
    (localSiteMap tail head D (extendedTensor D A) v).range = ⊤ := by
  rw [localSiteMap_extendedTensor_exterior D A v hv]
  exact LinearEquiv.range _

variable {G : Type*} [Group G]

/-- G-injectivity of the three physical core tensors extends through identity leaves. -/
theorem isGInjective_extendedTensor {Phys : Core → Type u}
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Core) → LocalConfig D v.1 → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (incidentRepresentation tail head D U v.1)
      (Matrix.mulVecLin (fun s η ↦ A v η s))) :
    ∀ v, IsGInjective (localRepresentation D U v)
      (localSiteMap tail head D (extendedTensor D A) v) := by
  intro v
  by_cases hv : v ∈ coreVertices
  · have hrep : localRepresentation D U v = incidentRepresentation tail head D U v :=
      partialIncidentRepresentation_of_eq_id tail head D U coreAction v
        (by simp [coreAction, hv])
    rw [hrep, localSiteMap_extendedTensor_core D A ⟨v, hv⟩]
    exact (hA ⟨v, hv⟩).comp_equiv _
  · have hrep : localRepresentation D U v = Representation.trivial ℂ G
        (LocalConfig D v → ℂ) :=
      partialIncidentRepresentation_of_eq_one tail head D U coreAction v
        (by simp [coreAction, hv])
    rw [hrep, isGInjective_trivial_iff, localSiteMap_extendedTensor_exterior D A v hv]
    exact (LinearEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ)
      (exteriorOutputEquiv D Phys v hv).symm).injective

/-- Semi-regular matrix representations have at least one virtual coordinate. -/
theorem nonempty_of_isSemiRegular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : G →* Matrix ι ι ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Nonempty ι := by
  obtain ⟨x, _, hx⟩ := hU.exists_mem_invariants_ne_zero
  by_contra h
  have : IsEmpty ι := not_nonempty_iff.mp h
  exact hx (Subsingleton.elim _ _)

/-- Every independently semi-regular bond alphabet is nonempty. -/
theorem nonempty_bonds_of_isSemiRegular
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (hU : ∀ e, Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e))) :
    ∀ e, Nonempty (D e) :=
  fun e ↦ nonempty_of_isSemiRegular (U e) (hU e)

end TNLean.PEPS.ThreeBlockDependent
