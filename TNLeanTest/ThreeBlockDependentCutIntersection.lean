/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockDependentCutIntersection

/-!
# Independently sized open-cut intersection regressions

The general signature permits unrelated finite bond alphabets and physical
alphabets. A concrete trivial-group example has ten different bond dimensions
and noncanonical, non-surjective physical maps. Its exterior coordinates are
not restricted to group-labelled bond matrices.
-/

open TNLean.PEPS TNLean.PEPS.DependentBondNetwork
open TNLean.PEPS.ThreeBlockDependent

example {G : Type*} [Group G] [Finite G]
    (D : Bond → Type*) [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]
    {Phys : Vertex → Type*} [∀ v, Finite (Phys v)]
    (U : (e : Bond) → G →* Matrix (D e) (D e) ℂ)
    (A : (v : Vertex) → ThreeBlockDependent.LocalConfig D v → Phys v → ℂ)
    (hA : ∀ v, IsGInjective (localRepresentation D U v) (localSiteMap tail head D A v)) :
    cutSpace tail head D A leftCut ⊓ cutSpace tail head D A rightCut =
      cutSpace tail head D A exteriorBonds :=
  cutSpace_left_inf_right D U A hA

example (p : Bond → Equiv.Perm (Fin 3)) :
    ∃ q : Vertex → Equiv.Perm (Fin 3), ∀ e, e ∉ exteriorBonds →
      coreAction (head e) (q (head e)) * p e *
        (coreAction (tail e) (q (tail e)))⁻¹ = 1 :=
  exists_remove_internal_labels p

namespace IndependentDimensions

abbrev D (e : Bond) := Fin (e.val + 1)
abbrev Phys (v : Vertex) := Option (ThreeBlockDependent.LocalConfig D v)

noncomputable def U (e : Bond) : PUnit.{1} →* Matrix (D e) (D e) ℂ := 1

noncomputable def A (v : Vertex) (η : ThreeBlockDependent.LocalConfig D v) (s : Phys v) : ℂ :=
  if s = some η then 2 else 0

private theorem localRepresentation_trivial (v : Vertex) :
    localRepresentation D U v = Representation.trivial ℂ PUnit.{1}
      (ThreeBlockDependent.LocalConfig D v → ℂ) := by
  apply MonoidHom.ext
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  rw [hg, map_one, map_one]

private theorem site_injective (v : Vertex) :
    Function.Injective (localSiteMap tail head D A v) := by
  classical
  intro x y h
  funext η
  have hη := congrFun h (some η)
  simpa [localSiteMap_apply, A] using hη

example :
    cutSpace tail head D A leftCut ⊓ cutSpace tail head D A rightCut =
      cutSpace tail head D A exteriorBonds := by
  apply cutSpace_left_inf_right D U A
  intro v
  rw [localRepresentation_trivial, isGInjective_trivial_iff]
  exact site_injective v

-- The ten bond alphabets are genuinely different, including nonregular ones.
example : Fintype.card (D 0) = 1 ∧ Fintype.card (D 9) = 10 := by decide

-- The physical alphabet has an extra coordinate outside the local tensor image.
example (v : Vertex) (η : ThreeBlockDependent.LocalConfig D v) : A v η none = 0 := by
  simp [A]

end IndependentDimensions

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.DependentBondNetwork.exists_openBondCoefficients_of_slices'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.exists_openBondCoefficients_of_slices

/--
info: 'TNLean.PEPS.DependentBondNetwork.iInf_cutSpace_eq_of_remove_labels'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.DependentBondNetwork.iInf_cutSpace_eq_of_remove_labels

/--
info: 'TNLean.PEPS.ThreeBlockDependent.cutSpace_left_inf_right'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ThreeBlockDependent.cutSpace_left_inf_right
