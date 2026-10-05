/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.NonuniformNativeParentClassification
import TNLean.PEPS.GInjectivePhysicalMap
import TNLean.Algebra.SemiRegularGroupAlgebra

/-!
# Native nonuniform nonabelian parent-classification regressions

One microscopic three-by-three model simultaneously has a nonabelian group,
unequal nonregular bond dimensions, and independent nonsurjective physical
maps. The edge representations are two or three copies of the regular S₃
representation, reindexed to the actual `Fin` bond alphabets. At every vertex
the averaging site is scaled by two and included in an `Option` alphabet,
whose extra coordinate is unused. Tests concern the existing canonical
positive plaquette parent and its full ambient kernel.
-/

noncomputable section
open scoped BigOperators
open TNLean.PEPS TNLean.PEPS.DependentBondNetwork

namespace NonuniformNativeClassificationTest

local instance : Fact (2 < 3) := ⟨by decide⟩
local instance : Fact (1 < 3) := ⟨by decide⟩
private abbrev V := TorusVertex 3 3
private abbrev Γ := torusGraph 3 3
private abbrev G := Equiv.Perm (Fin 3)

private def copyPermutation (m : ℕ) : G →* Equiv.Perm (G × Fin m) where
  toFun g := Equiv.prodCongr (MulAction.toPermHom G G g) (Equiv.refl _)
  map_one' := by ext x <;> simp
  map_mul' g h := by ext x <;> simp [mul_assoc]

private def regularCopies (m : ℕ) : G →* Matrix (G × Fin m) (G × Fin m) ℂ :=
  Matrix.permMatrixHom.comp (copyPermutation m)

private theorem regularCopies_apply (m : ℕ) (g : G)
    (x : G × Fin m → ℂ) (a : G × Fin m) :
    Matrix.toLinAlgEquiv' (regularCopies m g) x a = x (g⁻¹ * a.1, a.2) := by
  rcases a with ⟨a, i⟩
  simp [regularCopies, copyPermutation, Matrix.toLinAlgEquiv'_apply,
    Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec, MulAction.toPerm_symm_apply,
    smul_eq_mul]

private theorem regularCopies_semiRegular (m : ℕ) (hm : 0 < m) :
    Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (regularCopies m)) := by
  classical
  apply Representation.isSemiRegular_of_linearIndependent
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  let z : Fin m := ⟨0, hm⟩
  have heval (k : G) :
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (regularCopies m) k)
        (Pi.single (1, z) 1) (g, z) = if k = g then 1 else 0 := by
    change Matrix.toLinAlgEquiv' (regularCopies m k) _ _ = _
    rw [regularCopies_apply]
    simp [Pi.single_apply, inv_mul_eq_one, eq_comm]
  have h := congrArg (fun L : Module.End ℂ (G × Fin m → ℂ) =>
    L (Pi.single (1, z) 1) (g, z)) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, heval, LinearMap.zero_apply, Pi.zero_apply] at h
  simpa using h

private def multiplicity (e : Edge Γ) : ℕ :=
  if e = torusRightEdge (0 : V) then 3 else 2
private def N (e : Edge Γ) : ℕ := Fintype.card (G × Fin (multiplicity e))
private abbrev D (e : Edge Γ) := Fin (N e)
private def reindex (e : Edge Γ) :=
  Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin (G × Fin (multiplicity e)))
private def U (e : Edge Γ) : G →* Matrix (D e) (D e) ℂ :=
  (reindex e).toMonoidHom.comp (regularCopies (multiplicity e))

private theorem semiRegular (e : Edge Γ) :
    Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)) := by
  let T : Module.End ℂ (G × Fin (multiplicity e) → ℂ) ≃ₐ[ℂ]
      Module.End ℂ (D e → ℂ) :=
    Matrix.toLinAlgEquiv'.symm.trans ((reindex e).trans Matrix.toLinAlgEquiv')
  have hi := Representation.linearIndependent_of_isSemiRegular _
    (regularCopies_semiRegular (multiplicity e) (by unfold multiplicity; split_ifs <;> omega))
  have ht := hi.map' T.toLinearMap (LinearMap.ker_eq_bot.mpr T.injective)
  apply Representation.isSemiRegular_of_linearIndependent
  convert ht using 1
  funext g
  simp [T, U]
  rfl

private abbrev Virtual (v : V) := LocalConfig graphEdgeTail graphEdgeHead D v
private abbrev Phys (v : V) := Option (Virtual v)
private def inclusion (v : V) : Matrix (Phys v) (Virtual v) ℂ :=
  fun s η ↦ if s = some η then 2 else 0
private def A := physicalMapSite graphEdgeTail graphEdgeHead D inclusion
  (averagingSite graphEdgeTail graphEdgeHead D U)

private theorem inclusion_injective (v : V) :
    Function.Injective (Matrix.mulVecLin (inclusion v)) := by
  intro x y h
  funext η
  have hs := congrFun h (some η)
  change (∑ ζ, inclusion v (some η) ζ * x ζ) =
    ∑ ζ, inclusion v (some η) ζ * y ζ at hs
  simpa [inclusion] using hs

private theorem site_gInjective (v : V) :
    IsGInjective (incidentRepresentation graphEdgeTail graphEdgeHead D U v)
      (localSiteMap graphEdgeTail graphEdgeHead D A v) := by
  rw [A, localSiteMap_physicalMapSite]
  exact (isGInjective_averagingSite graphEdgeTail graphEdgeHead D U v).comp_of_injective
    (Matrix.mulVecLin (inclusion v)) (inclusion_injective v)

example (v : V) (η : Virtual v) :
    A v η (some η) = 2 * averagingSite graphEdgeTail graphEdgeHead D U v η η := by
  simp [A, DependentBondNetwork.physicalMapSite, inclusion]

-- Nonsurjectivity is proved symbolically, without enumerating physical configurations.
example (v : V) : ¬ Function.Surjective
    (localSiteMap graphEdgeTail graphEdgeHead D A v) := by
  intro h
  obtain ⟨x, hx⟩ := h (Pi.single none 1)
  have he := congrFun hx none
  simp [localSiteMap_apply, A, DependentBondNetwork.physicalMapSite, inclusion] at he

private abbrev B := graphPhysicalPaddingTensor N A
private def H (v : V) := canonicalRegionParentInteraction B (torusPlaquetteRegion v)

example : Fintype.card (D (torusRightEdge (0 : V))) = 18 := by
  norm_num [D, N, multiplicity, Fintype.card_perm]
example : Fintype.card (D (torusUpEdge (0 : V))) = 12 := by
  have hne : torusUpEdge (0 : V) ≠ torusRightEdge (0 : V) := by
    change torusEdgeEquiv (Sum.inr (0 : V)) ≠ torusEdgeEquiv (Sum.inl (0 : V))
    exact fun h ↦ Sum.inr_ne_inl (torusEdgeEquiv.injective h)
  norm_num [D, N, multiplicity, hne, Fintype.card_perm]

example (e : Edge Γ) : ¬ Nonempty ((D e → ℂ) ≃ₗ[ℂ] (G → ℂ)) := by
  rintro ⟨L⟩
  have h := L.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  change N e = Fintype.card G at h
  have hN : N e = 6 * multiplicity e := by norm_num [N, Fintype.card_perm]
  rw [hN] at h
  norm_num [Fintype.card_perm] at h
  unfold multiplicity at h
  split_ifs at h <;> norm_num at h

private def transposition : G := Equiv.swap 0 1
private def threeCycle : G := Equiv.swap 0 1 * Equiv.swap 1 2

example : ¬ Commute transposition threeCycle := by
  change ¬ transposition * threeCycle = threeCycle * transposition
  decide
example : threeCycle⁻¹ ≠ threeCycle := by decide
example : torusClosureEdgeAssignment transposition threeCycle (torusRightEdge (2, 0) : Edge Γ) =
    threeCycle⁻¹ := by
  rw [torusClosureEdgeAssignment_right]
  rfl
example : torusClosureEdgeAssignment transposition threeCycle (torusUpEdge (0, 2) : Edge Γ) =
    transposition := by
  rw [torusClosureEdgeAssignment_up]
  rfl
example : torusClosureEdgeAssignment transposition threeCycle (torusRightEdge (2, 0) : Edge Γ) ≠
    threeCycle := by
  rw [torusClosureEdgeAssignment_right]
  decide

-- Cardinality reduction enumerates only the four incident edges, never vectors
-- in these physical spaces or configurations of the nine-site network.
private theorem card_phys (v : V) : Fintype.card (Phys v) =
    (∏ p : IncidentEndpoint graphEdgeTail graphEdgeHead v, N p.1.1) + 1 := by
  change Fintype.card (Option (Virtual v)) = _
  rw [Fintype.card_option]
  change Fintype.card ((p : IncidentEndpoint graphEdgeTail graphEdgeHead v) → D p.1.1) + 1 = _
  rw [Fintype.card_pi]
  simp only [D, Fintype.card_fin]

set_option maxRecDepth 8192 in
example : Fintype.card (Phys (0 : V)) = 31105 := by
  rw [card_phys]
  simp only [N, Fintype.card_prod, Fintype.card_fin, Fintype.card_perm]
  decide
set_option maxRecDepth 8192 in
example : Fintype.card (Phys (1, 1)) = 20737 := by
  rw [card_phys]
  simp only [N, Fintype.card_prod, Fintype.card_fin, Fintype.card_perm]
  decide

private abbrev ParentKernel :=
  (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker
private abbrev ClosureSpace := NativeTorus.commutingClosureSpan D U A

/-- No support, image, cut, flatness, or independence premise is attached to
vectors in this equality of full ambient spaces. -/
theorem full_ambient_kernel : ParentKernel =
    ClosureSpace.map (dependentPhysicalProductFamilyMap
      (physicalPaddingMatrix (Phys := Phys))) :=
  ker_nonuniformTorusPlaquetteParent_eq_map_nativeCommutingClosureSpan N U semiRegular A
    site_gInjective H (fun v ↦ isRegionParentInteraction_canonical B (torusPlaquetteRegion v))

/-- The actual padded parent has exactly the commuting-conjugacy-class count. -/
theorem kernel_dimension : Module.finrank ℂ ParentKernel =
    Nat.card (CommutingPairConjugacyClass G) :=
  finrank_ker_nonuniformTorusPlaquetteParentHamiltonian N U semiRegular A site_gInjective H
    (fun v ↦ isRegionParentInteraction_canonical B (torusPlaquetteRegion v))

/-- Zero extension is a linear equivalence onto the entire ambient parent kernel. -/
def parentEquiv : ClosureSpace ≃ₗ[ℂ] ParentKernel :=
  nonuniformNativeParentEquiv N U semiRegular A site_gInjective H
    (fun v ↦ isRegionParentInteraction_canonical B (torusPlaquetteRegion v))

theorem parentEquiv_zero_extension (ψ : ClosureSpace) :
    (parentEquiv ψ : (V → Fin (physicalPaddingDimension (Phys := Phys))) → ℂ) =
      dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) ψ :=
  nonuniformNativeParentEquiv_apply N U semiRegular A site_gInjective H
    (fun v ↦ isRegionParentInteraction_canonical B (torusPlaquetteRegion v)) ψ

/-- Every ambient kernel vector is inverted by the actual product restriction. -/
theorem parentEquiv_restriction (Ψ : ParentKernel) :
    (parentEquiv.symm Ψ : ((v : V) → Phys v) → ℂ) =
      dependentPhysicalProductFamilyMap (physicalRestrictionMatrix (Phys := Phys)) Ψ :=
  nonuniformNativeParentEquiv_symm_apply N U semiRegular A site_gInjective H
    (fun v ↦ isRegionParentInteraction_canonical B (torusPlaquetteRegion v)) Ψ

/-- The explicit inverse lands in the original physical commuting-closure span. -/
theorem restriction_mem_original_span (Ψ : ParentKernel) :
    dependentPhysicalProductFamilyMap (physicalRestrictionMatrix (Phys := Phys)) Ψ ∈
      ClosureSpace := by
  rw [← parentEquiv_restriction]
  exact (parentEquiv.symm Ψ).property

/-- There is no residual component in any unused padded coordinate. -/
theorem every_parent_vector_reconstructed (Ψ : ParentKernel) :
    dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys))
      (dependentPhysicalProductFamilyMap (physicalRestrictionMatrix (Phys := Phys)) Ψ) = Ψ := by
  rw [← parentEquiv_restriction, ← parentEquiv_zero_extension]
  exact congrArg Subtype.val (parentEquiv.apply_symm_apply Ψ)

/-- Original physical representatives are unique for arbitrary ambient kernel vectors. -/
theorem every_parent_vector_unique
    {Ψ : (V → Fin (physicalPaddingDimension (Phys := Phys))) → ℂ}
    (hΨ : Ψ ∈ ParentKernel) :
    ∃! ψ : ((v : V) → Phys v) → ℂ,
      ψ ∈ ClosureSpace ∧
      dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) ψ = Ψ :=
  existsUnique_nativeClosureRepresentative_of_mem_nonuniformParentKernel N U semiRegular A
    site_gInjective H (fun v ↦ isRegionParentInteraction_canonical B (torusPlaquetteRegion v)) hΨ

end NonuniformNativeClassificationTest

set_option linter.hashCommand false

/--
info: 'NonuniformNativeClassificationTest.full_ambient_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NonuniformNativeClassificationTest.full_ambient_kernel

/--
info: 'NonuniformNativeClassificationTest.kernel_dimension' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NonuniformNativeClassificationTest.kernel_dimension

/--
info: 'NonuniformNativeClassificationTest.every_parent_vector_reconstructed' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NonuniformNativeClassificationTest.every_parent_vector_reconstructed
