/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LayoutEqualityCoordinates
import TNLean.PEPS.Approximation.OwnerMemoryTransport

/-!
# Partitioning registers after changing their owners

An owner map changes neither the ordered register spaces nor the Boolean test
used to select a register. The two canonical identifications therefore commute.
No injectivity assumption on the owner map is required.

## References

* Polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`,
  lines 383–427 and 565–588.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Layout
variable {P Q : Type}

/-- The selected memory contains the same ordered tensor factors before and
 after relabelling, with the selection pulled back to the original owners. -/
private theorem mem_restrict_mapOwner (f : P → Q) (g : Q → Bool) (a : Layout P) :
    Mem (restrict g (mapOwner f a)) = Mem (restrict (fun p ↦ g (f p)) a) := by
  rw [restrict_mapOwner, mem_mapOwner]

/-- Equality of linear maps on elementary tensors suffices after identifying
 their codomain Hilbert spaces. -/
private theorem apply_heq_of_tmul {U V W W' : HSpace} (hW : W = W')
    (F : U ⊗[ℂ] V →ₗ[ℂ] W) (G : U ⊗[ℂ] V →ₗ[ℂ] W')
    (h : ∀ u v, HEq (F (u ⊗ₜ[ℂ] v)) (G (u ⊗ₜ[ℂ] v)))
    (x : U ⊗[ℂ] V) : HEq (F x) (G x) := by
  subst W'
  have hFG : F = G := by
    ext u v
    exact eq_of_heq (h u v)
  exact heq_of_eq (congrArg (fun T ↦ T x) hFG)

/-- Reassociation preserves the equality identification of the two tail memories. -/
private theorem assoc_symm_tmul_heq (U : HSpace) {A B A' B' : HSpace}
    (ha : A = A') (hb : B = B') (u : U)
    {x : A ⊗[ℂ] B} {y : A' ⊗[ℂ] B'} (hxy : HEq x y) :
    HEq ((TensorProduct.assocIsometry ℂ U A B).symm (u ⊗ₜ[ℂ] x))
      ((TensorProduct.assocIsometry ℂ U A' B').symm (u ⊗ₜ[ℂ] y)) := by
  subst A'
  subst B'
  exact heq_of_eq (congrArg
    (fun z ↦ (TensorProduct.assocIsometry ℂ U A B).symm (u ⊗ₜ[ℂ] z))
    (eq_of_heq hxy))

/-- Moving an excluded head to the complementary side likewise preserves the
 equality identification of the two tail memories. -/
private theorem leftComm_tmul_heq (U : HSpace) {A B A' B' : HSpace}
    (ha : A = A') (hb : B = B') (u : U)
    {x : A ⊗[ℂ] B} {y : A' ⊗[ℂ] B'} (hxy : HEq x y) :
    HEq (leftCommIso U A B (u ⊗ₜ[ℂ] x))
      (leftCommIso U A' B' (u ⊗ₜ[ℂ] y)) := by
  subst A'
  subst B'
  exact heq_of_eq (congrArg (fun z ↦ leftCommIso U A B (u ⊗ₜ[ℂ] z))
    (eq_of_heq hxy))

/-- The partitioned vector is unchanged under relabelling, after identifying
 the actual selected and complementary memories. Source: polynomial-PEPS,
 `04-compression.tex`, lines 383–427 and 565–588. -/
theorem partitionIso_mapOwner_heq (f : P → Q) (g : Q → Bool)
    (a : Layout P) (x : Mem a) :
    HEq (partitionIso g (mapOwner f a) (mapOwnerIso f a x))
      (partitionIso (fun p ↦ g (f p)) a x) := by
  induction a with
  | nil => rfl
  | cons r a ih =>
      have hS := mem_restrict_mapOwner f g (r :: a)
      have hT := mem_restrict_mapOwner f (fun q ↦ !g q) (r :: a)
      apply apply_heq_of_tmul
        (congrArg₂ (fun A B : HSpace ↦ HSpace.of (A ⊗[ℂ] B)) hS hT)
        ((partitionIso g (mapOwner f (r :: a))).toLinearMap.comp
          (mapOwnerIso f (r :: a)).toLinearMap)
        (partitionIso (fun p ↦ g (f p)) (r :: a)).toLinearMap ?_ x
      intro u v
      change HEq
        (partitionIso g (⟨f r.owner, r.space⟩ :: mapOwner f a)
          (u ⊗ₜ[ℂ] mapOwnerIso f a v))
        (partitionIso (fun p ↦ g (f p)) (r :: a) (u ⊗ₜ[ℂ] v))
      cases h : g (f r.owner) with
      | true =>
          exact (partitionIso_cons_true_tmul g ⟨f r.owner, r.space⟩
            (mapOwner f a) h u (mapOwnerIso f a v)).trans
            ((assoc_symm_tmul_heq r.space
              (mem_restrict_mapOwner f g a)
              (mem_restrict_mapOwner f (fun q ↦ !g q) a) u (ih v)).trans
              (partitionIso_cons_true_tmul (fun p ↦ g (f p)) r a h u v).symm)
      | false =>
          exact (partitionIso_cons_false_tmul g ⟨f r.owner, r.space⟩
            (mapOwner f a) h u (mapOwnerIso f a v)).trans
            ((leftComm_tmul_heq r.space
              (mem_restrict_mapOwner f g a)
              (mem_restrict_mapOwner f (fun q ↦ !g q) a) u (ih v)).trans
              (partitionIso_cons_false_tmul (fun p ↦ g (f p)) r a h u v).symm)

/-- The selected-owner isometry has the same underlying vector as the original
 selected memory. -/
private theorem restrictMapOwnerIso_apply_heq (f : P → Q) (g : Q → Bool)
    (a : Layout P) (x : Mem (restrict (fun p ↦ g (f p)) a)) :
    HEq (restrictMapOwnerIso f g a x) x := by
  exact (memCongr_apply_heq (restrict_mapOwner f g a).symm
    (mapOwnerIso f _ x)).trans (mapOwnerIso_apply_heq f _ x)

/-- Tensor products of canonical identity identifications act as the identity
 after the two target Hilbert spaces have been identified. -/
private theorem tensorMap_apply_heq_refl {A B A' B' : HSpace}
    (ha : A' = A) (hb : B' = B) (e : A ≃ₗᵢ[ℂ] A') (d : B ≃ₗᵢ[ℂ] B')
    (he : ∀ x, HEq (e x) x) (hd : ∀ y, HEq (d y) y) (z : A ⊗[ℂ] B) :
    HEq (TensorProduct.mapIsometry e.toLinearIsometry d.toLinearIsometry z) z := by
  subst A'
  subst B'
  have he' : e = LinearIsometryEquiv.refl ℂ A := by
    ext x
    exact eq_of_heq (he x)
  have hd' : d = LinearIsometryEquiv.refl ℂ B := by
    ext x
    exact eq_of_heq (hd x)
  rw [he', hd']
  apply heq_of_eq
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => rfl

/-- Partitioning after relabelling agrees exactly with relabelling the two
 selected memories. The isometries are the canonical ordered-register maps.
 Source: polynomial-PEPS, `04-compression.tex`, lines 383–427 and 565–588. -/
theorem partitionIso_mapOwner (f : P → Q) (g : Q → Bool)
    (a : Layout P) (x : Mem a) :
    partitionIso g (mapOwner f a) (mapOwnerIso f a x) =
      TensorProduct.mapIsometry (restrictMapOwnerIso f g a).toLinearIsometry
        (restrictMapOwnerIso f (fun q ↦ !g q) a).toLinearIsometry
        (partitionIso (fun p ↦ g (f p)) a x) := by
  apply eq_of_heq
  exact (partitionIso_mapOwner_heq f g a x).trans
    (tensorMap_apply_heq_refl
      (mem_restrict_mapOwner f g a) (mem_restrict_mapOwner f (fun q ↦ !g q) a)
      (restrictMapOwnerIso f g a) (restrictMapOwnerIso f (fun q ↦ !g q) a)
      (restrictMapOwnerIso_apply_heq f g a)
      (restrictMapOwnerIso_apply_heq f (fun q ↦ !g q) a)
      (partitionIso (fun p ↦ g (f p)) a x)).symm

/-- If every register is excluded, the selected factor is the scalar unit and
 the complementary factor retains the whole original memory. -/
private theorem restrict_false_spec (g : P → Bool) (a : Layout P)
    (h : ∀ r ∈ a, g r.owner = false) :
    restrict g a = [] ∧ restrict (fun p ↦ !g p) a = a := by
  constructor
  · exact List.filter_eq_nil_iff.mpr (fun r hr ↦ by simp [h r hr])
  · exact List.filter_eq_self.mpr (fun r hr ↦ by simp [h r hr])

/-- With no selected registers, the canonical partition adjoins only the scalar
 unit. Source: polynomial-PEPS, `04-compression.tex`, lines 565–588. -/
theorem partitionIso_of_forall_false (g : P → Bool) (a : Layout P)
    (ha : ∀ r ∈ a, g r.owner = false) (x : Mem a) :
    HEq (partitionIso g a x) ((1 : ℂ) ⊗ₜ[ℂ] x) := by
  induction a with
  | nil => rfl
  | cons r a ih =>
      have ht : ∀ s ∈ a, g s.owner = false :=
        fun s hs ↦ ha s (List.mem_cons_of_mem r hs)
      have hfull := restrict_false_spec g (r :: a) ha
      have htail := restrict_false_spec g a ht
      apply apply_heq_of_tmul
        (congrArg₂ (fun A B : HSpace ↦ HSpace.of (A ⊗[ℂ] B))
          (congrArg Mem hfull.1) (congrArg Mem hfull.2))
        (partitionIso g (r :: a)).toLinearMap
        (TensorProduct.mk ℂ ℂ (Mem (r :: a)) (1 : ℂ)) ?_ x
      intro u v
      have hstep := (partitionIso_cons_false_tmul g r a
        (ha r List.mem_cons_self) u v).trans
        (leftComm_tmul_heq r.space (congrArg Mem htail.1)
          (congrArg Mem htail.2) u (ih ht v))
      simpa only [leftCommIso_tmul, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv,
        TensorProduct.mk_apply] using hstep

end TNLean.PEPS.PairEffect.Layout
