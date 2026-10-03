/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjective

/-!
# The physical range of a G-injective tensor

A G-injective tensor identifies its invariant virtual subspace with its physical
range. In particular, its kernel is exactly the kernel of the virtual averaging
projector. Two G-injective tensors for the same virtual representation therefore
induce a unique linear equivalence between their physical ranges, characterized
by sending the image of each virtual vector under the first tensor to its image
under the second.

These are local consequences of Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Definition 5.1, `Papers/1001.3807/paper_v3.tex`, lines 1278–1296.
They do not infer a relation between virtual representations from equality of
closed PEPS states; that is a separate Fundamental Theorem question.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

open Representation

variable {G W P Q : Type*} [Group G] [Fintype G]
variable [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]
variable [AddCommGroup Q] [Module ℂ Q]

noncomputable local instance instInvertibleCardRangeEquivalence :
    Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- The only virtual vectors annihilated by a G-injective tensor are those
annihilated by the invariant projector. Source: SCP10, Definition 5.1,
lines 1278–1296. -/
theorem IsGInjective.ker_eq_ker_averageMap {ρ : Representation ℂ G W}
    {T : W →ₗ[ℂ] P} (hT : IsGInjective ρ T) :
    LinearMap.ker T = LinearMap.ker ρ.averageMap := by
  ext x
  change T x = 0 ↔ ρ.averageMap x = 0
  exact ⟨fun hx => hT.injOn_invariants _ (ρ.averageMap_invariant x)
    ((apply_averageMap_of_forall_comp_eq hT.invariant x).trans hx),
    fun hx => (apply_averageMap_of_forall_comp_eq hT.invariant x).symm.trans
      (by rw [hx, map_zero])⟩

omit [Fintype G] in
/-- The invariant virtual space is carried bijectively onto the physical range.
Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.bijective_invariants_rangeRestrict [Finite G] {ρ : Representation ℂ G W}
    {T : W →ₗ[ℂ] P} (hT : IsGInjective ρ T) :
    Function.Bijective (T.rangeRestrict ∘ₗ ρ.invariants.subtype) := by
  let _ := Fintype.ofFinite G
  constructor
  · exact (injective_iff_map_eq_zero _).2 fun x hx =>
      Subtype.ext (hT.injOn_invariants x x.2 (congrArg Subtype.val hx))
  · rintro ⟨y, x, rfl⟩
    exact ⟨⟨ρ.averageMap x, ρ.averageMap_invariant x⟩,
      Subtype.ext (apply_averageMap_of_forall_comp_eq hT.invariant x)⟩

/-- A G-injective tensor identifies the invariant virtual space with its
physical range. Source: SCP10, Definition 5.1, lines 1278–1296. -/
noncomputable def IsGInjective.invariantsRangeEquiv {ρ : Representation ℂ G W}
    {T : W →ₗ[ℂ] P} (hT : IsGInjective ρ T) : ρ.invariants ≃ₗ[ℂ] T.range :=
  LinearEquiv.ofBijective (T.rangeRestrict ∘ₗ ρ.invariants.subtype)
    hT.bijective_invariants_rangeRestrict

/-- The equivalence acts by the tensor itself on invariant virtual vectors. -/
@[simp]
theorem IsGInjective.invariantsRangeEquiv_apply {ρ : Representation ℂ G W}
    {T : W →ₗ[ℂ] P} (hT : IsGInjective ρ T) (x : ρ.invariants) :
    (hT.invariantsRangeEquiv x : P) = T x := rfl

/-- G-injective tensors for the same virtual representation identify their
physical ranges through that invariant virtual space. Source: SCP10,
Definition 5.1, lines 1278–1296. -/
noncomputable def IsGInjective.rangeEquiv {ρ : Representation ℂ G W}
    {T : W →ₗ[ℂ] P} {S : W →ₗ[ℂ] Q}
    (hT : IsGInjective ρ T) (hS : IsGInjective ρ S) : T.range ≃ₗ[ℂ] S.range :=
  hT.invariantsRangeEquiv.symm.trans hS.invariantsRangeEquiv

/-- The physical range equivalence sends each virtual image under the first
tensor to its image under the second. Source: SCP10, Definition 5.1,
lines 1278–1296. -/
@[simp]
theorem IsGInjective.rangeEquiv_apply {ρ : Representation ℂ G W}
    {T : W →ₗ[ℂ] P} {S : W →ₗ[ℂ] Q}
    (hT : IsGInjective ρ T) (hS : IsGInjective ρ S) (x : W) :
    (hT.rangeEquiv hS (T.rangeRestrict x) : Q) = S x := by
  have hx : T.rangeRestrict x =
      hT.invariantsRangeEquiv ⟨ρ.averageMap x, ρ.averageMap_invariant x⟩ :=
    Subtype.ext (apply_averageMap_of_forall_comp_eq hT.invariant x).symm
  simpa only [hx, rangeEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    invariantsRangeEquiv_apply] using apply_averageMap_of_forall_comp_eq hS.invariant x

omit [Fintype G] in
/-- The physical range has the dimension of the invariant virtual subspace.
Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.finrank_range [Finite G] {ρ : Representation ℂ G W}
    {T : W →ₗ[ℂ] P} (hT : IsGInjective ρ T) :
    Module.finrank ℂ T.range = Module.finrank ℂ ρ.invariants := by
  let _ := Fintype.ofFinite G
  exact hT.invariantsRangeEquiv.finrank_eq.symm

/-- The range equivalence is the unique linear map that sends each virtual
image under the first tensor to its image under the second.
Source: SCP10, Definition 5.1, lines 1278–1296. -/
theorem IsGInjective.rangeEquiv_unique {ρ : Representation ℂ G W}
    {T : W →ₗ[ℂ] P} {S : W →ₗ[ℂ] Q}
    (hT : IsGInjective ρ T) (hS : IsGInjective ρ S)
    (F : T.range →ₗ[ℂ] S.range)
    (hF : ∀ x, (F (T.rangeRestrict x) : Q) = S x) :
    F = (hT.rangeEquiv hS).toLinearMap := by
  ext ⟨y, x, rfl⟩
  exact (hF x).trans (hT.rangeEquiv_apply hS x).symm

end TNLean.PEPS
