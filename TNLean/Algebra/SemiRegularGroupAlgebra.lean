/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CharacterProjectorTwirl
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Semi-regularity and faithful group-algebra actions

A finite-dimensional complex representation of a finite group contains every
irreducible representation exactly when its group operators are linearly independent,
or equivalently when its induced group-algebra homomorphism is injective. The converse
uses character projectors: an absent irreducible gives a zero projector whose
coefficient at the identity cannot vanish. The criterion also proves that reversing
bond orientation, by passing to the contragredient representation, preserves
semi-regularity.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 4.5 and
Lemma 4.6, `Papers/1001.3807/paper_v3.tex`, lines 1010–1029; the character projectors
in lines 983–990; and the link orientation in Definition 5.1 and Lemma 5.2,
lines 1278–1296 and 1334–1337. These are algebraic reformulations and consequences
of the source representation hypotheses. No unitarity assumption is needed here.
Faithfulness refers to the group algebra, not merely to the group homomorphism.
-/

open Module LinearMap
open scoped BigOperators

namespace Representation

section GroupAlgebra

variable {k M W : Type*} [CommSemiring k] [Monoid M] [AddCommMonoid W] [Module k W]

/-- Linear independence of the monoid operators is equivalent to injectivity of the
induced monoid-algebra homomorphism. This identifies group-algebra faithfulness, rather
than injectivity of the group homomorphism, in the criterion arising from SCP10,
Definition 4.5 and Lemma 4.6, lines 1010–1029. -/
theorem linearIndependent_iff_injective_asAlgebraHom (ρ : Representation k M W) :
    LinearIndependent k (fun g => ρ g) ↔ Function.Injective ρ.asAlgebraHom := by
  have heq : (MonoidAlgebra.basis M k).constr k (fun g => ρ g) =
      ρ.asAlgebraHom.toLinearMap := by
    apply (MonoidAlgebra.basis M k).ext
    intro g
    change ((MonoidAlgebra.basis M k).constr k (fun g => ρ g))
      ((MonoidAlgebra.basis M k) g) = _
    rw [Basis.constr_basis]
    simp
  constructor
  · intro h
    change Function.Injective ρ.asAlgebraHom.toLinearMap
    rw [← heq]
    exact (MonoidAlgebra.basis M k).injective_constr_of_linearIndependent (R₂ := k) h
  · intro h
    change Function.Injective ρ.asAlgebraHom.toLinearMap at h
    have hb := (ρ.asAlgebraHom.toLinearMap.linearIndependent_iff_of_injOn h.injOn).mpr
      (MonoidAlgebra.basis M k).linearIndependent
    simpa only [Function.comp_def, MonoidAlgebra.basis_apply,
      AlgHom.toLinearMap_apply, asAlgebraHom_single_one] using hb

end GroupAlgebra

section SemiRegular

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Independent group operators contain every irreducible representation. An absent
irreducible would yield a zero character projector with a nonzero identity coefficient.
Source: the converse algebraic criterion to SCP10, Definition 4.5 and Lemma 4.6,
lines 1010–1029. -/
theorem isSemiRegular_of_linearIndependent (ρ : Representation ℂ G V)
    (hρ : LinearIndependent ℂ fun g => ρ g) :
    ρ.IsSemiRegular := by
  let _ := Fintype.ofFinite G
  intro W _ _ _ σ hσ
  let := hσ
  classical
  by_contra! hf
  have hχ : ∀ (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible],
      S.toRepresentation.character ≠ σ.character := by
    intro S hS heq
    obtain ⟨e⟩ := (nonempty_equiv_iff_character_eq σ S.toRepresentation).mpr heq.symm
    let f : IntertwiningMap σ ρ :=
      ⟨S.toSubmodule.subtype ∘ₗ e.toLinearEquiv.toLinearMap, fun g => by
        ext w
        exact congrArg Subtype.val (LinearMap.congr_fun (e.isIntertwining' g) w)⟩
    have hzero := hf f
    have hezero : ∀ w, e w = 0 := by
      intro w
      apply Subtype.ext
      exact congrArg (fun F : IntertwiningMap σ ρ => F w) hzero
    have := nontrivial_of_isIrreducible σ
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (e.toLinearEquiv.injective (by simpa using hezero w))
  have hzero : charProjector ρ σ.character = 0 := by
    obtain ⟨s, hsA, hs⟩ := exists_isInternal_isAtom ρ
    apply hs.linearMap_ext
    intro S v hv
    let := Subrepresentation.isIrreducible_toRepresentation_of_isAtom (hsA S.1 S.2)
    rw [charProjector_apply_of_mem ρ σ S.1 hv, ite_eq_right (hχ S.1), LinearMap.zero_apply]
  have hd : σ.character 1 ≠ 0 := by
    rw [char_one, Nat.cast_ne_zero]
    exact (finrank_pos_of_isIrreducible σ).ne'
  have hsum : ∑ g : G, σ.character g⁻¹ • ρ g = 0 := by
    have hc : σ.character 1 / (Nat.card G : ℂ) ≠ 0 :=
      div_ne_zero hd (natCard_ne_zero_complex (G := G))
    exact (smul_eq_zero.mp hzero).resolve_left hc
  have hz := (Fintype.linearIndependent_iff.mp hρ) _ hsum 1
  exact hd (by simpa using hz)

/-- Semi-regularity is exactly linear independence of the group operators.
Source: SCP10, Definition 4.5 and the trace-dual identity in Lemma 4.6, lines 1010–1029,
together with the converse obtained from the character projectors of lines 983–990. -/
theorem isSemiRegular_iff_linearIndependent (ρ : Representation ℂ G V) :
    ρ.IsSemiRegular ↔ LinearIndependent ℂ fun g => ρ g :=
  ⟨linearIndependent_of_isSemiRegular ρ, isSemiRegular_of_linearIndependent ρ⟩

/-- A finite-dimensional complex representation is semi-regular exactly when its
group-algebra action is faithful. Source: algebraic reformulation of SCP10,
Definition 4.5 and Lemma 4.6, lines 1010–1029. -/
theorem isSemiRegular_iff_injective_asAlgebraHom (ρ : Representation ℂ G V) :
    ρ.IsSemiRegular ↔ Function.Injective ρ.asAlgebraHom :=
  (isSemiRegular_iff_linearIndependent ρ).trans
    (linearIndependent_iff_injective_asAlgebraHom ρ)

private theorem transpose_injective : Function.Injective
    (Module.Dual.transpose : Module.End ℂ V →ₗ[ℂ] Module.End ℂ (Module.Dual ℂ V)) := by
  intro f g hfg
  exact (Module.dualMap_dualMap_eq_iff ℂ V).mp (congrArg LinearMap.dualMap hfg)

/-- Reversing the orientation of a semi-regular bond preserves semi-regularity:
the outgoing leg carries the contragredient representation. Source: SCP10,
Definition 5.1 and the cancellation in Lemma 5.2, lines 1278–1296 and 1334–1337. -/
theorem IsSemiRegular.dual {ρ : Representation ℂ G V} (hρ : ρ.IsSemiRegular) :
    ρ.dual.IsSemiRegular := by
  apply isSemiRegular_of_linearIndependent
  exact ((linearIndependent_of_isSemiRegular ρ hρ).comp (fun g => g⁻¹)
    (Equiv.inv G).injective).map' Module.Dual.transpose
      (LinearMap.ker_eq_bot.mpr transpose_injective)

/-- A representation and its contragredient are semi-regular simultaneously.
Source: the orientation convention of SCP10, Definition 5.1 and Lemma 5.2,
lines 1278–1296 and 1334–1337. -/
theorem isSemiRegular_dual_iff (ρ : Representation ℂ G V) :
    ρ.dual.IsSemiRegular ↔ ρ.IsSemiRegular := by
  refine ⟨fun h => ?_, IsSemiRegular.dual⟩
  apply isSemiRegular_of_linearIndependent
  apply LinearIndependent.of_comp Module.Dual.transpose
  simpa only [Function.comp_def, dual_apply, inv_inv] using
    (linearIndependent_of_isSemiRegular ρ.dual h).comp (fun g => g⁻¹)
      (Equiv.inv G).injective

end SemiRegular

end Representation
