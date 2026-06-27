/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.StarSubalgebraIrreducibleDecomp
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Schur's lemma on the irreducible pieces of a star-subalgebra

This file proves the Schur step in the structure theory of Wolf Ch. 6 (towards Thm 6.14):
on an irreducible invariant subspace of a star-subalgebra of complex matrices, every
operator commuting with the subalgebra acts as a scalar.

The orthogonal irreducible decomposition (companion file) splits the representation space
into mutually orthogonal pieces on each of which the subalgebra acts irreducibly. The next
step towards the structure theorem groups these pieces by isomorphism type; the grouping is
driven by the size of the commutant of the subalgebra on each piece, and Schur's lemma pins
that commutant down to the scalars over an algebraically closed field.

## Main results

* `StarSubalgebra.intertwiner_zero_or_isomorphism` -- a complex-linear operator carrying one
  irreducible invariant subspace into another and commuting there with the subalgebra is
  either zero on the source or an isomorphism of the source onto the target.
* `StarSubalgebra.exists_eq_smul_of_commute_of_irreducible` -- on an irreducible invariant
  subspace, a complex-linear operator that preserves the subspace and commutes there with
  every member of the subalgebra is a scalar multiple of the identity on that subspace.

## Proof outline

Restrict the commuting operator to the irreducible piece, which is a nonzero
finite-dimensional complex vector space, so over the complex numbers it has an eigenvalue.
The corresponding eigenspace intersected with the piece is invariant under the subalgebra
(the operator commutes with the subalgebra and the scalar commutes with everything) and is
nonzero, so by irreducibility it is the whole piece: the operator equals that scalar there.

## Remaining gap towards Wolf Thm 6.14

The scalar commutant identified here measures the multiplicity with which an irreducible type
occurs. The remaining steps are to group the irreducible pieces into isotypic components, to
equip each component with a tensor identification of the form "matrix block on the
multiplicity space", and to assemble a single unitary change of basis. Those steps are not
formalized here.
-/

open scoped Matrix

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- Schur's lemma for irreducible pieces of a star-subalgebra of complex matrices: a
complex-linear operator `f` that carries an irreducible invariant subspace `p` into another
irreducible invariant subspace `q` and commutes on `p` with every member of the subalgebra is
either zero on `p` or an isomorphism of `p` onto `q` (injective on `p` with image exactly `q`).
The kernel of `f` inside `p` and the image of `p` under `f` are both invariant under the
subalgebra, so irreducibility of `p` and of `q` forces each to be trivial or everything. Wolf
Ch. 6, towards Thm 6.14. -/
theorem intertwiner_zero_or_isomorphism
    {p q : Submodule ℂ (EuclideanSpace ℂ n)} (hp : S.IsIrreducibleSubspace p)
    (hq : S.IsIrreducibleSubspace q) {f : Module.End ℂ (EuclideanSpace ℂ n)}
    (hmap : Submodule.map f p ≤ q)
    (hcomm : ∀ A ∈ S, ∀ x ∈ p,
      f (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin A (f x)) :
    (∀ x ∈ p, f x = 0) ∨ (Set.InjOn f p ∧ Submodule.map f p = q) := by
  obtain ⟨hpinv, -, hpmax⟩ := hp
  obtain ⟨hqinv, -, hqmax⟩ := hq
  by_cases hzero : ∀ x ∈ p, f x = 0
  · exact Or.inl hzero
  refine Or.inr ⟨?_, ?_⟩
  · -- The kernel of `f` inside `p` is invariant, hence trivial since `f` is not zero on `p`.
    have hker_inv : S.IsInvariantSubspace (p ⊓ LinearMap.ker f) := by
      intro A hA
      refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := Matrix.toEuclideanLin A)).mpr fun x hx => ?_
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hx ⊢
      refine ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := Matrix.toEuclideanLin A)).mp (hpinv A hA) x hx.1, ?_⟩
      rw [hcomm A hA x hx.1, hx.2, map_zero]
    have hker : p ⊓ LinearMap.ker f = ⊥ := by
      rcases hpmax _ hker_inv inf_le_left with h | h
      · exact h
      · have hple : p ≤ LinearMap.ker f := h ▸ inf_le_right
        exact absurd (fun x hx => LinearMap.mem_ker.mp (hple hx)) hzero
    intro x hx y hy hxy
    have : x - y ∈ p ⊓ LinearMap.ker f :=
      Submodule.mem_inf.mpr ⟨p.sub_mem hx hy, by rw [LinearMap.mem_ker, map_sub, hxy, sub_self]⟩
    rw [hker, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · -- The image of `p` under `f` is invariant, hence all of `q` since it is nonzero.
    have him_inv : S.IsInvariantSubspace (Submodule.map f p) := by
      intro A hA
      refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := Matrix.toEuclideanLin A)).mpr fun y hy => ?_
      obtain ⟨x, hxp, rfl⟩ := Submodule.mem_map.mp hy
      refine Submodule.mem_map.mpr ⟨Matrix.toEuclideanLin A x,
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
          (f := Matrix.toEuclideanLin A)).mp (hpinv A hA) x hxp, hcomm A hA x hxp⟩
    rcases hqmax _ him_inv hmap with h | h
    · refine absurd (fun x hx => ?_) hzero
      have : f x ∈ Submodule.map f p := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact this
    · exact h

/-- Schur's lemma for the irreducible pieces of a star-subalgebra of complex matrices: if `p`
is an irreducible invariant subspace and `f` is a complex-linear operator that maps `p` into
itself and commutes on `p` with every member of the subalgebra, then `f` acts on `p` as a
scalar multiple of the identity. Over the complex numbers the commutant of the subalgebra on
an irreducible piece is exactly the scalars. Wolf Ch. 6, towards Thm 6.14. -/
theorem exists_eq_smul_of_commute_of_irreducible
    {p : Submodule ℂ (EuclideanSpace ℂ n)} (hirr : S.IsIrreducibleSubspace p)
    {f : Module.End ℂ (EuclideanSpace ℂ n)} (hf : p ∈ Module.End.invtSubmodule f)
    (hcomm : ∀ A ∈ S, ∀ x ∈ p,
      f (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin A (f x)) :
    ∃ c : ℂ, ∀ x ∈ p, f x = c • x := by
  obtain ⟨hinv, hpne, hmax⟩ := hirr
  -- `f` restricts to an operator on the irreducible piece `p`.
  have hmaps : ∀ x ∈ p, f x ∈ p :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := f)).mp hf
  haveI hpnt : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hpne
  -- Over `ℂ` the restricted operator has an eigenvalue, hence an eigenvector inside `p`.
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (f.restrict hmaps)
  obtain ⟨w, hw_mem, hw_ne⟩ := hc.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hw_mem
  have hfw : f (w : EuclideanSpace ℂ n) = c • (w : EuclideanSpace ℂ n) := by
    have hcoe := congrArg (Subtype.val) hw_mem
    rwa [LinearMap.coe_restrict_apply, Submodule.coe_smul] at hcoe
  -- The `c`-eigenspace of `f` inside `p`.
  set q : Submodule ℂ (EuclideanSpace ℂ n) := p ⊓ Module.End.eigenspace f c with hq
  have hmemq : ∀ x : EuclideanSpace ℂ n, x ∈ q ↔ x ∈ p ∧ f x = c • x := fun x => by
    rw [hq, Submodule.mem_inf, Module.End.mem_eigenspace_iff]
  have hq_le : q ≤ p := inf_le_left
  -- The eigenspace inside `p` is invariant under the subalgebra: the operator commutes with the
  -- subalgebra and the eigenvalue scalar commutes with everything.
  have hq_inv : S.IsInvariantSubspace q := by
    intro A hA
    refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
      (f := Matrix.toEuclideanLin A)).mpr fun x hx => ?_
    obtain ⟨hxp, hxe⟩ := (hmemq x).mp hx
    refine (hmemq _).mpr ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
      (f := Matrix.toEuclideanLin A)).mp (hinv A hA) x hxp, ?_⟩
    rw [hcomm A hA x hxp, hxe, map_smul]
  -- The eigenvector lies in `q` and is nonzero, so `q` is not the zero subspace.
  have hq_ne : q ≠ ⊥ :=
    (Submodule.ne_bot_iff q).mpr ⟨w, (hmemq _).mpr ⟨w.2, hfw⟩, fun h => hw_ne (Subtype.ext h)⟩
  -- By irreducibility `q` is all of `p`, so `f` equals `c • id` on `p`.
  rcases hmax q hq_inv hq_le with h | h
  · exact absurd h hq_ne
  · exact ⟨c, fun x hx => ((hmemq x).mp (h.symm ▸ hx)).2⟩

end StarSubalgebra
