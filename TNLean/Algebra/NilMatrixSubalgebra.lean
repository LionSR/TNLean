/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Nil subalgebras of finite-dimensional endomorphism algebras

This file proves the finite-dimensional nil-matrix theorem: if every element of a possibly
nonunital associative subalgebra of endomorphisms is nilpotent, then every mixed product whose
length is the dimension of the space vanishes.  The proof applies Engel's theorem to the associated
Lie algebra and bounds its lower central series by dimension.

The bound is product length `finrank K V`, not a strict bound below it.

**Local fix (arXiv:1703.09188, lines 405--426):** the paper's strict intermediate estimate is
replaced by the dimension-sharp weak bound.  The source correction is documented in
`docs/paper-gaps/mpu_nil_matrix_bound.tex`.  Classically, the algebra of strictly upper-triangular
matrices shows that products of length one less than the dimension need not vanish; no formal
sharpness example is asserted here.

For `List.prod`, factors are multiplied from left to right.  Since multiplication in
`Module.End K V` is composition, the rightmost factor acts first.
-/

open Module

namespace LieModule

variable (K L V : Type*) [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [FiniteDimensional K V]

/-- A nilpotent Lie action on a finite-dimensional vector space has lower central series zero by
step `finrank K V`. -/
theorem lowerCentralSeries_finrank_eq_bot [IsNilpotent L V] :
    lowerCentralSeries K L V (finrank K V) = ⊥ := by
  let C : ℕ → LieSubmodule K L V := lowerCentralSeries K L V
  have hstrict (k : ℕ) (hk : C k ≠ ⊥) : C (k + 1) < C k := by
    refine lt_of_le_of_ne (antitone_lowerCentralSeries K L V (Nat.le_succ k)) ?_
    intro heq
    have hstable : ∀ m : ℕ, C (k + m) = C k := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          change lowerCentralSeries K L V ((k + m) + 1) = C k
          rw [lowerCentralSeries_succ]
          change ⁅(⊤ : LieSubmodule K L L), C (k + m)⁆ = C k
          rw [ih]
          exact (show C (k + 1) = ⁅(⊤ : LieSubmodule K L L), C k⁆ by
            simp only [C, lowerCentralSeries_succ]).symm.trans heq
    obtain ⟨N, hN⟩ := IsNilpotent.nilpotent K L V
    apply hk
    rw [← hstable N]
    exact eq_bot_iff.mpr <| hN ▸ antitone_lowerCentralSeries K L V (Nat.le_add_left N k)
  have hdim : ∀ k : ℕ, C k ≠ ⊥ → finrank K (C k : Submodule K V) + k ≤ finrank K V := by
    intro k
    induction k with
    | zero =>
        intro _
        change finrank K (⊤ : Submodule K V) + 0 ≤ finrank K V
        simp
    | succ k ih =>
        intro hk
        have hk' : C k ≠ ⊥ := fun h ↦ hk <| eq_bot_iff.mpr <|
          h ▸ antitone_lowerCentralSeries K L V (Nat.le_succ k)
        have hdrop := Submodule.finrank_lt_finrank_of_lt (hstrict k hk')
        have hbound := ih hk'
        omega
  by_contra hne
  have hpos : 0 < finrank K (C (finrank K V) : Submodule K V) :=
    Module.finrank_pos_iff.mpr <| (LieSubmodule.nontrivial_iff_ne_bot K L V).mpr hne
  have := hdim (finrank K V) hne
  omega

end LieModule

namespace NonUnitalSubalgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nonunital associative subalgebra of endomorphisms, regarded as a Lie subalgebra under the
commutator bracket. -/
def toLieSubalgebra (A : NonUnitalSubalgebra K (Module.End K V)) :
    LieSubalgebra K (Module.End K V) where
  carrier := A
  add_mem' := A.add_mem
  zero_mem' := A.zero_mem
  smul_mem' := fun c _ hx ↦ A.smul_mem c hx
  lie_mem' hx hy := by
    rw [LieRing.of_associative_ring_bracket]
    exact A.sub_mem (A.mul_mem hx hy) (A.mul_mem hy hx)

variable [FiniteDimensional K V]

/-- Every mixed product of `finrank K V` elements of a nil nonunital endomorphism subalgebra
vanishes.

The statement includes the zero-dimensional case: there `finrank K V = 0`, the empty product is
the identity endomorphism, and that identity equals zero. -/
theorem list_prod_eq_zero_of_forall_isNilpotent
    (A : NonUnitalSubalgebra K (Module.End K V))
    (hnil : ∀ a : A, IsNilpotent (a : Module.End K V))
    (l : List (Module.End K V)) (hl : ∀ a ∈ l, a ∈ A)
    (hlen : l.length = finrank K V) : l.prod = 0 := by
  let L := A.toLieSubalgebra
  have hLieNil : LieModule.IsNilpotent L V :=
    (LieModule.isNilpotent_iff_forall' (R := K)).mpr fun a ↦ by
      rw [LieSubalgebra.toEnd_eq, LieModule.toEnd_module_end]
      change IsNilpotent (a : Module.End K V)
      have ha : (a : Module.End K V) ∈ A := a.property
      exact hnil (⟨a, ha⟩ : A)
  letI : LieModule.IsNilpotent L V := hLieNil
  have hmem (v : V) : l.prod v ∈ LieModule.lowerCentralSeries K L V l.length := by
    clear hlen
    induction l with
    | nil => simp
    | cons a l ih =>
        simp only [List.prod_cons, List.length_cons, Module.End.mul_apply]
        rw [LieModule.lowerCentralSeries_succ]
        have ha : a ∈ L := by
          change a ∈ A
          exact hl a List.mem_cons_self
        change ⁅(⟨a, ha⟩ : L), l.prod v⁆ ∈ _
        exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) <|
          ih fun b hb ↦ hl b (List.mem_cons_of_mem a hb)
  ext v
  rw [LinearMap.zero_apply, ← LieSubmodule.mem_bot (R := K) (L := L),
    ← LieModule.lowerCentralSeries_finrank_eq_bot K L V, ← hlen]
  exact hmem v

end NonUnitalSubalgebra

namespace NonUnitalSubalgebra

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Matrix form of the finite-dimensional nil-matrix theorem: every mixed product of
`Fintype.card n` matrices in a nil nonunital matrix subalgebra is zero. -/
theorem matrix_list_prod_eq_zero_of_forall_isNilpotent
    (A : NonUnitalSubalgebra K (Matrix n n K))
    (hnil : ∀ a : A, IsNilpotent (a : Matrix n n K))
    (l : List (Matrix n n K)) (hl : ∀ a ∈ l, a ∈ A)
    (hlen : l.length = Fintype.card n) : l.prod = 0 := by
  let e : Matrix n n K ≃ₐ[K] Module.End K (n → K) := Matrix.toLinAlgEquiv'
  let B : NonUnitalSubalgebra K (Module.End K (n → K)) := A.map e.toAlgHom.toNonUnitalAlgHom
  have hBnil : ∀ b : B, IsNilpotent (b : Module.End K (n → K)) := by
    intro b
    obtain ⟨a, ha, hab⟩ := (NonUnitalSubalgebra.mem_map).mp b.property
    rw [← hab]
    exact (hnil ⟨a, ha⟩).map e
  have hlB : ∀ b ∈ l.map e, b ∈ B := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (NonUnitalSubalgebra.mem_map).mpr ⟨a, hl a ha, rfl⟩
  apply e.injective
  rw [map_zero, map_list_prod]
  exact B.list_prod_eq_zero_of_forall_isNilpotent hBnil (l.map e) hlB <| by
    simpa [Module.finrank_pi] using hlen

end NonUnitalSubalgebra
