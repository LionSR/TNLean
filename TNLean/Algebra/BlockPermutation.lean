/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Block permutation for products of simple rings

This file proves a key algebraic fact used in the multi-block Fundamental Theorem of MPS:

*If each factor `R i` is a simple (nontrivial) ring and `ι` is finite, then the atoms (minimal
nonzero two-sided ideals) of the product ring `∀ i, R i` are exactly the coordinate "block"
ideals.*

As a consequence, any ring automorphism of `∀ i, R i` permutes these atoms, yielding a permutation
of the index type.
-/

namespace MPSTensor

section PiTwoSidedIdeals

variable {ι : Type*} [Finite ι]
variable {R : ι → Type*} [∀ i, Ring (R i)]

/-- Two-sided ideals of a finite product ring are order-isomorphic to a product of two-sided ideal
lattices. -/
noncomputable def twoSidedIdealPiOrderIso :
    TwoSidedIdeal (∀ i, R i) ≃o (∀ i, TwoSidedIdeal (R i)) := by
  classical
  let fwd : TwoSidedIdeal (∀ i, R i) → (∀ i, TwoSidedIdeal (R i)) :=
    fun I i => (I.asIdeal.map (Pi.evalRingHom R i)).toTwoSided
  let bwd : (∀ i, TwoSidedIdeal (R i)) → TwoSidedIdeal (∀ i, R i) :=
    fun I => (Ideal.pi fun i => (I i).asIdeal).toTwoSided
  have hfwd_mono : Monotone fwd := by
    intro I J hIJ i x hx
    refine Ideal.mem_toTwoSided.2 ?_
    refine
      Ideal.map_mono (f := Pi.evalRingHom R i)
        (fun y hy => TwoSidedIdeal.mem_asIdeal.2 (hIJ (TwoSidedIdeal.mem_asIdeal.1 hy)))
        (Ideal.mem_toTwoSided.1 hx)
  have hbwd_mono : Monotone bwd := by
    intro I J hIJ x hx
    rw [Ideal.mem_toTwoSided] at hx ⊢
    rw [Ideal.mem_pi] at hx ⊢
    intro i
    exact TwoSidedIdeal.mem_asIdeal.2 (hIJ i (TwoSidedIdeal.mem_asIdeal.1 (hx i)))
  have hfb : ∀ x, fwd (bwd x) = x := by
    intro x
    funext i
    ext y
    simp only [fwd, bwd, Ideal.mem_toTwoSided, Ideal.asIdeal_toTwoSided,
      Ideal.map_evalRingHom_pi, TwoSidedIdeal.mem_asIdeal]
  have hbf : ∀ x, bwd (fwd x) = x := by
    intro x
    ext y
    have h_pi :
        Ideal.pi (fun i => x.asIdeal.map (Pi.evalRingHom R i)) = x.asIdeal :=
      (Ideal.piOrderIso (R := R)).symm_apply_apply x.asIdeal
    simp only [bwd, fwd, Ideal.mem_toTwoSided, Ideal.mem_pi, Ideal.asIdeal_toTwoSided]
    refine
      ⟨fun hy => TwoSidedIdeal.mem_asIdeal.1 (h_pi ▸ (Ideal.mem_pi ..).2 hy),
        fun hy i => ((Ideal.mem_pi ..).1 (h_pi ▸ TwoSidedIdeal.mem_asIdeal.2 hy)) i⟩
  exact
    { toFun := fwd
      invFun := bwd
      left_inv := hbf
      right_inv := hfb
      map_rel_iff' := by
        intro a b
        refine ⟨?_, ?_⟩
        · intro h
          simpa [hbf a, hbf b] using hbwd_mono h
        · intro h
          exact hfwd_mono h }

end PiTwoSidedIdeals

section BlockPermutation

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]

/-- The `i`-th *block ideal* in the product ring `∀ j, R j`. -/
noncomputable def blockIdeal (R : ι → Type*) [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)] (i : ι) :
    TwoSidedIdeal (∀ j, R j) :=
  (twoSidedIdealPiOrderIso (R := R)).symm
    (Function.update (⊥ : ∀ j, TwoSidedIdeal (R j)) i ⊤)

/-- An element belongs to the block ideal at `i` precisely when every other
component vanishes. -/
theorem mem_blockIdeal_iff {i : ι} {x : ∀ j, R j} :
    x ∈ blockIdeal R i ↔ ∀ j, j ≠ i → x j = 0 := by
  classical
  have hEq : blockIdeal R i =
      (Ideal.pi fun j ↦
        ((Function.update (⊥ : ∀ k, TwoSidedIdeal (R k)) i ⊤) j).asIdeal).toTwoSided := by
    simp [blockIdeal, twoSidedIdealPiOrderIso]
  rw [hEq, Ideal.mem_toTwoSided, Ideal.mem_pi]
  constructor
  · intro h j hj
    have hjMem := h j
    rw [Function.update_of_ne hj] at hjMem
    exact TwoSidedIdeal.mem_asIdeal.mp hjMem
  · intro h j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact TwoSidedIdeal.mem_asIdeal.mpr trivial
    · rw [Function.update_of_ne hj]
      exact TwoSidedIdeal.mem_asIdeal.mpr
        (h j hj ▸ (⊥ : TwoSidedIdeal (R j)).asIdeal.zero_mem)

/-- A tuple supported in one component belongs to the corresponding block
ideal. -/
theorem pi_single_mem_blockIdeal {i : ι} (x : R i) :
    Pi.single i x ∈ blockIdeal R i :=
  mem_blockIdeal_iff.mpr (fun _ hj ↦ Pi.single_eq_of_ne hj x)

/-- Under `twoSidedIdealPiOrderIso`, the block ideal becomes the function which is `⊤` at `i` and
`⊥` elsewhere. -/
@[simp] lemma twoSidedIdealPiOrderIso_blockIdeal (i : ι) :
    twoSidedIdealPiOrderIso (R := R) (blockIdeal R i) =
      Function.update (⊥ : ∀ j, TwoSidedIdeal (R j)) i ⊤ := by
  simp [blockIdeal]

/-- Each block ideal is an atom in the lattice of two-sided ideals. -/
theorem isAtom_blockIdeal (i : ι) : IsAtom (blockIdeal R i) := by
  classical
  rw [← (twoSidedIdealPiOrderIso (R := R)).isAtom_iff]
  simpa only [twoSidedIdealPiOrderIso_blockIdeal] using
    (@Pi.isAtom_single ι (fun j ↦ TwoSidedIdeal (R j)) i _ _ _ _
      (isAtom_top (α := TwoSidedIdeal (R i))))

/-- Atoms in `TwoSidedIdeal (∀ i, R i)` are exactly the block ideals. -/
theorem isAtom_iff_exists_eq_blockIdeal (I : TwoSidedIdeal (∀ i, R i)) :
    IsAtom I ↔ ∃ i, I = blockIdeal R i := by
  classical
  constructor
  · intro hI
    have hI' := (twoSidedIdealPiOrderIso (R := R)).isAtom_iff I |>.2 hI
    rcases Pi.isAtom_iff_eq_single.1 hI' with ⟨i, a, ha, haEq⟩
    refine ⟨i, ?_⟩
    have haTop := (IsSimpleOrder.eq_bot_or_eq_top a).resolve_left ha.ne_bot
    rw [haTop] at haEq
    simpa [blockIdeal] using congrArg (twoSidedIdealPiOrderIso (R := R)).symm haEq
  · rintro ⟨i, rfl⟩
    exact isAtom_blockIdeal i

/-- The assignment `i ↦ blockIdeal R i` is injective. -/
theorem blockIdeal_injective : Function.Injective (blockIdeal R) := by
  classical
  intro i j hij
  have hij' :
      Function.update (⊥ : ∀ k, TwoSidedIdeal (R k)) i ⊤ =
        Function.update (⊥ : ∀ k, TwoSidedIdeal (R k)) j ⊤ := by
    simpa [blockIdeal] using congrArg (twoSidedIdealPiOrderIso (R := R)) hij
  by_contra hne
  exact
    (top_ne_bot (α := TwoSidedIdeal (R i)))
      (by simpa [Function.update_of_ne hne] using congrFun hij' i)

/-- Any atom of `TwoSidedIdeal (∀ i, R i)` corresponds to a *unique* block ideal. -/
theorem existsUnique_eq_blockIdeal (I : TwoSidedIdeal (∀ i, R i)) (hI : IsAtom I) :
    ∃! i, I = blockIdeal R i := by
  rcases (isAtom_iff_exists_eq_blockIdeal I).1 hI with ⟨i, hi⟩
  exact ⟨i, hi, fun j hj => (blockIdeal_injective (hi.symm.trans hj)).symm⟩

/-- A ring automorphism of `∀ i, R i` (product of simple rings) permutes the block ideals,
yielding a permutation `σ : ι ≃ ι`. -/
theorem ringEquiv_pi_simple_permutes_blockIdeals
    (T : (∀ i, R i) ≃+* (∀ i, R i)) :
    ∃ σ : ι ≃ ι, ∀ i : ι, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R (σ i) := by
  classical
  have huniq :
      ∀ i, ∃! j, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R j :=
    fun i =>
      existsUnique_eq_blockIdeal _
        ((T.mapTwoSidedIdeal.isAtom_iff _).2 (isAtom_blockIdeal (R := R) i))
  let σfun : ι → ι := fun i => (huniq i).choose
  have hσfun :
      ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R (σfun i) :=
    fun i => (huniq i).choose_spec.1
  have hσfun_inj : Function.Injective σfun := by
    intro i j hij
    refine blockIdeal_injective (R := R) ?_
    refine T.mapTwoSidedIdeal.injective ?_
    simp [hσfun, hij]
  have hσfun_surj : Function.Surjective σfun := by
    intro k
    have hAtom : IsAtom (T.mapTwoSidedIdeal.symm (blockIdeal R k)) := by
      rw [← T.mapTwoSidedIdeal.isAtom_iff]
      simp [isAtom_blockIdeal]
    rcases (isAtom_iff_exists_eq_blockIdeal (R := R) _).1 hAtom with ⟨i, hi⟩
    refine ⟨i, blockIdeal_injective (R := R) ?_⟩
    rw [← hσfun i, ← hi]
    simp
  refine
    ⟨Equiv.ofBijective σfun ⟨hσfun_inj, hσfun_surj⟩, fun i => ?_⟩
  simpa using hσfun i

/-- A ring isomorphism between two finite products of simple rings matches
their block ideals through an equivalence of the two index types.

This is the simple-summand correspondence used in arXiv:1606.00608,
Appendix C.4, line 1997, and in the proof of Wolf--Perez-Garcia,
arXiv:1005.4545, Theorem 8, source lines 322--324. -/
theorem exists_blockEquiv_of_ringEquiv_pi_simple
    {κ : Type*} [Finite κ] [DecidableEq κ]
    {S : κ → Type*} [∀ j, Ring (S j)] [∀ j, IsSimpleRing (S j)]
    (T : (∀ i, R i) ≃+* (∀ j, S j)) :
    ∃ σ : ι ≃ κ,
      ∀ i : ι, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal S (σ i) := by
  classical
  have huniq :
      ∀ i, ∃! j, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal S j :=
    fun i ↦
      existsUnique_eq_blockIdeal _
        ((T.mapTwoSidedIdeal.isAtom_iff _).2 (isAtom_blockIdeal (R := R) i))
  let σfun : ι → κ := fun i ↦ (huniq i).choose
  have hσfun :
      ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal S (σfun i) :=
    fun i ↦ (huniq i).choose_spec.1
  have hσfun_inj : Function.Injective σfun := by
    intro i j hij
    refine blockIdeal_injective (R := R) ?_
    refine T.mapTwoSidedIdeal.injective ?_
    rw [hσfun i, hσfun j, hij]
  have hσfun_surj : Function.Surjective σfun := by
    intro k
    have hAtom : IsAtom (T.mapTwoSidedIdeal.symm (blockIdeal S k)) := by
      rw [← T.mapTwoSidedIdeal.isAtom_iff]
      simp [isAtom_blockIdeal]
    rcases (isAtom_iff_exists_eq_blockIdeal (R := R) _).1 hAtom with ⟨i, hi⟩
    refine ⟨i, blockIdeal_injective (R := S) ?_⟩
    rw [← hσfun i, ← hi]
    simp
  refine ⟨Equiv.ofBijective σfun ⟨hσfun_inj, hσfun_surj⟩, ?_⟩
  intro i
  simpa using hσfun i

end BlockPermutation

section BlockComponentMap

variable {ι κ : Type*} [Finite ι] [DecidableEq ι] [Finite κ] [DecidableEq κ]
variable {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]
variable {S : κ → Type*} [∀ j, Ring (S j)] [∀ j, IsSimpleRing (S j)]

/-- The component map from one simple factor to its paired factor under a
ring isomorphism of finite products.

This is the restriction to a paired summand used in the proof of
Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8, source lines 322--324. -/
noncomputable def blockComponentMap
    (T : (∀ i, R i) ≃+* (∀ j, S j)) (σ : ι ≃ κ) (i : ι) : R i → S (σ i) :=
  fun x ↦ T (Pi.single i x) (σ i)

/-- A tuple supported in one source factor is mapped into its paired target
factor.

This is the block-support consequence underlying arXiv:1005.4545,
Theorem 8, source lines 322--324. -/
theorem ringEquiv_maps_single_support_between
    (T : (∀ i, R i) ≃+* (∀ j, S j)) (σ : ι ≃ κ)
    (hσ : ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal S (σ i))
    {i : ι} (x : R i) (j : κ) (hj : j ≠ σ i) :
    T (Pi.single i x) j = 0 := by
  have hMem : T (Pi.single i x) ∈ blockIdeal S (σ i) := by
    rw [← hσ i, RingEquiv.mapTwoSidedIdeal_apply, TwoSidedIdeal.mem_comap]
    simp [pi_single_mem_blockIdeal x]
  exact (mem_blockIdeal_iff.mp hMem) j hj

/-- The inverse isomorphism carries a paired target block ideal back to its
source block ideal.

This is the inverse block-support consequence underlying arXiv:1005.4545,
Theorem 8, source lines 322--324. -/
theorem ringEquiv_symm_maps_blockIdeal_between
    (T : (∀ i, R i) ≃+* (∀ j, S j)) (σ : ι ≃ κ)
    (hσ : ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal S (σ i))
    (i : ι) :
    T.symm.mapTwoSidedIdeal (blockIdeal S (σ i)) = blockIdeal R i := by
  rw [← hσ i]
  ext x
  simp [RingEquiv.mapTwoSidedIdeal_apply, TwoSidedIdeal.mem_comap]

/-- The component map between paired simple factors is injective.

This is the injectivity used in the paired-summand argument of
arXiv:1005.4545, Theorem 8, source lines 322--324. -/
theorem blockComponentMap_injective
    (T : (∀ i, R i) ≃+* (∀ j, S j)) (σ : ι ≃ κ)
    (hσ : ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal S (σ i))
    (i : ι) : Function.Injective (blockComponentMap T σ i) := by
  intro x y hxy
  have hFull : T (Pi.single i x) = T (Pi.single i y) := by
    ext j
    by_cases hj : j = σ i
    · subst hj
      simpa only [blockComponentMap] using hxy
    · rw [ringEquiv_maps_single_support_between T σ hσ x j hj,
        ringEquiv_maps_single_support_between T σ hσ y j hj]
  have hSingle := T.injective hFull
  simpa using congrFun hSingle i

/-- The component map between paired simple factors is surjective.

This is the surjectivity used in the paired-summand argument of
arXiv:1005.4545, Theorem 8, source lines 322--324. -/
theorem blockComponentMap_surjective
    (T : (∀ i, R i) ≃+* (∀ j, S j)) (σ : ι ≃ κ)
    (hσ : ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal S (σ i))
    (i : ι) : Function.Surjective (blockComponentMap T σ i) := by
  intro y
  have hMem : T.symm (Pi.single (σ i) y) ∈ blockIdeal R i := by
    rw [← ringEquiv_symm_maps_blockIdeal_between T σ hσ i,
      RingEquiv.mapTwoSidedIdeal_apply, TwoSidedIdeal.mem_comap]
    simp [pi_single_mem_blockIdeal]
  have hEq : T.symm (Pi.single (σ i) y) =
      Pi.single i (T.symm (Pi.single (σ i) y) i) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [mem_blockIdeal_iff.mp hMem j hj, Pi.single_eq_of_ne hj]
  refine ⟨T.symm (Pi.single (σ i) y) i, ?_⟩
  simp only [blockComponentMap, ← hEq, T.apply_symm_apply, Pi.single_eq_same]

/-- The component map between paired simple factors is bijective.

This is the bijectivity used to match summand dimensions in
arXiv:1005.4545, Theorem 8, source lines 322--324. -/
theorem blockComponentMap_bijective
    (T : (∀ i, R i) ≃+* (∀ j, S j)) (σ : ι ≃ κ)
    (hσ : ∀ i, T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal S (σ i))
    (i : ι) : Function.Bijective (blockComponentMap T σ i) :=
  ⟨blockComponentMap_injective T σ hσ i,
    blockComponentMap_surjective T σ hσ i⟩

end BlockComponentMap

end MPSTensor
