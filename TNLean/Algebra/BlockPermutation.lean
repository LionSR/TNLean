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
  simpa using Pi.isAtom_single (isAtom_top (α := TwoSidedIdeal (R i)))

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

end BlockPermutation

end MPSTensor
