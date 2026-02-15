import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Order.Atoms

/-!
# Block permutation for products of simple rings

This file proves a key algebraic fact used in the multi-block Fundamental Theorem of MPS:

*If each factor `R i` is a simple (nontrivial) ring and `ι` is finite, then the atoms (minimal
nonzero two-sided ideals) of the product ring `∀ i, R i` are exactly the coordinate "block" ideals.*

As a consequence, any ring automorphism of `∀ i, R i` permutes these atoms, yielding a permutation
of the index type.
-/

set_option linter.unusedSectionVars false

namespace MPSTensor

section PiTwoSidedIdeals

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable {R : ι → Type*} [∀ i, Ring (R i)]

/-- Two-sided ideals of a finite product ring are order-isomorphic to a product of two-sided
ideal lattices. -/
noncomputable def twoSidedIdealPiOrderIso :
    TwoSidedIdeal (∀ i, R i) ≃o (∀ i, TwoSidedIdeal (R i)) := by
  classical
  -- We use Ideal.piOrderIso and conjugate with asIdeal/toTwoSided.
  -- Key helper: for any TwoSidedIdeal I, I.asIdeal.toTwoSided = I
  -- and for any Ideal J [J.IsTwoSided], J.toTwoSided.asIdeal = J.
  let fwd : TwoSidedIdeal (∀ i, R i) → (∀ i, TwoSidedIdeal (R i)) :=
    fun I i => (I.asIdeal.map (Pi.evalRingHom R i)).toTwoSided
  let bwd : (∀ i, TwoSidedIdeal (R i)) → TwoSidedIdeal (∀ i, R i) :=
    fun I => (Ideal.pi fun i => (I i).asIdeal).toTwoSided
  have hfwd_mono : Monotone fwd := by
    intro I J hIJ i x hx
    exact (Ideal.mem_toTwoSided).2
      (Ideal.map_mono (f := Pi.evalRingHom R i)
        (show I.asIdeal ≤ J.asIdeal from fun x hx =>
          (TwoSidedIdeal.mem_asIdeal).2 (hIJ ((TwoSidedIdeal.mem_asIdeal).1 hx)))
        ((Ideal.mem_toTwoSided).1 hx))
  have hbwd_mono : Monotone bwd := by
    intro I J hIJ x hx
    refine (Ideal.mem_toTwoSided).2 ?_
    rw [Ideal.mem_pi]
    intro i
    have hx' : x i ∈ (I i).asIdeal := by
      have h := (Ideal.mem_toTwoSided).1 hx
      rw [Ideal.mem_pi] at h; exact h i
    exact (TwoSidedIdeal.mem_asIdeal).2 (hIJ i ((TwoSidedIdeal.mem_asIdeal).1 hx'))
  -- Round-trip: fwd (bwd x) = x
  have hfb : ∀ x, fwd (bwd x) = x := by
    intro x; funext i
    -- fwd (bwd x) i = ((bwd x).asIdeal.map (Pi.evalRingHom R i)).toTwoSided
    -- bwd x = (Ideal.pi (fun i => (x i).asIdeal)).toTwoSided
    -- (bwd x).asIdeal = Ideal.pi (fun i => (x i).asIdeal)  [by Ideal.asIdeal_toTwoSided]
    -- So fwd (bwd x) i = ((Ideal.pi (fun j => (x j).asIdeal)).map (Pi.evalRingHom R i)).toTwoSided
    -- = ((x i).asIdeal).toTwoSided  [by Ideal.map_evalRingHom_pi]
    -- = x i  [by simp]
    have h_asIdeal : (bwd x).asIdeal = Ideal.pi (fun j => (x j).asIdeal) :=
      Ideal.asIdeal_toTwoSided _
    have h_map : (Ideal.pi fun j => (x j).asIdeal).map (Pi.evalRingHom R i) = (x i).asIdeal :=
      Ideal.map_evalRingHom_pi (R := R) (I := fun j => (x j).asIdeal) i
    ext y
    simp only [fwd, Ideal.mem_toTwoSided]
    rw [h_asIdeal, h_map]
    exact TwoSidedIdeal.mem_asIdeal
  -- Round-trip: bwd (fwd x) = x
  have hbf : ∀ x, bwd (fwd x) = x := by
    intro x
    -- bwd (fwd x) = (Ideal.pi (fun i => (fwd x i).asIdeal)).toTwoSided
    -- (fwd x i).asIdeal = (x.asIdeal.map (Pi.evalRingHom R i)).toTwoSided.asIdeal
    --                    = x.asIdeal.map (Pi.evalRingHom R i)  [by Ideal.asIdeal_toTwoSided]
    -- So bwd (fwd x) = (Ideal.pi (fun i => x.asIdeal.map (Pi.evalRingHom R i))).toTwoSided
    --                 = x.asIdeal.toTwoSided  [by Ideal.piOrderIso.symm_apply_apply]
    --                 = x
    have h_each : ∀ i, (fwd x i).asIdeal = x.asIdeal.map (Pi.evalRingHom R i) := by
      intro i; exact Ideal.asIdeal_toTwoSided _
    have h_pi : Ideal.pi (fun i => x.asIdeal.map (Pi.evalRingHom R i)) = x.asIdeal :=
      (Ideal.piOrderIso (R := R)).symm_apply_apply x.asIdeal
    ext y
    simp only [bwd, fwd, Ideal.mem_toTwoSided]
    constructor
    · intro hy
      have hmem : ∀ i, y i ∈ (fwd x i).asIdeal := by rw [Ideal.mem_pi] at hy; exact hy
      have hy' : y ∈ Ideal.pi (fun i => x.asIdeal.map (Pi.evalRingHom R i)) := by
        rw [Ideal.mem_pi]; intro i; rw [← h_each i]; exact hmem i
      rw [h_pi] at hy'; exact (TwoSidedIdeal.mem_asIdeal).1 hy'
    · intro hy
      rw [Ideal.mem_pi]; intro i
      have hy' : y ∈ x.asIdeal := (TwoSidedIdeal.mem_asIdeal).2 hy
      rw [← h_pi] at hy'
      have hmem : y i ∈ x.asIdeal.map (Pi.evalRingHom R i) := by
        rw [Ideal.mem_pi] at hy'; exact hy' i
      simp only [Ideal.asIdeal_toTwoSided]; exact hmem
  exact {
    toFun := fwd
    invFun := bwd
    left_inv := hbf
    right_inv := hfb
    map_rel_iff' := by
      intro a b
      exact ⟨fun h => (hbf a).symm ▸ (hbf b).symm ▸ hbwd_mono h, fun h => hfwd_mono h⟩
  }

end PiTwoSidedIdeals

section BlockPermutation

variable {ι : Type*} [Finite ι] [DecidableEq ι]
variable {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)]

/-- The `i`-th *block ideal* in the product ring `∀ j, R j`. -/
noncomputable def blockIdeal (R : ι → Type*) [∀ i, Ring (R i)] [∀ i, IsSimpleRing (R i)] (i : ι) :
    TwoSidedIdeal (∀ j, R j) :=
  (twoSidedIdealPiOrderIso (R := R)).symm (Function.update (⊥ : ∀ j, TwoSidedIdeal (R j)) i ⊤)

@[simp] lemma twoSidedIdealPiOrderIso_blockIdeal (i : ι) :
    twoSidedIdealPiOrderIso (R := R) (blockIdeal R i) =
      Function.update (⊥ : ∀ j, TwoSidedIdeal (R j)) i ⊤ := by
  simp [blockIdeal]

/-- Each block ideal is an atom in the lattice of two-sided ideals. -/
theorem isAtom_blockIdeal (i : ι) : IsAtom (blockIdeal R i) := by
  classical
  have htop : IsAtom (⊤ : TwoSidedIdeal (R i)) := isAtom_top
  have himage :
      IsAtom (Function.update (⊥ : ∀ j, TwoSidedIdeal (R j)) i (⊤ : TwoSidedIdeal (R i))) :=
    Pi.isAtom_single htop
  rw [← (twoSidedIdealPiOrderIso (R := R)).isAtom_iff]
  simpa [twoSidedIdealPiOrderIso_blockIdeal] using himage

/-- Atoms in `TwoSidedIdeal (∀ i, R i)` are exactly the block ideals. -/
theorem isAtom_iff_exists_eq_blockIdeal (I : TwoSidedIdeal (∀ i, R i)) :
    IsAtom I ↔ ∃ i, I = blockIdeal R i := by
  classical
  constructor
  · intro hI
    have hI' : IsAtom (twoSidedIdealPiOrderIso (R := R) I) :=
      (twoSidedIdealPiOrderIso (R := R)).isAtom_iff I |>.2 hI
    rcases (Pi.isAtom_iff_eq_single (f := twoSidedIdealPiOrderIso (R := R) I)).1 hI' with
      ⟨i, a, ha, haEq⟩
    have haTop : a = (⊤ : TwoSidedIdeal (R i)) :=
      (IsSimpleOrder.eq_bot_or_eq_top a).resolve_left ha.ne_bot
    have hUpdate :
        twoSidedIdealPiOrderIso (R := R) I =
          Function.update (⊥ : ∀ j, TwoSidedIdeal (R j)) i ⊤ := by
      rw [haEq, haTop]
    refine ⟨i, ?_⟩
    have h := congrArg ((twoSidedIdealPiOrderIso (R := R)).symm) hUpdate
    simp at h
    simp [blockIdeal, h]
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
  have : (⊤ : TwoSidedIdeal (R i)) = (⊥ : TwoSidedIdeal (R i)) := by
    have := congrFun hij' i
    simp only [Function.update_self, Function.update_of_ne hne] at this
    exact this
  exact top_ne_bot this

/-- Any atom of `TwoSidedIdeal (∀ i, R i)` corresponds to a *unique* block ideal. -/
theorem existsUnique_eq_blockIdeal (I : TwoSidedIdeal (∀ i, R i)) (hI : IsAtom I) :
    ∃! i, I = blockIdeal R i := by
  rcases (isAtom_iff_exists_eq_blockIdeal I).1 hI with ⟨i, hi⟩
  refine ⟨i, hi, fun j hj => ?_⟩
  have : blockIdeal R i = blockIdeal R j := hi.symm.trans hj
  exact (blockIdeal_injective this).symm

/-- A ring automorphism of `∀ i, R i` (product of simple rings) permutes the block ideals,
yielding a permutation `σ : ι ≃ ι`. -/
theorem ringEquiv_pi_simple_permutes_blockIdeals
    (T : (∀ i, R i) ≃+* (∀ i, R i)) :
    ∃ σ : ι ≃ ι, ∀ i : ι,
      T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R (σ i) := by
  classical
  have huniq : ∀ i : ι, ∃! j : ι,
      T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R j := by
    intro i
    exact existsUnique_eq_blockIdeal _
      ((T.mapTwoSidedIdeal.isAtom_iff _).2 (isAtom_blockIdeal i))
  let σfun : ι → ι := fun i => (huniq i).choose
  have hσfun : ∀ i,
      T.mapTwoSidedIdeal (blockIdeal R i) = blockIdeal R (σfun i) :=
    fun i => (huniq i).choose_spec.1
  have hσfun_inj : Function.Injective σfun := by
    intro i j hij
    have : T.mapTwoSidedIdeal (blockIdeal R i) =
           T.mapTwoSidedIdeal (blockIdeal R j) := by
      rw [hσfun i, hσfun j, hij]
    exact blockIdeal_injective (T.mapTwoSidedIdeal.injective this)
  have hσfun_surj : Function.Surjective σfun := by
    intro k
    let Ipre := T.mapTwoSidedIdeal.symm (blockIdeal R k)
    have hAtomIpre : IsAtom Ipre := by
      rw [← T.mapTwoSidedIdeal.isAtom_iff]
      simp only [Ipre, OrderIso.apply_symm_apply]
      exact isAtom_blockIdeal k
    rcases (isAtom_iff_exists_eq_blockIdeal Ipre).1 hAtomIpre with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have himg : T.mapTwoSidedIdeal Ipre = blockIdeal R k := by simp [Ipre]
    rw [hi] at himg
    apply blockIdeal_injective (R := R)
    rw [← himg, hσfun i]
  exact ⟨Equiv.ofBijective σfun ⟨hσfun_inj, hσfun_surj⟩, fun i => by
    simp only [Equiv.ofBijective_apply]; exact hσfun i⟩

end BlockPermutation

end MPSTensor
