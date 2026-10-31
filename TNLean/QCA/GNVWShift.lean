/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.GNVWIndex
import TNLean.QCA.KroneckerSupportAlgebra
import TNLean.QCA.QuasiLocalTranslation

/-!
# Direct GNVW normalization of the two one-site translations

The source Heisenberg shift moves observables left, so it is translation
by minus one. Its actual finite image is the full left tensor factor;
its supports are therefore full on the left and scalar on the right.
The opposite translation has the reversed pair of support factors.

Source: GNVW, arXiv:0910.3675v2, equations RR2x and dimtransfer and their
shift example, lines 1251--1268 and 1317--1329. The inverse-orientation
calculation is a convention check, not a printed composition/inversion law.

**Scope restriction (homogeneous chain):** The fixed on-site size is
positive; see `docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
No regrouping-independence or composition theorem is used.

**Local fix (shift-example subscript):** The scalar support in the source
shift example is the odd support; line 1268 repeats the even subscript.
The correction is recorded in
`docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
-/

namespace SpinChain

variable (d : ℕ) [NeZero d]

/-- Translation has its actual singleton propagation neighbourhood.
This identifies the source Heisenberg shift orientation before enlarging
the neighbourhood; GNVW, arXiv:0910.3675v2, lines 609--621 and 1251--1268. -/
theorem quasiLocalTranslation_propagatesWithin_singleton (a : ℤ) :
    PropagatesWithin (quasiLocalTranslation d a) {a} := by
  intro Λ z hz
  obtain ⟨A, rfl⟩ := hz
  rw [quasiLocalTranslation_quasiLocalObservable, regionSumset_singleton_right]
  exact QuasiLocalSupportedIn.quasiLocalObservable _

/-- The source Heisenberg shift, which moves observables left and states
right, has the required nearest-neighbour presentation. Source: GNVW,
arXiv:0910.3675v2, lines 609--621 and 1251--1268. -/
theorem quasiLocalTranslation_propagatesWithin_neg_one :
    PropagatesWithin (quasiLocalTranslation d (-1)) (Finset.Icc (-1) 1) := by
  apply (quasiLocalTranslation_propagatesWithin_singleton d (-1)).mono
  intro a ha
  have ha' : a = -1 := Finset.mem_singleton.mp ha
  subst a
  norm_num

/-- The opposite observable translation also has a nearest-neighbour
presentation; this is the direct inverse-orientation convention check
for GNVW, arXiv:0910.3675v2, lines 609--621 and 1317--1329. -/
theorem quasiLocalTranslation_propagatesWithin_one :
    PropagatesWithin (quasiLocalTranslation d 1) (Finset.Icc (-1) 1) := by
  apply (quasiLocalTranslation_propagatesWithin_singleton d 1).mono
  intro a ha
  have ha' : a = 1 := Finset.mem_singleton.mp ha
  subst a
  norm_num

/-- Translation maps a full finite-region algebra onto the full algebra
of the translated region, not just into it. This is the local content
of the GNVW shift example, arXiv:0910.3675v2, lines 1251--1268. -/
theorem range_quasiLocalTranslation_comp_quasiLocalObservable (a : ℤ) (Λ : Finset ℤ) :
    ((quasiLocalTranslation d a).toStarAlgHom.comp (quasiLocalObservable d Λ)).range =
      (quasiLocalObservable d (translateRegion a Λ)).range := by
  ext z
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨localTranslation d a Λ A,
      (quasiLocalTranslation_quasiLocalObservable d a Λ A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨(localTranslation d a Λ).symm A, ?_⟩
    change quasiLocalTranslation d a
      (quasiLocalObservable d Λ ((localTranslation d a Λ).symm A)) = _
    rw [quasiLocalTranslation_quasiLocalObservable, StarAlgEquiv.apply_symm_apply]
    rfl

variable {d}

/-- The source left-moving observable shift sends the source even pair
exactly onto its left target pair; GNVW, arXiv:0910.3675v2, RR2x shift example. -/
theorem translateRegion_neg_one_evenPair (x : ℤ) :
    translateRegion (-1) (evenPair x) = leftPair x := by
  ext i
  simp only [mem_translateRegion, evenPair, leftPair,
    Finset.mem_insert, Finset.mem_singleton]
  omega

/-- The opposite observable shift sends the source even pair onto its
right target pair; direct GNVW convention check, arXiv:0910.3675v2, lines 1251--1268. -/
theorem translateRegion_one_evenPair (x : ℤ) :
    translateRegion 1 (evenPair x) = rightPair x := by
  ext i
  simp only [mem_translateRegion, evenPair, rightPair,
    Finset.mem_insert, Finset.mem_singleton]
  omega

namespace PropagatesWithin

/-- The source shift's actual finite local image is the full left tensor
factor in canonical ordered coordinates; GNVW, arXiv:0910.3675v2,
equation RR2x and shift example, lines 1251--1268. -/
theorem evenPairLocalImage_quasiLocalTranslation_neg_one (x : ℤ) :
    evenPairLocalImage (quasiLocalTranslation_propagatesWithin_neg_one d) x =
      (Matrix.leftKroneckerEmbed (m := Config d (leftPair x))
        (n := Config d (rightPair x))).range := by
  apply StarSubalgebra.map_injective
    (bipartiteMatrixToQuasiLocalObservable_injective (disjoint_leftPair_rightPair x))
  rw [evenPairLocalImage_map_bipartiteMatrixToQuasiLocalObservable,
    map_range_leftKroneckerEmbed_bipartiteMatrixToQuasiLocalObservable,
    range_quasiLocalTranslation_comp_quasiLocalObservable, translateRegion_neg_one_evenPair]

/-- The opposite translation has the full right tensor factor as its
actual finite image; direct orientation check for GNVW,
arXiv:0910.3675v2, equation RR2x, lines 1251--1268. -/
theorem evenPairLocalImage_quasiLocalTranslation_one (x : ℤ) :
    evenPairLocalImage (quasiLocalTranslation_propagatesWithin_one d) x =
      (Matrix.rightKroneckerEmbed (m := Config d (leftPair x))
        (n := Config d (rightPair x))).range := by
  apply StarSubalgebra.map_injective
    (bipartiteMatrixToQuasiLocalObservable_injective (disjoint_leftPair_rightPair x))
  rw [evenPairLocalImage_map_bipartiteMatrixToQuasiLocalObservable,
    map_range_rightKroneckerEmbed_bipartiteMatrixToQuasiLocalObservable,
    range_quasiLocalTranslation_comp_quasiLocalObservable, translateRegion_one_evenPair]

/-- Directly computed full-even/scalar-odd support of the source shift.
The scalar factor corrects the repeated even subscript in GNVW's printed
example; arXiv:0910.3675v2, line 1268. -/
theorem supportAlgebras_quasiLocalTranslation_neg_one (x : ℤ) :
    evenSupportAlgebra (quasiLocalTranslation_propagatesWithin_neg_one d) x = ⊤ ∧
      oddSupportAlgebra (quasiLocalTranslation_propagatesWithin_neg_one d) x = ⊥ := by
  simp only [evenSupportAlgebra, oddSupportAlgebra,
    evenPairLocalImage_quasiLocalTranslation_neg_one,
    Matrix.leftSupportAlgebra_range_leftKroneckerEmbed,
    Matrix.rightSupportAlgebra_range_leftKroneckerEmbed, and_self]

/-- Directly computed scalar-even/full-odd supports of the opposite
translation; this checks the GNVW shift orientation without assuming
an index-inversion theorem, arXiv:0910.3675v2, lines 609--621 and 1317--1329. -/
theorem supportAlgebras_quasiLocalTranslation_one (x : ℤ) :
    evenSupportAlgebra (quasiLocalTranslation_propagatesWithin_one d) x = ⊥ ∧
      oddSupportAlgebra (quasiLocalTranslation_propagatesWithin_one d) x = ⊤ := by
  simp only [evenSupportAlgebra, oddSupportAlgebra,
    evenPairLocalImage_quasiLocalTranslation_one,
    Matrix.leftSupportAlgebra_range_rightKroneckerEmbed,
    Matrix.rightSupportAlgebra_range_rightKroneckerEmbed, and_self]

private noncomputable def fullMatrixSubtypeEquiv (m : Type*) [Fintype m] [DecidableEq m] :
    ↥(⊤ : StarSubalgebra ℂ (Matrix m m ℂ)) ≃⋆ₐ[ℂ] Matrix m m ℂ :=
  StarAlgEquiv.ofBijective (⊤ : StarSubalgebra ℂ (Matrix m m ℂ)).subtype
    ⟨Subtype.val_injective, fun A ↦ ⟨⟨A, StarSubalgebra.mem_top⟩, rfl⟩⟩

/-- The actual even support matrix size of the source shift is the full
physical pair size, computed by its full-matrix presentation;
GNVW, arXiv:0910.3675v2, shift example, lines 1251--1268 and 1325--1329. -/
theorem supportAlgebraMatrixSize_quasiLocalTranslation_neg_one_even (x : ℤ) :
    supportAlgebraMatrixSize (quasiLocalTranslation_propagatesWithin_neg_one d) (2 * x) =
      d * d := by
  let e : ↥(evenSupportAlgebra (quasiLocalTranslation_propagatesWithin_neg_one d) x)
      ≃⋆ₐ[ℂ] Matrix (Fin (Fintype.card (Config d (leftPair x))))
        (Fin (Fintype.card (Config d (leftPair x)))) ℂ := by
    rw [(supportAlgebras_quasiLocalTranslation_neg_one x).1]
    exact (fullMatrixSubtypeEquiv (Config d (leftPair x))).trans
      (Matrix.matrixReindexStarAlgEquiv (Fintype.equivFin (Config d (leftPair x))))
  have hsize := supportAlgebraMatrixSize_even_eq_of_equiv
    (quasiLocalTranslation_propagatesWithin_neg_one d) x e
  have hcard : Fintype.card (Config d (leftPair x)) = d * d := by
    rw [card_config]
    have hne : 2 * x - 1 ≠ 2 * x := by omega
    simp [leftPair, hne, pow_two]
  exact hsize.trans hcard

/-- The source shift's scalar odd factor has actual matrix size one,
derived from its companion full factor and the product identity;
GNVW, arXiv:0910.3675v2, shift example, lines 1251--1268 and 1325--1329. -/
theorem supportAlgebraMatrixSize_quasiLocalTranslation_neg_one_odd (x : ℤ) :
    supportAlgebraMatrixSize (quasiLocalTranslation_propagatesWithin_neg_one d) (2 * x + 1) =
      1 := by
  have h := (supportAlgebraMatrixSize_spec
    (quasiLocalTranslation_propagatesWithin_neg_one d)).2.2.2.1 x
  rw [supportAlgebraMatrixSize_quasiLocalTranslation_neg_one_even] at h
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne d)) (Nat.pos_of_ne_zero (NeZero.ne d)))
  simpa only [mul_one] using h

/-- The opposite translation's full odd support has matrix size equal to
the full physical pair size; direct inverse-orientation check for GNVW,
arXiv:0910.3675v2, lines 1251--1268 and 1325--1329. -/
theorem supportAlgebraMatrixSize_quasiLocalTranslation_one_odd (x : ℤ) :
    supportAlgebraMatrixSize (quasiLocalTranslation_propagatesWithin_one d) (2 * x + 1) =
      d * d := by
  let e : ↥(oddSupportAlgebra (quasiLocalTranslation_propagatesWithin_one d) x)
      ≃⋆ₐ[ℂ] Matrix (Fin (Fintype.card (Config d (rightPair x))))
        (Fin (Fintype.card (Config d (rightPair x)))) ℂ := by
    rw [(supportAlgebras_quasiLocalTranslation_one x).2]
    exact (fullMatrixSubtypeEquiv (Config d (rightPair x))).trans
      (Matrix.matrixReindexStarAlgEquiv (Fintype.equivFin (Config d (rightPair x))))
  have hsize := supportAlgebraMatrixSize_odd_eq_of_equiv
    (quasiLocalTranslation_propagatesWithin_one d) x e
  have hcard : Fintype.card (Config d (rightPair x)) = d * d := by
    rw [card_config]
    have hne : 2 * x + 1 ≠ 2 * x + 2 := by omega
    simp [rightPair, hne, pow_two]
  exact hsize.trans hcard

/-- The opposite translation's scalar even support has matrix size one;
this follows directly from its computed full odd support and the actual
size identity, with no index-inversion premise. GNVW convention check,
arXiv:0910.3675v2, lines 1251--1268 and 1325--1329. -/
theorem supportAlgebraMatrixSize_quasiLocalTranslation_one_even (x : ℤ) :
    supportAlgebraMatrixSize (quasiLocalTranslation_propagatesWithin_one d) (2 * x) = 1 := by
  have h := (supportAlgebraMatrixSize_spec
    (quasiLocalTranslation_propagatesWithin_one d)).2.2.2.1 x
  rw [supportAlgebraMatrixSize_quasiLocalTranslation_one_odd] at h
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne d)) (Nat.pos_of_ne_zero (NeZero.ne d)))
  simpa only [one_mul] using h

/-- Direct normalization of the source Heisenberg shift: moving
observables left, and states right, has positive-rational index d.
Source: GNVW, arXiv:0910.3675v2, dimtransfer shift calculation, lines 1325--1329. -/
theorem gnvwIndex_quasiLocalTranslation_neg_one :
    gnvwIndex (quasiLocalTranslation_propagatesWithin_neg_one d) =
      ⟨(d : ℚ), by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)⟩ := by
  apply Subtype.ext
  change (gnvwIndex (quasiLocalTranslation_propagatesWithin_neg_one d) : ℚ) = (d : ℚ)
  rw [coe_gnvwIndex_eq_even (quasiLocalTranslation_propagatesWithin_neg_one d) 0,
    supportAlgebraMatrixSize_quasiLocalTranslation_neg_one_even]
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne d
  push_cast
  field_simp [hd]

/-- Direct inverse-orientation normalization: observable translation
right has index d⁻¹. This is a convention check from its actual finite
supports, without assuming a composition or inversion law; GNVW,
arXiv:0910.3675v2, lines 609--621 and 1325--1329. -/
theorem gnvwIndex_quasiLocalTranslation_one :
    gnvwIndex (quasiLocalTranslation_propagatesWithin_one d) =
      ⟨(d : ℚ)⁻¹, inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))⟩ := by
  apply Subtype.ext
  change (gnvwIndex (quasiLocalTranslation_propagatesWithin_one d) : ℚ) = (d : ℚ)⁻¹
  rw [coe_gnvwIndex_eq_even (quasiLocalTranslation_propagatesWithin_one d) 0,
    supportAlgebraMatrixSize_quasiLocalTranslation_one_even]
  simp only [Nat.cast_one, one_div]

end PropagatesWithin
end SpinChain
