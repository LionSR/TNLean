/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.TwoCutEdgeSupports
import QICLean.ManyBody.Sites.ThreeRegion.Cut
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.Algebra.OperatorSchmidt.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Support of three-region operator factors

An operator supported on a set of sites induces the corresponding support
on its partial matrix elements in the middle region. Canonical embeddings
and equality of middle factors are expressed in the same three-region
coordinates `ManyBody.threeCutEquiv` of regions `A ⊆ B`, whose middle region
is `B \ A`; for two disjoint regions `T` and `E` these are the coordinates of
`A = T` and `B = T ∪ E`, whose middle region `(T ∪ E) \ T` is `E`.

For two windows of nearest-neighbour operators, the regional factors may
be chosen with their original labels. The selected crossings have operator
Schmidt rank at most the square of the local dimension. The other window
terms have middle factors supported on the complement of the strict core.
Their weighted sum is the central term plus an operator with that support.

The conclusions include zero local dimension and empty regions wherever
the stated data exist. No commutativity of the operators is assumed.

## References

Supporting locality algebra for ALVV, arXiv:1602.08828v2,
equation H-mid-cut, lines 810–821, and Proposition 5.7, lines 1324–1333.
-/

open ManyBody (disjoint_interval_interval interval interval_mono mem_interval)

open Matrix
open scoped BigOperators Kronecker

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Every matrix on a subsingleton configuration type has any designated
support. This supplies the zero-local-dimension branches without adding a
nonempty-site or nonempty-configuration premise. -/
private theorem isSupportedOn_of_subsingleton_siteConfig
    {V : Type*} {n : V → ℕ}
    [Subsingleton (∀ v, Fin (n v))]
    (X : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ) (D : Finset V) :
    ManyBody.IsSupportedOn X D := by
  refine ⟨?_, ?_⟩
  · intro σ τ hστ
    obtain ⟨v, _hv, hne⟩ := hστ
    exact False.elim (hne (congrFun (Subsingleton.elim σ τ) v))
  · intro σ τ σ' τ' _h1 _h2 _h3 _h4
    exact congrArg₂ X (Subsingleton.elim σ σ') (Subsingleton.elim τ τ')

/-- In three-region coordinates, a configuration glued from `((x, y), z)` and one glued from
`((x, y'), z)` agree at every site of `D` when `y` and `y'` agree at the sites of `D` in the
middle region `B \ A`. -/
private theorem threeCutEquiv_symm_agree_of_middle
    {V : Type*} [DecidableEq V] {q : ℕ} {A B : Finset V} (hAB : A ⊆ B) (D : Finset V)
    (c : A → Fin q) (x x' : ↥(B \ A) → Fin q) (r : {v // v ∉ B} → Fin q)
    (hxx' : ∀ e ∈ Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D), x e = x' e) :
    ∀ v ∈ D, (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm ((c, x), r) v =
      (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm ((c, x'), r) v := by
  intro v hvD
  by_cases hvM : v ∈ B \ A
  · rw [ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB hvM,
      ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB hvM]
    exact hxx' ⟨v, hvM⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD⟩)
  · by_cases hvA : v ∈ A
    · rw [ManyBody.threeCutEquiv_symm_apply_of_mem hAB hvA,
        ManyBody.threeCutEquiv_symm_apply_of_mem hAB hvA]
    · have hvB : v ∉ B := fun hvB ↦ hvM (Finset.mem_sdiff.mpr ⟨hvB, hvA⟩)
      rw [ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB hvB,
        ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB hvB]

/-- In three-region coordinates, at a site of `D` the configurations glued from
`((a, x), z)` and `((b, y), w)` agree if and only if those glued from `((a, x'), z)` and
`((b, y'), w)` agree, when `x, y` and `x', y'` agree at the middle sites outside `D`. -/
private theorem threeCutEquiv_symm_coincide_iff
    {V : Type*} [DecidableEq V] {q : ℕ} {A B : Finset V} (hAB : A ⊆ B) (D : Finset V)
    (a b : A → Fin q) (x y x' y' : ↥(B \ A) → Fin q) (z w : {v // v ∉ B} → Fin q)
    (h3 : ∀ e ∉ Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D), x e = y e)
    (h4 : ∀ e ∉ Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D), x' e = y' e) :
    ∀ v ∉ D, ((ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm ((a, x), z) v =
        (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm ((b, y), w) v ↔
      (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm ((a, x'), z) v =
        (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm ((b, y'), w) v) := by
  intro v hvD
  by_cases hvM : v ∈ B \ A
  · rw [ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB hvM,
      ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB hvM,
      ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB hvM,
      ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB hvM]
    have heD : (⟨v, hvM⟩ : ↥(B \ A)) ∉
        Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D) := by
      intro he
      exact hvD (Finset.mem_filter.mp he).2
    exact ⟨fun _ ↦ h4 _ heD, fun _ ↦ h3 _ heD⟩
  · by_cases hvA : v ∈ A
    · rw [ManyBody.threeCutEquiv_symm_apply_of_mem hAB hvA,
        ManyBody.threeCutEquiv_symm_apply_of_mem hAB hvA,
        ManyBody.threeCutEquiv_symm_apply_of_mem hAB hvA,
        ManyBody.threeCutEquiv_symm_apply_of_mem hAB hvA]
    · have hvB : v ∉ B := fun hvB ↦ hvM (Finset.mem_sdiff.mpr ⟨hvB, hvA⟩)
      rw [ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB hvB,
        ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB hvB,
        ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB hvB,
        ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB hvB]

/-- The right operator blocks of the actual left crossing inherit the
original operator's support in the middle region `B \ A` of the three-region
coordinates of `A ⊆ B`. The outer bra and ket need not agree outside the
original support. Supporting locality algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem operatorBlock_isSupportedOn_of_threeCut_left
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    {A B : Finset V} (hAB : A ⊆ B) (D : Finset V)
    (P : Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) P D)
    (UL : Matrix ((A → Fin q) × (↥(B \ A) → Fin q))
      ((A → Fin q) × (↥(B \ A) → Fin q)) ℂ)
    (hUL : P.submatrix (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm
        (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm =
      UL ⊗ₖ (1 : Matrix ({v // v ∉ B} → Fin q) ({v // v ∉ B} → Fin q) ℂ))
    (a b : A → Fin q) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (Matrix.operatorBlock UL a b)
      (Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D)) := by
  classical
  by_cases hq : q = 0
  · subst q
    exact isSupportedOn_of_subsingleton_siteConfig (n := fun _ : ↥(B \ A) ↦ 0)
      (Matrix.operatorBlock UL a b)
      (Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D))
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let g := ManyBody.threeCutEquiv (fun _ : V ↦ Fin q) hAB
    let r₀ : {v // v ∉ B} → Fin q := fun _ ↦ ⟨0, hqpos⟩
    have hslice (x y : ↥(B \ A) → Fin q) :
        Matrix.operatorBlock UL a b x y = P (g.symm ((a, x), r₀))
          (g.symm ((b, y), r₀)) := by
      have h := congrFun (congrFun hUL ((a, x), r₀)) ((b, y), r₀)
      change P (g.symm ((a, x), r₀)) (g.symm ((b, y), r₀)) =
        UL (a, x) (b, y) *
          (1 : Matrix ({v // v ∉ B} → Fin q) ({v // v ∉ B} → Fin q) ℂ) r₀ r₀ at h
      simpa only [Matrix.operatorBlock, Matrix.one_apply_eq, mul_one] using h.symm
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨e, heD, hne⟩ := hxy
      have heD' : e.val ∉ D := by
        intro he
        exact heD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      rw [hslice x y]
      apply hP.1
      refine ⟨e.val, heD', ?_⟩
      rw [ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB e.property,
        ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB e.property]
      exact hne
    · intro x y x' y' h1 h2 h3 h4
      rw [hslice x y, hslice x' y']
      exact hP.apply_eq (threeCutEquiv_symm_agree_of_middle hAB D a x x' r₀ h1)
        (threeCutEquiv_symm_agree_of_middle hAB D b y y' r₀ h2)
        (threeCutEquiv_symm_coincide_iff hAB D a b x y x' y' r₀ r₀ h3 h4)

/-- An actual ordinary middle factor inherits the original support restricted
to the middle-site subtype `B \ A`, including zero local dimension and empty
regions. Supporting locality algebra for ALVV, arXiv:1602.08828v2,
equation H-mid-cut, lines 810–821, and Proposition 5.7, lines 1324–1333. -/
private theorem isSupportedOn_of_threeCut_middle
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    {A B : Finset V} (hAB : A ⊆ B) (D : Finset V)
    (P : Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) P D)
    (W : Matrix (↥(B \ A) → Fin q) (↥(B \ A) → Fin q) ℂ)
    (hW : P.submatrix (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm
        (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm =
      ((1 : Matrix (A → Fin q) (A → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
        (1 : Matrix ({v // v ∉ B} → Fin q) ({v // v ∉ B} → Fin q) ℂ)) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) W
      (Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D)) := by
  classical
  by_cases hq : q = 0
  · subst q
    exact isSupportedOn_of_subsingleton_siteConfig (n := fun _ : ↥(B \ A) ↦ 0) W _
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let a : A → Fin q := fun _ ↦ ⟨0, hqpos⟩
    have hsupp := operatorBlock_isSupportedOn_of_threeCut_left
      hAB D P hP ((1 : Matrix (A → Fin q) (A → Fin q) ℂ) ⊗ₖ W)
      hW a a
    have hblock : Matrix.operatorBlock
        ((1 : Matrix (A → Fin q) (A → Fin q) ℂ) ⊗ₖ W) a a = W := by
      ext x y
      simp only [Matrix.operatorBlock, Matrix.kroneckerMap_apply,
        Matrix.one_apply_eq, one_mul]
    simpa only [hblock] using hsupp

/-- Simultaneous regional forms for the two-window family of ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, in the three-region
coordinates of `T`, of the middle region `(T ∪ E) \ T` (which is `E`) and of the
complement of `T ∪ E`. The three bulk operators are independently supplied; no
equality with complementary bond sums is required.
The regional pieces are chosen by the original label and selected edge position.
The central label has only a middle component, while every window middle
component is supported outside the strict core interior. -/
theorem exists_threeCut_two_window_factors_with_collars
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + r.val) (a + r.val + 2) : Finset (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + r.val) (b + r.val + 2) : Finset (Fin L)))
    (hL : F (Sum.inr 0) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L 0 (a + 1) : Finset (Fin L)))
    (hM : F (Sum.inr 1) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (a + 2 * ℓ) (b + 1) : Finset (Fin L)))
    (hR : F (Sum.inr 2) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
      (interval L (b + 2 * ℓ) L : Finset (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) :
    let T := interval L 0 ((a + p.val) + 1)
    let E := interval L ((a + p.val) + 1) ((b + s.val) + 1)
    let M := (T ∪ E) \ T
    let g := ManyBody.threeCutEquiv (fun _ : Fin L ↦ Fin q)
      (Finset.subset_union_left : T ⊆ T ∪ E)
    let C : Finset M := Finset.univ.filter
      (fun x : M ↦ x.val ∉ interval L (a + 2 * ℓ + 1) b)
    ∃ (HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (T → Fin q) (T → Fin q) ℂ)
      (HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (M → Fin q) (M → Fin q) ℂ)
      (HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
        Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ)
      (UL : Matrix ((T → Fin q) × (M → Fin q))
        ((T → Fin q) × (M → Fin q)) ℂ)
      (VR : Matrix ((M → Fin q) × ({v // v ∉ T ∪ E} → Fin q))
        ((M → Fin q) × ({v // v ∉ T ∪ E} → Fin q)) ℂ),
      (∀ r, r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
        (F r).submatrix g.symm g.symm =
          (HL r ⊗ₖ (1 : Matrix (M → Fin q) (M → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
              (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (M → Fin q))
              ((T → Fin q) × (M → Fin q)) ℂ) ⊗ₖ HR r) ∧
      (F (Sum.inl (Sum.inl p))).submatrix g.symm g.symm =
        UL ⊗ₖ (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) ∧
      (F (Sum.inl (Sum.inr s))).submatrix g.symm g.symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
          (Equiv.prodAssoc (T → Fin q) (M → Fin q)
            ({v // v ∉ T ∪ E} → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (M → Fin q)
            ({v // v ∉ T ∪ E} → Fin q)).symm ∧
      operatorSchmidtRank UL ≤ q ^ 2 ∧ operatorSchmidtRank VR ≤ q ^ 2 ∧
      HM (Sum.inr 0) = 0 ∧ HM (Sum.inr 2) = 0 ∧
      HL (Sum.inr 1) = 0 ∧ HR (Sum.inr 1) = 0 ∧
      (∀ r, r ≤ p → HM (Sum.inl (Sum.inl r)) = 0) ∧
      (∀ r, s ≤ r → HM (Sum.inl (Sum.inr r)) = 0) ∧
      (∀ r, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
        (HM (Sum.inl (Sum.inl r))) C) ∧
      (∀ r, ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
        (HM (Sum.inl (Sum.inr r))) C) := by
  classical
  intro T E M g C
  have hTE : Disjoint T E := disjoint_interval_interval (L := L) 0 _ _
  have hAB : T ⊆ T ∪ E := Finset.subset_union_left
  have hME : M = E := Finset.union_sdiff_cancel_left hTE
  have huv : a + p.val < b + s.val := by
    have := p.isLt
    omega
  have hv : b + s.val + 1 < L := by
    have := s.isLt
    omega
  obtain ⟨huD, huT, hvD, hvE, _hord⟩ :=
    interval_edge_classification_of_lt (L := L) huv hv
  obtain ⟨UL, hUL, hrUL⟩ :=
    ManyBody.exists_reindex_threeCutEquiv_eq_kronecker_one_operatorSchmidtRank_le hAB huD
      (hleft p)
  obtain ⟨VR, hVR, hrVR⟩ :=
    ManyBody.exists_reindex_threeCutEquiv_eq_reindex_one_kronecker_operatorSchmidtRank_le hAB
      hvD (hright s)
  have hULrank : operatorSchmidtRank UL ≤ q ^ 2 := by
    simpa only [T, huT, Finset.card_singleton, Nat.mul_one] using hrUL
  have hvM : interval L (b + s.val) (b + s.val + 2) ∩ ((T ∪ E) \ T) =
      {⟨b + s.val, by omega⟩} := by
    rw [Finset.union_sdiff_cancel_left hTE]
    exact hvE
  have hVRrank : operatorSchmidtRank VR ≤ q ^ 2 := by
    simpa only [hvM, Finset.card_singleton, Nat.mul_one] using hrVR
  have hp := p.isLt
  have hs := s.isLt
  have hzero : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (0 : Matrix (M → Fin q) (M → Fin q) ℂ) C := by
    change _ ∈ ManyBody.supportedOperators _ _
    exact zero_mem (ManyBody.supportedOperators (fun _ : M ↦ Fin q) C)
  have hLeft : ∀ r : Fin (2 * ℓ),
      ∃ (B : Matrix (T → Fin q) (T → Fin q) ℂ)
        (W : Matrix (M → Fin q) (M → Fin q) ℂ),
        (r ≠ p → (F (Sum.inl (Sum.inl r))).submatrix g.symm g.symm =
          (B ⊗ₖ (1 : Matrix (M → Fin q) (M → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
              (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ)) ∧
        (r ≤ p → W = 0) ∧ ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) W C := by
    intro r
    by_cases hrp : r = p
    · subst r
      exact ⟨0, 0, by simp, fun _ ↦ rfl, hzero⟩
    · by_cases hlt : r < p
      · have hrT : F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) T :=
          ManyBody.supportedOperators_mono (interval_mono (by omega) (by omega)) (hleft r)
        obtain ⟨B, hB⟩ :=
          ManyBody.exists_reindex_threeCutEquiv_eq_kronecker_one_kronecker_one hAB
            (Finset.Subset.refl T) hrT
        refine ⟨B, 0, ?_, fun _ ↦ rfl, hzero⟩
        intro _
        simpa using hB
      · have hpr : p.val < r.val := by
          have hne : r.val ≠ p.val := fun h ↦ hrp (Fin.ext h)
          have hnr : ¬r.val < p.val := hlt
          omega
        have hr := r.isLt
        have hrE : F (Sum.inl (Sum.inl r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) E :=
          ManyBody.supportedOperators_mono (interval_mono (by omega) (by omega)) (hleft r)
        obtain ⟨W, hW⟩ :=
          ManyBody.exists_reindex_threeCutEquiv_eq_one_kronecker_kronecker_one hAB hME.ge hrE
        have hWsupp := isSupportedOn_of_threeCut_middle hAB
          (interval L (a + r.val) (a + r.val + 2))
          (F (Sum.inl (Sum.inl r)))
          (hleft r) W hW
        have hcollar : (Finset.univ.filter
            (fun x : M ↦ x.val ∈ interval L (a + r.val) (a + r.val + 2))) ⊆ C := by
          intro x hx
          have hxD := mem_interval.mp (Finset.mem_filter.mp hx).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro hxZ
          have hxZ' := mem_interval.mp hxZ
          omega
        refine ⟨0, W, ?_, ?_, hWsupp.mono hcollar⟩
        · intro _
          simpa using hW
        · intro hle
          have hle' : r.val ≤ p.val := hle
          omega
  have hRight : ∀ r : Fin (2 * ℓ),
      ∃ (W : Matrix (M → Fin q) (M → Fin q) ℂ)
        (B : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ),
        (r ≠ s → (F (Sum.inl (Sum.inr r))).submatrix g.symm g.symm =
          ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
              (1 : Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (M → Fin q))
              ((T → Fin q) × (M → Fin q)) ℂ) ⊗ₖ B) ∧
        (s ≤ r → W = 0) ∧ ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) W C := by
    intro r
    by_cases hrs : r = s
    · subst r
      exact ⟨0, 0, by simp, fun _ ↦ rfl, hzero⟩
    · by_cases hgt : s < r
      · have hrR : F (Sum.inl (Sum.inr r)) ∈
            ManyBody.supportedOperators (fun _ ↦ Fin q) ((T ∪ E)ᶜ : Finset (Fin L)) := by
          apply ManyBody.supportedOperators_mono ?_ (hright r)
          intro x hx
          have hx' := mem_interval.mp hx
          simp only [Finset.mem_compl, Finset.mem_union, T, E, mem_interval]
          omega
        obtain ⟨B, hB⟩ := ManyBody.exists_reindex_threeCutEquiv_eq_one_kronecker hAB
          (Finset.Subset.refl _) hrR
        refine ⟨0, B, ?_, fun _ ↦ rfl, hzero⟩
        intro _
        simpa using hB
      · have hrs' : r.val < s.val := by
          have hne : r.val ≠ s.val := fun h ↦ hrs (Fin.ext h)
          have hng : ¬s.val < r.val := hgt
          omega
        have hrE : F (Sum.inl (Sum.inr r)) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) E :=
          ManyBody.supportedOperators_mono (interval_mono (by omega) (by omega)) (hright r)
        obtain ⟨W, hW⟩ :=
          ManyBody.exists_reindex_threeCutEquiv_eq_one_kronecker_kronecker_one hAB hME.ge hrE
        have hWsupp := isSupportedOn_of_threeCut_middle hAB
          (interval L (b + r.val) (b + r.val + 2))
          (F (Sum.inl (Sum.inr r)))
          (hright r) W hW
        have hcollar : (Finset.univ.filter
            (fun x : M ↦ x.val ∈ interval L (b + r.val) (b + r.val + 2))) ⊆ C := by
          intro x hx
          have hxD := mem_interval.mp (Finset.mem_filter.mp hx).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro hxZ
          have hxZ' := mem_interval.mp hxZ
          omega
        refine ⟨W, 0, ?_, ?_, hWsupp.mono hcollar⟩
        · intro _
          simpa using hW
        · intro hle
          have hle' : s.val ≤ r.val := hle
          omega
  choose LL LM hLeftData using hLeft
  choose RM RR hRightData using hRight
  have hbulkL : F (Sum.inr 0) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) T :=
    ManyBody.supportedOperators_mono (interval_mono (by omega) (by omega)) hL
  have hbulkM : F (Sum.inr 1) ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) E :=
    ManyBody.supportedOperators_mono (interval_mono (by omega) (by omega)) hM
  have hbulkR : F (Sum.inr 2) ∈
      ManyBody.supportedOperators (fun _ ↦ Fin q) ((T ∪ E)ᶜ : Finset (Fin L)) := by
    apply ManyBody.supportedOperators_mono ?_ hR
    intro x hx
    have hx' := mem_interval.mp hx
    simp only [Finset.mem_compl, Finset.mem_union, T, E, mem_interval]
    omega
  obtain ⟨BL, hBL⟩ := ManyBody.exists_reindex_threeCutEquiv_eq_kronecker_one_kronecker_one hAB
    (Finset.Subset.refl T) hbulkL
  obtain ⟨BM, hBM⟩ := ManyBody.exists_reindex_threeCutEquiv_eq_one_kronecker_kronecker_one hAB
    hME.ge hbulkM
  obtain ⟨BR, hBR⟩ := ManyBody.exists_reindex_threeCutEquiv_eq_one_kronecker hAB
    (Finset.Subset.refl _) hbulkR
  let HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (T → Fin q) (T → Fin q) ℂ :=
    Sum.elim (Sum.elim LL (fun _ ↦ 0)) (fun j ↦ if j = 0 then BL else 0)
  let HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (M → Fin q) (M → Fin q) ℂ :=
    Sum.elim (Sum.elim LM RM) (fun j ↦ if j = 1 then BM else 0)
  let HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix ({v // v ∉ T ∪ E} → Fin q) ({v // v ∉ T ∪ E} → Fin q) ℂ :=
    Sum.elim (Sum.elim (fun _ ↦ 0) RR) (fun j ↦ if j = 2 then BR else 0)
  refine ⟨HL, HM, HR, UL, VR, ?_, hUL, hVR, hULrank, hVRrank,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hru hrv
    rcases r with (r | r) | j
    · have hrp : r ≠ p := by
        intro h
        apply hru
        exact congrArg (fun z : Fin (2 * ℓ) ↦
          (Sum.inl (Sum.inl z) : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)) h
      simpa [HL, HM, HR] using (hLeftData r).1 hrp
    · have hrs : r ≠ s := by
        intro h
        apply hrv
        exact congrArg (fun z : Fin (2 * ℓ) ↦
          (Sum.inl (Sum.inr z) : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)) h
      simpa [HL, HM, HR] using (hRightData r).1 hrs
    · fin_cases j
      · simpa [HL, HM, HR] using hBL
      · simpa [HL, HM, HR] using hBM
      · simpa [HL, HM, HR] using hBR
  · simp [HM]
  · simp [HM]
  · simp [HL]
  · simp [HR]
  · intro r hr
    simpa [HM] using (hLeftData r).2.1 hr
  · intro r hr
    simpa [HM] using (hRightData r).2.1 hr
  · intro r
    simpa [HM] using (hLeftData r).2.2
  · intro r
    simpa [HM] using (hRightData r).2.2

/-- The left partial blocks of the actual right crossing inherit the original
support in the middle region `B \ A` of the three-region coordinates of
`A ⊆ B`. The two right configurations need not agree off the original
support. Supporting locality algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem leftBlock_isSupportedOn_of_threeCut_right
    {V : Type*} [DecidableEq V] {q : ℕ}
    {A B : Finset V} (hAB : A ⊆ B) (D : Finset V)
    (P : Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) P D)
    (VR : Matrix ((↥(B \ A) → Fin q) × ({v // v ∉ B} → Fin q))
      ((↥(B \ A) → Fin q) × ({v // v ∉ B} → Fin q)) ℂ)
    (hVR : P.submatrix (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm
        (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm =
      ((1 : Matrix (A → Fin q) (A → Fin q) ℂ) ⊗ₖ VR).reindex
        (Equiv.prodAssoc (A → Fin q) (↥(B \ A) → Fin q) ({v // v ∉ B} → Fin q)).symm
        (Equiv.prodAssoc (A → Fin q) (↥(B \ A) → Fin q) ({v // v ∉ B} → Fin q)).symm)
    (a b : {v // v ∉ B} → Fin q) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (fun x y : ↥(B \ A) → Fin q ↦ VR (x, a) (y, b))
      (Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D)) := by
  classical
  by_cases hq : q = 0
  · subst q
    exact isSupportedOn_of_subsingleton_siteConfig (n := fun _ : ↥(B \ A) ↦ 0)
      (fun x y : ↥(B \ A) → Fin 0 ↦ VR (x, a) (y, b))
      (Finset.univ.filter (fun e : ↥(B \ A) ↦ e.val ∈ D))
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let g := ManyBody.threeCutEquiv (fun _ : V ↦ Fin q) hAB
    let ℓ₀ : A → Fin q := fun _ ↦ ⟨0, hqpos⟩
    have hslice (x y : ↥(B \ A) → Fin q) :
        VR (x, a) (y, b) = P (g.symm ((ℓ₀, x), a))
          (g.symm ((ℓ₀, y), b)) := by
      have h := congrFun (congrFun hVR ((ℓ₀, x), a)) ((ℓ₀, y), b)
      change P (g.symm ((ℓ₀, x), a)) (g.symm ((ℓ₀, y), b)) =
        (1 : Matrix (A → Fin q) (A → Fin q) ℂ) ℓ₀ ℓ₀ * VR (x, a) (y, b) at h
      simpa only [Matrix.one_apply_eq, one_mul] using h.symm
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨e, heD, hne⟩ := hxy
      have heD' : e.val ∉ D := by
        intro he
        exact heD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      change VR (x, a) (y, b) = 0
      rw [hslice x y]
      apply hP.1
      refine ⟨e.val, heD', ?_⟩
      rw [ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB e.property,
        ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB e.property]
      exact hne
    · intro x y x' y' h1 h2 h3 h4
      change VR (x, a) (y, b) = VR (x', a) (y', b)
      rw [hslice x y, hslice x' y']
      exact hP.apply_eq (threeCutEquiv_symm_agree_of_middle hAB D ℓ₀ x x' a h1)
        (threeCutEquiv_symm_agree_of_middle hAB D ℓ₀ y y' b h2)
        (threeCutEquiv_symm_coincide_iff hAB D ℓ₀ ℓ₀ x y x' y' a b h3 h4)

/-- Two middle factors with the same identity tensor lift are equal when an
actual middle site is supplied. This identifies the deliberately chosen
middle factor with the actual regional central operator in ALVV,
arXiv:1602.08828v2, equation H-mid-cut, lines 810–821, and Proposition 5.7,
lines 1324–1333. No positive-local-dimension hypothesis is required. -/
theorem eq_of_threeCut_middle_lift_eq
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (A B : Finset V) (e₀ : ↥(B \ A))
    (W M : Matrix (↥(B \ A) → Fin q) (↥(B \ A) → Fin q) ℂ)
    (hWM :
      ((1 : Matrix (A → Fin q) (A → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
          (1 : Matrix ({v // v ∉ B} → Fin q) ({v // v ∉ B} → Fin q) ℂ) =
        ((1 : Matrix (A → Fin q) (A → Fin q) ℂ) ⊗ₖ M) ⊗ₖ
          (1 : Matrix ({v // v ∉ B} → Fin q) ({v // v ∉ B} → Fin q) ℂ)) :
    W = M := by
  classical
  by_cases hq : q = 0
  · subst q
    ext x y
    exact Fin.elim0 (x e₀)
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let a : A → Fin q := fun _ ↦ ⟨0, hqpos⟩
    let r : {v // v ∉ B} → Fin q := fun _ ↦ ⟨0, hqpos⟩
    ext x y
    have hxy := congrFun (congrFun hWM ((a, x), r)) ((a, y), r)
    simpa only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
      one_mul, mul_one] using hxy

/-- Canonically placing an operator on the middle region `B \ A` gives the
corresponding middle factor in the three-region coordinates of `A ⊆ B`,
including empty regions and local dimension zero. Supporting locality algebra
for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem place_submatrix_threeCut
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    {A B : Finset V} (hAB : A ⊆ B)
    (W : Matrix (↥(B \ A) → Fin q) (↥(B \ A) → Fin q) ℂ) :
    (ManyBody.place (X := fun _ ↦ Fin q) (B \ A) W).submatrix
        (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm
        (ManyBody.threeCutEquiv (fun _ ↦ Fin q) hAB).symm =
      ((1 : Matrix (A → Fin q) (A → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
        (1 : Matrix ({v // v ∉ B} → Fin q) ({v // v ∉ B} → Fin q) ℂ) := by
  classical
  let g := ManyBody.threeCutEquiv (fun _ : V ↦ Fin q) hAB
  have hrestrict (t : A → Fin q) (e : ↥(B \ A) → Fin q)
      (r : {v // v ∉ B} → Fin q) :
      (fun v : ↥(B \ A) ↦ g.symm ((t, e), r) v) = e := by
    funext v
    exact ManyBody.threeCutEquiv_symm_apply_of_mem_sdiff hAB v.property
  ext ⟨⟨t, e⟩, r⟩ ⟨⟨t', e'⟩, r'⟩
  have hagree : (∀ v ∉ B \ A, g.symm ((t, e), r) v = g.symm ((t', e'), r') v) ↔
      t = t' ∧ r = r' := by
    constructor
    · intro h
      constructor
      · funext v
        have hvM : v.val ∉ B \ A := fun hv ↦ (Finset.mem_sdiff.mp hv).2 v.property
        have hp := h v.val hvM
        rw [ManyBody.threeCutEquiv_symm_apply_of_mem hAB v.property,
          ManyBody.threeCutEquiv_symm_apply_of_mem hAB v.property] at hp
        exact hp
      · funext v
        have hvM : v.val ∉ B \ A := fun hv ↦ v.property (Finset.mem_sdiff.mp hv).1
        have hp := h v.val hvM
        rw [ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB v.property,
          ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB v.property] at hp
        exact hp
    · rintro ⟨rfl, rfl⟩
      intro v hvM
      by_cases hvA : v ∈ A
      · rw [ManyBody.threeCutEquiv_symm_apply_of_mem hAB hvA,
          ManyBody.threeCutEquiv_symm_apply_of_mem hAB hvA]
      · have hvB : v ∉ B := fun hvB ↦ hvM (Finset.mem_sdiff.mpr ⟨hvB, hvA⟩)
        rw [ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB hvB,
          ManyBody.threeCutEquiv_symm_apply_of_not_mem hAB hvB]
  change ManyBody.place (X := fun _ ↦ Fin q) (B \ A) W
      (g.symm ((t, e), r)) (g.symm ((t', e'), r')) =
    ((1 : Matrix (A → Fin q) (A → Fin q) ℂ) t t' * W e e') *
      (1 : Matrix ({v // v ∉ B} → Fin q) ({v // v ∉ B} → Fin q) ℂ) r r'
  rw [ManyBody.place_apply, hrestrict t e r, hrestrict t' e' r']
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := hagree.mp h
    simp
  · rcases not_and_or.mp fun h' ↦ h (hagree.mpr h') with ht | hr
    · simp [Matrix.one_apply, ht]
    · simp [Matrix.one_apply, hr]

/-- The ordinary weighted sum is the weighted central term plus the two
strict window tails, whose sum remains supported on the selected collar.
The weight of the central term is arbitrary. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem exists_weighted_ordinary_middle_eq_central_add_supported
    {E : Type*} [Finite E] {q ℓ : ℕ}
    (HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (E → Fin q) (E → Fin q) ℂ)
    (p s : Fin (2 * ℓ))
    (z : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → ℂ)
    (C : Finset E)
    (hL0 : HM (Sum.inr (0 : Fin 3)) = 0)
    (hR0 : HM (Sum.inr (2 : Fin 3)) = 0)
    (hleft0 : ∀ r : Fin (2 * ℓ), r ≤ p → HM (Sum.inl (Sum.inl r)) = 0)
    (hleftC : ∀ r : Fin (2 * ℓ), p < r →
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (HM (Sum.inl (Sum.inl r))) C)
    (hright0 : ∀ r : Fin (2 * ℓ), s ≤ r → HM (Sum.inl (Sum.inr r)) = 0)
    (hrightC : ∀ r : Fin (2 * ℓ), r < s →
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) (HM (Sum.inl (Sum.inr r))) C) :
    let O : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :=
      (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
    ∃ K : Matrix (E → Fin q) (E → Fin q) ℂ,
      (∑ i ∈ O, z i • HM i) = z (Sum.inr (1 : Fin 3)) • HM (Sum.inr (1 : Fin 3)) + K ∧
        ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) K C := by
  classical
  let := Fintype.ofFinite E
  intro O
  let KL : Matrix (E → Fin q) (E → Fin q) ℂ :=
    ∑ r ∈ (Finset.univ : Finset (Fin (2 * ℓ))).filter (fun r ↦ p < r),
      z (Sum.inl (Sum.inl r)) • HM (Sum.inl (Sum.inl r))
  let KR : Matrix (E → Fin q) (E → Fin q) ℂ :=
    ∑ r ∈ (Finset.univ : Finset (Fin (2 * ℓ))).filter (fun r ↦ r < s),
      z (Sum.inl (Sum.inr r)) • HM (Sum.inl (Sum.inr r))
  have hp0 : z (Sum.inl (Sum.inl p)) • HM (Sum.inl (Sum.inl p)) = 0 := by
    rw [hleft0 p le_rfl, smul_zero]
  have hs0 : z (Sum.inl (Sum.inr s)) • HM (Sum.inl (Sum.inr s)) = 0 := by
    rw [hright0 s le_rfl, smul_zero]
  have hOrd : (∑ i ∈ O, z i • HM i) = ∑ i, z i • HM i := by
    change (∑ i ∈ (Finset.univ.erase (Sum.inl (Sum.inl p))).erase
      (Sum.inl (Sum.inr s)), z i • HM i) = _
    rw [Finset.sum_erase (Finset.univ.erase (Sum.inl (Sum.inl p)))
      (f := fun i ↦ z i • HM i) hs0,
      Finset.sum_erase Finset.univ (f := fun i ↦ z i • HM i) hp0]
  have hKL : (∑ r : Fin (2 * ℓ),
      z (Sum.inl (Sum.inl r)) • HM (Sum.inl (Sum.inl r))) = KL := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r _ hr
    have hnot : ¬p < r := by
      intro hpr
      exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpr⟩)
    rw [hleft0 r (le_of_not_gt hnot), smul_zero]
  have hKR : (∑ r : Fin (2 * ℓ),
      z (Sum.inl (Sum.inr r)) • HM (Sum.inl (Sum.inr r))) = KR := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r _ hr
    have hnot : ¬r < s := by
      intro hrs
      exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs⟩)
    rw [hright0 r (le_of_not_gt hnot), smul_zero]
  have hKLmem : KL ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) C := by
    change (∑ r ∈ (Finset.univ : Finset (Fin (2 * ℓ))).filter (fun r ↦ p < r),
      z (Sum.inl (Sum.inl r)) • HM (Sum.inl (Sum.inl r))) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin q) C
    refine sum_mem fun r hr ↦ ?_
    exact SMulMemClass.smul_mem _
      (hleftC r (Finset.mem_filter.mp hr).2)
  have hKRmem : KR ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) C := by
    change (∑ r ∈ (Finset.univ : Finset (Fin (2 * ℓ))).filter (fun r ↦ r < s),
      z (Sum.inl (Sum.inr r)) • HM (Sum.inl (Sum.inr r))) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin q) C
    refine sum_mem fun r hr ↦ ?_
    exact SMulMemClass.smul_mem _
      (hrightC r (Finset.mem_filter.mp hr).2)
  refine ⟨KL + KR, ?_, ?_⟩
  · calc
      (∑ i ∈ O, z i • HM i) = ∑ i, z i • HM i := hOrd
      _ = (KL + KR) + z (Sum.inr (1 : Fin 3)) • HM (Sum.inr (1 : Fin 3)) := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hKL, hKR]
        rw [Fin.sum_univ_three]
        simp only [hL0, hR0, smul_zero, add_zero, zero_add]
      _ = z (Sum.inr (1 : Fin 3)) • HM (Sum.inr (1 : Fin 3)) + (KL + KR) :=
        add_comm _ _
  · exact (add_mem hKLmem hKRmem)

end TNLean.MPS.AreaLaw

end
