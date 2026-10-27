/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.RegionalOperatorForms
import TNLean.Lattice.Sheet.SupportedSchmidtRank
import TNLean.Lattice.Sheet.LeftSupportedSchmidtRank
import TNLean.MPS.AreaLaw.TwoCutEdgeSupports
import TNLean.Circuit.EntropySupport
import TNLean.Circuit.SiteEmbedding
import QICLean.Entropy.SupportedMarginalTails
import QICLean.Algebra.OperatorBlock
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Support of three-region operator factors

An operator supported on a set of sites induces the corresponding support
on its partial matrix elements in the middle region. Canonical embeddings
and equality of middle factors are expressed in the same three-region
coordinates.

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

open Matrix QuantumCircuit
open scoped BigOperators Kronecker
open TNLean.Lattice.Sheet

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- Every matrix on a subsingleton configuration type has any designated
support. This supplies the zero-local-dimension branches without adding a
nonempty-site or nonempty-configuration premise. -/
private theorem isSupportedOn_of_subsingleton_siteConfig
    {V : Type*} {n : V → ℕ}
    [Subsingleton (Entropy.SiteConfig n)]
    (X : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ) (D : Finset V) :
    Entropy.IsSupportedOn X D := by
  refine ⟨?_, ?_⟩
  · intro σ τ hστ
    obtain ⟨v, _hv, hne⟩ := hστ
    exact False.elim (hne (congrFun (Subsingleton.elim σ τ) v))
  · intro σ τ σ' τ' _h1 _h2 _h3 _h4
    exact congrArg₂ X (Subsingleton.elim σ σ') (Subsingleton.elim τ τ')

/-- The right operator blocks of the actual left crossing inherit the
original operator's support in the middle region. The outer bra and ket
need not agree outside the original support. Supporting locality algebra
for ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem operatorBlock_isSupportedOn_of_threeSplit_left
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (T E D : Finset V) (hTE : Disjoint T E)
    (P : Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : Entropy.IsSupportedOn (n := fun _ : V ↦ q) P D)
    (UL : Matrix ((T → Fin q) × (E → Fin q))
      ((T → Fin q) × (E → Fin q)) ℂ)
    (hUL : P.submatrix (threeSplit q T E hTE).symm
        (threeSplit q T E hTE).symm =
      UL ⊗ₖ (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ))
    (a b : T → Fin q) :
    Entropy.IsSupportedOn (n := fun _ : E ↦ q) (Matrix.operatorBlock UL a b)
      (Finset.univ.filter (fun e : E ↦ e.val ∈ D)) := by
  classical
  by_cases hq : q = 0
  · subst q
    exact isSupportedOn_of_subsingleton_siteConfig (n := fun _ : E ↦ 0)
      (Matrix.operatorBlock UL a b)
      (Finset.univ.filter (fun e : E ↦ e.val ∈ D))
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let g := threeSplit q T E hTE
    let r₀ : ↥(T ∪ E)ᶜ → Fin q := fun _ ↦ ⟨0, hqpos⟩
    let DE : Finset E := Finset.univ.filter (fun e : E ↦ e.val ∈ D)
    change Entropy.IsSupportedOn (n := fun _ : E ↦ q) (Matrix.operatorBlock UL a b) DE
    have hslice (x y : E → Fin q) :
        Matrix.operatorBlock UL a b x y = P (g.symm ((a, x), r₀))
          (g.symm ((b, y), r₀)) := by
      have h := congrFun (congrFun hUL ((a, x), r₀)) ((b, y), r₀)
      change P (g.symm ((a, x), r₀)) (g.symm ((b, y), r₀)) =
        UL (a, x) (b, y) *
          (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) r₀ r₀ at h
      simpa only [Matrix.operatorBlock, Matrix.one_apply_eq, mul_one] using h.symm
    have hkeep (c : T → Fin q) (x x' : E → Fin q)
        (hxx' : ∀ e ∈ DE, x e = x' e) :
        ∀ v ∈ D, g.symm ((c, x), r₀) v = g.symm ((c, x'), r₀) v := by
      intro v hvD
      by_cases hvE : v ∈ E
      · rw [threeSplit_symm_apply_of_mem_right hTE c x r₀ hvE,
          threeSplit_symm_apply_of_mem_right hTE c x' r₀ hvE]
        exact hxx' ⟨v, hvE⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD⟩)
      · by_cases hvT : v ∈ T
        · rw [threeSplit_symm_apply_of_mem_left hTE c x r₀ hvT,
            threeSplit_symm_apply_of_mem_left hTE c x' r₀ hvT]
        · have hvR : v ∉ T ∪ E := by
            simpa only [Finset.mem_union, not_or] using And.intro hvT hvE
          rw [threeSplit_symm_apply_of_notMem hTE c x r₀ hvR,
            threeSplit_symm_apply_of_notMem hTE c x' r₀ hvR]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨e, heD, hne⟩ := hxy
      have heD' : e.val ∉ D := by
        intro he
        exact heD (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      rw [hslice x y]
      apply hP.1
      refine ⟨e.val, heD', ?_⟩
      rw [threeSplit_symm_apply_of_mem_right hTE a x r₀ e.property,
        threeSplit_symm_apply_of_mem_right hTE b y r₀ e.property]
      exact hne
    · intro x y x' y' h1 h2 h3 h4
      rw [hslice x y, hslice x' y']
      apply hP.apply_eq (hkeep a x x' h1) (hkeep b y y' h2)
      intro v hvD
      by_cases hvE : v ∈ E
      · rw [threeSplit_symm_apply_of_mem_right hTE a x r₀ hvE,
          threeSplit_symm_apply_of_mem_right hTE b y r₀ hvE,
          threeSplit_symm_apply_of_mem_right hTE a x' r₀ hvE,
          threeSplit_symm_apply_of_mem_right hTE b y' r₀ hvE]
        have heD : (⟨v, hvE⟩ : E) ∉ DE := by
          intro he
          exact hvD (Finset.mem_filter.mp he).2
        exact ⟨fun _ ↦ h4 _ heD, fun _ ↦ h3 _ heD⟩
      · by_cases hvT : v ∈ T
        · rw [threeSplit_symm_apply_of_mem_left hTE a x r₀ hvT,
            threeSplit_symm_apply_of_mem_left hTE b y r₀ hvT,
            threeSplit_symm_apply_of_mem_left hTE a x' r₀ hvT,
            threeSplit_symm_apply_of_mem_left hTE b y' r₀ hvT]
        · have hvR : v ∉ T ∪ E := by
            simpa only [Finset.mem_union, not_or] using And.intro hvT hvE
          rw [threeSplit_symm_apply_of_notMem hTE a x r₀ hvR,
            threeSplit_symm_apply_of_notMem hTE b y r₀ hvR,
            threeSplit_symm_apply_of_notMem hTE a x' r₀ hvR,
            threeSplit_symm_apply_of_notMem hTE b y' r₀ hvR]

/-- An actual ordinary middle factor inherits the original support restricted
to the middle-site subtype, including zero local dimension and empty regions.
Supporting locality algebra for ALVV, arXiv:1602.08828v2,
equation H-mid-cut, lines 810–821, and Proposition 5.7, lines 1324–1333. -/
private theorem isSupportedOn_of_threeSplit_middle
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (T E D : Finset V) (hTE : Disjoint T E)
    (P : Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : Entropy.IsSupportedOn (n := fun _ : V ↦ q) P D)
    (W : Matrix (E → Fin q) (E → Fin q) ℂ)
    (hW : P.submatrix (threeSplit q T E hTE).symm
        (threeSplit q T E hTE).symm =
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
        (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)) :
    Entropy.IsSupportedOn (n := fun _ : E ↦ q) W
      (Finset.univ.filter (fun e : E ↦ e.val ∈ D)) := by
  classical
  by_cases hq : q = 0
  · subst q
    exact isSupportedOn_of_subsingleton_siteConfig (n := fun _ : E ↦ 0) W _
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let a : T → Fin q := fun _ ↦ ⟨0, hqpos⟩
    have hsupp := operatorBlock_isSupportedOn_of_threeSplit_left
      T E D hTE P hP ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W)
      hW a a
    have hblock : Matrix.operatorBlock
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W) a a = W := by
      ext x y
      simp only [Matrix.operatorBlock, Matrix.kroneckerMap_apply,
        Matrix.one_apply_eq, one_mul]
    simpa only [hblock] using hsupp

/-- Simultaneous regional forms for the two-window family of ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. The three bulk operators
are independently supplied; no equality with complementary bond sums is required.
The regional pieces are chosen by the original label and selected edge position.
The central label has only a middle component, while every window middle
component is supported outside the strict core interior. -/
theorem exists_threeSplit_two_window_factors_with_collars
    {L q ℓ a b : ℕ}
    (F : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hleft : ∀ r, F (Sum.inl (Sum.inl r)) ∈ supportedOperators q
      (interval L (a + r.val) (a + r.val + 2) : Set (Fin L)))
    (hright : ∀ r, F (Sum.inl (Sum.inr r)) ∈ supportedOperators q
      (interval L (b + r.val) (b + r.val + 2) : Set (Fin L)))
    (hL : F (Sum.inr 0) ∈ supportedOperators q
      (interval L 0 (a + 1) : Set (Fin L)))
    (hM : F (Sum.inr 1) ∈ supportedOperators q
      (interval L (a + 2 * ℓ) (b + 1) : Set (Fin L)))
    (hR : F (Sum.inr 2) ∈ supportedOperators q
      (interval L (b + 2 * ℓ) L : Set (Fin L)))
    (hab : a + 2 * ℓ ≤ b) (hb : b + 2 * ℓ ≤ L - 1)
    (p s : Fin (2 * ℓ)) :
    let T := interval L 0 ((a + p.val) + 1)
    let E := interval L ((a + p.val) + 1) ((b + s.val) + 1)
    let hTE : Disjoint T E := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [T, E, mem_interval] at hx hx'
      omega
    let g := threeSplit q T E hTE
    let C : Finset E := Finset.univ.filter
      (fun x : E ↦ x.val ∉ interval L (a + 2 * ℓ + 1) b)
    ∃ (HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (T → Fin q) (T → Fin q) ℂ)
      (HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → Matrix (E → Fin q) (E → Fin q) ℂ)
      (HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
        Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)
      (UL : Matrix ((T → Fin q) × (E → Fin q))
        ((T → Fin q) × (E → Fin q)) ℂ)
      (VR : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
        ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ),
      (∀ r, r ≠ Sum.inl (Sum.inl p) → r ≠ Sum.inl (Sum.inr s) →
        (F r).submatrix g.symm g.symm =
          (HL r ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ HM r) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (E → Fin q))
              ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ HR r) ∧
      (F (Sum.inl (Sum.inl p))).submatrix g.symm g.symm =
        UL ⊗ₖ (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) ∧
      (F (Sum.inl (Sum.inr s))).submatrix g.symm g.symm =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm
          (Equiv.prodAssoc (T → Fin q) (E → Fin q)
            (↥(T ∪ E)ᶜ → Fin q)).symm ∧
      operatorSchmidtRank UL ≤ q ^ 2 ∧ operatorSchmidtRank VR ≤ q ^ 2 ∧
      HM (Sum.inr 0) = 0 ∧ HM (Sum.inr 2) = 0 ∧
      HL (Sum.inr 1) = 0 ∧ HR (Sum.inr 1) = 0 ∧
      (∀ r, r ≤ p → HM (Sum.inl (Sum.inl r)) = 0) ∧
      (∀ r, s ≤ r → HM (Sum.inl (Sum.inr r)) = 0) ∧
      (∀ r, Entropy.IsSupportedOn (n := fun _ : E ↦ q)
        (HM (Sum.inl (Sum.inl r))) C) ∧
      (∀ r, Entropy.IsSupportedOn (n := fun _ : E ↦ q)
        (HM (Sum.inl (Sum.inr r))) C) := by
  classical
  intro T E hTE g C
  have huv : a + p.val < b + s.val := by
    have := p.isLt
    omega
  have hv : b + s.val + 1 < L := by
    have := s.isLt
    omega
  obtain ⟨huD, huT, hvD, hvE, _hord⟩ :=
    interval_edge_classification_of_lt (L := L) huv hv
  obtain ⟨UL, hUL, hrUL⟩ :=
    exists_threeSplit_eq_kronecker_one_rank_le hTE huD (hleft p)
  obtain ⟨VR, hVR, hrVR⟩ :=
    exists_threeSplit_eq_reindex_one_kronecker_rank_le hTE hvD (hright s)
  have hULrank : operatorSchmidtRank UL ≤ q ^ 2 := by
    simpa only [T, huT, Finset.card_singleton, Nat.mul_one] using hrUL
  have hVRrank : operatorSchmidtRank VR ≤ q ^ 2 := by
    simpa only [E, hvE, Finset.card_singleton, Nat.mul_one] using hrVR
  have hp := p.isLt
  have hs := s.isLt
  have hzero : Entropy.IsSupportedOn (n := fun _ : E ↦ q)
      (0 : Matrix (E → Fin q) (E → Fin q) ℂ) C :=
    isSupportedOn_of_mem_supportedOperators (Submodule.zero_mem _)
  have hLeft : ∀ r : Fin (2 * ℓ),
      ∃ (B : Matrix (T → Fin q) (T → Fin q) ℂ)
        (W : Matrix (E → Fin q) (E → Fin q) ℂ),
        (r ≠ p → (F (Sum.inl (Sum.inl r))).submatrix g.symm g.symm =
          (B ⊗ₖ (1 : Matrix (E → Fin q) (E → Fin q) ℂ)) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)) ∧
        (r ≤ p → W = 0) ∧ Entropy.IsSupportedOn (n := fun _ : E ↦ q) W C := by
    intro r
    by_cases hrp : r = p
    · subst r
      exact ⟨0, 0, by simp, fun _ ↦ rfl, hzero⟩
    · by_cases hlt : r < p
      · have hrT : F (Sum.inl (Sum.inl r)) ∈ supportedOperators q (T : Set (Fin L)) :=
          supportedOperators_mono
            (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) (hleft r)
        obtain ⟨B, hB⟩ := exists_threeSplit_eq_kronecker_one_kronecker_one hTE
          (Set.Subset.rfl) hrT
        refine ⟨B, 0, ?_, fun _ ↦ rfl, hzero⟩
        intro _
        simpa using hB
      · have hpr : p.val < r.val := by
          have hne : r.val ≠ p.val := fun h ↦ hrp (Fin.ext h)
          have hnr : ¬r.val < p.val := hlt
          omega
        have hr := r.isLt
        have hrE : F (Sum.inl (Sum.inl r)) ∈ supportedOperators q (E : Set (Fin L)) :=
          supportedOperators_mono
            (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) (hleft r)
        obtain ⟨W, hW⟩ := exists_threeSplit_eq_one_kronecker_kronecker_one hTE
          (Set.Subset.rfl) hrE
        have hWsupp := isSupportedOn_of_threeSplit_middle T E
          (interval L (a + r.val) (a + r.val + 2)) hTE
          (F (Sum.inl (Sum.inl r)))
          (isSupportedOn_of_mem_supportedOperators (hleft r)) W hW
        have hcollar : (Finset.univ.filter
            (fun x : E ↦ x.val ∈ interval L (a + r.val) (a + r.val + 2))) ⊆ C := by
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
      ∃ (W : Matrix (E → Fin q) (E → Fin q) ℂ)
        (B : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ),
        (r ≠ s → (F (Sum.inl (Sum.inr r))).submatrix g.symm g.symm =
          ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
              (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) +
            (1 : Matrix ((T → Fin q) × (E → Fin q))
              ((T → Fin q) × (E → Fin q)) ℂ) ⊗ₖ B) ∧
        (s ≤ r → W = 0) ∧ Entropy.IsSupportedOn (n := fun _ : E ↦ q) W C := by
    intro r
    by_cases hrs : r = s
    · subst r
      exact ⟨0, 0, by simp, fun _ ↦ rfl, hzero⟩
    · by_cases hgt : s < r
      · have hrR : F (Sum.inl (Sum.inr r)) ∈
            supportedOperators q ((T ∪ E)ᶜ : Finset (Fin L)) := by
          apply supportedOperators_mono ?_ (hright r)
          intro x hx
          have hx' := mem_interval.mp hx
          change x ∈ (T ∪ E)ᶜ
          simp only [Finset.mem_compl, Finset.mem_union, T, E, mem_interval]
          omega
        obtain ⟨B, hB⟩ := exists_threeSplit_eq_one_kronecker hTE (Set.Subset.rfl) hrR
        refine ⟨0, B, ?_, fun _ ↦ rfl, hzero⟩
        intro _
        simpa using hB
      · have hrs' : r.val < s.val := by
          have hne : r.val ≠ s.val := fun h ↦ hrs (Fin.ext h)
          have hng : ¬s.val < r.val := hgt
          omega
        have hrE : F (Sum.inl (Sum.inr r)) ∈ supportedOperators q (E : Set (Fin L)) :=
          supportedOperators_mono
            (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) (hright r)
        obtain ⟨W, hW⟩ := exists_threeSplit_eq_one_kronecker_kronecker_one hTE
          (Set.Subset.rfl) hrE
        have hWsupp := isSupportedOn_of_threeSplit_middle T E
          (interval L (b + r.val) (b + r.val + 2)) hTE
          (F (Sum.inl (Sum.inr r)))
          (isSupportedOn_of_mem_supportedOperators (hright r)) W hW
        have hcollar : (Finset.univ.filter
            (fun x : E ↦ x.val ∈ interval L (b + r.val) (b + r.val + 2))) ⊆ C := by
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
  have hbulkL : F (Sum.inr 0) ∈ supportedOperators q (T : Set (Fin L)) :=
    supportedOperators_mono
      (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) hL
  have hbulkM : F (Sum.inr 1) ∈ supportedOperators q (E : Set (Fin L)) :=
    supportedOperators_mono
      (Finset.coe_subset.mpr (interval_mono (by omega) (by omega))) hM
  have hbulkR : F (Sum.inr 2) ∈
      supportedOperators q ((T ∪ E)ᶜ : Finset (Fin L)) := by
    apply supportedOperators_mono ?_ hR
    intro x hx
    have hx' := mem_interval.mp hx
    change x ∈ (T ∪ E)ᶜ
    simp only [Finset.mem_compl, Finset.mem_union, T, E, mem_interval]
    omega
  obtain ⟨BL, hBL⟩ := exists_threeSplit_eq_kronecker_one_kronecker_one hTE
    (Set.Subset.rfl) hbulkL
  obtain ⟨BM, hBM⟩ := exists_threeSplit_eq_one_kronecker_kronecker_one hTE
    (Set.Subset.rfl) hbulkM
  obtain ⟨BR, hBR⟩ := exists_threeSplit_eq_one_kronecker hTE
    (Set.Subset.rfl) hbulkR
  let HL : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (T → Fin q) (T → Fin q) ℂ :=
    Sum.elim (Sum.elim LL (fun _ ↦ 0)) (fun j ↦ if j = 0 then BL else 0)
  let HM : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (E → Fin q) (E → Fin q) ℂ :=
    Sum.elim (Sum.elim LM RM) (fun j ↦ if j = 1 then BM else 0)
  let HR : ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) →
      Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ :=
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
support in the middle region. The two right configurations need not agree
off the original support. Supporting locality algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem leftBlock_isSupportedOn_of_threeSplit_right
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (T E D : Finset V) (hTE : Disjoint T E)
    (P : Matrix (V → Fin q) (V → Fin q) ℂ)
    (hP : Entropy.IsSupportedOn (n := fun _ : V ↦ q) P D)
    (VR : Matrix ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((E → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (hVR : P.submatrix (threeSplit q T E hTE).symm
        (threeSplit q T E hTE).symm =
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ VR).reindex
        (Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).symm
        (Equiv.prodAssoc (T → Fin q) (E → Fin q) (↥(T ∪ E)ᶜ → Fin q)).symm)
    (a b : ↥(T ∪ E)ᶜ → Fin q) :
    Entropy.IsSupportedOn (n := fun _ : E ↦ q)
      (fun x y : E → Fin q ↦ VR (x, a) (y, b))
      (Finset.univ.filter (fun e : E ↦ e.val ∈ D)) := by
  classical
  by_cases hq : q = 0
  · subst q
    exact isSupportedOn_of_subsingleton_siteConfig (n := fun _ : E ↦ 0)
      (fun x y : E → Fin 0 ↦ VR (x, a) (y, b))
      (Finset.univ.filter (fun e : E ↦ e.val ∈ D))
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let g := threeSplit q T E hTE
    let ℓ₀ : T → Fin q := fun _ ↦ ⟨0, hqpos⟩
    let DE : Finset E := Finset.univ.filter (fun e : E ↦ e.val ∈ D)
    change Entropy.IsSupportedOn (n := fun _ : E ↦ q)
      (fun x y : E → Fin q ↦ VR (x, a) (y, b)) DE
    have hslice (x y : E → Fin q) :
        VR (x, a) (y, b) = P (g.symm ((ℓ₀, x), a))
          (g.symm ((ℓ₀, y), b)) := by
      have h := congrFun (congrFun hVR ((ℓ₀, x), a)) ((ℓ₀, y), b)
      change P (g.symm ((ℓ₀, x), a)) (g.symm ((ℓ₀, y), b)) =
        (1 : Matrix (T → Fin q) (T → Fin q) ℂ) ℓ₀ ℓ₀ * VR (x, a) (y, b) at h
      simpa only [Matrix.one_apply_eq, one_mul] using h.symm
    have hkeep (c : ↥(T ∪ E)ᶜ → Fin q) (x x' : E → Fin q)
        (hxx' : ∀ e ∈ DE, x e = x' e) :
        ∀ v ∈ D, g.symm ((ℓ₀, x), c) v = g.symm ((ℓ₀, x'), c) v := by
      intro v hvD
      by_cases hvE : v ∈ E
      · rw [threeSplit_symm_apply_of_mem_right hTE ℓ₀ x c hvE,
          threeSplit_symm_apply_of_mem_right hTE ℓ₀ x' c hvE]
        exact hxx' ⟨v, hvE⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvD⟩)
      · by_cases hvT : v ∈ T
        · rw [threeSplit_symm_apply_of_mem_left hTE ℓ₀ x c hvT,
            threeSplit_symm_apply_of_mem_left hTE ℓ₀ x' c hvT]
        · have hvR : v ∉ T ∪ E := by
            simpa only [Finset.mem_union, not_or] using And.intro hvT hvE
          rw [threeSplit_symm_apply_of_notMem hTE ℓ₀ x c hvR,
            threeSplit_symm_apply_of_notMem hTE ℓ₀ x' c hvR]
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
      rw [threeSplit_symm_apply_of_mem_right hTE ℓ₀ x a e.property,
        threeSplit_symm_apply_of_mem_right hTE ℓ₀ y b e.property]
      exact hne
    · intro x y x' y' h1 h2 h3 h4
      change VR (x, a) (y, b) = VR (x', a) (y', b)
      rw [hslice x y, hslice x' y']
      apply hP.apply_eq (hkeep a x x' h1) (hkeep b y y' h2)
      intro v hvD
      by_cases hvE : v ∈ E
      · rw [threeSplit_symm_apply_of_mem_right hTE ℓ₀ x a hvE,
          threeSplit_symm_apply_of_mem_right hTE ℓ₀ y b hvE,
          threeSplit_symm_apply_of_mem_right hTE ℓ₀ x' a hvE,
          threeSplit_symm_apply_of_mem_right hTE ℓ₀ y' b hvE]
        have heD : (⟨v, hvE⟩ : E) ∉ DE := by
          intro he
          exact hvD (Finset.mem_filter.mp he).2
        exact ⟨fun _ ↦ h4 _ heD, fun _ ↦ h3 _ heD⟩
      · by_cases hvT : v ∈ T
        · rw [threeSplit_symm_apply_of_mem_left hTE ℓ₀ x a hvT,
            threeSplit_symm_apply_of_mem_left hTE ℓ₀ y b hvT,
            threeSplit_symm_apply_of_mem_left hTE ℓ₀ x' a hvT,
            threeSplit_symm_apply_of_mem_left hTE ℓ₀ y' b hvT]
        · have hvR : v ∉ T ∪ E := by
            simpa only [Finset.mem_union, not_or] using And.intro hvT hvE
          rw [threeSplit_symm_apply_of_notMem hTE ℓ₀ x a hvR,
            threeSplit_symm_apply_of_notMem hTE ℓ₀ y b hvR,
            threeSplit_symm_apply_of_notMem hTE ℓ₀ x' a hvR,
            threeSplit_symm_apply_of_notMem hTE ℓ₀ y' b hvR]

/-- Two middle factors with the same identity tensor lift are equal when an
actual middle site is supplied. This identifies the deliberately chosen
middle factor with the actual regional central operator in ALVV,
arXiv:1602.08828v2, equation H-mid-cut, lines 810–821, and Proposition 5.7,
lines 1324–1333. No positive-local-dimension hypothesis is required. -/
theorem eq_of_threeSplit_middle_lift_eq
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (T E : Finset V) (e₀ : E)
    (W M : Matrix (E → Fin q) (E → Fin q) ℂ)
    (hWM :
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
          (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) =
        ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ M) ⊗ₖ
          (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ)) :
    W = M := by
  classical
  by_cases hq : q = 0
  · subst q
    ext x y
    exact Fin.elim0 (x e₀)
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let a : T → Fin q := fun _ ↦ ⟨0, hqpos⟩
    let r : ↥(T ∪ E)ᶜ → Fin q := fun _ ↦ ⟨0, hqpos⟩
    ext x y
    have hxy := congrFun (congrFun hWM ((a, x), r)) ((a, y), r)
    simpa only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
      one_mul, mul_one] using hxy

/-- Canonically placing the actual E-operator gives the corresponding middle
factor in threeSplit coordinates, including empty regions and local dimension
zero. Supporting locality algebra for ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. -/
theorem embedOp_subtype_val_submatrix_threeSplit
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (T E : Finset V) (hTE : Disjoint T E)
    (W : Matrix (E → Fin q) (E → Fin q) ℂ) :
    (QuantumCircuit.embedOp (Subtype.val : E → V) W).submatrix
        (threeSplit q T E hTE).symm (threeSplit q T E hTE).symm =
      ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) ⊗ₖ W) ⊗ₖ
        (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) := by
  classical
  let g := threeSplit q T E hTE
  have hrestrict (t : T → Fin q) (e : E → Fin q)
      (r : ↥(T ∪ E)ᶜ → Fin q) :
      g.symm ((t, e), r) ∘ (Subtype.val : E → V) = e := by
    funext v
    exact threeSplit_symm_apply_of_mem_right hTE t e r v.property
  ext ⟨⟨t, e⟩, r⟩ ⟨⟨t', e'⟩, r'⟩
  have hagree : QuantumCircuit.AgreeOff (Subtype.val : E → V)
      (g.symm ((t, e), r)) (g.symm ((t', e'), r')) ↔ t = t' ∧ r = r' := by
    constructor
    · intro h
      constructor
      · funext v
        have hvE : v.val ∉ E := fun hv ↦ Finset.disjoint_left.mp hTE v.property hv
        have hp := h v.val (fun j hj ↦ hvE (hj ▸ j.property))
        rw [threeSplit_symm_apply_of_mem_left hTE t e r v.property,
          threeSplit_symm_apply_of_mem_left hTE t' e' r' v.property] at hp
        exact hp
      · funext v
        have hvR : v.val ∉ T ∪ E := Finset.mem_compl.mp v.property
        have hvE : v.val ∉ E := fun hv ↦ hvR (Finset.mem_union_right T hv)
        have hp := h v.val (fun j hj ↦ hvE (hj ▸ j.property))
        rw [threeSplit_symm_apply_of_notMem hTE t e r hvR,
          threeSplit_symm_apply_of_notMem hTE t' e' r' hvR] at hp
        exact hp
    · rintro ⟨rfl, rfl⟩
      intro v hoff
      have hvE : v ∉ E := by
        intro hv
        exact hoff ⟨v, hv⟩ rfl
      by_cases hvT : v ∈ T
      · rw [threeSplit_symm_apply_of_mem_left hTE t e r hvT,
          threeSplit_symm_apply_of_mem_left hTE t e' r hvT]
      · have hvR : v ∉ T ∪ E := by
          simpa only [Finset.mem_union, not_or] using And.intro hvT hvE
        rw [threeSplit_symm_apply_of_notMem hTE t e r hvR,
          threeSplit_symm_apply_of_notMem hTE t e' r hvR]
  change QuantumCircuit.embedOp (Subtype.val : E → V) W
      (g.symm ((t, e), r)) (g.symm ((t', e'), r')) =
    ((1 : Matrix (T → Fin q) (T → Fin q) ℂ) t t' * W e e') *
      (1 : Matrix (↥(T ∪ E)ᶜ → Fin q) (↥(T ∪ E)ᶜ → Fin q) ℂ) r r'
  simp only [QuantumCircuit.embedOp_apply, hrestrict t e r,
    hrestrict t' e' r', hagree]
  by_cases ht : t = t' <;> by_cases hr : r = r' <;>
    simp [Matrix.one_apply, ht, hr]

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
      Entropy.IsSupportedOn (n := fun _ : E ↦ q) (HM (Sum.inl (Sum.inl r))) C)
    (hright0 : ∀ r : Fin (2 * ℓ), s ≤ r → HM (Sum.inl (Sum.inr r)) = 0)
    (hrightC : ∀ r : Fin (2 * ℓ), r < s →
      Entropy.IsSupportedOn (n := fun _ : E ↦ q) (HM (Sum.inl (Sum.inr r))) C) :
    let O : Finset ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :=
      (Finset.univ.erase (Sum.inl (Sum.inl p))).erase (Sum.inl (Sum.inr s))
    ∃ K : Matrix (E → Fin q) (E → Fin q) ℂ,
      (∑ i ∈ O, z i • HM i) = z (Sum.inr (1 : Fin 3)) • HM (Sum.inr (1 : Fin 3)) + K ∧
        Entropy.IsSupportedOn (n := fun _ : E ↦ q) K C := by
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
  have hKLmem : KL ∈ QuantumCircuit.supportedOperators q (C : Set E) := by
    change (∑ r ∈ (Finset.univ : Finset (Fin (2 * ℓ))).filter (fun r ↦ p < r),
      z (Sum.inl (Sum.inl r)) • HM (Sum.inl (Sum.inl r))) ∈
        QuantumCircuit.supportedOperators q (C : Set E)
    refine Submodule.sum_mem _ fun r hr ↦ ?_
    exact Submodule.smul_mem _ _
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn
        (hleftC r (Finset.mem_filter.mp hr).2))
  have hKRmem : KR ∈ QuantumCircuit.supportedOperators q (C : Set E) := by
    change (∑ r ∈ (Finset.univ : Finset (Fin (2 * ℓ))).filter (fun r ↦ r < s),
      z (Sum.inl (Sum.inr r)) • HM (Sum.inl (Sum.inr r))) ∈
        QuantumCircuit.supportedOperators q (C : Set E)
    refine Submodule.sum_mem _ fun r hr ↦ ?_
    exact Submodule.smul_mem _ _
      (QuantumCircuit.mem_supportedOperators_of_isSupportedOn
        (hrightC r (Finset.mem_filter.mp hr).2))
  refine ⟨KL + KR, ?_, ?_⟩
  · calc
      (∑ i ∈ O, z i • HM i) = ∑ i, z i • HM i := hOrd
      _ = (KL + KR) + z (Sum.inr (1 : Fin 3)) • HM (Sum.inr (1 : Fin 3)) := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hKL, hKR]
        rw [Fin.sum_univ_three]
        simp only [hL0, hR0, smul_zero, add_zero, zero_add]
      _ = z (Sum.inr (1 : Fin 3)) • HM (Sum.inr (1 : Fin 3)) + (KL + KR) :=
        add_comm _ _
  · exact QuantumCircuit.isSupportedOn_of_mem_supportedOperators
      (Submodule.add_mem _ hKLmem hKRmem)

end TNLean.MPS.AreaLaw

end
