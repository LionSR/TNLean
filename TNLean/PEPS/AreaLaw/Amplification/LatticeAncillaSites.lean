/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LatticeAncillaTransport
import TNLean.PEPS.AreaLaw.Amplification.AncillaSiteEntropy
import TNLean.Circuit.SiteEmbedding

/-!
# The physical sites enlarged by two copies of the target

The final entropy comparison of the amplification proof treats the two ancillary copies
`s', e'` of the target `X` as additional sites, each copy carrying the local dimension `q`.
This module sets up the enlarged site set `Λ ⊔ (X ⊔ X)`, whose configurations are pairs of a
physical configuration and two configurations of `X`, and identifies there:

* physical operators, operators on `s'`, and the supports of the transported restoring
  operator `R₀`;
* the restored vector `η = Ω ⊗ χ`, in which the copy `e'` has no mutual information with
  any physical region;
* the copied vector `φ`, which is `Ω` with the target relabelled as `e'`, tensored with
  blank vectors on `X` and `s'`; its mutual information between a part of `e'` and a
  physical region disjoint from `X` equals that of `Ω` between the corresponding part of
  `X` and the same region.

## Main definitions

* `TNLean.PEPS.AreaLaw.AncillaSites`, `TNLean.PEPS.AreaLaw.ancillaSplit`,
  `TNLean.PEPS.AreaLaw.ancillaCopyRegion`.

## Main statements

* `TNLean.PEPS.AreaLaw.kronecker_submatrix_ancillaSplit_mem_supportedOperators`.
* `TNLean.PEPS.AreaLaw.mutualInformation_ancillaProduct_copy_eq_zero`.
* `TNLean.PEPS.AreaLaw.mutualInformation_ancillaCopy_eq`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 330–347
  and 547–556: the copies `s', e'` of the Hilbert space on `X`, the swapped and restored
  vectors, and the comparison of `I(e' : J)` with `I_Ω(X : J)`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker

namespace TNLean.PEPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- The physical sites of `Λ` together with two copies `s'` and `e'` of the target `X`.
Source: `09-amplification.tex`, lines 330–331. -/
abbrev AncillaSites (Λ : Finset (ℤ × ℤ)) (X : Finset (Site Λ)) := Site Λ ⊕ (↥X ⊕ ↥X)

/-- Shortcut instance, which keeps instance search on regions of the enlarged sites short. -/
instance (X : Finset (Site Λ)) : DecidableEq (AncillaSites Λ X) := inferInstance

/-- Shortcut instance, which keeps instance search on regions of the enlarged sites short. -/
instance (X : Finset (Site Λ)) : Fintype (AncillaSites Λ X) := inferInstance

/-- The configurations of the enlarged sites as a physical configuration together with the
configurations of `s'` and of `e'`. -/
def ancillaSplit (q : ℕ) (X : Finset (Site Λ)) :
    (AncillaSites Λ X → Fin q) ≃
      Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X) :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans
    ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _))

theorem ancillaSplit_apply (X : Finset (Site Λ)) (c : AncillaSites Λ X → Fin q) :
    ancillaSplit q X c = (c ∘ Sum.inl, (c ∘ Sum.inr ∘ Sum.inl, c ∘ Sum.inr ∘ Sum.inr)) :=
  rfl

/-- The copy `e'` of a part `X'` of the target, as a region of the enlarged sites. -/
def ancillaCopyRegion {X : Finset (Site Λ)} (X' : Finset ↥X) : Finset (AncillaSites Λ X) :=
  (∅ : Finset (Site Λ)).disjSum ((∅ : Finset ↥X).disjSum X')

/-- A physical region, as a region of the enlarged sites. -/
def ancillaPhysicalRegion (X J : Finset (Site Λ)) : Finset (AncillaSites Λ X) :=
  J.disjSum ∅

/-! ### Operators -/

/-- A physical operator acting trivially on both copies is placed on the physical sites. -/
theorem kronecker_one_submatrix_ancillaSplit (X : Finset (Site Λ))
    (L : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :
    (L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
      (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)).submatrix
        (ancillaSplit q X) (ancillaSplit q X) = embedOp Sum.inl L := by
  ext c c'
  simp only [submatrix_apply, kroneckerMap_apply, one_apply, embedOp_apply, ancillaSplit_apply]
  have hagree : AgreeOff (Sum.inl : Site Λ → AncillaSites Λ X) c c' ↔
      (c ∘ Sum.inr ∘ Sum.inl, c ∘ Sum.inr ∘ Sum.inr) =
        (c' ∘ Sum.inr ∘ Sum.inl, c' ∘ Sum.inr ∘ Sum.inr) := by
    constructor
    · intro h
      exact Prod.ext (funext fun x => h _ fun j => Sum.inl_ne_inr)
        (funext fun x => h _ fun j => Sum.inl_ne_inr)
    · intro h i hi
      rcases i with i | i | i
      · exact absurd rfl (hi i)
      · exact congrFun (Prod.ext_iff.mp h).1 i
      · exact congrFun (Prod.ext_iff.mp h).2 i
  by_cases h : AgreeOff (Sum.inl : Site Λ → AncillaSites Λ X) c c'
  · simp only [h, hagree.mp h, ite_true, mul_one]
  · simp only [h, hagree.not.mp h, ite_false, mul_zero]

/-- An operator on the copy `s'` alone is placed on the sites of `s'`. -/
theorem one_kronecker_submatrix_ancillaSplit (X : Finset (Site Λ))
    (b : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) :
    ((1 : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) ⊗ₖ
      (b ⊗ₖ (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ))).submatrix
        (ancillaSplit q X) (ancillaSplit q X) =
      embedOp (Sum.inr ∘ Sum.inl : ↥X → AncillaSites Λ X) b := by
  ext c c'
  simp only [submatrix_apply, kroneckerMap_apply, one_apply, embedOp_apply, ancillaSplit_apply]
  have hagree : AgreeOff (Sum.inr ∘ Sum.inl : ↥X → AncillaSites Λ X) c c' ↔
      c ∘ Sum.inl = c' ∘ Sum.inl ∧ c ∘ Sum.inr ∘ Sum.inr = c' ∘ Sum.inr ∘ Sum.inr := by
    constructor
    · intro h
      exact ⟨funext fun x => h _ fun j => by simp,
        funext fun x => h _ fun j => by simp⟩
    · intro h i hi
      rcases i with i | i | i
      · exact congrFun h.1 i
      · exact absurd rfl (hi i)
      · exact congrFun h.2 i
  by_cases h : AgreeOff (Sum.inr ∘ Sum.inl : ↥X → AncillaSites Λ X) c c'
  · obtain ⟨h1, h2⟩ := hagree.mp h
    simp only [h, h1, h2, ite_true, one_mul, mul_one]
  · rcases not_and_or.mp (hagree.not.mp h) with h1 | h2
    · simp [h, h1]
    · simp [h, h2]

/-- **Supports on the enlarged sites.** An operator `P ⊗ (b ⊗ 1_{e'})`, with `P` acting on a
physical region `S` and `b` acting on `s'`, acts on `S ⊔ s'`.
Source: `09-amplification.tex`, lines 345–346 and 524–525. -/
theorem kronecker_submatrix_ancillaSplit_mem_supportedOperators {X S : Finset (Site Λ)}
    {P : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hP : P ∈ supportedOperators q (S : Set (Site Λ)))
    (b : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) :
    (P ⊗ₖ (b ⊗ₖ (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ))).submatrix
        (ancillaSplit q X) (ancillaSplit q X) ∈
      supportedOperators q ((S.disjSum (Finset.univ.disjSum ∅) : Finset (AncillaSites Λ X)) :
        Set (AncillaSites Λ X)) := by
  have hsplit : P ⊗ₖ (b ⊗ₖ (1 : Matrix (RegionalConfiguration q X)
      (RegionalConfiguration q X) ℂ)) = (P ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
        RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *
      ((1 : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) ⊗ₖ
        (b ⊗ₖ (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ))) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hsplit, ← submatrix_mul_equiv _ _ _ (ancillaSplit q X),
    kronecker_one_submatrix_ancillaSplit, one_kronecker_submatrix_ancillaSplit]
  refine mul_mem_supportedOperators (supportedOperators_mono ?_
    (embedOp_mem_supportedOperators_image Sum.inl_injective hP))
    (supportedOperators_mono ?_ (embedOp_mem_supportedOperators
      (Sum.inr_injective.comp Sum.inl_injective) b))
  · rintro _ ⟨v, hv, rfl⟩
    simpa using hv
  · rintro _ ⟨x, rfl⟩
    simp

/-- **Physical operators on the enlarged sites.** A physical operator acting on a region `S`,
tensored with the identity on both copies, acts on `S ⊔ s'`. -/
theorem kronecker_one_submatrix_ancillaSplit_mem_supportedOperators {X S : Finset (Site Λ)}
    {L : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hL : L ∈ supportedOperators q (S : Set (Site Λ))) :
    (L ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
      (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)).submatrix
        (ancillaSplit q X) (ancillaSplit q X) ∈
      supportedOperators q ((S.disjSum (Finset.univ.disjSum ∅) : Finset (AncillaSites Λ X)) :
        Set (AncillaSites Λ X)) := by
  rw [kronecker_one_submatrix_ancillaSplit]
  refine supportedOperators_mono ?_ (embedOp_mem_supportedOperators_image Sum.inl_injective hL)
  rintro _ ⟨v, hv, rfl⟩
  simpa using hv

/-! ### Vectors and mutual information -/

/-- The value of `restoringSplit` inverted at a configuration whose `X` part is replaced. -/
theorem restoringSplit_symm_replace (X Y : Finset (Site Λ)) (hXY : Disjoint X Y)
    (c : Configuration Λ q) (e : RegionalConfiguration q X) :
    (restoringSplit q X Y hXY).symm ((e, (restoringSplit q X Y hXY c).1.2),
        (restoringSplit q X Y hXY c).2) =
      fun v => if hv : v ∈ X then e ⟨v, hv⟩ else c v := by
  funext v
  change (FiniteProduct.splitEquiv (fun _ : Site Λ ↦ Fin q) (X ∪ Y)).symm
    ((FiniteProduct.unionEquiv (fun _ : Site Λ ↦ Fin q) X Y hXY).symm
      (e, fun w : ↥Y => c w), fun w => c w) v = _
  by_cases hv : v ∈ X ∪ Y
  · rw [FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _ hv]
    by_cases hvX : v ∈ X
    · simp [FiniteProduct.unionEquiv, hvX]
    · simp [FiniteProduct.unionEquiv, hvX]
  · have hvX : v ∉ X := fun h => hv (Finset.mem_union_left Y h)
    rw [FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hv]
    simp [hvX]

/-- The swap of each site of the target `X` with its copy in `e'`. -/
def ancillaSwapFun (X : Finset (Site Λ)) : AncillaSites Λ X → AncillaSites Λ X
  | .inl v => if hv : v ∈ X then .inr (.inr ⟨v, hv⟩) else .inl v
  | .inr (.inl x) => .inr (.inl x)
  | .inr (.inr x) => .inl x.val

theorem ancillaSwapFun_involutive (X : Finset (Site Λ)) :
    Function.Involutive (ancillaSwapFun X) := by
  rintro (v | x | x)
  · by_cases hv : v ∈ X <;> simp [ancillaSwapFun, hv]
  · rfl
  · simp [ancillaSwapFun, x.2]

/-- The swap of the target with its copy `e'`, as a permutation of the enlarged sites. -/
def ancillaSwap (X : Finset (Site Λ)) : Equiv.Perm (AncillaSites Λ X) :=
  (ancillaSwapFun_involutive X).toPerm _

/-- **The restored vector has a product reduction on `e'` and a physical region.** For a
unit physical vector `Ω` and a unit ancillary vector `χ`, the vector `Ω ⊗ χ` on the enlarged
sites has no mutual information between `e'` and any physical region.
Source: `09-amplification.tex`, lines 342–347 and 550–551. -/
theorem mutualInformation_ancillaProduct_copy_eq_zero {X : Finset (Site Λ)}
    {Ω : StateSpace Λ q} (hΩ : ‖Ω‖ = 1)
    {χ : RegionalConfiguration q X × RegionalConfiguration q X → ℂ}
    (hχ : ‖WithLp.toLp 2 χ‖ = 1) (X' : Finset ↥X) (J : Finset (Site Λ)) :
    FiniteProduct.mutualInformation (fun _ : AncillaSites Λ X => Fin q)
        (WithLp.toLp 2 ((fun c => Ω c.1 * χ c.2) ∘ ancillaSplit q X))
        (ancillaCopyRegion X') (ancillaPhysicalRegion X J) = 0 := by
  set g : EuclideanSpace ℂ (↥X ⊕ ↥X → Fin q) :=
    WithLp.toLp 2 fun d => χ (d ∘ Sum.inl, d ∘ Sum.inr)
  have hg : ‖g‖ = 1 := by
    rw [← hχ]
    exact EuclideanSpace.norm_toLp_comp_equiv (Equiv.sumArrowEquivProdArrow _ _ _) χ
  have hvec : WithLp.toLp 2 ((fun c => Ω c.1 * χ c.2) ∘ ancillaSplit q X) =
      FiniteProduct.sumSitesProduct (F := Fin q) Ω g := rfl
  rw [hvec, ancillaCopyRegion, ancillaPhysicalRegion]
  exact FiniteProduct.mutualInformation_sumSitesProduct_inr_inl hΩ hg _ J

/-- **The copied vector carries the original reduction of the target, on `e'`.** Let `φ` be
the vector whose value at a physical configuration `c` and an ancillary pair `(s, e)` is
`a(s) b(c_X) Ω(c')`, where `c'` agrees with `c` off `X` and reads `e` on `X`, for unit
vectors `a, b`. For a part `X'` of `X` and a physical region `J` disjoint from `X`, the
mutual information of `φ` between the copy of `X'` in `e'` and `J` equals `I_Ω(X' : J)`.
Source: `09-amplification.tex`, lines 342–344 and 547–550. -/
theorem mutualInformation_ancillaCopy_eq {X Y : Finset (Site Λ)} (hXY : Disjoint X Y)
    {Ω : StateSpace Λ q} (hΩ : ‖Ω‖ = 1) {a b : RegionalConfiguration q X → ℂ}
    (ha : ‖WithLp.toLp 2 a‖ = 1) (hb : ‖WithLp.toLp 2 b‖ = 1) (X' : Finset ↥X)
    {J : Finset (Site Λ)} (hJ : Disjoint J X) :
    FiniteProduct.mutualInformation (fun _ : AncillaSites Λ X => Fin q)
        (WithLp.toLp 2 ((fun c : Configuration Λ q × (RegionalConfiguration q X ×
          RegionalConfiguration q X) => a c.2.1 * b (restoringSplit q X Y hXY c.1).1.1 *
            Ω ((restoringSplit q X Y hXY).symm ((c.2.2, (restoringSplit q X Y hXY c.1).1.2),
              (restoringSplit q X Y hXY c.1).2))) ∘ ancillaSplit q X))
        (ancillaCopyRegion X') (ancillaPhysicalRegion X J) =
      FiniteProduct.mutualInformation (fun _ : Site Λ => Fin q) Ω (X'.map
        (Function.Embedding.subtype _)) J := by
  set g : EuclideanSpace ℂ (↥X ⊕ ↥X → Fin q) :=
    WithLp.toLp 2 fun d => a (d ∘ Sum.inl) * b (d ∘ Sum.inr)
  have hab : ‖WithLp.toLp 2 (fun p : RegionalConfiguration q X × RegionalConfiguration q X =>
      a p.1 * b p.2)‖ = 1 := by
    have h := EuclideanSpace.norm_vecKron (WithLp.toLp 2 a) (WithLp.toLp 2 b)
    rw [ha, hb, mul_one] at h
    exact h
  have hg : ‖g‖ = 1 := by
    rw [← hab]
    exact EuclideanSpace.norm_toLp_comp_equiv (Equiv.sumArrowEquivProdArrow ↥X ↥X (Fin q))
      (fun p : RegionalConfiguration q X × RegionalConfiguration q X => a p.1 * b p.2)
  have hσ : ∀ x, (ancillaSwap X).symm x = ancillaSwapFun X x := fun x => rfl
  have hvec : WithLp.toLp 2 ((fun c : Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X) => a c.2.1 * b (restoringSplit q X Y hXY c.1).1.1 *
        Ω ((restoringSplit q X Y hXY).symm ((c.2.2, (restoringSplit q X Y hXY c.1).1.2),
          (restoringSplit q X Y hXY c.1).2))) ∘ ancillaSplit q X) =
      FiniteProduct.relabelSites (ancillaSwap X) (FiniteProduct.sumSitesProduct Ω g) := by
    congr 1
    funext c
    simp only [Function.comp_apply, ancillaSplit_apply, restoringSplit_symm_replace,
      FiniteProduct.sumSitesProduct, g, PiLp.toLp_apply]
    have h1 : (c ∘ (ancillaSwap X).symm) ∘ Sum.inl =
        fun v => if hv : v ∈ X then c (Sum.inr (Sum.inr ⟨v, hv⟩)) else c (Sum.inl v) := by
      funext v
      simp only [Function.comp_apply, hσ, ancillaSwapFun]
      split_ifs <;> rfl
    have h2 : ((c ∘ (ancillaSwap X).symm) ∘ Sum.inr) ∘ Sum.inl = c ∘ Sum.inr ∘ Sum.inl := rfl
    have h3 : ((c ∘ (ancillaSwap X).symm) ∘ Sum.inr) ∘ Sum.inr =
        fun x : ↥X => c (Sum.inl x.val) := rfl
    rw [h1, h2, h3]
    have h4 : (restoringSplit q X Y hXY (c ∘ Sum.inl)).1.1 = fun x : ↥X => c (Sum.inl x.val) :=
      rfl
    rw [h4]
    ring
  have hcopy : (ancillaCopyRegion X').map (ancillaSwap X).toEmbedding =
      (X'.map (Function.Embedding.subtype _)).disjSum ∅ := by
    ext x
    rw [Finset.mem_map_equiv, hσ]
    rcases x with v | y | y
    · by_cases hv : v ∈ X
      · simp only [ancillaSwapFun, hv, dite_true, ancillaCopyRegion, Finset.inr_mem_disjSum,
          Finset.inl_mem_disjSum, Finset.mem_map, Function.Embedding.coe_subtype]
        constructor
        · intro h
          exact ⟨_, h, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact hx
      · simp only [ancillaSwapFun, hv, dite_false, ancillaCopyRegion, Finset.inl_mem_disjSum,
          Finset.notMem_empty, false_iff, Finset.mem_map, Function.Embedding.coe_subtype,
          not_exists, not_and]
        exact fun x _ hx => hv (hx ▸ x.2)
    · simp [ancillaSwapFun, ancillaCopyRegion]
    · simp [ancillaSwapFun, ancillaCopyRegion]
  have hphys : (ancillaPhysicalRegion X J).map (ancillaSwap X).toEmbedding = J.disjSum ∅ := by
    ext x
    rw [Finset.mem_map_equiv, hσ]
    rcases x with v | y | y
    · by_cases hv : v ∈ X
      · have hvJ : v ∉ J := fun h => Finset.disjoint_left.mp hJ h hv
        simp [ancillaSwapFun, ancillaPhysicalRegion, hv, hvJ]
      · simp [ancillaSwapFun, ancillaPhysicalRegion, hv]
    · simp [ancillaSwapFun, ancillaPhysicalRegion]
    · have hyJ : (y : Site Λ) ∉ J := fun h => Finset.disjoint_left.mp hJ h y.2
      simp [ancillaSwapFun, ancillaPhysicalRegion, hyJ]
  rw [hvec, FiniteProduct.mutualInformation_relabelSites, hcopy, hphys]
  exact FiniteProduct.mutualInformation_sumSitesProduct_inl hΩ hg _ _

end TNLean.PEPS.AreaLaw
