/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusTwoByTwoBlocking
import TNLean.PEPS.RegularSiteGram
import TNLean.PEPS.GIsometricCoordinateTransport
import TNLean.Algebra.FinSumPermutation

/-!
# G-isometry of the explicit four-site contraction

The Gram operator of the literal two-by-two contraction is derived from its
four local Gram operators. The internal cycle forces the four translations
to coincide and contributes one factor of the group order. No blocked Gram
operator, support condition, or factorization is assumed.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 6.2 and
Observations 6.5–6.6, lines 1704–1716 and 1825–1920.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {G : Type*} [Group G]

/-- Translating every boundary and internal label translates every fine leg.
Source: SCP10, the virtual symmetry in Observations 6.5–6.6. -/
theorem twoByTwoSiteLegs_smul (g : G) (α : Fin 4 → G × G) (x : Fin 4 → G) :
    twoByTwoSiteLegs (g • α) (g • x) = g • twoByTwoSiteLegs α x := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Group G] in
private theorem twoByTwoSiteLegs_eq_iff (α β : Fin 4 → G × G) (x y : Fin 4 → G) :
    twoByTwoSiteLegs α x = twoByTwoSiteLegs β y ↔ α = β ∧ x = y := by
  simp only [funext_iff, Fin.forall_fin_succ, Fin.isValue,
    twoByTwoSiteLegs, Matrix.cons_val_zero, Prod.ext_iff]
  aesop

/-- The four internal bonds force all four local translations to coincide.
The remaining conditions are exactly translation of the eight boundary labels
and of the four internal labels. Source: SCP10, Lemma 6.2 and Observation 6.6. -/
theorem twoByTwoSiteLegs_compatible_iff
    (α β : Fin 4 → G × G) (x y q : Fin 4 → G) :
    (∀ i, twoByTwoSiteLegs α x i = q i • twoByTwoSiteLegs β y i) ↔
      q = (fun _ => q 0) ∧ α = q 0 • β ∧ x = q 0 • y := by
  constructor
  · intro h
    have h01 : q 0 = q 1 := mul_right_cancel
      ((congrFun (h 0) 2).symm.trans (congrFun (h 1) 0))
    have h12 : q 1 = q 2 := mul_right_cancel
      ((congrFun (h 1) 3).symm.trans (congrFun (h 2) 1))
    have h23 : q 2 = q 3 := mul_right_cancel
      ((congrFun (h 2) 0).symm.trans (congrFun (h 3) 2))
    have hq : q = fun _ => q 0 := by
      funext i
      fin_cases i
      · rfl
      · exact h01.symm
      · exact (h01.trans h12).symm
      · exact (h01.trans (h12.trans h23)).symm
    refine ⟨hq, ?_⟩
    apply (twoByTwoSiteLegs_eq_iff α (q 0 • β) x (q 0 • y)).mp
    rw [twoByTwoSiteLegs_smul]
    funext i
    simpa only [Pi.smul_apply, congrFun hq i] using h i
  · rintro ⟨hq, rfl, rfl⟩ i
    rw [twoByTwoSiteLegs_smul]
    simp only [Pi.smul_apply, congrFun hq i]

variable [Fintype G] [DecidableEq G]

omit [Group G] in
private theorem sum_constant_translation (p : G → Prop) [DecidablePred p] :
    (∑ q : Fin 4 → G, if q = (fun _ => q 0) ∧ p (q 0) then (1 : ℂ) else 0) =
      ∑ g : G, if p g then 1 else 0 := by
  classical
  have hq (q : Fin 4 → G) :
      (if q = (fun _ => q 0) ∧ p (q 0) then (1 : ℂ) else 0) =
        ∑ g : G, if q = (fun _ => g) ∧ p g then 1 else 0 := by
    symm
    apply Finset.sum_eq_single (q 0)
    · intro g _ hg
      have hn : q ≠ fun _ => g := by
        intro h
        exact hg (congrFun h 0).symm
      simp only [hn, false_and, ite_false]
    · simp
  simp_rw [hq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h : p g <;> simp [h]

/-- Four free internal ket labels remain after all four local group constraints
are imposed. Source: SCP10, the cycle in the two-by-two blocking diagram. -/
theorem sum_twoByTwoSiteLegs_compatible (α β : Fin 4 → G × G) :
    (∑ x : Fin 4 → G, ∑ y : Fin 4 → G, ∑ q : Fin 4 → G,
      if ∀ i, twoByTwoSiteLegs α x i = q i • twoByTwoSiteLegs β y i
      then (1 : ℂ) else 0) =
      (Fintype.card G : ℂ) ^ 4 * ∑ g : G, if α = g • β then 1 else 0 := by
  classical
  simp_rw [twoByTwoSiteLegs_compatible_iff]
  rw [Finset.sum_comm]
  have hy (y : Fin 4 → G) :
      (∑ x : Fin 4 → G, ∑ q : Fin 4 → G,
        if q = (fun _ => q 0) ∧ α = q 0 • β ∧ x = q 0 • y then (1 : ℂ) else 0) =
      ∑ g : G, if α = g • β then 1 else 0 := by
    rw [Finset.sum_comm]
    have hx (q : Fin 4 → G) :
        (∑ x : Fin 4 → G,
          if q = (fun _ => q 0) ∧ α = q 0 • β ∧ x = q 0 • y then (1 : ℂ) else 0) =
        if q = (fun _ => q 0) ∧ α = q 0 • β then 1 else 0 := by
      rw [Finset.sum_eq_single (q 0 • y)]
      · simp only [and_true]
      · intro x _ hx
        exact ite_eq_right (fun h => hx h.2.2)
      · simp
    simp_rw [hx]
    exact sum_constant_translation (fun g => α = g • β)
  simp_rw [hy]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow]

variable {P : Type*} [Fintype P]

omit [Group G] [DecidableEq G] in
/-- The physical Gram sum of the literal four-site contraction factors into
four local physical Gram sums. Source: SCP10, Lemma 6.2 and Observation 6.6. -/
theorem twoByTwoTensor_gram_expansion
    (a : Fin 4 → (Fin 4 → G) → P → ℂ) (α β : Fin 4 → G × G) :
    (∑ σ : Fin 4 → P, star (twoByTwoTensor a α σ) * twoByTwoTensor a β σ) =
      ∑ x : Fin 4 → G, ∑ y : Fin 4 → G, ∏ i : Fin 4,
        ∑ s : P, star (a i (twoByTwoSiteLegs α x i) s) *
          a i (twoByTwoSiteLegs β y i) s := by
  classical
  simp only [twoByTwoTensor, star_sum, star_prod, Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_reverse_three]
  apply Finset.sum_congr₂
  intro x _ y _
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin 4) (s : P) =>
    star (a i (twoByTwoSiteLegs α x i) s) * a i (twoByTwoSiteLegs β y i) s)).symm

private theorem twoByTwoTensor_gram_of_local
    (a : Fin 4 → (Fin 4 → G) → P → ℂ) (c : Fin 4 → ℂ)
    (hlocal : ∀ i η θ, (∑ s : P, star (a i η s) * a i θ s) =
      (c i / (Fintype.card G : ℂ)) * ∑ g : G, if η = g • θ then 1 else 0)
    (α β : Fin 4 → G × G) :
    (∑ σ : Fin 4 → P, star (twoByTwoTensor a α σ) * twoByTwoTensor a β σ) =
      (∏ i, c i) * ∑ g : G, if α = g • β then 1 else 0 := by
  classical
  rw [twoByTwoTensor_gram_expansion]
  simp_rw [hlocal, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.prod_sum,
    Fintype.prod_boole, ← Finset.mul_sum]
  calc
    _ = ((∏ i, c i) / (Fintype.card G : ℂ) ^ 4) *
        ((Fintype.card G : ℂ) ^ 4 * ∑ g : G, if α = g • β then (1 : ℂ) else 0) := by
      congr 1
      convert sum_twoByTwoSiteLegs_compatible α β using 4
      split_ifs <;> rfl
    _ = _ := by
      rw [← mul_assoc, div_mul_cancel₀ _
        (pow_ne_zero 4 (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := G))))]

/-- Fine-site G-isometry determines the actual blocked Gram operator. The
positive block isometry factor is the group order times the four site factors.
Source: SCP10, Lemma 6.2 and the two-by-two blocking in Observation 6.6. -/
theorem exists_twoByTwoTensor_gram
    (a : Fin 4 → (Fin 4 → G) → P → ℂ)
    (ha : ∀ i, IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap (a i))) :
    ∃ c : Fin 4 → ℝ, (∀ i, 0 < c i) ∧
      ∀ α β : Fin 4 → G × G,
        (∑ σ : Fin 4 → P, star (twoByTwoTensor a α σ) * twoByTwoTensor a β σ) =
          (∏ i, (c i : ℂ)) * ∑ g : G, if α = g • β then 1 else 0 := by
  choose c hc h using fun i => (ha i).exists_regularSiteGram
  exact ⟨c, hc, twoByTwoTensor_gram_of_local a (fun i => (c i : ℂ)) h⟩

omit [Fintype P] [DecidableEq G] in
/-- The explicit contraction retains simultaneous translation of the paired
boundary labels. Source: SCP10, the virtual symmetry of the blocked tensor. -/
theorem twoByTwoTensor_translation
    (a : Fin 4 → (Fin 4 → G) → P → ℂ)
    (ha : ∀ i, IsGInjective (regularLegRepresentation (Fin 4)) (regularSiteMap (a i)))
    (g : G) (α : Fin 4 → G × G) (σ : Fin 4 → P) :
    twoByTwoTensor a (g • α) σ = twoByTwoTensor a α σ := by
  classical
  unfold twoByTwoTensor
  rw [← Equiv.sum_comp (MulAction.toPermHom G (Fin 4 → G) g)]
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, twoByTwoSiteLegs_smul,
    Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro i _
  exact (ha i).regularSiteMap_translation g _ _

omit [Group G] [DecidableEq G] [Fintype P] in
/-- The same literal four-site contraction, with all eight boundary bonds
separately indexed. Source: SCP10, the boundary of the two-by-two diagram. -/
def twoByTwoSeparatedTensor (a : Fin 4 → (Fin 4 → G) → P → ℂ)
    (β : Fin 4 × Fin 2 → G) (σ : Fin 4 → P) : ℂ :=
  twoByTwoTensor a (twoByTwoBoundaryEquiv.symm β) σ

attribute [local instance] Representation.invertibleFintypeCardComplex

omit [DecidableEq G] in
/-- The actual two-by-two contraction is G-isometric from fine-site
G-isometry alone, on all eight regular boundary bonds and all four original
physical registers. Source: SCP10, Lemma 6.2 and Observation 6.6. -/
theorem isGIsometric_twoByTwoSeparatedTensor
    (a : Fin 4 → (Fin 4 → G) → P → ℂ)
    (ha : ∀ i, IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap (a i))) :
    IsGIsometric (regularLegRepresentation (Fin 4 × Fin 2))
      (regularSiteMap (twoByTwoSeparatedTensor a)) := by
  classical
  obtain ⟨c, hc, hgram⟩ := exists_twoByTwoTensor_gram a ha
  have htrans (g : G) (β : Fin 4 × Fin 2 → G) (σ : Fin 4 → P) :
      twoByTwoSeparatedTensor a (g • β) σ = twoByTwoSeparatedTensor a β σ :=
    twoByTwoTensor_translation a (fun i => (ha i).toIsGInjective) g
      (twoByTwoBoundaryEquiv.symm β) σ
  have hinv (g : G) : regularSiteMap (twoByTwoSeparatedTensor a) ∘ₗ
      regularLegRepresentation (Fin 4 × Fin 2) g =
        regularSiteMap (twoByTwoSeparatedTensor a) := by
    apply LinearMap.ext
    intro x
    funext σ
    change (∑ η, twoByTwoSeparatedTensor a η σ *
      (regularLegRepresentation (Fin 4 × Fin 2) g x) η) =
        ∑ η, twoByTwoSeparatedTensor a η σ * x η
    simp only [regularLegRepresentation_apply]
    rw [← Equiv.sum_comp (MulAction.toPermHom G ((Fin 4 × Fin 2) → G) g)]
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, inv_smul_smul, htrans]
  apply isGIsometric_of_coordinateAdjoint_comp hinv
    (show 0 < (Fintype.card G : ℝ) * ∏ i, c i from
      mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Finset.prod_pos fun i _ => hc i))
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_comp, coordinateAdjoint, LinearMap.toMatrix'_toLin',
    toMatrix_regularSiteMap, map_smul]
  ext η θ
  change (∑ σ : Fin 4 → P,
    star (twoByTwoTensor a (twoByTwoBoundaryEquiv.symm η) σ) *
      twoByTwoTensor a (twoByTwoBoundaryEquiv.symm θ) σ) =
    (((Fintype.card G : ℝ) * ∏ i, c i : ℝ) : ℂ) *
      regularLegProjector (Fin 4 × Fin 2) η θ
  have he (g : G) : twoByTwoBoundaryEquiv.symm η = g • twoByTwoBoundaryEquiv.symm θ ↔
      η = g • θ := (twoByTwoBoundaryEquiv (X := G)).symm.injective.eq_iff
        (a := η) (b := g • θ)
  rw [hgram, regularLegProjector_apply]
  simp only [he, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_prod]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end TNLean.PEPS
