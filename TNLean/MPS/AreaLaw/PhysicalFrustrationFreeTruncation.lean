/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.PhysicalDetectability
import QICLean.Algebra.MatrixAux

/-!
# The actual regional frustration-free truncation

For an interval of sites, retain the original interactions outside the
interval and replace its two parity layers by the complements of their
actual projection products. The construction is ALVV, arXiv:1602.08828v2,
`def:FF-tH`, lines 1467–1487. Positivity and the common kernel are proved
without a uniqueness or gap hypothesis.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- Restrict a physical bond family to the bonds contained in the site interval
`[a,b)`. This is the internal family in ALVV, arXiv:1602.08828v2,
`def:FF-tH`, lines 1467–1487. -/
noncomputable def intervalBondRestriction
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (a b : ℕ)
    (i : Fin (L - 1)) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  if a ≤ i.val ∧ i.val + 1 < b then h i else 0

/-- The actual regional Hamiltonian obtained by replacing the two internal
parity layers by their complementary products. ALVV, arXiv:1602.08828v2,
`def:FF-tH`, lines 1467–1487. -/
noncomputable def physicalFrustrationFreeTruncation
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (a b : ℕ) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  (∑ i, if a ≤ i.val ∧ i.val + 1 < b then 0 else h i) +
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
      (1 - physicalParityProduct (intervalBondRestriction h a b) 0) +
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
      (1 - physicalParityProduct (intervalBondRestriction h a b) 1)

private theorem intervalBondRestriction_isStarProjection
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i)) (a b : ℕ) (i : Fin (L - 1)) :
    IsStarProjection (intervalBondRestriction h a b i) := by
  unfold intervalBondRestriction
  split_ifs <;> first | exact hp i | exact IsStarProjection.zero _

private theorem intervalBondRestriction_supported
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (a b : ℕ) (i : Fin (L - 1)) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (intervalBondRestriction h a b i) (interval L i.val (i.val + 2)) := by
  unfold intervalBondRestriction
  split_ifs <;> first
    | exact hs i
    | exact QuantumCircuit.isSupportedOn_of_mem_supportedOperators (Submodule.zero_mem _)

private theorem regionalParityComplement_isStarProjection
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (a b p : ℕ) :
    IsStarProjection
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
        (1 - physicalParityProduct (intervalBondRestriction h a b) p)) := by
  exact (physicalParityProduct_isStarProjection _
    (intervalBondRestriction_isStarProjection h hp a b)
    (intervalBondRestriction_supported h hs a b) p).one_sub.map
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm.toStarAlgHom

/-- The actual regional frustration-free truncation is positive semidefinite.
ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`,
lines 1467–1487 and 1543–1550. -/
theorem physicalFrustrationFreeTruncation_posSemidef
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (a b : ℕ) :
    (physicalFrustrationFreeTruncation h a b).PosSemidef := by
  unfold physicalFrustrationFreeTruncation
  refine (Matrix.PosSemidef.add (Matrix.PosSemidef.add ?_
    (Matrix.nonneg_iff_posSemidef.mp
      (regionalParityComplement_isStarProjection h hp hs a b 0).nonneg))
      (Matrix.nonneg_iff_posSemidef.mp
        (regionalParityComplement_isStarProjection h hp hs a b 1).nonneg))
  exact Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ ↦ ite_nonneg (le_refl 0) (hp i).nonneg)

private noncomputable def regionalTruncationTerm
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (a b : ℕ) :
    Fin (L - 1) ⊕ Fin 2 →
      (EuclideanSpace ℂ (Fin L → Fin q) →L[ℂ] EuclideanSpace ℂ (Fin L → Fin q))
  | .inl i => if a ≤ i.val ∧ i.val + 1 < b then 0 else
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (h i)
  | .inr p => 1 - physicalParityProduct (intervalBondRestriction h a b) p.val

private theorem sum_regionalTruncationTerm
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (a b : ℕ) :
    (∑ i, regionalTruncationTerm h a b i) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (physicalFrustrationFreeTruncation h a b) := by
  simp only [Fintype.sum_sum_type, regionalTruncationTerm, Fin.sum_univ_two,
    physicalFrustrationFreeTruncation, map_add, map_sum, apply_ite, map_zero,
    StarAlgEquiv.apply_symm_apply, Fin.val_zero, Fin.val_one]
  exact (add_assoc _ _ _).symm

private theorem regionalTruncationTerm_isStarProjection
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (a b : ℕ)
    (i : Fin (L - 1) ⊕ Fin 2) : IsStarProjection (regionalTruncationTerm h a b i) := by
  cases i <;> dsimp only [regionalTruncationTerm]
  case inl i =>
    split_ifs <;> first
      | exact IsStarProjection.zero _
      | exact (hp i).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))
  case inr p =>
    exact (physicalParityProduct_isStarProjection _
      (intervalBondRestriction_isStarProjection h hp a b)
      (intervalBondRestriction_supported h hs a b) p.val).one_sub

/-- The actual regional truncation preserves the full kernel of the original
Hamiltonian. This does not require a ground vector, uniqueness, or a gap.
ALVV, arXiv:1602.08828v2, `thm:FF-tH`, lines 1543–1550. -/
theorem physicalFrustrationFreeTruncation_kernel_iff
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (a b : ℕ)
    (x : EuclideanSpace ℂ (Fin L → Fin q)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (physicalFrustrationFreeTruncation h a b) x = 0 ↔
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (∑ i, h i) x = 0 := by
  constructor
  · intro hx
    have hsum : (∑ i, (regionalTruncationTerm h a b i).toLinearMap) x = 0 := by
      simpa only [← sum_regionalTruncationTerm, _root_.sum_apply, LinearMap.sum_apply,
        ContinuousLinearMap.coe_coe] using hx
    have hterm (i : Fin (L - 1) ⊕ Fin 2) : regionalTruncationTerm h a b i x = 0 :=
      ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero _
        (fun j ↦ ContinuousLinearMap.IsStarProjection.isSymmetricProjection
          (regionalTruncationTerm_isStarProjection h hp hs a b j)) hsum i
    have hfix (p : Fin 2) :
        physicalParityProduct (intervalBondRestriction h a b) p.val x = x := by
      exact (sub_eq_zero.mp (hterm (.inr p))).symm
    have hzero (i : Fin (L - 1)) :
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (h i) x = 0 := by
      by_cases hi : a ≤ i.val ∧ i.val + 1 < b
      · have hm := (physicalParityProduct_apply_eq_self_iff _
          (intervalBondRestriction_isStarProjection h hp a b) (i.val % 2) x).mp
            (hfix ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩) i rfl
        simpa only [intervalBondRestriction, ite_eq_left hi] using hm
      · simpa only [regionalTruncationTerm, ite_eq_right hi] using hterm (.inl i)
    simp only [map_sum, _root_.sum_apply, hzero, Finset.sum_const_zero]
  · intro hx
    have hzero (i : Fin (L - 1)) :
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) (h i) x = 0 :=
      ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero
        (fun j ↦ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
          (h j)).toLinearMap)
        (fun j ↦ ContinuousLinearMap.IsStarProjection.isSymmetricProjection
          ((hp j).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q))))
        (by simpa only [map_sum, _root_.sum_apply, LinearMap.sum_apply,
          ContinuousLinearMap.coe_coe] using hx) i
    have hmask : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)
        (∑ i, intervalBondRestriction h a b i) x = 0 := by
      simp only [map_sum, _root_.sum_apply, intervalBondRestriction, apply_ite,
        map_zero, DFunLike.ite_apply, _root_.zero_apply, hzero, ite_self, Finset.sum_const_zero]
    have hfix (p : Fin 2) :
        physicalParityProduct (intervalBondRestriction h a b) p.val x = x :=
      physicalParityProduct_fixes_kernel _
        (intervalBondRestriction_isStarProjection h hp a b) hmask p.val
    suffices hterm : ∀ i, regionalTruncationTerm h a b i x = 0 by
      simp only [← sum_regionalTruncationTerm, _root_.sum_apply, hterm, Finset.sum_const_zero]
    rintro (i | p) <;> simp [regionalTruncationTerm, DFunLike.ite_apply, hzero, hfix]

/-- The two actual regional replacement terms have total operator norm at
most two. ALVV, arXiv:1602.08828v2, `def:FF-tH` and `def:HLeven-odd`,
lines 1467–1487. -/
theorem norm_physicalFrustrationFreeTruncation_region_le_two
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hp : ∀ i, IsStarProjection (h i))
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (a b : ℕ) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
        (1 - physicalParityProduct (intervalBondRestriction h a b) 0) +
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q)).symm
        (1 - physicalParityProduct (intervalBondRestriction h a b) 1)‖ ≤ 2 := by
  simpa only [one_add_one_eq_two] using (norm_add_le _ _).trans
    (add_le_add
      (IsStarProjection.norm_le _ (regionalParityComplement_isStarProjection h hp hs a b 0))
      (IsStarProjection.norm_le _ (regionalParityComplement_isStarProjection h hp hs a b 1)))

end TNLean.MPS.AreaLaw
