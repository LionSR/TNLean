/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LinearMarkedTensor
import TNLean.MPS.MPDO.ReflectedMarkedChain

/-!
# Pairwise Gram comparison for vertical corners

Hermiticity gives the reflected marked-chain identity of Figure 7 separately
for each vertical corner.  Conjugating its open indices by the adjoint of the
vertical gauge identifies the resulting left side with the Gram-dressed
vertical tensor, while the right side becomes the reflected adjoint of the
common representative.  Consequently two corners of the same representative
have equal marked chains after Gram dressing.

The final separation uses only marks in the span of the physical letters of
the horizontal tensor.  The corner equations give the required coefficient
families explicitly.  This module uses normalized BNT-refined horizontal form;
`TNLean.MPS.MPDO.CPSVFigureEight` gives the literal-CPSV counterpart.

## Main results

* `IsMPDO.markedChainCoefficient_gramDressing_eq_reflectedAdjoint`: the
  Gram-dressed chain of one corner has the common reflected chain.
* `IsHorizontalCF.gramDressing_eq_of_two_grouped_corners`: two grouped
  corners of a common vertical representative have equal Gram dressings.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, Figures 7--8 and lines 1909--1919.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D n : ℕ}

/-- Multiply every vertical letter on its two virtual sides. -/
def bondMul (P : Matrix (Fin n) (Fin n) ℂ) (A : MPSTensor (D * D) n)
    (Q : Matrix (Fin n) (Fin n) ℂ) : MPSTensor (D * D) n :=
  fun v ↦ P * A v * Q

/-- Conjugation of a vertical tensor by the Gram matrix of an invertible
gauge.

This is the tensor appearing in the second diagram of arXiv:1606.00608,
Proposition 4.13, lines 1914--1919. -/
noncomputable def gramDressing (X : GL (Fin n) ℂ) (A : MPSTensor (D * D) n) :
    MPSTensor (D * D) n :=
  fun v ↦
    ((X : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (X : Matrix (Fin n) (Fin n) ℂ)) * A v *
      (((X : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (X : Matrix (Fin n) (Fin n) ℂ))⁻¹)

/-- Multiplication on the open virtual indices is a finite linear
combination of marked horizontal slices. -/
theorem horizontalSlice_bondMul
    (P Q : Matrix (Fin n) (Fin n) ℂ) (A : MPSTensor (D * D) n)
    (r s : Fin n) :
    horizontalSlice (bondMul P A Q) r s =
      ∑ p : Fin n, ∑ q : Fin n,
        (P r p * Q q s) • horizontalSlice A p q := by
  ext a b
  simp only [horizontalSlice, bondMul, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Multiplication on the open virtual indices gives the corresponding
finite linear combination of marked-chain coefficients. -/
theorem markedChainCoefficient_bondMul
    (P Q : Matrix (Fin n) (Fin n) ℂ) (A : MPSTensor (D * D) n)
    (M : MPOTensor d D) (r s : Fin n) (σs τs : List (Fin d)) :
    markedChainCoefficient (bondMul P A Q) M r s σs τs =
      ∑ p : Fin n, ∑ q : Fin n,
        P r p * markedChainCoefficient A M p q σs τs * Q q s := by
  simp_rw [markedChainCoefficient]
  rw [horizontalSlice_bondMul, Finset.sum_mul,
    Matrix.trace_sum]
  simp_rw [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- A pointwise equality of marked chains is preserved by common
multiplication on their open virtual indices. -/
theorem markedChainCoefficient_bondMul_eq_of_eq
    (P Q : Matrix (Fin n) (Fin n) ℂ)
    (A B : MPSTensor (D * D) n) (M N : MPOTensor d D)
    (r s : Fin n) (σs τs σs' τs' : List (Fin d))
    (h : ∀ p q : Fin n,
      markedChainCoefficient A M p q σs τs =
        markedChainCoefficient B N p q σs' τs') :
    markedChainCoefficient (bondMul P A Q) M r s σs τs =
      markedChainCoefficient (bondMul P B Q) N r s σs' τs' := by
  rw [markedChainCoefficient_bondMul, markedChainCoefficient_bondMul]
  simp_rw [h]

/-- The marked chain of a Gram-dressed vertical corner has a reflected form
which is independent of the corner gauge.

The proof conjugates the two open indices in the reflected Figure 7 identity
by $X^\dagger$.  On the original side this produces
$X^\dagger X A^v (X^\dagger X)^{-1}$; on the reflected side the two gauge
factors cancel.  This is the common right side used in Figure 8 of
arXiv:1606.00608, Proposition 4.13, lines 1909--1919. -/
theorem IsMPDO.markedChainCoefficient_gramDressing_eq_reflectedAdjoint
    {M : MPOTensor d D} (hM : IsMPDO M)
    (A : MPSTensor (D * D) n) (V : Matrix (Fin d) (Fin n) ℂ)
    (X : GL (Fin n) ℂ) (c : ℂ) (hc : (0 : ℂ) < c)
    (hcorner : ∀ v,
      Vᴴ * verticalTensor M v * V =
        c • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))
    (N : ℕ) (r s : Fin n) (σ τ : Fin N → Fin d) :
    markedChainCoefficient (gramDressing X A) M r s
        (List.ofFn σ) (List.ofFn τ) =
      markedChainCoefficient (reflectedAdjoint A) (MPOTensor.adjointTensor M) r s
        (List.ofFn σ).reverse (List.ofFn τ).reverse := by
  let Xm : Matrix (Fin n) (Fin n) ℂ := X
  let Xi : Matrix (Fin n) (Fin n) ℂ :=
    (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  let B : MPSTensor (D * D) n := bondMul Xm A Xi
  have hFigure : ∀ p q : Fin n,
      markedChainCoefficient B M p q (List.ofFn σ) (List.ofFn τ) =
        markedChainCoefficient (reflectedAdjoint B) (MPOTensor.adjointTensor M) p q
          (List.ofFn σ).reverse (List.ofFn τ).reverse := by
    intro p q
    apply hM.markedChainCoefficient_eq_reflectedAdjoint B V c hc
    intro v
    exact hcorner v
  have hCov := markedChainCoefficient_bondMul_eq_of_eq Xmᴴ Xiᴴ
    B (reflectedAdjoint B) M (MPOTensor.adjointTensor M) r s
    (List.ofFn σ) (List.ofFn τ)
    (List.ofFn σ).reverse (List.ofFn τ).reverse hFigure
  have hLeft : bondMul Xmᴴ B Xiᴴ = gramDressing X A := by
    funext v
    dsimp only [B, Xm, Xi, bondMul, gramDressing]
    rw [Matrix.coe_units_inv, Matrix.mul_inv_rev,
      Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
  have hRight : bondMul Xmᴴ (reflectedAdjoint B) Xiᴴ =
      reflectedAdjoint A := by
    funext v
    dsimp only [B, Xm, Xi, bondMul, reflectedAdjoint]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.coe_units_inv]
    simp only [Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      ← Matrix.coe_units_inv, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul]
    have hXX : X⁻¹ * X = (1 : GL (Fin n) ℂ) := inv_mul_cancel X
    rw [hXX, Units.val_one, Matrix.one_mul]
  rw [hLeft, hRight] at hCov
  exact hCov

/-- Two grouped corners of the same vertical representative have identical
Gram-dressed marked chains.

Both sides are identified with the reflected marked chain of the common
representative.  This is the pairwise use of Figures 7--8 in
arXiv:1606.00608, Proposition 4.13, lines 1909--1919. -/
theorem IsMPDO.markedChainCoefficient_gramDressing_eq_of_two_corners
    {M : MPOTensor d D} (hM : IsMPDO M)
    (A : MPSTensor (D * D) n)
    (VX VY : Matrix (Fin d) (Fin n) ℂ) (X Y : GL (Fin n) ℂ)
    (cX cY : ℂ) (hcX : (0 : ℂ) < cX) (hcY : (0 : ℂ) < cY)
    (hcornerX : ∀ v,
      VXᴴ * verticalTensor M v * VX =
        cX • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))
    (hcornerY : ∀ v,
      VYᴴ * verticalTensor M v * VY =
        cY • ((Y : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((Y)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))
    (N : ℕ) (r s : Fin n) (σ τ : Fin N → Fin d) :
    markedChainCoefficient (gramDressing X A) M r s
        (List.ofFn σ) (List.ofFn τ) =
      markedChainCoefficient (gramDressing Y A) M r s
        (List.ofFn σ) (List.ofFn τ) := by
  exact (hM.markedChainCoefficient_gramDressing_eq_reflectedAdjoint
    A VX X cX hcX hcornerX N r s σ τ).trans
      (hM.markedChainCoefficient_gramDressing_eq_reflectedAdjoint
        A VY Y cY hcY hcornerY N r s σ τ).symm

/-- A two-sided physical compression gives a linear combination of the
physical letters after horizontal slicing. -/
theorem horizontalSlice_twoSidedCompression
    (M : MPOTensor d D) (L R : Matrix (Fin d) (Fin n) ℂ) (r s : Fin n) :
    horizontalSlice (fun v ↦ Lᴴ * verticalTensor M v * R) r s =
      ∑ i : Fin d, ∑ j : Fin d,
        (star (L i r) * R j s) • M i j := by
  ext a b
  simp only [horizontalSlice, Matrix.mul_apply, Matrix.conjTranspose_apply,
    verticalTensor_finProdFinEquiv, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Coefficients expressing a Gram-dressed corner in the physical-letter
span of the horizontal tensor. -/
noncomputable def cornerGramCoefficients
    (V : Matrix (Fin d) (Fin n) ℂ) (X : GL (Fin n) ℂ) (c : ℂ) :
    Fin (n * n) → Fin (d * d) → ℂ :=
  fun u z ↦ c⁻¹ *
    star ((V * (X : Matrix (Fin n) (Fin n) ℂ)) z.divNat u.divNat) *
      (V * ((((X)⁻¹ : GL (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ))ᴴ) z.modNat u.modNat

/-- The coefficients of a grouped corner recover the horizontal slices of
its Gram-dressed representative. -/
theorem linearMarkedTensor_cornerGramCoefficients
    {M : MPOTensor d D} (A : MPSTensor (D * D) n)
    (V : Matrix (Fin d) (Fin n) ℂ) (X : GL (Fin n) ℂ)
    (c : ℂ) (hc : (0 : ℂ) < c)
    (hcorner : ∀ v,
      Vᴴ * verticalTensor M v * V =
        c • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))
    (u : Fin (n * n)) :
    MPSTensor.linearMarkedTensor (cornerGramCoefficients V X c)
        M.toMPSTensor u =
      horizontalSlice (gramDressing X A) u.divNat u.modNat := by
  let Xi : Matrix (Fin n) (Fin n) ℂ :=
    (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hScaled : ∀ v,
      c • gramDressing X A v =
        (V * (X : Matrix (Fin n) (Fin n) ℂ))ᴴ *
          verticalTensor M v * (V * Xiᴴ) := by
    intro v
    calc
      c • gramDressing X A v =
          (X : Matrix (Fin n) (Fin n) ℂ)ᴴ *
            (c • ((X : Matrix (Fin n) (Fin n) ℂ) * A v * Xi)) * Xiᴴ := by
        dsimp only [gramDressing, Xi]
        rw [Matrix.coe_units_inv, Matrix.mul_inv_rev,
          Matrix.conjTranspose_nonsing_inv]
        simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
      _ = (X : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          (Vᴴ * verticalTensor M v * V) * Xiᴴ := by rw [hcorner]
      _ = (V * (X : Matrix (Fin n) (Fin n) ℂ))ᴴ *
          verticalTensor M v * (V * Xiᴴ) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hRecover : gramDressing X A = fun v ↦
      c⁻¹ • ((V * (X : Matrix (Fin n) (Fin n) ℂ))ᴴ *
        verticalTensor M v * (V * Xiᴴ)) := by
    funext v
    rw [← hScaled v]
    simp [hc0]
  rw [hRecover, horizontalSlice_smul,
    horizontalSlice_twoSidedCompression]
  rw [MPSTensor.linearMarkedTensor]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  dsimp only [cornerGramCoefficients, MPOTensor.toMPSTensor, Xi]
  simp only [MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [smul_smul]
  congr 1
  ring

/-- Evaluating the doubled-index MPS view on paired physical letters is the
same as evaluating the ket and bra words separately. -/
theorem evalWord_toMPSTensor_ofFn (M : MPOTensor d D) (N : ℕ)
    (w : Fin N → Fin (d * d)) :
    MPSTensor.evalWord M.toMPSTensor (List.ofFn w) =
      evalWord M (List.ofFn fun k ↦ (w k).divNat)
        (List.ofFn fun k ↦ (w k).modNat) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      change M (w 0).divNat (w 0).modNat *
          MPSTensor.evalWord M.toMPSTensor (List.ofFn (w ∘ Fin.succ)) =
        M (w 0).divNat (w 0).modNat *
          evalWord M (List.ofFn fun k ↦ (w (Fin.succ k)).divNat)
            (List.ofFn fun k ↦ (w (Fin.succ k)).modNat)
      rw [ih (w ∘ Fin.succ)]
      rfl

end MPOTensor

namespace MPOTensor.IsHorizontalCF

variable {d D n : ℕ}

/-- **The pairwise Gram identity of Figure 8.**

Suppose two vertical corners of the same representative tensor are positive
scalar multiples of similarities by `X` and `Y`.  If the horizontal tensor
is in normalized BNT-refined form and defines positive operators at every
length, then
conjugation of the representative by the two Gram matrices gives the same
tensor:
$X^\dagger X A^v (X^\dagger X)^{-1}
 =Y^\dagger Y A^v (Y^\dagger Y)^{-1}$.

Hermiticity first identifies both marked chains with the common reflected
chain of the representative.  The corner equations express the two marks as
linear combinations of physical letters, so normalized BNT-refined horizontal
form separates them.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines
1909--1919. -/
theorem gramDressing_eq_of_two_grouped_corners
    (M : MPOTensor d D) (hHorizontal : M.IsHorizontalCF) (hM : IsMPDO M)
    (A : MPSTensor (D * D) n)
    (VX VY : Matrix (Fin d) (Fin n) ℂ) (X Y : GL (Fin n) ℂ)
    (cX cY : ℂ) (hcX : (0 : ℂ) < cX) (hcY : (0 : ℂ) < cY)
    (hcornerX : ∀ v,
      VXᴴ * verticalTensor M v * VX =
        cX • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))
    (hcornerY : ∀ v,
      VYᴴ * verticalTensor M v * VY =
        cY • ((Y : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((Y)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))) :
    gramDressing X A = gramDressing Y A := by
  let fX := cornerGramCoefficients VX X cX
  let fY := cornerGramCoefficients VY Y cY
  have hTrace : ∀ (L : ℕ) (u : Fin (n * n))
      (w : Fin L → Fin (d * d)),
      Matrix.trace
          (MPSTensor.linearMarkedTensor fX M.toMPSTensor u *
            MPSTensor.evalWord M.toMPSTensor (List.ofFn w)) =
        Matrix.trace
          (MPSTensor.linearMarkedTensor fY M.toMPSTensor u *
            MPSTensor.evalWord M.toMPSTensor (List.ofFn w)) := by
    intro L u w
    rw [show MPSTensor.linearMarkedTensor fX M.toMPSTensor u =
        horizontalSlice (gramDressing X A) u.divNat u.modNat by
      exact linearMarkedTensor_cornerGramCoefficients
        A VX X cX hcX hcornerX u]
    rw [show MPSTensor.linearMarkedTensor fY M.toMPSTensor u =
        horizontalSlice (gramDressing Y A) u.divNat u.modNat by
      exact linearMarkedTensor_cornerGramCoefficients
        A VY Y cY hcY hcornerY u]
    rw [evalWord_toMPSTensor_ofFn]
    exact hM.markedChainCoefficient_gramDressing_eq_of_two_corners
      A VX VY X Y cX cY hcX hcY hcornerX hcornerY L
        u.divNat u.modNat (fun k ↦ (w k).divNat) (fun k ↦ (w k).modNat)
  have hMarks : MPSTensor.linearMarkedTensor fX M.toMPSTensor =
      MPSTensor.linearMarkedTensor fY M.toMPSTensor :=
    hHorizontal.linearMarkedTensor_eq_of_trace_agree M fX fY hTrace
  funext v
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective v
  ext r s
  have hSlice := congrFun hMarks (finProdFinEquiv (r, s))
  rw [linearMarkedTensor_cornerGramCoefficients
      A VX X cX hcX hcornerX,
    linearMarkedTensor_cornerGramCoefficients
      A VY Y cY hcY hcornerY] at hSlice
  simpa only [horizontalSlice, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat] using congrFun (congrFun hSlice a) b

end MPOTensor.IsHorizontalCF
