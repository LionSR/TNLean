/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalCommutant
import TNLean.MPS.MPDO.CPSVOriginalSpaceLemmaL
import TNLean.MPS.MPDO.FigureEightPairwise

/-!
# Figure 8 for literal CPSV canonical form

The reflected marked-chain identity identifies the Gram-dressed chains of two supplied vertical
corners of one representative.  Lemma L for literal CPSV canonical form then gives equality of the
two Gram-dressed tensors on the original horizontal bond space.  When the representative is normal,
commutant rigidity makes the two Gram matrices positive real scalar multiples of one another.

Inactive listed horizontal coordinates remain present throughout Lemma L; their contributions
vanish only through their zero raw weights.

## Main results

* `MPSTensor.IsCPSVCanonicalForm.gramDressing_eq_of_two_grouped_corners`: the pairwise Figure 8
  identity under literal CPSV canonical form.
* `MPSTensor.IsCPSVCanonicalForm.gram_eq_pos_smul_gram_of_two_grouped_corners`: the positive
  relative Gram scalar for a normal representative.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, proof of Proposition 4.13,
  Figures 7--8 and lines 1909--1921.
-/

open scoped Matrix ComplexOrder
open MPOTensor

namespace MPSTensor.IsCPSVCanonicalForm

variable {d D n : ℕ}

/-- **The pairwise Gram identity of Figure 8 under literal CPSV canonical form.**

Suppose two vertical corners of the same representative tensor are positive scalar multiples of
similarities by `X` and `Y`.  The reflected marked-chain identity makes their Gram-dressed marked
chains equal.  Lemma L for the literal CPSV canonical form separates the corresponding physical
linear marks, giving
$X^\dagger X A^v (X^\dagger X)^{-1}=Y^\dagger Y A^v (Y^\dagger Y)^{-1}$.

**Scope restriction (conditional corners):** The theorem assumes the two positive corner
similarity equations; it does not construct the representative group or its corners.  See
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figures 7--8 and lines 1909--1919. -/
theorem gramDressing_eq_of_two_grouped_corners
    (M : MPOTensor d D) (hCanonical : IsCPSVCanonicalForm M.toMPSTensor) (hM : IsMPDO M)
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
          (linearMarkedTensor fX M.toMPSTensor u *
            evalWord M.toMPSTensor (List.ofFn w)) =
        Matrix.trace
          (linearMarkedTensor fY M.toMPSTensor u *
            evalWord M.toMPSTensor (List.ofFn w)) := by
    intro L u w
    rw [show linearMarkedTensor fX M.toMPSTensor u =
        horizontalSlice (gramDressing X A) u.divNat u.modNat by
      exact linearMarkedTensor_cornerGramCoefficients
        A VX X cX hcX hcornerX u]
    rw [show linearMarkedTensor fY M.toMPSTensor u =
        horizontalSlice (gramDressing Y A) u.divNat u.modNat by
      exact linearMarkedTensor_cornerGramCoefficients
        A VY Y cY hcY hcornerY u]
    rw [evalWord_toMPSTensor_ofFn]
    exact hM.markedChainCoefficient_gramDressing_eq_of_two_corners
      A VX VY X Y cX cY hcX hcY hcornerX hcornerY L
        u.divNat u.modNat (fun k ↦ (w k).divNat) (fun k ↦ (w k).modNat)
  have hMarks : linearMarkedTensor fX M.toMPSTensor =
      linearMarkedTensor fY M.toMPSTensor :=
    hCanonical.linearMarkedTensor_eq_of_trace_agree M.toMPSTensor fX fY hTrace
  funext v
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective v
  ext r s
  have hSlice := congrFun hMarks (finProdFinEquiv (r, s))
  rw [linearMarkedTensor_cornerGramCoefficients
      A VX X cX hcX hcornerX,
    linearMarkedTensor_cornerGramCoefficients
      A VY Y cY hcY hcornerY] at hSlice
  simpa only [horizontalSlice, finProdFinEquiv_divNat,
    finProdFinEquiv_modNat] using congrFun (congrFun hSlice a) b

/-- **The positive relative Gram scalar of Figure 8.**

If the common representative is normal, equality of the two Gram conjugations implies
$X^\dagger X=\omega\,Y^\dagger Y$ for a real number $\omega>0$.

**Scope restriction (conditional corners):** The theorem assumes the two positive corner
similarity equations; it does not construct the representative group or its corners.  See
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, proof of Proposition 4.13, equation `eq3:proof.IV.12` and lines
1909--1921. -/
theorem gram_eq_pos_smul_gram_of_two_grouped_corners
    (M : MPOTensor d D) (hCanonical : IsCPSVCanonicalForm M.toMPSTensor) (hM : IsMPDO M)
    (A : MPSTensor (D * D) n) (hA : IsNormal A)
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
    ∃ ω : ℝ, 0 < ω ∧
      (X : Matrix (Fin n) (Fin n) ℂ)ᴴ * X =
        (ω : ℂ) • ((Y : Matrix (Fin n) (Fin n) ℂ)ᴴ * Y) := by
  have hDress := hCanonical.gramDressing_eq_of_two_grouped_corners
    M hM A VX VY X Y cX cY hcX hcY hcornerX hcornerY
  apply hA.gram_eq_pos_smul_gram_of_gram_conj_eq
      (Matrix.isUnits_det_units X) (Matrix.isUnits_det_units Y)
  intro v
  simpa only [gramDressing] using congrFun hDress v

end MPSTensor.IsCPSVCanonicalForm
