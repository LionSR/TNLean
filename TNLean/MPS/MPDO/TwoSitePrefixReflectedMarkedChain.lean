/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.FigureEightPairwise
import TNLean.MPS.MPDO.PhysicalBlocking

/-!
# Reflected marked chains from a two-site prefix

A joint compression of the first two physical sites of an MPDO gives a
vertical corner of the two-site blocking, followed by an unblocked tail of
the original MPO tensor. Hermiticity therefore relates this mixed chain to
the reflected adjoint of the corner with the adjoint original tensor as tail.

Conjugating the open indices by the adjoint of an invertible corner gauge
then gives the corresponding Gram-dressed identity. The result differs from
applying the ordinary reflected-chain theorem to the blocked tensor: its tail
consists of single original sites, rather than two-site blocks.

## Main result

* `IsMPDO.markedChainCoefficient_blockTwoPrefix_gramDressing_eq_reflectedAdjoint`:
  a gauge-dressed two-site prefix has the reflected marked chain with an
  unblocked original-tensor tail.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, Figures 7--8 and lines 1909--1919, together with the
  two-site blocking in Appendix C.4, lines 1951--1956
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D n : ℕ}

/-- Jointly compressing the first two physical sites gives the marked-chain
coefficient of the corresponding corner of `blockTwo M`, followed by an
unblocked tail of `M`.

Source: arXiv:1606.00608, Proposition 4.13, Figure 7 and lines 1909--1913,
together with Appendix C.4, lines 1951--1956. -/
private theorem blockTwoPrefixCoordinateCompression_eq_markedChainCoefficient
    (M : MPOTensor d D) (V : Matrix (Fin (d * d)) (Fin n) ℂ)
    (N : ℕ) (r s : Fin n) (σ τ : Fin N → Fin d) :
    (∑ i : Fin (d * d), ∑ j : Fin (d * d),
        star (V i r) *
          mpo M (N + 2)
            (Fin.cons (finProdFinEquiv.symm i).1
              (Fin.cons (finProdFinEquiv.symm i).2 σ))
            (Fin.cons (finProdFinEquiv.symm j).1
              (Fin.cons (finProdFinEquiv.symm j).2 τ)) *
          V j s) =
      markedChainCoefficient
        (fun v ↦ Vᴴ * verticalTensor (blockTwo M) v * V) M r s
        (List.ofFn σ) (List.ofFn τ) := by
  have hslice :
      horizontalSlice
          (fun v ↦ Vᴴ * verticalTensor (blockTwo M) v * V) r s =
        ∑ i : Fin (d * d), ∑ j : Fin (d * d),
          (star (V i r) * V j s) • blockTwo M i j := by
    exact horizontalSlice_twoSidedCompression (blockTwo M) V V r s
  rw [markedChainCoefficient, hslice, Finset.sum_mul, Matrix.trace_sum]
  simp_rw [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [mpo_apply, mpoMatrixEntry, List.ofFn_succ, Fin.cons_zero,
    Fin.cons_succ, evalWord_cons, blockTwo]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_assoc]
  ring

/-- Hermiticity of every positive-length MPO makes the joint two-site-prefix
compression Hermitian for every remaining tail length.

Source: arXiv:1606.00608, Proposition 4.13, Figure 7 and lines 1909--1913,
together with Appendix C.4, lines 1951--1956. -/
private theorem IsMPDO.blockTwoPrefixCoordinateCompression_star
    {M : MPOTensor d D} (hM : IsMPDO M)
    (V : Matrix (Fin (d * d)) (Fin n) ℂ) (N : ℕ)
    (r s : Fin n) (σ τ : Fin N → Fin d) :
    (∑ i : Fin (d * d), ∑ j : Fin (d * d),
        star (V i r) *
          mpo M (N + 2)
            (Fin.cons (finProdFinEquiv.symm i).1
              (Fin.cons (finProdFinEquiv.symm i).2 σ))
            (Fin.cons (finProdFinEquiv.symm j).1
              (Fin.cons (finProdFinEquiv.symm j).2 τ)) *
          V j s) =
      star (∑ i : Fin (d * d), ∑ j : Fin (d * d),
        star (V i s) *
          mpo M (N + 2)
            (Fin.cons (finProdFinEquiv.symm i).1
              (Fin.cons (finProdFinEquiv.symm i).2 τ))
            (Fin.cons (finProdFinEquiv.symm j).1
              (Fin.cons (finProdFinEquiv.symm j).2 σ)) *
          V j r) := by
  have hstar :
      star (∑ i : Fin (d * d), ∑ j : Fin (d * d),
          star (V i s) *
            mpo M (N + 2)
              (Fin.cons (finProdFinEquiv.symm i).1
                (Fin.cons (finProdFinEquiv.symm i).2 τ))
              (Fin.cons (finProdFinEquiv.symm j).1
                (Fin.cons (finProdFinEquiv.symm j).2 σ)) *
            V j r) =
        ∑ i : Fin (d * d), ∑ j : Fin (d * d),
          star (V j r) *
            star (mpo M (N + 2)
              (Fin.cons (finProdFinEquiv.symm i).1
                (Fin.cons (finProdFinEquiv.symm i).2 τ))
              (Fin.cons (finProdFinEquiv.symm j).1
                (Fin.cons (finProdFinEquiv.symm j).2 σ))) *
            V i s := by
    change (starRingEnd ℂ) (∑ i : Fin (d * d), ∑ j : Fin (d * d),
        star (V i s) *
          mpo M (N + 2)
            (Fin.cons (finProdFinEquiv.symm i).1
              (Fin.cons (finProdFinEquiv.symm i).2 τ))
            (Fin.cons (finProdFinEquiv.symm j).1
              (Fin.cons (finProdFinEquiv.symm j).2 σ)) *
          V j r) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change star (star (V i s) *
        mpo M (N + 2)
          (Fin.cons (finProdFinEquiv.symm i).1
            (Fin.cons (finProdFinEquiv.symm i).2 τ))
          (Fin.cons (finProdFinEquiv.symm j).1
            (Fin.cons (finProdFinEquiv.symm j).2 σ)) *
        V j r) = _
    rw [star_mul', star_mul', star_star]
    ring
  rw [hstar, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(hM (N + 2) (by omega)).isHermitian.apply]

/-- A two-site prefix corner has the reflected-adjoint marked chain with an
unblocked tail of the original tensor.

Source: arXiv:1606.00608, Proposition 4.13, Figure 7 and lines 1909--1913,
together with Appendix C.4, lines 1951--1956. -/
private theorem IsMPDO.markedChainCoefficient_blockTwoPrefix_eq_reflectedAdjoint
    {M : MPOTensor d D} (hM : IsMPDO M)
    (A : MPSTensor (D * D) n)
    (V : Matrix (Fin (d * d)) (Fin n) ℂ)
    (c : ℂ) (hc : (0 : ℂ) < c)
    (hcorner : ∀ v,
      Vᴴ * verticalTensor (MPOTensor.blockTwo M) v * V = c • A v)
    (N : ℕ) (r s : Fin n) (σ τ : Fin N → Fin d) :
    markedChainCoefficient A M r s (List.ofFn σ) (List.ofFn τ) =
      markedChainCoefficient (reflectedAdjoint A)
        (MPOTensor.adjointTensor M) r s
        (List.ofFn σ).reverse (List.ofFn τ).reverse := by
  have hcstar : star c = c := by
    obtain ⟨_, hcim⟩ := Complex.pos_iff.mp hc
    apply Complex.ext
    · simp
    · change -c.im = c.im
      calc
        -c.im = -0 := congrArg Neg.neg hcim.symm
        _ = 0 := neg_zero
        _ = c.im := hcim
  have hscale : ∀ (r s : Fin n) (σs τs : List (Fin d)),
      markedChainCoefficient
          (fun v ↦ Vᴴ * verticalTensor (MPOTensor.blockTwo M) v * V)
          M r s σs τs =
        c * markedChainCoefficient A M r s σs τs := by
    intro r s σs τs
    rw [show (fun v ↦ Vᴴ * verticalTensor (MPOTensor.blockTwo M) v * V) =
        fun v ↦ c • A v by
      funext v
      exact hcorner v]
    simp [markedChainCoefficient]
  have hscaleSwap :
      markedChainCoefficient
          (fun v ↦ Vᴴ * verticalTensor (MPOTensor.blockTwo M) v * V)
          M s r (List.ofFn τ) (List.ofFn σ) =
        c * markedChainCoefficient A M s r (List.ofFn τ) (List.ofFn σ) := by
    exact hscale s r (List.ofFn τ) (List.ofFn σ)
  have hcoord := hM.blockTwoPrefixCoordinateCompression_star V N r s σ τ
  rw [blockTwoPrefixCoordinateCompression_eq_markedChainCoefficient,
    blockTwoPrefixCoordinateCompression_eq_markedChainCoefficient,
    hscale r s (List.ofFn σ) (List.ofFn τ), hscaleSwap] at hcoord
  change c * markedChainCoefficient A M r s (List.ofFn σ) (List.ofFn τ) =
    (starRingEnd ℂ)
      (c * markedChainCoefficient A M s r (List.ofFn τ) (List.ofFn σ)) at hcoord
  rw [map_mul] at hcoord
  change c * markedChainCoefficient A M r s (List.ofFn σ) (List.ofFn τ) =
    star c * star (markedChainCoefficient A M s r
      (List.ofFn τ) (List.ofFn σ)) at hcoord
  rw [hcstar] at hcoord
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [markedChainCoefficient_reflectedAdjoint A M r s
    (List.ofFn σ) (List.ofFn τ) (by simp)]
  exact mul_left_cancel₀ hc0 hcoord

/-- The marked chain of a Gram-dressed two-site prefix corner has a reflected
form with an unblocked tail, independent of the corner gauge.

The first two physical sites are compressed jointly through a corner of
`blockTwo M`, while every remaining site is evaluated in `M`. Hermiticity of
the length-`N + 2` density operator gives the reflected chain. Conjugating the
two open indices by the adjoint of `X` produces `gramDressing X A` on the
original side and cancels the gauge on the reflected side.

**Local fix (mixed one-site/two-site prefix):** Appendix C.4 invokes
Proposition 4.13 after choosing one-site and two-site vertical forms.  Keeping
the two-site prefix but the one-site tail supplies the omitted common-space
comparison.  This is documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Proposition 4.13, Figures 7--8 and lines
1909--1919, together with Appendix C.4, lines 1951--1956 and 2048--2057. -/
theorem IsMPDO.markedChainCoefficient_blockTwoPrefix_gramDressing_eq_reflectedAdjoint
    {M : MPOTensor d D} (hM : IsMPDO M)
    (A : MPSTensor (D * D) n)
    (V : Matrix (Fin (d * d)) (Fin n) ℂ)
    (X : GL (Fin n) ℂ) (c : ℂ) (hc : (0 : ℂ) < c)
    (hcorner : ∀ v,
      Vᴴ * verticalTensor (MPOTensor.blockTwo M) v * V =
        c • ((X : Matrix (Fin n) (Fin n) ℂ) * A v *
          (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))
    (N : ℕ) (r s : Fin n) (σ τ : Fin N → Fin d) :
    markedChainCoefficient (gramDressing X A) M r s
        (List.ofFn σ) (List.ofFn τ) =
      markedChainCoefficient (reflectedAdjoint A)
        (MPOTensor.adjointTensor M) r s
        (List.ofFn σ).reverse (List.ofFn τ).reverse := by
  let Xm : Matrix (Fin n) (Fin n) ℂ := X
  let Xi : Matrix (Fin n) (Fin n) ℂ :=
    (((X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  let B : MPSTensor (D * D) n := bondMul Xm A Xi
  have hFigure : ∀ p q : Fin n,
      markedChainCoefficient B M p q (List.ofFn σ) (List.ofFn τ) =
        markedChainCoefficient (reflectedAdjoint B)
          (MPOTensor.adjointTensor M) p q
          (List.ofFn σ).reverse (List.ofFn τ).reverse := by
    intro p q
    apply hM.markedChainCoefficient_blockTwoPrefix_eq_reflectedAdjoint
      B V c hc
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

end MPOTensor
