/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalCF

/-!
# Reflected marked chains for vertical sectors

Hermiticity of a matrix-product density operator gives a reflected identity
for a chain with one vertical sector marked.  Taking the adjoint exchanges the
two oriented horizontal bond indices and reverses the unmarked tail.  This is
the indexed content of Figure 7 in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1909--1913.

The reflected tail is retained explicitly.  In particular, the result is not
a same-tail first-site identity and does not assert that an individual
sector-dressed tensor equals its raw reflected adjoint.  The latter statement
is not invariant under the horizontal invertible similarities allowed by
canonical form.  Figure 8 requires a subsequent relative comparison of two
grouped sectors.

## Main definitions

* `horizontalSlice`: the horizontal-bond matrix obtained by fixing the two
  vertical indices of a vertically viewed tensor.
* `reflectedAdjoint`: conjugate transpose together with exchange of the
  oriented horizontal bond indices.
* `markedChainCoefficient`: the closed horizontal chain with one vertical
  tensor marked.

## Main statement

* `IsMPDO.markedChainCoefficient_eq_reflectedAdjoint`: Hermiticity of the
  density operators gives the reflected marked-chain identity of Figure 7.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  proof of Proposition 4.13, lines 1909--1919
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D n : ℕ}

/-- Fixing the two vertical indices of a vertically viewed tensor gives a
matrix on the horizontal bond space.

For a tensor $A^v$ with $v=(a,b)$, this matrix has entries
$(\mathcal R(A)^{rs})_{ab}=(A^{(a,b)})_{rs}$.  It is the marked horizontal
matrix in Figure 7 of arXiv:1606.00608, lines 1909--1913. -/
def horizontalSlice (A : MPSTensor (D * D) n) (r s : Fin n) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun a b => A (finProdFinEquiv (a, b)) r s

/-- Reflect a vertical tensor by exchanging its oriented horizontal bond
indices and taking the conjugate transpose of each vertical matrix:
$(A^\sharp)^v=(A^{v^{\mathrm{op}}})^\dagger$.

This is the marked tensor on the right side of Figure 7 in
arXiv:1606.00608, lines 1909--1913. -/
def reflectedAdjoint (A : MPSTensor (D * D) n) : MPSTensor (D * D) n :=
  fun v => (A (bondPairSwap v))ᴴ

/-- Horizontal slicing converts the reflected vertical tensor into the
conjugate transpose of the oppositely ordered slice. -/
@[simp] theorem horizontalSlice_reflectedAdjoint
    (A : MPSTensor (D * D) n) (r s : Fin n) :
    horizontalSlice (reflectedAdjoint A) r s = (horizontalSlice A s r)ᴴ := by
  ext a b
  simp [horizontalSlice, reflectedAdjoint, Matrix.conjTranspose_apply]

/-- Horizontal slicing commutes with scalar multiplication of every vertical
letter. -/
@[simp] theorem horizontalSlice_smul (c : ℂ) (A : MPSTensor (D * D) n)
    (r s : Fin n) :
    horizontalSlice (fun v => c • A v) r s = c • horizontalSlice A r s := by
  ext a b
  simp [horizontalSlice]

/-- The coefficient of a closed horizontal chain with one vertical tensor
marked and an unmarked MPO tail. -/
noncomputable def markedChainCoefficient (A : MPSTensor (D * D) n)
    (M : MPOTensor d D) (r s : Fin n) (σs τs : List (Fin d)) : ℂ :=
  Matrix.trace (horizontalSlice A r s * evalWord M σs τs)

/-- The reflected marked chain is the complex conjugate of the original
chain with the two open vertical indices exchanged.

The right tail is evaluated in the adjoint tensor on the reversed ket and bra
words.  Thus neither the reversal nor the change from `M` to
`adjointTensor M` is hidden in a same-tail equality.  This is the algebraic
form of the right side of Figure 7 in arXiv:1606.00608, lines 1909--1913. -/
theorem markedChainCoefficient_reflectedAdjoint (A : MPSTensor (D * D) n)
    (M : MPOTensor d D) (r s : Fin n) (σs τs : List (Fin d))
    (hlen : σs.length = τs.length) :
    markedChainCoefficient (reflectedAdjoint A) (adjointTensor M) r s
        σs.reverse τs.reverse =
      star (markedChainCoefficient A M s r τs σs) := by
  rw [markedChainCoefficient, markedChainCoefficient,
    horizontalSlice_reflectedAdjoint,
    evalWord_adjointTensor M σs.reverse τs.reverse (by simp [hlen]),
    List.reverse_reverse, List.reverse_reverse,
    ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
  exact Matrix.trace_mul_comm _ _

/-- Compressing the first physical site by a matrix gives the marked-chain
coefficient of the corresponding vertical corner.

This is the entrywise conversion between a first-site compression and the
left side of Figure 7 in arXiv:1606.00608, lines 1909--1913. -/
theorem coordinateCompression_eq_markedChainCoefficient
    (M : MPOTensor d D) (V : Matrix (Fin d) (Fin n) ℂ)
    (N : ℕ) (r s : Fin n) (σ τ : Fin N → Fin d) :
    (∑ i : Fin d, ∑ j : Fin d,
        star (V i r) *
          mpo M (N + 1) (Fin.cons i σ) (Fin.cons j τ) * V j s) =
      markedChainCoefficient
        (fun v => Vᴴ * verticalTensor M v * V) M r s
        (List.ofFn σ) (List.ofFn τ) := by
  have hslice :
      horizontalSlice (fun v => Vᴴ * verticalTensor M v * V) r s =
        ∑ i : Fin d, ∑ j : Fin d, (star (V i r) * V j s) • M i j := by
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
  rw [markedChainCoefficient, hslice, Finset.sum_mul, Matrix.trace_sum]
  simp_rw [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  simp only [mpo_apply, mpoMatrixEntry, List.ofFn_succ, Fin.cons_zero,
    Fin.cons_succ, evalWord_cons]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The coordinate compression of an MPDO is Hermitian for every tail
length. -/
theorem IsMPDO.coordinateCompression_star
    {M : MPOTensor d D} (hM : IsMPDO M)
    (V : Matrix (Fin d) (Fin n) ℂ) (N : ℕ)
    (r s : Fin n) (σ τ : Fin N → Fin d) :
    (∑ i : Fin d, ∑ j : Fin d,
        star (V i r) *
          mpo M (N + 1) (Fin.cons i σ) (Fin.cons j τ) * V j s) =
      star (∑ i : Fin d, ∑ j : Fin d,
        star (V i s) *
          mpo M (N + 1) (Fin.cons i τ) (Fin.cons j σ) * V j r) := by
  have hstar :
      star (∑ i : Fin d, ∑ j : Fin d,
          star (V i s) *
            mpo M (N + 1) (Fin.cons i τ) (Fin.cons j σ) * V j r) =
        ∑ i : Fin d, ∑ j : Fin d,
          star (V j r) *
            star (mpo M (N + 1) (Fin.cons i τ) (Fin.cons j σ)) * V i s := by
    change (starRingEnd ℂ) (∑ i : Fin d, ∑ j : Fin d,
        star (V i s) *
          mpo M (N + 1) (Fin.cons i τ) (Fin.cons j σ) * V j r) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change star (star (V i s) *
        mpo M (N + 1) (Fin.cons i τ) (Fin.cons j σ) * V j r) = _
    rw [star_mul', star_mul', star_star]
    ring
  rw [hstar, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(hM (N + 1)).isHermitian.apply]

/-- **The reflected marked-chain identity of Figure 7.**

Suppose that the vertical corner selected by `V` is a positive scalar `c`
times a tensor `A`.  Hermiticity of every MPDO density operator then identifies
the marked chain of `A` with the chain of its reflected adjoint, evaluated in
the adjoint MPO tensor on the reversed tail.

The conclusion is valid for every tail length, including the empty tail.  It
does not identify the two marked tensors letterwise: the two sides have
different unmarked tails.  A relative reflected form of Lemma L is still
needed to pass from this identity for two grouped sectors to Figure 8.

Source: arXiv:1606.00608, proof of Proposition 4.13, Figure 7 and lines
1909--1913. -/
theorem IsMPDO.markedChainCoefficient_eq_reflectedAdjoint
    {M : MPOTensor d D} (hM : IsMPDO M)
    (A : MPSTensor (D * D) n) (V : Matrix (Fin d) (Fin n) ℂ)
    (c : ℂ) (hc : (0 : ℂ) < c)
    (hcorner : ∀ v, Vᴴ * verticalTensor M v * V = c • A v)
    (N : ℕ) (r s : Fin n) (σ τ : Fin N → Fin d) :
    markedChainCoefficient A M r s (List.ofFn σ) (List.ofFn τ) =
      markedChainCoefficient (reflectedAdjoint A) (MPOTensor.adjointTensor M) r s
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
          (fun v => Vᴴ * verticalTensor M v * V) M r s
          σs τs = c * markedChainCoefficient A M r s σs τs := by
    intro r s σs τs
    rw [show (fun v => Vᴴ * verticalTensor M v * V) = fun v => c • A v by
      funext v
      exact hcorner v]
    simp [markedChainCoefficient]
  have hscaleSwap :
      markedChainCoefficient
          (fun v => Vᴴ * verticalTensor M v * V) M s r
          (List.ofFn τ) (List.ofFn σ) =
        c * markedChainCoefficient A M s r (List.ofFn τ) (List.ofFn σ) := by
    exact hscale s r (List.ofFn τ) (List.ofFn σ)
  have hcoord := hM.coordinateCompression_star V N r s σ τ
  rw [coordinateCompression_eq_markedChainCoefficient,
    coordinateCompression_eq_markedChainCoefficient,
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
  rw [MPOTensor.markedChainCoefficient_reflectedAdjoint A M r s
    (List.ofFn σ) (List.ofFn τ) (by simp)]
  exact mul_left_cancel₀ hc0 hcoord

end MPOTensor
