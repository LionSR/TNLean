/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SourceVIsometry
import TNLean.MPS.MPU.SuppliedFixedWitnesses

/-!
# The complete network for the paper source gate v

This file contracts the same-tensor network of arXiv:1703.09188, equation
`vUnitary` (lines 577--588), for the paper gate $v=X_1\mathbin{-}X_2$ of one
tensor $\mathcal U$.  Every cut, rank, factor, and the gate refer to that tensor.

The dressed Gram matrix $(Y_1\otimes Y_2)^\dagger v^\dagger v(Y_1\otimes Y_2)$
is first identified, entry by entry, with the product of two double-layer
letters, using only the two source-cut factorizations `XY`.  The undressed
Gram matrix $(Y_1\otimes Y_2)^\dagger(Y_1\otimes Y_2)$ is identified with the
same two letters separated by the rank-one insertion $|\rho^{\mathsf T})(\Phi|$,
using the two normalizations `X1X2b`.  Hence the dressed Gram equation holds
exactly when the two-letter identity `simple2` holds with that insertion.
Cancelling $Z_1\otimes Z_2$ by `YZ=1` gives $v^\dagger v=\Id$.

**Local fix (source-weight orientation):** the weighted normalization
$X_1^\dagger(\Id_d\otimes\rho)X_1=\Id$ pairs the conjugated leg of $X_1$ with the
row index of $\rho$, whereas the transfer fixed point inserted between two
double-layer letters pairs the conjugated leg with the column index of $\rho$
in the column-stacking coordinates of `Matrix.vec`.  The source works with a
diagonal $\rho$, where both readings agree.  The formal statements keep the
printed weight and insert the column-stacking vector of $\rho^{\mathsf T}$; the
source gate for a tensor whose transfer fixed point is $\rho$ is therefore the
gate built from the weight $\rho^{\mathsf T}$.  Documented in
`docs/paper-gaps/mpu_source_cut_orientation.tex`.

## Main results

* `MPOTensor.sourceYTensor_conjTranspose_sourceV_gram_apply`: the dressed Gram entry is
  the ordinary two-letter double-layer entry.
* `MPOTensor.sourceYTensor_gram_apply_eq_doubleLayerTensor_rankOne_mul_apply`: the
  undressed Gram entry is the two-letter entry with $|\rho^{\mathsf T})(\Phi|$ inserted.
* `MPOTensor.sourceVDressedGram_iff_simple2_transpose_fixed_pair`: the dressed Gram
  equation is equivalent to `simple2` with the insertion $|\rho^{\mathsf T})(\Phi|$.
* `MPOTensor.IsMPUSimple.sourceV_transpose_isIsometry`,
  `MPOTensor.IsMPUSimple.rightRank_mul_leftRank_le`: the forward direction of
  Theorem `ThmFund1`, $1\to2$: a simple tensor with stabilized fixed pair has
  $v^\dagger v=\Id$ and $r\ell\le d^2$.
* `MPOTensor.IsMPU.isMPUSimple_of_sourceV_isIsometry`: the direction $4\to1$ of
  Theorem `ThmFund1` from $v^\dagger v=\Id$.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188], equations
  `simple2`, `X1X2b`, `XY`, `YZ=1`, `uuvv`, and `vUnitary`, and the proof of
  Theorem `ThmFund1` (lines 363--374, 487--543, and 563--600).
-/

open scoped Matrix BigOperators Kronecker ComplexOrder
open Matrix

namespace MPOTensor

variable {d D : ℕ} (U : MPOTensor d D)

private lemma sum_comm_pair {A B C P R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [AddCommMonoid R]
    (f : A → B → C → P → R) :
    (∑ a, ∑ b, ∑ c, ∑ p, f a b c p) = ∑ c, ∑ p, ∑ a, ∑ b, f a b c p := by
  let e : (((A × B) × C) × P) ≃ (((C × P) × A) × B) :=
    { toFun := fun x ↦ (((x.1.2, x.2), x.1.1.1), x.1.1.2)
      invFun := fun x ↦ (((x.1.2, x.2), x.1.1.1), x.1.1.2)
      left_inv := by rintro ⟨⟨⟨a, b⟩, c⟩, p⟩; rfl
      right_inv := by rintro ⟨⟨⟨c, p⟩, a⟩, b⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1.1 x.1.1.2 x.1.2 x.2)
    (fun x ↦ f x.1.2 x.2 x.1.1.1 x.1.1.2)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

private lemma sum_perm_five {A B C P Q R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype Q] [AddCommMonoid R]
    (f : A → B → C → P → Q → R) :
    (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, f a b c p q) =
      ∑ p, ∑ b, ∑ a, ∑ c, ∑ q, f a b c p q := by
  let e : ((((A × B) × C) × P) × Q) ≃ ((((P × B) × A) × C) × Q) :=
    { toFun := fun x ↦ ((((x.1.2, x.1.1.1.2), x.1.1.1.1), x.1.1.2), x.2)
      invFun := fun x ↦ ((((x.1.1.2, x.1.1.1.2), x.1.2), x.1.1.1.1), x.2)
      left_inv := by rintro ⟨⟨⟨⟨a, b⟩, c⟩, p⟩, q⟩; rfl
      right_inv := by rintro ⟨⟨⟨⟨p, b⟩, a⟩, c⟩, q⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun x ↦ f x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2)
    (fun x ↦ f x.1.1.2 x.1.1.1.2 x.1.2 x.1.1.1.1 x.2)
    (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using h

/-- The dressed Gram entry of the paper gate $v=X_1\mathbin{-}X_2$ is the
entry of two ordinary double-layer letters.  The physical pair `p` is starred
and `q` is unstarred; the doubled-bond row and column are `(a.1, b.1)` and
`(a.2, b.2)`.

Only the two source-cut factorizations are used: after regrouping
$Y^\dagger(v^\dagger v)Y=(vY)^\dagger(vY)$, each factor $vY$ closes to two
tensor coefficients by `XY`.  This is the first equality in arXiv:1703.09188,
equation `vUnitary` (lines 577--588), before `simple2` is applied. -/
theorem sourceYTensor_conjTranspose_sourceV_gram_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (p q : Fin d × Fin d) (a b : Fin D × Fin D) :
    ((sourceYTensor U ρ hρ)ᴴ * ((sourceV U ρ hρ)ᴴ * sourceV U ρ hρ) *
        sourceYTensor U ρ hρ) ((a.1, p.1), (p.2, a.2)) ((b.1, q.1), (q.2, b.2)) =
      (doubleLayerTensor U p.1 q.1 * doubleLayerTensor U p.2 q.2)
        (finProdFinEquiv (a.1, b.1)) (finProdFinEquiv (a.2, b.2)) := by
  classical
  have hY : (sourceYTensor U ρ hρ)ᴴ * ((sourceV U ρ hρ)ᴴ * sourceV U ρ hρ) *
      sourceYTensor U ρ hρ =
      (sourceV U ρ hρ * sourceYTensor U ρ hρ)ᴴ *
        (sourceV U ρ hρ * sourceYTensor U ρ hρ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hY, Matrix.mul_apply, doubleLayerTensor_mul_apply_four_u]
  simp only [Matrix.conjTranspose_apply, sourceV_mul_sourceYTensor_apply,
    Fintype.sum_prod_type, star_sum, star_mul', Finset.sum_mul_sum]
  rw [sum_comm_pair]
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦
    Finset.sum_congr rfl fun j₁ _ ↦ Finset.sum_congr rfl fun j₂ _ ↦ ?_
  ring

/-- The undressed Gram entry of $Y_1\otimes Y_2$ is the entry of two
double-layer letters separated by the rank-one insertion
$|\rho^{\mathsf T})(\Phi|$, where $|\rho^{\mathsf T})$ is the column-stacking
vector of $\rho^{\mathsf T}$ and $(\Phi|$ is that of the identity.  The physical
pair `p` is starred and `q` is unstarred.

This is the last equality in arXiv:1703.09188, equation `vUnitary`
(lines 577--588), obtained from the two normalizations `X1X2b`
(lines 487--526).  The transpose records the source-weight orientation
described in the module docstring. -/
theorem sourceYTensor_gram_apply_eq_doubleLayerTensor_rankOne_mul_apply
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (p q : Fin d × Fin d) (a b : Fin D × Fin D) :
    ((sourceYTensor U ρ hρ)ᴴ * sourceYTensor U ρ hρ)
        ((a.1, p.1), (p.2, a.2)) ((b.1, q.1), (q.2, b.2)) =
      (doubleLayerTensor U p.1 q.1 *
        Matrix.vecMulVec (fun x ↦ ρᵀ.vec (finProdFinEquiv.symm x))
          (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)) *
        doubleLayerTensor U p.2 q.2)
        (finProdFinEquiv (a.1, b.1)) (finProdFinEquiv (a.2, b.2)) := by
  classical
  have h := doubleLayerTensor_rankOne_mul_apply_four_u U ρᵀ p q a b
  simp only [Matrix.transpose_apply] at h
  rw [h, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [sourceYTensor_gram_eq_four_u_weighted]
  conv_rhs => rw [sum_perm_five]
  refine Finset.sum_congr rfl fun i₁ _ ↦ Finset.sum_congr rfl fun β' _ ↦
    Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun δ _ ↦
    Finset.sum_congr rfl fun i₂ _ ↦ ?_
  ring

/-- The complete same-tensor source-$v$ network: the dressed Gram equation
$(Y_1\otimes Y_2)^\dagger v^\dagger v(Y_1\otimes Y_2)
=(Y_1\otimes Y_2)^\dagger(Y_1\otimes Y_2)$ holds if and only if the two-letter
identity `simple2` holds with the insertion $|\rho^{\mathsf T})(\Phi|$.

Both directions compare the two entry identities above; the network is kept
combined, and neither source cut is contracted separately.  This is
arXiv:1703.09188, equation `vUnitary` (lines 577--588), read in both directions
as in the proof of Theorem `ThmFund1`, $1\to2$ and $4\to1$ (lines 577--600). -/
theorem sourceVDressedGram_iff_simple2_transpose_fixed_pair
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SourceVDressedGram U ρ hρ ↔
      ∀ i j k l : Fin d,
        doubleLayerTensor U i j * doubleLayerTensor U k l =
          doubleLayerTensor U i j *
            Matrix.vecMulVec (fun x ↦ ρᵀ.vec (finProdFinEquiv.symm x))
              (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec
                (finProdFinEquiv.symm x)) *
            doubleLayerTensor U k l := by
  constructor
  · intro h i j k l
    have h' : (sourceYTensor U ρ hρ)ᴴ * ((sourceV U ρ hρ)ᴴ * sourceV U ρ hρ) *
        sourceYTensor U ρ hρ = (sourceYTensor U ρ hρ)ᴴ * sourceYTensor U ρ hρ := h
    ext x y
    obtain ⟨⟨a₁, b₁⟩, rfl⟩ := finProdFinEquiv.surjective x
    obtain ⟨⟨a₂, b₂⟩, rfl⟩ := finProdFinEquiv.surjective y
    have hA := sourceYTensor_conjTranspose_sourceV_gram_apply U ρ hρ
      (i, k) (j, l) (a₁, a₂) (b₁, b₂)
    have hB := sourceYTensor_gram_apply_eq_doubleLayerTensor_rankOne_mul_apply U ρ hρ
      (i, k) (j, l) (a₁, a₂) (b₁, b₂)
    dsimp only at hA hB
    rw [← hA, h', hB]
  · intro h
    unfold SourceVDressedGram
    ext ⟨⟨a₁, p₁⟩, ⟨p₂, a₂⟩⟩ ⟨⟨b₁, q₁⟩, ⟨q₂, b₂⟩⟩
    have hA := sourceYTensor_conjTranspose_sourceV_gram_apply U ρ hρ
      (p₁, p₂) (q₁, q₂) (a₁, a₂) (b₁, b₂)
    have hB := sourceYTensor_gram_apply_eq_doubleLayerTensor_rankOne_mul_apply U ρ hρ
      (p₁, p₂) (q₁, q₂) (a₁, a₂) (b₁, b₂)
    dsimp only at hA hB
    rw [hA, hB, h]

/-- Theorem `ThmFund1`, $1\to2$: a simple tensor whose normalized double-layer
diagonal stabilizes to $|\rho)(\Phi|$ has $v^\dagger v=\Id$ for the paper gate
$v$ built from the weight $\rho^{\mathsf T}$.

The supplied-projector theorem aligns `simple2` with the stabilized pair,
the complete network gives the dressed Gram equation, and $Z_1\otimes Z_2$
cancels the dressing by `YZ=1`.  The transposed weight is the source-weight
orientation described in the module docstring.

Source: arXiv:1703.09188, proof of Theorem `ThmFund1`, $1\to2$
(lines 577--588). -/
theorem IsMPUSimple.sourceV_transpose_isIsometry [NeZero d]
    {U : MPOTensor d D} (hU : IsMPUSimple U)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (J : ℕ) (hJ : 0 < J)
    (hpower : normalizedDiagonal (doubleLayerTensor U) ^ J =
      Matrix.vecMulVec (fun x ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))) :
    (sourceV U ρᵀ hρ.transpose).IsIsometry := by
  rw [← sourceVDressedGram_iff_isIsometry,
    sourceVDressedGram_iff_simple2_transpose_fixed_pair]
  simpa only [Matrix.transpose_transpose] using
    hU.simple2_of_normalizedDiagonal_pow_eq_vecMulVec _ _ J hJ hpower

/-- Theorem `ThmFund1`, $1\to2$, rank consequence: a simple tensor with
stabilized fixed pair satisfies $r\ell\le d^2$, since the isometry $v$ maps
$\C^r\otimes\C^\ell$ into $\C^d\otimes\C^d$.

Source: arXiv:1703.09188, proof of Theorem `ThmFund1`, $1\to2$
(lines 577--588). -/
theorem IsMPUSimple.rightRank_mul_leftRank_le [NeZero d]
    {U : MPOTensor d D} (hU : IsMPUSimple U)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) (J : ℕ) (hJ : 0 < J)
    (hpower : normalizedDiagonal (doubleLayerTensor U) ^ J =
      Matrix.vecMulVec (fun x ↦ ρ.vec (finProdFinEquiv.symm x))
        (fun x ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))) :
    r[U] * ℓ[U] ≤ d * d := by
  have h := Matrix.IsIsometry.card_le _ (hU.sourceV_transpose_isIsometry ρ hρ J hJ hpower)
  simpa only [Fintype.card_prod, Fintype.card_fin] using h

/-- Theorem `ThmFund1`, $4\to1$: if the paper gate $v$ of an MPU tensor
satisfies $v^\dagger v=\Id$, then the tensor is simple, with witnesses
$|\rho^{\mathsf T})$ and $(\Phi|$.

The dressed Gram equation follows from $v^\dagger v=\Id$, the complete network
turns it into `simple2` with the insertion $|\rho^{\mathsf T})(\Phi|$, and
`simple1` with the same witnesses follows from unitarity, as in Corollary
`cor:simple1`.

Source: arXiv:1703.09188, proof of Theorem `ThmFund1`, $4\to1$
(lines 596--600). -/
theorem IsMPU.isMPUSimple_of_sourceV_isIsometry
    {U : MPOTensor d D} (hU : IsMPU U)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hv : (sourceV U ρ hρ).IsIsometry) : IsMPUSimple U := by
  have h₂ := (sourceVDressedGram_iff_simple2_transpose_fixed_pair U ρ hρ).mp
    ((sourceVDressedGram_iff_isIsometry U ρ hρ).mpr hv)
  exact ⟨_, _, hU.simple1_of_simple2_supplied _ _ h₂, h₂⟩

end MPOTensor
