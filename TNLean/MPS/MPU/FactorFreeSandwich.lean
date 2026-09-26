/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.DoubleLayerContraction
import TNLean.MPS.MPU.VirtualSandwich

/-!
# Factor-free virtual sandwiching

This module expresses the final contraction in the proof of
[Cirac--Perez-Garcia--Schuch--Verstraete 2017, arXiv:1703.09188],
Proposition IV.5, without choosing factors of the doubled-virtual matrix.

For a doubled-virtual matrix `E`, the contraction is
$$
  C(W,E)^{ij}_{ab} = \sum_{c,e} E_{(b,e),(c,a)} W^{ij}_{ce}.
$$
The pairs are encoded by `finProdFinEquiv`. When `E` is rank one, Mathlib's
column-stacking convention for `Matrix.vec` identifies this contraction with
an ordinary virtual sandwich, with no transpose, adjoint, or scalar factor.

For a transfer map $X\mapsto\operatorname{tr}(LX)R$, the left vector in its
rank-one matrix is the vectorization of $L^{\mathsf T}$. Reversing the column
pair before contraction therefore gives $L W^{ij}R$. This expression is
continuous in $W$ without any continuity assumption on the chosen factors.

The results do not deduce positivity from arbitrary factors, construct reduced
representatives, or assert rank constancy.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Contract an MPO tensor with a matrix on its doubled virtual indices:
$C(W,E)^{ij}_{ab}=\sum_{c,e}E_{(b,e),(c,a)}W^{ij}_{ce}$.

Source: arXiv:1703.09188, Proposition IV.5, Figure `IV_index4.png`, lines
807--812. -/
noncomputable def doubledVirtualContraction (W : MPOTensor d D)
    (E : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) : MPOTensor d D :=
  fun i j a b ↦ ∑ c : Fin D, ∑ e : Fin D,
    E (finProdFinEquiv (b, e)) (finProdFinEquiv (c, a)) * W i j c e

/-- Entrywise expansion of the doubled-virtual contraction. -/
@[simp] theorem doubledVirtualContraction_apply (W : MPOTensor d D)
    (E : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) (i j : Fin d) (a b : Fin D) :
    doubledVirtualContraction W E i j a b =
      ∑ c : Fin D, ∑ e : Fin D,
        E (finProdFinEquiv (b, e)) (finProdFinEquiv (c, a)) * W i j c e :=
  rfl

/-- A rank-one doubled-virtual contraction is an ordinary virtual sandwich.
The left matrix unvectorizes `Phi`, while the right matrix unvectorizes `rho`.

Source: arXiv:1703.09188, Proposition IV.5, Figure `IV_index4.png`, lines
807--812. -/
theorem doubledVirtualContraction_vecMulVec (W : MPOTensor d D)
    (rho Phi : Fin (D * D) → ℂ) :
    doubledVirtualContraction W (Matrix.vecMulVec rho Phi) =
      virtualSandwich
        (fun a c ↦ Phi (finProdFinEquiv (c, a))) W
        (fun e b ↦ rho (finProdFinEquiv (b, e))) := by
  classical
  ext i j a b
  simp only [doubledVirtualContraction_apply, Matrix.vecMulVec_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  change (∑ c : Fin D,
      rho (finProdFinEquiv (b, e)) * Phi (finProdFinEquiv (c, a)) * W i j c e) =
    (∑ c : Fin D, Phi (finProdFinEquiv (c, a)) * W i j c e) *
      rho (finProdFinEquiv (b, e))
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- For matrices `L` and `R`, column vectorization of the rank-one doubled
matrix gives exactly the sandwich $L W^{ij}R$.

Source: arXiv:1703.09188, Proposition IV.5, Figure `IV_index4.png`, lines
807--812. -/
theorem doubledVirtualContraction_vecMulVec_vec (W : MPOTensor d D)
    (L R : Matrix (Fin D) (Fin D) ℂ) :
    doubledVirtualContraction W
        (Matrix.vecMulVec
          (fun k ↦ R.vec (finProdFinEquiv.symm k))
          (fun k ↦ L.vec (finProdFinEquiv.symm k))) =
      virtualSandwich L W R := by
  simpa using doubledVirtualContraction_vecMulVec W
    (fun k ↦ R.vec (finProdFinEquiv.symm k))
    (fun k ↦ L.vec (finProdFinEquiv.symm k))

/-- The doubled-virtual contraction is jointly continuous in the MPO tensor and
contracting matrix.

Source: arXiv:1703.09188, Proposition IV.5, Figure `IV_index4.png`, lines
807--812. -/
theorem continuous_doubledVirtualContraction {X : Type*} [TopologicalSpace X]
    {W : X → MPOTensor d D}
    {E : X → Matrix (Fin (D * D)) (Fin (D * D)) ℂ}
    (hW : Continuous W) (hE : Continuous E) :
    Continuous (fun x ↦ doubledVirtualContraction (W x) (E x)) := by
  unfold doubledVirtualContraction
  fun_prop

/-- The physical-adjoint double layer depends continuously on the MPO tensor. -/
theorem continuous_doubleLayerTensor :
    Continuous (doubleLayerTensor : MPOTensor d D → MPOTensor d (D * D)) := by
  refine continuous_pi fun i ↦ continuous_pi fun j ↦
    continuous_pi fun p ↦ continuous_pi fun q ↦ ?_
  rcases finProdFinEquiv.surjective p with ⟨⟨p₁, p₂⟩, rfl⟩
  rcases finProdFinEquiv.surjective q with ⟨⟨q₁, q₂⟩, rfl⟩
  simp only [doubleLayerTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.kronecker_apply, physicalAdjointTensor_apply, Equiv.symm_apply_apply,
    RCLike.star_def]
  fun_prop

/-- The normalized physical diagonal depends continuously on the MPO tensor. -/
theorem continuous_normalizedDiagonal :
    Continuous (normalizedDiagonal : MPOTensor d D → Matrix (Fin D) (Fin D) ℂ) := by
  unfold normalizedDiagonal contractPhysical
  fun_prop

/-- The normalized diagonal of the physical-adjoint double layer depends
continuously on the MPO tensor.

Source: arXiv:1703.09188, Proposition IV.5, Figure `IV_index4.png`, lines
807--812. -/
theorem continuous_normalizedDiagonal_doubleLayerTensor :
    Continuous (fun W : MPOTensor d D ↦ normalizedDiagonal (doubleLayerTensor W)) :=
  continuous_normalizedDiagonal.comp continuous_doubleLayerTensor

/-- Contract the normalized double-layer diagonal into the original MPO tensor,
reversing its column pair to represent the trace pairing. This gives
$L W^{ij}R$ whenever the normalized transfer map is $X\mapsto\operatorname{tr}(LX)R$.

Source: arXiv:1703.09188, Proposition IV.5, Figure `IV_index4.png`, lines
807--812. -/
noncomputable def factorFreeSandwich (W : MPOTensor d D) : MPOTensor d D :=
  doubledVirtualContraction W
    ((normalizedDiagonal (doubleLayerTensor W)).submatrix id
      (fun k ↦ finProdFinEquiv (Prod.swap (finProdFinEquiv.symm k))))

/-- Entrywise expansion of the factor-free sandwich. -/
@[simp] theorem factorFreeSandwich_apply (W : MPOTensor d D)
    (i j : Fin d) (a b : Fin D) :
    factorFreeSandwich W i j a b =
      ∑ c : Fin D, ∑ e : Fin D,
        normalizedDiagonal (doubleLayerTensor W)
          (finProdFinEquiv (b, e)) (finProdFinEquiv (a, c)) * W i j c e := by
  simp [factorFreeSandwich, doubledVirtualContraction]

/-- The factor-free contraction equals $L W^{ij}R$ when the normalized
transfer map has the trace-factor form $X\mapsto\operatorname{tr}(LX)R$.
No positivity or normalization assumption on the factors is needed.

Source: arXiv:1703.09188, Proposition IV.5, lines 807--812. -/
theorem factorFreeSandwich_eq_of_trace_pair [NeZero d]
    (W : MPOTensor d D) (L R : Matrix (Fin D) (Fin D) ℂ)
    (hmap : ∀ X, Kraus.transferMap W.normalizedFlattening X =
      Matrix.trace (L * X) • R) :
    factorFreeSandwich W = virtualSandwich L W R := by
  unfold factorFreeSandwich
  rw [normalizedDiagonal_doubleLayerTensor]
  convert doubledVirtualContraction_vecMulVec_vec W L R using 2
  ext p q
  simp [Matrix.submatrix_apply, transferMatrix, hmap, Matrix.trace_mul_single,
    Matrix.vecMulVec_apply, Matrix.vec, mul_comm]

/-- The factor-free sandwich is continuous in the entries of the MPO tensor.

Source: arXiv:1703.09188, Proposition IV.5, Figure `IV_index4.png`, lines
807--812. -/
theorem continuous_factorFreeSandwich :
    Continuous (factorFreeSandwich : MPOTensor d D → MPOTensor d D) := by
  apply continuous_doubledVirtualContraction continuous_id
  exact continuous_normalizedDiagonal_doubleLayerTensor.matrix_submatrix _ _

/-- For a continuous tensor family whose normalized transfer maps have the
pointwise form $X\mapsto\operatorname{tr}(L(x)X)R(x)$, the sandwiched tensors
$L(x)W^{ij}(x)R(x)$ are continuous. The factors need not be chosen continuously.

Source: arXiv:1703.09188, Proposition IV.5, lines 807--812. -/
theorem continuous_virtualSandwich_of_trace_pair {X : Type*} [TopologicalSpace X]
    [NeZero d] (W : X → MPOTensor d D)
    (L R : X → Matrix (Fin D) (Fin D) ℂ) (hW : Continuous W)
    (hmap : ∀ x A, Kraus.transferMap (W x).normalizedFlattening A =
      Matrix.trace (L x * A) • R x) :
    Continuous (fun x ↦ virtualSandwich (L x) (W x) (R x)) := by
  simpa only [Function.comp_def, factorFreeSandwich_eq_of_trace_pair _ _ _ (hmap _)] using
    (continuous_factorFreeSandwich.comp hW)

end MPOTensor

namespace Continuous

/-- A continuous MPO family remains continuous after the factor-free sandwich.

Source: arXiv:1703.09188, Proposition IV.5, Figure `IV_index4.png`, lines
807--812. -/
theorem factorFreeSandwich {X : Type*} [TopologicalSpace X] {d D : ℕ}
    {W : X → MPOTensor d D} (hW : Continuous W) :
    Continuous (fun x ↦ MPOTensor.factorFreeSandwich (W x)) :=
  MPOTensor.continuous_factorFreeSandwich.comp hW

end Continuous
