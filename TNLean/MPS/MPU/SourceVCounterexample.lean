/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking
import TNLean.MPS.MPU.SourceVIsometry
import TNLean.MPS.MPU.TransferStabilization

/-!
# Counterexample to the unrestricted source-v Gram identification

This file shows that MPU unitarity, a positive-definite matrix, and the exact
fixed-witness `simple1` and `simple2` contractions do not identify the
source-$Y$ Gram contraction with the rank-one-inserted double-layer
contraction used in the proposed low-level route to arXiv:1703.09188,
Theorem III.8, equations (31)--(32), lines 563--601.

Take physical dimension one, bond dimension two, and
\[
  U^{00}=\begin{pmatrix}1&1\\0&0\end{pmatrix},\qquad
  \rho=\tfrac12 I_2.
\]
The local matrix is idempotent with trace one, so every positive-length periodic
MPO is the one-dimensional identity. With $b=\operatorname{vec}(\rho)$ and
$\Phi=\operatorname{vec}(I_2)$, the exact supplied `simple2` identity holds,
and MPU unitarity recovers `simple1` with the same witnesses. Nevertheless,
at the all-zero external entry the actual `sourceYTensor` Gram contraction is
$1/2$, while the inserted contraction is $1$.

The evaluation of `sourceYTensor` uses its public Gram expansion, so it is
independent of the noncomputable compact-SVD witness selected in the source
factor definitions. The example has no positive-definite transfer fixed point
and therefore has no canonical-form-II presentation with full active support.
The file does not prove the corrected source-v theorem under that reduced
canonical-form hypothesis.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor.SourceVCounterexample

noncomputable section

/-- The idempotent bond matrix in the source-v counterexample. -/
def bondMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i _ => if i = 0 then 1 else 0

/-- The one-letter MPU tensor with bond matrix
$\left(\begin{smallmatrix}1&1\\0&0\end{smallmatrix}\right)$. -/
def tensor : MPOTensor 1 2 := fun _ _ => bondMatrix

/-- The positive-definite source weight $\rho=\frac12 I_2$. -/
def weight : Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ)⁻¹ • 1

/-- The vectorized identity, used as the supplied left witness. -/
def leftWitness : Fin (2 * 2) → ℂ := fun x =>
  (1 : Matrix (Fin 2) (Fin 2) ℂ).vec (finProdFinEquiv.symm x)

/-- The vectorized source weight, used as the supplied right witness. -/
def rightWitness : Fin (2 * 2) → ℂ := fun x =>
  weight.vec (finProdFinEquiv.symm x)

private lemma bondMatrix_mul_self : bondMatrix * bondMatrix = bondMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [bondMatrix, Matrix.mul_apply]

private lemma trace_bondMatrix : Matrix.trace bondMatrix = 1 := by
  norm_num [Matrix.trace, Matrix.diag, bondMatrix]

private lemma tensor_apply (i j : Fin 1) : tensor i j = bondMatrix := rfl

private lemma evalWord_eq_bondMatrix (is js : List (Fin 1))
    (hlen : is.length = js.length) (hne : is ≠ []) :
    evalWord tensor is js = bondMatrix := by
  induction is generalizing js with
  | nil => contradiction
  | cons i is ih =>
      cases js with
      | nil => simp at hlen
      | cons j js =>
          rw [evalWord_cons, tensor_apply]
          by_cases his : is = []
          · subst is
            simp at hlen
            subst js
            simp
          · rw [ih js (by simpa using hlen) his, bondMatrix_mul_self]

/-- The counterexample tensor is an MPU: every periodic MPO of length greater
than one is the one-dimensional identity. -/
theorem tensor_isMPU : IsMPU tensor := by
  intro N hN
  have hmpo : mpo tensor N =
      (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ) := by
    ext sigma tau
    have hst : sigma = tau := Subsingleton.elim _ _
    subst tau
    rw [mpo_apply, mpoMatrixEntry, Matrix.one_apply, ite_eq_left rfl]
    rw [evalWord_eq_bondMatrix]
    · exact trace_bondMatrix
    · simp
    · intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      omega
  rw [hmpo, Matrix.mem_unitaryGroup_iff]
  simp

/-- The source weight $\rho=\frac12 I_2$ is positive definite. -/
theorem weight_posDef : weight.PosDef := by
  apply Matrix.PosDef.smul Matrix.PosDef.one
  norm_num

/-- The exact flattened rank-one insertion identity holds with
$b=\operatorname{vec}(\rho)$ and $\Phi=\operatorname{vec}(I_2)$. -/
theorem tensor_simple2 : ∀ i j k l : Fin 1,
    doubleLayerTensor tensor i j * doubleLayerTensor tensor k l =
      doubleLayerTensor tensor i j *
        Matrix.vecMulVec rightWitness leftWitness *
          doubleLayerTensor tensor k l := by
  intro i j k l
  fin_cases i
  fin_cases j
  fin_cases k
  fin_cases l
  ext x y
  rw [← finProdFinEquiv.apply_symm_apply x,
    ← finProdFinEquiv.apply_symm_apply y]
  obtain ⟨x1, x2⟩ := finProdFinEquiv.symm x
  obtain ⟨y1, y2⟩ := finProdFinEquiv.symm y
  change
    (doubleLayerTensor tensor 0 0 * doubleLayerTensor tensor 0 0)
        (finProdFinEquiv (x1, x2)) (finProdFinEquiv (y1, y2)) =
      (doubleLayerTensor tensor 0 0 *
          Matrix.vecMulVec
            (fun z => weight.vec (finProdFinEquiv.symm z))
            (fun z => (1 : Matrix (Fin 2) (Fin 2) ℂ).vec
              (finProdFinEquiv.symm z)) *
        doubleLayerTensor tensor 0 0)
        (finProdFinEquiv (x1, x2)) (finProdFinEquiv (y1, y2))
  have hord := doubleLayerTensor_mul_apply_four_u tensor
    ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)
    (x1, y1) (x2, y2)
  have hins := doubleLayerTensor_rankOne_mul_apply_four_u tensor weight
    ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)
    (x1, y1) (x2, y2)
  rw [hord, hins]
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
    norm_num [tensor, bondMatrix, weight, Fin.sum_univ_two]

/-- MPU unitarity and the supplied `simple2` identity recover the exact
flattened `simple1` identity with the same witnesses. -/
theorem tensor_simple1 : ∀ i j : Fin 1,
    leftWitness ⬝ᵥ (doubleLayerTensor tensor i j *ᵥ rightWitness) =
      if i = j then 1 else 0 :=
  tensor_isMPU.simple1_of_simple2_supplied
    leftWitness rightWitness tensor_simple2

/-- At the all-zero external entry, the Gram contraction of the actual
noncomputably chosen `sourceYTensor` is $1/2$. -/
theorem sourceYTensor_gram_zero_eq_half :
    (∑ t : Fin r[tensor] × Fin ℓ[tensor],
      star (sourceYTensor tensor weight weight_posDef t
        (((0 : Fin 1), (0 : Fin 2)), ((0 : Fin 1), (0 : Fin 2)))) *
      sourceYTensor tensor weight weight_posDef t
        (((0 : Fin 1), (0 : Fin 2)), ((0 : Fin 1), (0 : Fin 2)))) =
      (2 : ℂ)⁻¹ := by
  have h := sourceYTensor_gram_eq_four_u_weighted
    tensor weight weight_posDef
    ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)
    ((0, 0) : Fin 2 × Fin 2) ((0, 0) : Fin 2 × Fin 2)
  calc
    _ = ∑ alpha : Fin 2, ∑ alpha' : Fin 2, ∑ beta : Fin 2,
        ∑ j1 : Fin 1, ∑ j2 : Fin 1,
          star (tensor 0 j1 alpha 0) * weight alpha alpha' *
            tensor 0 j1 alpha' 0 *
              (star (tensor j2 0 beta 0) * tensor j2 0 beta 0) := h
    _ = (2 : ℂ)⁻¹ := by
      norm_num [tensor, bondMatrix, weight, Fin.sum_univ_two]

/-- At the all-zero external entry, inserting the exact supplied rank-one
witness between two double-layer letters gives $1$. -/
theorem inserted_doubleLayer_zero_eq_one :
    (doubleLayerTensor tensor 0 0 *
        Matrix.vecMulVec rightWitness leftWitness *
      doubleLayerTensor tensor 0 0)
      (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)))
      (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2))) = 1 := by
  have h := doubleLayerTensor_rankOne_mul_apply_four_u tensor weight
    ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)
    ((0, 0) : Fin 2 × Fin 2) ((0, 0) : Fin 2 × Fin 2)
  change
    (doubleLayerTensor tensor 0 0 *
        Matrix.vecMulVec
          (fun z => weight.vec (finProdFinEquiv.symm z))
          (fun z => (1 : Matrix (Fin 2) (Fin 2) ℂ).vec
            (finProdFinEquiv.symm z)) *
      doubleLayerTensor tensor 0 0)
      (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)))
      (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2))) = 1
  calc
    _ = ∑ alpha : Fin 2, ∑ alpha' : Fin 2, ∑ beta : Fin 2,
        ∑ j1 : Fin 1, ∑ j2 : Fin 1,
          star (tensor j1 0 0 alpha) * tensor j1 0 0 alpha' *
            weight alpha' alpha *
              (star (tensor j2 0 beta 0) * tensor j2 0 beta 0) := h
    _ = 1 := by
      norm_num [tensor, bondMatrix, weight, Fin.sum_univ_two]

/-- The unrestricted identification of the `sourceYTensor` Gram contraction with the
rank-one-inserted double-layer contraction is false, even under MPU unitarity,
positive definiteness, and the exact supplied `simple1` and `simple2`
identities.

This is the obstruction to the low-level route proposed for
arXiv:1703.09188, Theorem III.8, equations (31)--(32), lines 563--601. -/
theorem sourceYTensor_gram_ne_inserted :
    (∑ t : Fin r[tensor] × Fin ℓ[tensor],
      star (sourceYTensor tensor weight weight_posDef t
        (((0 : Fin 1), (0 : Fin 2)), ((0 : Fin 1), (0 : Fin 2)))) *
      sourceYTensor tensor weight weight_posDef t
        (((0 : Fin 1), (0 : Fin 2)), ((0 : Fin 1), (0 : Fin 2)))) ≠
    (doubleLayerTensor tensor 0 0 *
        Matrix.vecMulVec rightWitness leftWitness *
      doubleLayerTensor tensor 0 0)
      (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)))
      (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2))) := by
  rw [sourceYTensor_gram_zero_eq_half, inserted_doubleLayer_zero_eq_one]
  norm_num

/-- The counterexample normalized flattening has no positive-definite fixed
point of its transfer map. -/
theorem no_posDef_fixed (sigma : Matrix (Fin 2) (Fin 2) ℂ)
    (hsigma : sigma.PosDef) :
    MPSTensor.transferMap tensor.normalizedFlattening sigma ≠ sigma := by
  intro h
  have hentry := congrArg (fun M => M (1 : Fin 2) (1 : Fin 2)) h
  norm_num [normalizedFlattening, toMPSTensor, MPSTensor.transferMap_apply,
    tensor, bondMatrix, Matrix.mul_apply] at hentry
  have hdiag : 0 < sigma (1 : Fin 2) (1 : Fin 2) := hsigma.diag_pos
  rw [← hentry] at hdiag
  exact lt_irrefl 0 hdiag

/-- Canonical-form-II data for the counterexample normalized flattening cannot
have full active support. Such data would supply a positive-definite transfer
fixed point, contradicting `no_posDef_fixed`.

This excludes the counterexample from the reduced-representative hypotheses
used for arXiv:1703.09188, equations (6a)--(6b), lines 269--280 and 397--405. -/
theorem not_hasFullActiveSupport
    (cfii : MPSTensor.CPSVCanonicalFormIIData tensor.normalizedFlattening) :
    ¬ cfii.toCPSVCanonicalFormData.HasFullActiveSupport := by
  intro hfull
  obtain ⟨_, _, sigma, _, _, _, _, _, _, hsigma_pd, _, hsigma_fix, _, _⟩ :=
    tensor_isMPU.normalized_transfer_power_eq_vecMulVec_of_reduced_cfii
      (by omega) cfii hfull
  exact no_posDef_fixed sigma hsigma_pd hsigma_fix

end

end MPOTensor.SourceVCounterexample
