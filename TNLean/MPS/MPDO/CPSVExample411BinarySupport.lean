/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixCyclicTracePower
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.CyclicEdgeWeightTensor

/-!
# Effective binary-support model for CPSV16 Example 4.11

This module formalizes the classical binary cycle carried by the support of the
four diagonal neighboring operators printed in CPSV16 Example 4.11. Its
coefficient matrix, extracted from those operators, is
\[
  W=\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix}.
\]
The resulting cyclic-edge tensor has an exact diagonal MPO formula, and its
partition function is
\[
  Z_N=\operatorname{tr}(W^N)=\frac{3^N+1}{2^N}
\]
for every positive length.

**Scope restriction (supported binary encoding):** the physical dimension in
this module is $2$. A supported label $k$ selects the ambient two-qubit basis
vector $|k,k\rangle$ at each site. The literal tensor printed in the paper has
physical dimension $4$; identifying it requires a later support embedding. See
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. No spectrum, entropy,
SAL, ZCL, or ambient-tensor equivalence is asserted here.

## Main definitions

* `weightMatrix`: the coefficient matrix extracted from the four printed diagonal
  neighboring operators.
* `edgeWeight`: the diagonal ket--bra edge weight.
* `M`: the associated cyclic-edge matrix-product tensor.
* `cycleWeight`: the unnormalized weight of a binary cycle labeling.
* `partitionFunction`: the sum of all binary cycle weights.
* `internalTransitionCount`: the number of transitions internal to a retained word.
* `internalEdgeProduct`: the product of edge weights internal to a retained word.
* `firstLabel`: the first label of a nonempty retained word.
* `lastLabel`: the final label of a nonempty retained word.
* `complementPathWeight`: the complementary path weight with fixed endpoints.

## Main results

* `mpo_M_apply`: the exact positive-length diagonal MPO entry formula.
* `mpo_M_eq_diagonal`: the corresponding matrix formula.
* `partitionFunction_eq_trace_pow`: the cycle sum equals `tr(W^N)`.
* `trace_weightMatrix_pow`: the closed trace-power formula.
* `partitionFunction_closed_form`: the closed positive-length normalization.
* `weightMatrix_pow_apply`: the closed form for every entry of a weight-matrix power.
* `sum_complementPathWeight_eq_weightMatrix_pow`: the complementary path sum.
* `sum_cycleWeight_append_eq_internalEdgeProduct_mul_pow`: the retained-word cycle sum.
* `internalEdgeProduct_eq`: the transition-count formula for internal edges.
* `reducedBlockState_apply_eq_internal_mul_pow`: the exact normalized path formula.
* `reducedBlockState_apply`: the closed finite-ring block probability.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.CPSVExample411BinarySupport

/-- The coefficient matrix extracted from the four diagonal neighboring
operators printed in CPSV16 Example 4.11.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def weightMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1 / 2; 1 / 2, 1]

/-- The scalar edge weight, diagonal in both endpoint ket--bra pairs.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def edgeWeight (i j i' j' : Fin 2) : ℂ :=
  if i = j ∧ i' = j' then weightMatrix i i' else 0

/-- The bond-dimension-$4$ cyclic-edge tensor for the effective binary model.
A supported physical label $k$ selects the ambient basis vector $|k,k\rangle$.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def M : MPOTensor 2 4 := cyclicEdgeWeightTensor edgeWeight

/-- The unnormalized weight of a binary labeling of a periodic cycle.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def cycleWeight {N : ℕ} [NeZero N] (σ : Fin N → Fin 2) : ℂ :=
  ∏ n : Fin N, weightMatrix (σ n) (σ (n + 1))

/-- The partition function obtained by summing all binary cycle weights.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
def partitionFunction (N : ℕ) [NeZero N] : ℂ :=
  ∑ σ : Fin N → Fin 2, cycleWeight σ

/-- The number of internal nearest-neighbor transitions in a binary word.

This excludes the closing edge from the final site back to the first site. It is
used below for a project-derived finite-ring consequence of CPSV16 Example 4.11. -/
def internalTransitionCount : {L : ℕ} → (Fin L → Fin 2) → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | L + 2, x => (if x 0 = x 1 then 0 else 1) +
      internalTransitionCount (fun i : Fin (L + 1) ↦ x i.succ)

/-- The product of the internal edge weights of a binary word. -/
def internalEdgeProduct {L : ℕ} (x : Fin L → Fin 2) : ℂ :=
  ∏ i : Fin (L - 1), weightMatrix (x (Fin.castLE (Nat.sub_le L 1) i))
    (x ⟨i.val + 1, by have hi := i.isLt; omega⟩)

/-- The first label of a nonempty binary word. -/
def firstLabel {L : ℕ} (hL : 1 ≤ L) (x : Fin L → Fin 2) : Fin 2 := x ⟨0, by omega⟩

/-- The final label of a nonempty binary word. -/
def lastLabel {L : ℕ} (hL : 1 ≤ L) (x : Fin L → Fin 2) : Fin 2 := x ⟨L - 1, by omega⟩

/-- The product along the complementary path from $a$ to $b$ through the
listed internal labels. -/
def complementPathWeight (a b : Fin 2) : {K : ℕ} → (Fin K → Fin 2) → ℂ
  | 0, _ => weightMatrix a b
  | K + 1, w => weightMatrix a (w 0) *
      complementPathWeight (w 0) b (fun i : Fin K ↦ w i.succ)

@[simp] private theorem complementPathWeight_zero (a b : Fin 2) (w : Fin 0 → Fin 2) :
    complementPathWeight a b w = weightMatrix a b := rfl

@[simp] private theorem complementPathWeight_cons {K : ℕ} (a b c : Fin 2)
    (w : Fin K → Fin 2) :
    complementPathWeight a b (Fin.cons c w) =
      weightMatrix a c * complementPathWeight c b w := rfl

/-- The endpoint-augmented vertex list of a complementary path. -/
private def pathVertices {R : ℕ} (a b : Fin 2) (w : Fin R → Fin 2) :
    Fin (R + 2) → Fin 2 :=
  Fin.cons a (Fin.snoc w b)

private theorem pathVertices_tail {R : ℕ} (a b : Fin 2) (w : Fin (R + 1) → Fin 2)
    (i : Fin (R + 2)) :
    pathVertices (w 0) b (fun j : Fin R ↦ w j.succ) i = pathVertices a b w i.succ := by
  change (Fin.cons (w 0) (Fin.snoc (fun j : Fin R ↦ w j.succ) b) :
      Fin (R + 2) → Fin 2) i =
    (Fin.cons a (Fin.snoc w b) : Fin (R + 3) → Fin 2) i.succ
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · change (Fin.snoc (fun k : Fin R ↦ w k.succ) b : Fin (R + 1) → Fin 2) j =
      (Fin.snoc w b : Fin (R + 2) → Fin 2) j.succ
    by_cases hj : j.val < R
    · have hcast : j = Fin.castSucc (⟨j.val, hj⟩ : Fin R) := by apply Fin.ext; rfl
      rw [hcast, Fin.snoc_castSucc]
      rw [show (Fin.castSucc (⟨j.val, hj⟩ : Fin R)).succ =
          Fin.castSucc (⟨j.val + 1, by omega⟩ : Fin (R + 1)) by apply Fin.ext; rfl,
        Fin.snoc_castSucc]
      congr
    · have hlast : j = Fin.last R := by apply Fin.ext; simp; omega
      subst j
      simp

private theorem complementPathWeight_eq_prod {R : ℕ} (a b : Fin 2)
    (w : Fin R → Fin 2) :
    complementPathWeight a b w =
      ∏ i : Fin (R + 1), weightMatrix (pathVertices a b w i.castSucc)
        (pathVertices a b w i.succ) := by
  induction R generalizing a with
  | zero =>
      rw [complementPathWeight_zero, Fin.prod_univ_one]
      rfl
  | succ R ih =>
      rw [complementPathWeight, Fin.prod_univ_succ, ih (w 0)]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      change weightMatrix
          ((Fin.cons (w 0) (Fin.snoc (fun j : Fin R ↦ w j.succ) b) :
            Fin (R + 2) → Fin 2) i.castSucc)
          ((Fin.cons (w 0) (Fin.snoc (fun j : Fin R ↦ w j.succ) b) :
            Fin (R + 2) → Fin 2) i.succ) =
        weightMatrix ((Fin.cons a (Fin.snoc w b) : Fin (R + 3) → Fin 2) i.succ.castSucc)
          ((Fin.cons a (Fin.snoc w b) : Fin (R + 3) → Fin 2) i.succ.succ)
      change weightMatrix
          (pathVertices (w 0) b (fun j : Fin R ↦ w j.succ) i.castSucc)
          (pathVertices (w 0) b (fun j : Fin R ↦ w j.succ) i.succ) =
        weightMatrix (pathVertices a b w i.succ.castSucc)
          (pathVertices a b w i.succ.succ)
      rw [pathVertices_tail a b w i.castSucc, pathVertices_tail a b w i.succ]
      congr 2

/-- The effective binary tensor has exactly the expected diagonal cycle entries.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
theorem mpo_M_apply {N : ℕ} [NeZero N] (σ τ : Fin N → Fin 2) :
    mpo M N σ τ = if σ = τ then cycleWeight σ else 0 := by
  rw [M, mpo_cyclicEdgeWeightTensor]
  by_cases hστ : σ = τ
  · subst τ
    simp only [edgeWeight, cycleWeight, true_and, ↓reduceIte]
  · rw [ite_eq_right hστ]
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hστ
    apply Finset.prod_eq_zero (Finset.mem_univ n)
    simp only [edgeWeight]
    rw [ite_eq_right]
    exact fun hdiag ↦ hn hdiag.1

/-- The diagonal MPO matrix formula, as an equality of matrices.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
theorem mpo_M_eq_diagonal {N : ℕ} [NeZero N] :
    mpo M N = Matrix.diagonal cycleWeight := by
  ext σ τ
  rw [mpo_M_apply, Matrix.diagonal_apply]

/-- The binary cycle partition function is the trace of the corresponding
matrix power.

Source: arXiv:1606.00608, Example 4.11, lines 907--924. -/
theorem partitionFunction_eq_trace_pow {N : ℕ} [NeZero N] :
    partitionFunction N = Matrix.trace (weightMatrix ^ N) := by
  rw [partitionFunction, trace_pow_eq_sum_cyclic_product]
  simp only [cycleWeight]

private def hadamard : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

private def eigenvalueMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![3 / 2, 1 / 2]

private lemma hadamard_mul_half_hadamard :
    hadamard * ((1 / 2 : ℂ) • hadamard) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

private lemma half_hadamard_mul_hadamard :
    ((1 / 2 : ℂ) • hadamard) * hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

private lemma hadamard_mul_eigenvalueMatrix_eq_weightMatrix_mul_hadamard :
    hadamard * eigenvalueMatrix = weightMatrix * hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, eigenvalueMatrix, weightMatrix, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num

/-- Every entry of a power of the binary weight matrix has its exact Hadamard-basis
closed form. -/
theorem weightMatrix_pow_apply (N : ℕ) (a b : Fin 2) :
    (weightMatrix ^ N) a b =
      (((3 : ℂ) / 2) ^ N + (if a = b then 1 else -1) * ((1 : ℂ) / 2) ^ N) / 2 := by
  have hmatrix : weightMatrix ^ N =
      hadamard * eigenvalueMatrix ^ N * ((1 / 2 : ℂ) • hadamard) := by
    calc
      weightMatrix ^ N = weightMatrix ^ N * 1 := by rw [Matrix.mul_one]
      _ = weightMatrix ^ N * (hadamard * ((1 / 2 : ℂ) • hadamard)) := by
        rw [hadamard_mul_half_hadamard]
      _ = (weightMatrix ^ N * hadamard) * ((1 / 2 : ℂ) • hadamard) := by
        rw [Matrix.mul_assoc]
      _ = hadamard * eigenvalueMatrix ^ N * ((1 / 2 : ℂ) • hadamard) := by
        rw [(show SemiconjBy hadamard eigenvalueMatrix weightMatrix from
          hadamard_mul_eigenvalueMatrix_eq_weightMatrix_mul_hadamard).pow_right N]
  rw [hmatrix]
  fin_cases a <;> fin_cases b <;>
    simp [hadamard, eigenvalueMatrix, Matrix.diagonal_pow, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring


/-- A cycle with a nonempty retained prefix factors into its internal edges and
its complementary endpoint path. -/
private theorem cycleWeight_append_eq_internal_mul_complement {L R : ℕ}
    (hL : 1 ≤ L) (x : Fin L → Fin 2) (w : Fin R → Fin 2) :
    letI : NeZero (L + R) := ⟨by omega⟩
    cycleWeight (Fin.append x w) =
      internalEdgeProduct x * complementPathWeight (lastLabel hL x) (firstLabel hL x) w := by
  let : NeZero (L + R) := ⟨by omega⟩
  unfold cycleWeight internalEdgeProduct
  let q : Fin (L + R) → Fin 2 := Fin.append x w
  have hsplit : L + R = (L - 1) + (R + 1) := by omega
  rw [Fintype.prod_equiv (finCongr hsplit)
    (fun n : Fin (L + R) ↦ weightMatrix (q n) (q (n + 1)))
    (fun n : Fin ((L - 1) + (R + 1)) ↦
      weightMatrix (q (Fin.cast hsplit.symm n)) (q (Fin.cast hsplit.symm n + 1)))]
  · rw [Fin.prod_univ_add, complementPathWeight_eq_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      congr 2
      · change Fin.append x w _ = x _
        rw [show Fin.cast hsplit.symm (Fin.castAdd (R + 1) i) =
            Fin.castAdd R (Fin.castLE (Nat.sub_le L 1) i) by apply Fin.ext; rfl,
          Fin.append_left]
      · have hi : i.val + 1 < L := by have := i.isLt; omega
        have hbase : Fin.cast hsplit.symm (Fin.castAdd (R + 1) i) =
            Fin.castAdd R (Fin.castLE (Nat.sub_le L 1) i) := by
          apply Fin.ext
          rfl
        have hvalbase : (Fin.castAdd R (Fin.castLE (Nat.sub_le L 1) i)).val = i.val := rfl
        have hadd_lt : (Fin.castAdd R (Fin.castLE (Nat.sub_le L 1) i)).val +
            (1 : Fin (L + R)).val < L + R := by
          rw [hvalbase]
          have hsize : 2 ≤ L + R := by omega
          have hone : (1 : Fin (L + R)).val = 1 := by
            exact Nat.mod_eq_of_lt hsize
          rw [hone]
          omega
        have hstep : Fin.castAdd R (Fin.castLE (Nat.sub_le L 1) i) + 1 =
            Fin.castAdd R (⟨i.val + 1, hi⟩ : Fin L) := by
          apply Fin.ext
          rw [Fin.val_add_eq_of_add_lt hadd_lt, hvalbase]
          have hsize : 2 ≤ L + R := by omega
          have hone : (1 : Fin (L + R)).val = 1 := by
            exact Nat.mod_eq_of_lt hsize
          rw [hone]
          rfl
        have hindex : Fin.cast hsplit.symm (Fin.castAdd (R + 1) i) + 1 =
            Fin.castAdd R (⟨i.val + 1, hi⟩ : Fin L) := by
          rw [hbase]
          exact hstep
        change Fin.append x w _ = x _
        rw [hindex, Fin.append_left]
    · apply Finset.prod_congr rfl
      intro i _
      congr 2
      · refine Fin.cases ?_ (fun j ↦ ?_) i
        · change Fin.append x w _ = lastLabel hL x
          rw [show Fin.cast hsplit.symm (Fin.natAdd (L - 1) (0 : Fin (R + 1))) =
              Fin.castAdd R (⟨L - 1, by omega⟩ : Fin L) by apply Fin.ext; simp,
            Fin.append_left]
          rfl
        · change Fin.append x w _ =
            pathVertices (lastLabel hL x) (firstLabel hL x) w j.succ.castSucc
          rw [show pathVertices (lastLabel hL x) (firstLabel hL x) w j.succ.castSucc = w j by
            simp [pathVertices]]
          rw [show Fin.cast hsplit.symm (Fin.natAdd (L - 1) j.succ) =
              Fin.natAdd L j by apply Fin.ext; simp; omega,
            Fin.append_right]
      · by_cases hi : i.val < R
        · let j : Fin R := ⟨i.val, hi⟩
          have hicast : i = Fin.castSucc j := by apply Fin.ext; rfl
          rw [hicast]
          change Fin.append x w _ =
            pathVertices (lastLabel hL x) (firstLabel hL x) w (Fin.castSucc j).succ
          rw [show pathVertices (lastLabel hL x) (firstLabel hL x) w
            (Fin.castSucc j).succ = w j by simp [pathVertices]]
          have hraw : Fin.cast hsplit.symm (Fin.natAdd (L - 1) (Fin.castSucc j)) =
              ⟨L - 1 + j.val, by omega⟩ := by
            apply Fin.ext
            rfl
          have hsize : 2 ≤ L + R := by omega
          have hone : (1 : Fin (L + R)).val = 1 := Nat.mod_eq_of_lt hsize
          have hlt : L - 1 + j.val + (1 : Fin (L + R)).val < L + R := by
            rw [hone]
            omega
          have hindex : Fin.cast hsplit.symm (Fin.natAdd (L - 1) (Fin.castSucc j)) + 1 =
              Fin.natAdd L j := by
            rw [hraw]
            apply Fin.ext
            rw [Fin.val_add_eq_of_add_lt hlt]
            rw [hone]
            simp only [Fin.val_natAdd]
            omega
          rw [hindex, Fin.append_right]
        · have hilast : i = Fin.last R := by apply Fin.ext; simp; omega
          subst i
          change Fin.append x w _ =
            pathVertices (lastLabel hL x) (firstLabel hL x) w (Fin.last R).succ
          rw [show pathVertices (lastLabel hL x) (firstLabel hL x) w (Fin.last R).succ =
            firstLabel hL x by simp [pathVertices]]
          have hbefore : Fin.cast hsplit.symm (Fin.natAdd (L - 1) (Fin.last R)) =
              ⟨L + R - 1, by omega⟩ := by
            apply Fin.ext
            simp
            omega
          have hindex : Fin.cast hsplit.symm (Fin.natAdd (L - 1) (Fin.last R)) + 1 =
              (0 : Fin (L + R)) := by
            rw [hbefore]
            apply Fin.ext
            simp only [Fin.add_def]
            simp only [Fin.val_zero]
            by_cases hsize : L + R = 1
            · have hfin : (1 : Fin (L + R)).val = 0 := by
                change 1 % (L + R) = 0
                rw [hsize]
              rw [hfin, hsize]
            · have htwo : 2 ≤ L + R := by omega
              have hone : (1 : Fin (L + R)).val = 1 := Nat.mod_eq_of_lt htwo
              rw [hone]
              have hadd : L + R - 1 + 1 = L + R := Nat.sub_add_cancel (by omega)
              rw [hadd]
              exact Nat.mod_self (L + R)
          rw [hindex]
          change Fin.append x w 0 = x ⟨0, by omega⟩
          rw [show (0 : Fin (L + R)) = Fin.castAdd R (⟨0, by omega⟩ : Fin L) by rfl,
            Fin.append_left]
  · intro i
    rfl

/-- The sum of endpoint-fixed complementary path weights is the corresponding
matrix-power entry. -/
theorem sum_complementPathWeight_eq_weightMatrix_pow (K : ℕ) (a b : Fin 2) :
    ∑ w : Fin K → Fin 2, complementPathWeight a b w = (weightMatrix ^ (K + 1)) a b := by
  induction K generalizing a with
  | zero =>
      rw [Fintype.sum_unique]
      rw [complementPathWeight_zero, pow_one]
  | succ K ih =>
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (K + 1) ↦ Fin 2))]
      rw [Fintype.sum_prod_type]
      change ∑ c : Fin 2, ∑ w : Fin K → Fin 2,
          weightMatrix a c * complementPathWeight c b w = _
      calc
        (∑ c : Fin 2, ∑ w : Fin K → Fin 2,
            weightMatrix a c * complementPathWeight c b w) =
            ∑ c : Fin 2, weightMatrix a c * (weightMatrix ^ (K + 1)) c b := by
          apply Finset.sum_congr rfl
          intro c _
          rw [← Finset.mul_sum, ih c]
        _ = (weightMatrix ^ (K + 1 + 1)) a b := by
          change (weightMatrix * weightMatrix ^ (K + 1)) a b = _
          rw [← pow_succ', show K + 1 + 1 = (K + 1) + 1 by omega]

/-- Summing the actual cycle weights over all complementary configurations gives
the internal edge product times the endpoint matrix-power entry. -/
theorem sum_cycleWeight_append_eq_internalEdgeProduct_mul_pow {L K : ℕ}
    (hL : 1 ≤ L) (x : Fin L → Fin 2) :
    letI : NeZero (L + K) := ⟨by omega⟩
    ∑ w : Fin K → Fin 2, cycleWeight (Fin.append x w) =
      internalEdgeProduct x * (weightMatrix ^ (K + 1))
        (lastLabel hL x) (firstLabel hL x) := by
  simp_rw [cycleWeight_append_eq_internal_mul_complement hL]
  rw [← Finset.mul_sum, sum_complementPathWeight_eq_weightMatrix_pow]

/-- The trace of every power of the coefficient matrix extracted from the four
printed diagonal neighboring operators has the closed form
`(3^N + 1) / 2^N`.

Project derivation from the neighboring operators printed in arXiv:1606.00608,
Example 4.11, lines 907--924; see
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. -/
theorem trace_weightMatrix_pow (N : ℕ) :
    Matrix.trace (weightMatrix ^ N) = ((3 : ℂ) ^ N + 1) / (2 : ℂ) ^ N := by
  rw [Matrix.trace_pow_eq_of_intertwining
    hadamard_mul_eigenvalueMatrix_eq_weightMatrix_mul_hadamard
    hadamard_mul_half_hadamard half_hadamard_mul_hadamard,
    eigenvalueMatrix, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_two, Pi.pow_apply, Matrix.vecEmpty, Matrix.vecCons]
  change ((3 : ℂ) / 2) ^ N + ((1 : ℂ) / 2) ^ N =
    ((3 : ℂ) ^ N + 1) / (2 : ℂ) ^ N
  rw [div_pow, div_pow]
  field_simp
  ring

/-- The exact positive-length normalization of the effective binary model.

Project derivation from the neighboring operators printed in arXiv:1606.00608,
Example 4.11, lines 907--924; see
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. -/
theorem partitionFunction_closed_form {N : ℕ} [NeZero N] :
    partitionFunction N = ((3 : ℂ) ^ N + 1) / (2 : ℂ) ^ N := by
  rw [partitionFunction_eq_trace_pow, trace_weightMatrix_pow]

private theorem internalEdgeProduct_more {L : ℕ} (x : Fin (L + 2) → Fin 2) :
    internalEdgeProduct x = weightMatrix (x 0) (x 1) *
      internalEdgeProduct (fun i : Fin (L + 1) ↦ x i.succ) := by
  unfold internalEdgeProduct
  change (∏ i : Fin (L + 1), weightMatrix (x i.castSucc)
      (x ⟨i.val + 1, by omega⟩)) = _
  rw [Fin.prod_univ_succ]
  congr 1

/-- The internal edge product is determined exactly by the number of transitions. -/
theorem internalEdgeProduct_eq {L : ℕ} (x : Fin L → Fin 2) :
    internalEdgeProduct x = 1 / (2 : ℂ) ^ internalTransitionCount x := by
  induction L using Nat.twoStepInduction with
  | zero => simp [internalEdgeProduct, internalTransitionCount]
  | one => simp [internalEdgeProduct, internalTransitionCount]
  | more L ih0 ih1 =>
      rw [internalEdgeProduct_more, internalTransitionCount, ih1]
      by_cases h : x 0 = x 1
      · rw [ite_eq_left h, h]
        have hx : x 1 = 0 ∨ x 1 = 1 := by omega
        rcases hx with hx | hx <;> simp [hx, weightMatrix]
      · rw [ite_eq_right h]
        have hx0 : x 0 = 0 ∨ x 0 = 1 := by omega
        have hx1 : x 1 = 0 ∨ x 1 = 1 := by omega
        rcases hx0 with hx0 | hx0 <;> rcases hx1 with hx1 | hx1 <;>
          simp_all [weightMatrix]
        all_goals ring

/-- The existing reduced block state of the effective binary MPO is diagonal, with
its diagonal entry given by the internal edge product and complementary matrix power. -/
theorem reducedBlockState_apply_eq_internal_mul_pow {N L : ℕ} [NeZero N] (hL : 1 ≤ L)
    (hLN : L ≤ N) (x y : Fin L → Fin 2) :
    reducedBlockState M N L hLN x y = if x = y then
      internalEdgeProduct x * (weightMatrix ^ (N - L + 1))
        (lastLabel hL x) (firstLabel hL x) / partitionFunction N else 0 := by
  generalize hK : N - L = K
  have hN : N = L + K := by omega
  subst N
  have hsub : L + K - L = K := Nat.add_sub_cancel_left L K
  rw [reducedBlockState_eq_sum, normalizedMPO]
  simp only [Matrix.smul_apply, smul_eq_mul, mpo_M_apply]
  by_cases hxy : x = y
  · subst y
    simp only [↓reduceIte]
    rw [← Finset.mul_sum]
    let : NeZero (L + (L + K - L)) := ⟨by omega⟩
    have htotal : L + K = L + (L + K - L) := by omega
    have hcastsum :
        (∑ i : Fin (L + K - L) → Fin 2,
          cycleWeight (Fin.append x i ∘ Fin.cast htotal)) =
        ∑ i : Fin (L + K - L) → Fin 2, cycleWeight (Fin.append x i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold cycleWeight
      symm
      apply Finset.prod_bij (fun n _ ↦ Fin.cast htotal.symm n)
      · intro n _
        exact Finset.mem_univ _
      · intro n _ m _ h
        apply Fin.ext
        simpa using congrArg Fin.val h
      · intro n _
        exact ⟨Fin.cast htotal n, Finset.mem_univ _, by simp⟩
      · intro n _
        congr 2
        apply Fin.ext
        simp [Fin.add_def]
    rw [hcastsum]
    have hsum' := sum_cycleWeight_append_eq_internalEdgeProduct_mul_pow
      (K := L + K - L) hL x
    rw [hsum', hsub]
    have htrace : (mpo M (L + K)).trace = partitionFunction (L + K) := by
      rw [mpo_M_eq_diagonal, Matrix.trace_diagonal]
      rfl
    rw [htrace]
    simp only [div_eq_mul_inv]
    ring
  · rw [ite_eq_right hxy]
    apply Finset.sum_eq_zero
    intro w _
    rw [ite_eq_right]
    · ring
    intro h
    apply hxy
    funext i
    have htotal : L + K = L + (L + K - L) := by omega
    have := congrFun h (Fin.cast htotal.symm (Fin.castAdd (L + K - L) i))
    simpa using this

/-- The parity of the internal transition count records whether the endpoints agree. -/
private theorem neg_one_pow_internalTransitionCount {L : ℕ} (hL : 1 ≤ L)
    (x : Fin L → Fin 2) :
    (-1 : ℂ) ^ internalTransitionCount x =
      if lastLabel hL x = firstLabel hL x then 1 else -1 := by
  induction L using Nat.twoStepInduction with
  | zero => omega
  | one =>
      simp only [internalTransitionCount, pow_zero]
      rw [ite_eq_left]
      congr
  | more L ih0 ih1 =>
      rw [internalTransitionCount]
      have htail : (1 : ℕ) ≤ L + 1 := by omega
      rw [pow_add, ih1 htail]
      change ((-1 : ℂ) ^ (if x 0 = x 1 then 0 else 1)) *
          (if x ⟨L + 1, by omega⟩ = x 1 then 1 else -1) =
        if x ⟨L + 1, by omega⟩ = x 0 then 1 else -1
      by_cases h01 : x 0 = x 1
      · rw [ite_eq_left h01, pow_zero, one_mul, h01]
      · rw [ite_eq_right h01, pow_one]
        have hx0 : x 0 = 0 ∨ x 0 = 1 := by omega
        have hx1 : x 1 = 0 ∨ x 1 = 1 := by omega
        have hxlast : x ⟨L + 1, by omega⟩ = 0 ∨ x ⟨L + 1, by omega⟩ = 1 := by omega
        rcases hx0 with hx0 | hx0 <;> rcases hx1 with hx1 | hx1 <;>
          rcases hxlast with hxlast | hxlast <;> simp_all

/-- The project-derived exact finite-ring block probability in a form involving
only nonnegative natural-number exponents. This includes the endpoint cases
$L = 1$ and $L = N$; no zero-length block formula is asserted.

Project derivation from the neighboring operators printed in arXiv:1606.00608,
Example 4.11, lines 907--924; see
`docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`. -/
theorem reducedBlockState_apply {N L : ℕ} [NeZero N] (hL : 1 ≤ L) (hLN : L ≤ N)
    (x y : Fin L → Fin 2) :
    reducedBlockState M N L hLN x y = if x = y then
      (2 : ℂ) ^ L * ((3 : ℂ) ^ (N - L + 1) +
        (-1 : ℂ) ^ internalTransitionCount x) /
          ((2 : ℂ) ^ (internalTransitionCount x + 2) * ((3 : ℂ) ^ N + 1))
      else 0 := by
  rw [reducedBlockState_apply_eq_internal_mul_pow hL hLN]
  split_ifs with hxy
  · subst y
    rw [internalEdgeProduct_eq, weightMatrix_pow_apply,
      neg_one_pow_internalTransitionCount hL, partitionFunction_closed_form]
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    have hthree : (3 : ℂ) ^ N + 1 ≠ 0 := by
      intro h
      have hcast : ((3 : ℕ) ^ N + 1 : ℂ) = 0 := by exact_mod_cast h
      have hz : (3 : ℕ) ^ N + 1 = 0 := by exact_mod_cast hcast
      exact (Nat.ne_of_gt (Nat.zero_lt_succ ((3 : ℕ) ^ N))) hz
    rw [div_pow, div_pow]
    field_simp
    rw [show N = L + (N - L) by omega]
    simp only [Nat.add_sub_cancel_left, pow_add]
    ring
  · rfl

end MPOTensor.CPSVExample411BinarySupport
