/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MajumdarGhoshHamiltonian
import TNLean.MPS.ParentHamiltonian.CyclicWindow
import TNLean.MPS.ParentHamiltonian.IntersectionProperty
import TNLean.MPS.ParentHamiltonian.KernelChainGroundSpace
import TNLean.MPS.ParentHamiltonian.UniqueGroundState

/-!
# Majumdar-Ghosh: the ground space of the parent Hamiltonian

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127),
Appendix A, `Papers/2011.12127/TN-Review-main.tex` lines 2397–2405: the
Majumdar-Ghosh ground state "is a superposition of singlet pairs
\((1,2),(3,4),\dots\) and \((2,3),(4,5),\dots,(N,1)\), and can be written as an
MPS". The parent-Hamiltonian construction is that of Pérez-García, Verstraete,
Wolf, Cirac 2007 (arXiv:quant-ph/0608197), Section 5.
Review: arXiv:2011.12127, Appendix A, "The Majumdar-Ghosh model".

**Formalized here.** The review does not state the dimension of the ground
space. The results below are project results about the range-three parent
Hamiltonian of the bond-dimension-three tensor `majumdarGhoshTensor`, whose
kernel is the periodic chain ground space \(\mathcal G_{N,3}\):
* on an even ring of \(N\ge4\) sites, \(\mathcal G_{N,3}\) is spanned by the two
  nearest-neighbour singlet coverings, and is two-dimensional;
* on an odd ring of \(N\ge5\) sites, \(\mathcal G_{N,3}\) is zero.

The relation to the review's Hamiltonian \(H\) is only through
`majumdarGhoshHamiltonian_apply_of_mem_chainGroundSpace`: every vector of
\(\mathcal G_{N,3}\) is an eigenvector of \(H\) with eigenvalue
\(-\tfrac{3N}8\). The lower bound \(H\ge-\tfrac{3N}8\), which would identify
\(\mathcal G_{N,3}\) with the ground space of \(H\), is not formalized.

## Proof outline

The grading \(G=\operatorname{diag}(1,-1,-1)\) anticommutes with both matrices
of the tensor, so every vector of the local space \(\mathcal G_K\) is
\(\Gamma_K(X)\) for a boundary matrix of parity \((-1)^K\), that is,
\(GX=(-1)^KXG\). For \(K\ge3\), \(\Gamma_K\) is injective on such matrices: the
base case \(K=3\) is a four-coordinate check, and the step uses the
left-canonical equation. This gives the intersection property
\((\mathcal G_M\otimes\mathbb C^2)\cap(\mathbb C^2\otimes\mathcal G_M)
=\mathcal G_{M+1}\) for \(M\ge4\); the case \(M=3\) is a sixteen-coordinate
computation. Hence \(\mathcal G_{N,3}\subseteq\mathcal G_N\). Comparing the
boundary matrices of a vector and of its translate by one site gives
\(XA^a=A^aY\), which forces \(X\in\operatorname{span}\{1,G\}\) on even rings
and \(X=0\) on odd rings.

## Main results
* `MPSTensor.majumdarGhosh_eq_zero_of_groundSpaceMap_eq_zero` : graded
  injectivity of \(\Gamma_K\) for \(K\ge3\)
* `MPSTensor.majumdarGhosh_groundSpace_intersection` : the intersection property
  from three sites on
* `MPSTensor.majumdarGhosh_chainGroundSpace_le_groundSpace`
* `MPSTensor.majumdarGhosh_chainGroundSpace_eq_span`,
  `MPSTensor.majumdarGhosh_ker_parentHamiltonian_eq_span`,
  `MPSTensor.majumdarGhosh_finrank_chainGroundSpace`
* `MPSTensor.majumdarGhosh_chainGroundSpace_eq_bot_of_odd`

## References
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*
- [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197) -- Pérez-García,
  Verstraete, Wolf, Cirac, *Matrix product state representations*
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

/-! ### Parity of boundary matrices -/

lemma majumdarGhoshGrading_mul_self :
    majumdarGhoshGrading * majumdarGhoshGrading = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [majumdarGhoshGrading, Matrix.mul_apply, Fin.sum_univ_three]

/-- The grading passes through a word of length \(K\) with the sign \((-1)^K\). -/
lemma majumdarGhoshGrading_mul_evalWord (w : List (Fin 2)) :
    majumdarGhoshGrading * Kraus.evalWord majumdarGhoshTensor w =
      (-1 : ℂ) ^ w.length • (Kraus.evalWord majumdarGhoshTensor w * majumdarGhoshGrading) := by
  induction w with
  | nil => simp [Kraus.evalWord]
  | cons a w ih =>
    rw [Kraus.evalWord_cons, ← Matrix.mul_assoc, majumdarGhoshGrading_mul, Matrix.smul_mul,
      Matrix.mul_assoc, ih, Matrix.mul_smul, smul_smul, List.length_cons, pow_succ,
      mul_comm, Matrix.mul_assoc]

/-- Left multiplication by a matrix of the tensor flips the parity. -/
lemma majumdarGhosh_parity_mul_left {ε : ℂ} {X : Matrix (Fin 3) (Fin 3) ℂ}
    (hX : majumdarGhoshGrading * X = ε • (X * majumdarGhoshGrading)) (a : Fin 2) :
    majumdarGhoshGrading * (majumdarGhoshTensor a * X) =
      (-ε) • (majumdarGhoshTensor a * X * majumdarGhoshGrading) := by
  rw [← Matrix.mul_assoc, majumdarGhoshGrading_mul, Matrix.smul_mul, Matrix.mul_assoc, hX,
    Matrix.mul_smul, smul_smul, neg_one_mul, Matrix.mul_assoc]

/-- Right multiplication by a matrix of the tensor flips the parity. -/
lemma majumdarGhosh_parity_mul_right {ε : ℂ} {X : Matrix (Fin 3) (Fin 3) ℂ}
    (hX : majumdarGhoshGrading * X = ε • (X * majumdarGhoshGrading)) (a : Fin 2) :
    majumdarGhoshGrading * (X * majumdarGhoshTensor a) =
      (-ε) • (X * majumdarGhoshTensor a * majumdarGhoshGrading) := by
  rw [← Matrix.mul_assoc, hX, Matrix.smul_mul, Matrix.mul_assoc, majumdarGhoshGrading_mul,
    Matrix.mul_smul, smul_smul, mul_neg_one, ← Matrix.mul_assoc]

lemma majumdarGhosh_parity_sub {ε : ℂ} {X Y : Matrix (Fin 3) (Fin 3) ℂ}
    (hX : majumdarGhoshGrading * X = ε • (X * majumdarGhoshGrading))
    (hY : majumdarGhoshGrading * Y = ε • (Y * majumdarGhoshGrading)) :
    majumdarGhoshGrading * (X - Y) = ε • ((X - Y) * majumdarGhoshGrading) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, smul_sub, hX, hY]

/-- Conjugating the boundary matrix by the grading multiplies \(\Gamma_K\) by
\((-1)^K\). -/
lemma majumdarGhosh_groundSpaceMap_conj (K : ℕ) (X : Matrix (Fin 3) (Fin 3) ℂ) :
    groundSpaceMap majumdarGhoshTensor K (majumdarGhoshGrading * X * majumdarGhoshGrading) =
      (-1 : ℂ) ^ K • groundSpaceMap majumdarGhoshTensor K X := by
  ext σ
  simp only [groundSpaceMap_apply, Pi.smul_apply, smul_eq_mul]
  have hW := majumdarGhoshGrading_mul_evalWord (List.ofFn σ)
  rw [List.length_ofFn] at hW
  set W := Kraus.evalWord majumdarGhoshTensor (List.ofFn σ)
  set G := majumdarGhoshGrading
  calc Matrix.trace (W * (G * X * G)) = Matrix.trace (G * (W * G * X)) := by
        rw [Matrix.trace_mul_comm G]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((-1 : ℂ) ^ K • (W * G)) * G * X) := by
        rw [← hW]; simp only [Matrix.mul_assoc]
    _ = (-1 : ℂ) ^ K * Matrix.trace (W * X) := by
        rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc W G G,
          majumdarGhoshGrading_mul_self, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- Every vector of the local space \(\mathcal G_K\) is \(\Gamma_K(X)\) for a
boundary matrix of parity \((-1)^K\). -/
lemma majumdarGhosh_exists_parity_rep {K : ℕ} {ψ : NSiteSpace 2 K}
    (hψ : ψ ∈ groundSpace majumdarGhoshTensor K) :
    ∃ X : Matrix (Fin 3) (Fin 3) ℂ,
      majumdarGhoshGrading * X = (-1 : ℂ) ^ K • (X * majumdarGhoshGrading) ∧
        groundSpaceMap majumdarGhoshTensor K X = ψ := by
  obtain ⟨X₀, rfl⟩ := hψ
  set G := majumdarGhoshGrading
  set ε : ℂ := (-1) ^ K
  have hε : ε * ε = 1 := by rw [← mul_pow]; norm_num
  have hGG : G * G = 1 := majumdarGhoshGrading_mul_self
  have hGG' : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, G * (G * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hGG, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (X₀ + ε • (G * X₀ * G)), ?_, ?_⟩
  · simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc, hGG', hGG, Matrix.mul_one, smul_add, smul_smul]
    rw [show ε * (1 / 2 * ε) = 1 / 2 by linear_combination (1 / 2 : ℂ) * hε]
    rw [add_comm, mul_comm ε (1 / 2)]
  · rw [map_smul, map_add, map_smul, majumdarGhosh_groundSpaceMap_conj, smul_smul, hε,
      one_smul, ← two_smul ℂ, smul_smul]
    norm_num

/-- The entries of an odd boundary matrix vanish on the diagonal blocks. -/
lemma majumdarGhosh_entries_of_odd {X : Matrix (Fin 3) (Fin 3) ℂ}
    (h : majumdarGhoshGrading * X = -(X * majumdarGhoshGrading)) :
    X 0 0 = 0 ∧ X 1 1 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0 ∧ X 2 2 = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e21 := e 2 1
  have e22 := e 2 2
  simp only [majumdarGhoshGrading, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_zero, Fin.sum_univ_three, one_mul, cons_val_one, zero_mul,
    add_zero, Matrix.cons_val, Matrix.neg_apply, mul_one, mul_zero, neg_mul, zero_add, mul_neg,
    neg_neg] at e00 e11 e12 e21 e22
  exact ⟨by linear_combination e00 / 2, by linear_combination -e11 / 2,
    by linear_combination -e12 / 2, by linear_combination -e21 / 2,
    by linear_combination -e22 / 2⟩

/-- The entries of an even boundary matrix vanish off the diagonal blocks. -/
lemma majumdarGhosh_entries_of_even {X : Matrix (Fin 3) (Fin 3) ℂ}
    (h : majumdarGhoshGrading * X = X * majumdarGhoshGrading) :
    X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 1 0 = 0 ∧ X 2 0 = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e20 := e 2 0
  simp only [majumdarGhoshGrading, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
    cons_val_fin_one, cons_val_one, cons_val_zero, Fin.sum_univ_three, zero_mul, neg_mul,
    one_mul, zero_add, Matrix.cons_val, add_zero, mul_one, mul_zero, mul_neg] at e01 e02 e10 e20
  exact ⟨by linear_combination e01 / 2, by linear_combination e02 / 2,
    by linear_combination -e10 / 2, by linear_combination -e20 / 2⟩

/-! ### Graded injectivity of the boundary map -/

/-- Project result: for \(K\ge3\), the boundary map \(\Gamma_K\) of
`majumdarGhoshTensor` is injective on boundary matrices of parity \((-1)^K\).
The words of length three span the odd matrices; longer lengths follow from the
left-canonical equation. -/
theorem majumdarGhosh_eq_zero_of_groundSpaceMap_eq_zero {K : ℕ} (hK : 3 ≤ K)
    {X : Matrix (Fin 3) (Fin 3) ℂ}
    (hpar : majumdarGhoshGrading * X = (-1 : ℂ) ^ K • (X * majumdarGhoshGrading))
    (h0 : groundSpaceMap majumdarGhoshTensor K X = 0) : X = 0 := by
  induction K, hK using Nat.le_induction generalizing X with
  | base =>
    have hs := Complex.invSqrtTwo_ne_zero
    rw [show ((-1 : ℂ) ^ 3) = -1 by norm_num, neg_one_smul] at hpar
    obtain ⟨e00, e11, e12, e21, e22⟩ := majumdarGhosh_entries_of_odd hpar
    have c1 := congrFun h0 ![0, 0, 1]
    have c2 := congrFun h0 ![1, 0, 0]
    have c3 := congrFun h0 ![0, 1, 1]
    have c4 := congrFun h0 ![1, 1, 0]
    simp only [groundSpaceMap_three_apply, Pi.zero_apply, majumdarGhoshTensor,
      Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      Matrix.tail_cons] at c1 c2 c3 c4
    have x02 : X 0 2 = 0 := mul_left_cancel₀ (pow_ne_zero 2 hs) (by linear_combination -c1)
    have x10 : X 1 0 = 0 := mul_left_cancel₀ hs (by linear_combination c2)
    have x20 : X 2 0 = 0 := mul_left_cancel₀ hs (by linear_combination -c3)
    have x01 : X 0 1 = 0 := mul_left_cancel₀ (pow_ne_zero 2 hs) (by linear_combination -c4)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e11, e12, e21, e22, x01, x02, x10, x20]
  | succ K hK ih =>
    have hA : ∀ a : Fin 2, majumdarGhoshTensor a * X = 0 := by
      intro a
      apply ih
      · rw [majumdarGhosh_parity_mul_left hpar a, pow_succ]; simp
      · ext σ
        have := congrFun h0 (Fin.snoc σ a)
        rw [groundSpaceMap_apply, evalWord_ofFn_snoc, Matrix.mul_assoc] at this
        simpa [groundSpaceMap_apply] using this
    calc X = ((majumdarGhoshTensor 0)ᴴ * majumdarGhoshTensor 0 +
          (majumdarGhoshTensor 1)ᴴ * majumdarGhoshTensor 1) * X := by
          rw [majumdarGhosh_left_canonical, Matrix.one_mul]
      _ = 0 := by
          rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hA 0, hA 1, Matrix.mul_zero,
            Matrix.mul_zero, add_zero]

/-! ### The intersection property -/

private lemma snoc_vec_three (a b c e : Fin 2) :
    (Fin.snoc (![a, b, c] : Fin 3 → Fin 2) e : Fin 4 → Fin 2) = ![a, b, c, e] := by
  ext k
  fin_cases k <;> rfl

private lemma cons_vec_three (a b c e : Fin 2) :
    (Fin.cons a (![b, c, e] : Fin 3 → Fin 2) : Fin 4 → Fin 2) = ![a, b, c, e] := rfl

private lemma groundSpaceMap_four_apply (X : Matrix (Fin 3) (Fin 3) ℂ) (a b c e : Fin 2) :
    groundSpaceMap majumdarGhoshTensor 4 X ![a, b, c, e] =
      Matrix.trace (majumdarGhoshTensor a * (majumdarGhoshTensor b *
        (majumdarGhoshTensor c * (majumdarGhoshTensor e * X)))) := by
  simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, Matrix.mul_assoc]

/-- The four coordinate conditions of a three-site vector of \(\mathcal G_3\). -/
private lemma majumdarGhosh_coords_of_mem {v : NSiteSpace 2 3}
    (hv : v ∈ groundSpace majumdarGhoshTensor 3) :
    v ![0, 0, 0] = 0 ∧ v ![1, 1, 1] = 0 ∧
      v ![0, 0, 1] + v ![0, 1, 0] + v ![1, 0, 0] = 0 ∧
      v ![0, 1, 1] + v ![1, 0, 1] + v ![1, 1, 0] = 0 := by
  rw [majumdarGhosh_groundSpace_three_eq_eigenspace, Module.End.mem_eigenspace_iff] at hv
  exact (majumdarGhoshTerm_eigen_iff_coords v).mp hv

/-- The intersection property at three sites, by a computation on the sixteen
coordinates of a four-site vector. -/
private lemma majumdarGhosh_mem_groundSpace_four {ψ : NSiteSpace 2 (3 + 1)}
    (hL : ∀ b : Fin 2, restrictLast ψ b ∈ groundSpace majumdarGhoshTensor 3)
    (hR : ∀ a : Fin 2, restrictFirst ψ a ∈ groundSpace majumdarGhoshTensor 3) :
    ψ ∈ groundSpace majumdarGhoshTensor (3 + 1) := by
  obtain ⟨hL0a, hL0b, hL0c, hL0d⟩ := majumdarGhosh_coords_of_mem (hL 0)
  obtain ⟨hL1a, hL1b, hL1c, hL1d⟩ := majumdarGhosh_coords_of_mem (hL 1)
  obtain ⟨hR0a, hR0b, hR0c, hR0d⟩ := majumdarGhosh_coords_of_mem (hR 0)
  simp only [restrictLast_apply, restrictFirst_apply, snoc_vec_three,
    cons_vec_three] at hL0a hL0b hL0c hL0d hL1a hL1b hL1c hL1d hR0a hR0b hR0c hR0d
  have hs := Complex.invSqrtTwo_mul_self
  refine ⟨!![-2 * ψ ![0, 1, 1, 0], 0, 0; 0, -2 * ψ ![1, 1, 0, 0], 2 * ψ ![0, 1, 0, 0];
    0, 2 * ψ ![1, 0, 1, 1], -2 * ψ ![0, 0, 1, 1]], ?_⟩
  ext σ
  rw [Matrix.eq_vecCons_fin_four σ]
  generalize σ 0 = a, σ 1 = b, σ 2 = c, σ 3 = e
  rw [groundSpaceMap_four_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp only [Fin.zero_eta, Fin.mk_one, majumdarGhoshTensor, Matrix.trace_fin_three,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons]
  · linear_combination -hL0a
  · linear_combination -hL1a
  · linear_combination hL1a - hR0c + (-2*ψ ![0, 1, 0, 0]) * hs
  · linear_combination (2*ψ ![0, 0, 1, 1]) * hs
  · linear_combination (2*ψ ![0, 1, 0, 0]) * hs
  · linear_combination -hR0d + (-2*ψ ![0, 0, 1, 1] - 2*ψ ![0, 1, 1, 0]) * hs
  · linear_combination (2*ψ ![0, 1, 1, 0]) * hs
  · linear_combination -hR0b
  · linear_combination -hL0c - hL1a + hR0c
  · linear_combination -hL1c + hR0d + (2*ψ ![0, 1, 1, 0]) * hs
  · linear_combination -hL0d + (-2*ψ ![0, 1, 1, 0] - 2*ψ ![1, 1, 0, 0]) * hs
  · linear_combination (2*ψ ![1, 0, 1, 1]) * hs
  · linear_combination (2*ψ ![1, 1, 0, 0]) * hs
  · linear_combination -hL1d + hR0b + (-2*ψ ![1, 0, 1, 1]) * hs
  · linear_combination -hL0b
  · linear_combination -hL1b

/-- The intersection property from four sites on: the overlap comparison of
the two restrictions is decided by graded injectivity at \(M-1\ge3\) sites,
and the left-canonical equation grows the boundary matrix back. -/
private lemma majumdarGhosh_mem_groundSpace_succ {M : ℕ} (hM : 4 ≤ M)
    {ψ : NSiteSpace 2 (M + 1)}
    (hL : ∀ b : Fin 2, restrictLast ψ b ∈ groundSpace majumdarGhoshTensor M)
    (hR : ∀ a : Fin 2, restrictFirst ψ a ∈ groundSpace majumdarGhoshTensor M) :
    ψ ∈ groundSpace majumdarGhoshTensor (M + 1) := by
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  choose Y hYpar hY using fun a => majumdarGhosh_exists_parity_rep (hR a)
  choose Z hZpar hZ using fun b => majumdarGhosh_exists_parity_rep (hL b)
  refine mem_groundSpace_succ_of_intertwine (Z := Z) (fun j => (majumdarGhoshTensor j)ᴴ)
    (by simpa [Fin.sum_univ_two] using majumdarGhosh_left_canonical) (fun i => (hY i).symm)
    fun i j => ?_
  rw [← sub_eq_zero]
  apply majumdarGhosh_eq_zero_of_groundSpaceMap_eq_zero (K := K) (by omega)
  · have h1 := majumdarGhosh_parity_mul_left (hYpar i) j
    have h2 := majumdarGhosh_parity_mul_right (hZpar j) i
    rw [pow_succ, mul_neg_one, neg_neg] at h1 h2
    exact majumdarGhosh_parity_sub h1 h2
  · rw [map_sub, groundSpaceMap_mul_eq_of_restrict (fun i => (hY i).symm) (fun j => (hZ j).symm),
      sub_self]

/-- Project result: the intersection property of the local spaces of
`majumdarGhoshTensor` from three sites on,
\((\mathcal G_M\otimes\mathbb C^2)\cap(\mathbb C^2\otimes\mathcal G_M)
=\mathcal G_{M+1}\) for \(M\ge3\). The tensor is not normal, so the general
intersection property of arXiv:2011.12127, Section IV.C, lines 2013--2078,
does not apply. -/
theorem majumdarGhosh_groundSpace_intersection {M : ℕ} (hM : 3 ≤ M) :
    ((⨅ b : Fin 2, (groundSpace majumdarGhoshTensor M).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin 2, (groundSpace majumdarGhoshTensor M).comap (restrictFirstₗ a))) =
      groundSpace majumdarGhoshTensor (M + 1) := by
  apply le_antisymm
  · intro ψ hψ
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hψ
    obtain ⟨hL, hR⟩ := hψ
    rcases (show M = 3 ∨ 4 ≤ M by omega) with rfl | hM4
    · exact majumdarGhosh_mem_groundSpace_four hL hR
    · exact majumdarGhosh_mem_groundSpace_succ hM4 hL hR
  · intro ψ hψ
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
    exact ⟨groundSpace_inLeftGround _ M hψ, groundSpace_inRightGround _ M hψ⟩

/-- Project result: on a ring of \(N\ge3\) sites, every vector of the periodic
three-site chain ground space of `majumdarGhoshTensor` lies in the open-chain
local space \(\mathcal G_N\). -/
theorem majumdarGhosh_chainGroundSpace_le_groundSpace {N : ℕ} (hN3 : 3 ≤ N) :
    chainGroundSpace majumdarGhoshTensor 3 N ≤ groundSpace majumdarGhoshTensor N := by
  intro ψ hψ
  have hN : 0 < N := by omega
  rw [chainGroundSpace, dite_eq_left ⟨hN, hN3⟩] at hψ
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ
  refine contiguous_mem_of_restriction_intersection_submodules (groundSpace majumdarGhoshTensor)
    (by norm_num) hN3 (fun M hM => majumdarGhosh_groundSpace_intersection hM) ?_
  intro s hs τ
  rw [← cyclicRestrictₗ_eq_contiguousRestrictₗ hN hN3
    (show (⟨s, by omega⟩ : Fin N).val + 3 ≤ N from hs)]
  exact hψ ⟨s, by omega⟩ τ

/-! ### Closing the ring -/

/-- Comparing a vector of the periodic chain ground space with its translate by
one site: the two parity representatives intertwine every matrix of the tensor. -/
private lemma majumdarGhosh_exists_intertwine {n : ℕ} (hn : 3 ≤ n)
    {ψ : NSiteSpace 2 (n + 1)} (hψ : ψ ∈ chainGroundSpace majumdarGhoshTensor 3 (n + 1))
    {X : Matrix (Fin 3) (Fin 3) ℂ}
    (hXpar : majumdarGhoshGrading * X = (-1 : ℂ) ^ (n + 1) • (X * majumdarGhoshGrading))
    (hX : groundSpaceMap majumdarGhoshTensor (n + 1) X = ψ) :
    ∃ Y : Matrix (Fin 3) (Fin 3) ℂ,
      majumdarGhoshGrading * Y = (-1 : ℂ) ^ (n + 1) • (Y * majumdarGhoshGrading) ∧
      groundSpaceMap majumdarGhoshTensor (n + 1) Y =
        cyclicTranslateState (⟨n, by omega⟩ : Fin (n + 1)) ψ ∧
      ∀ a : Fin 2, X * majumdarGhoshTensor a = majumdarGhoshTensor a * Y := by
  have hT := cyclicTranslateState_mem_chainGroundSpace majumdarGhoshTensor (by omega)
    (by omega) (⟨n, by omega⟩ : Fin (n + 1)) hψ
  obtain ⟨Y, hYpar, hY⟩ :=
    majumdarGhosh_exists_parity_rep (majumdarGhosh_chainGroundSpace_le_groundSpace (by omega) hT)
  refine ⟨Y, hYpar, hY, fun a => ?_⟩
  rw [← sub_eq_zero]
  apply majumdarGhosh_eq_zero_of_groundSpaceMap_eq_zero (K := n) hn
  · have h1 := majumdarGhosh_parity_mul_right hXpar a
    have h2 := majumdarGhosh_parity_mul_left hYpar a
    rw [pow_succ, mul_neg_one, neg_neg] at h1 h2
    exact majumdarGhosh_parity_sub h1 h2
  · rw [map_sub, groundSpaceMap_mul_eq_of_cyclicTranslate_groundSpaceMap_eq X Y
      (by rw [hX, hY]) a, sub_self]

/-- An even boundary matrix intertwined with an even one by both matrices of the
tensor is \(\operatorname{diag}(x,y,y)=\tfrac{x+y}2\,1+\tfrac{x-y}2\,G\). -/
private lemma majumdarGhosh_eq_of_intertwine_even {X Y : Matrix (Fin 3) (Fin 3) ℂ}
    (hX : majumdarGhoshGrading * X = X * majumdarGhoshGrading)
    (h : ∀ a : Fin 2, X * majumdarGhoshTensor a = majumdarGhoshTensor a * Y) :
    X = ((X 0 0 + X 1 1) / 2) • (1 : Matrix (Fin 3) (Fin 3) ℂ) +
      ((X 0 0 - X 1 1) / 2) • majumdarGhoshGrading := by
  have hs := Complex.invSqrtTwo_ne_zero
  have x12 := congrFun (congrFun (h 0) 1) 0
  have x22 := congrFun (congrFun (h 0) 2) 0
  have x11 := congrFun (congrFun (h 1) 1) 0
  have x21 := congrFun (congrFun (h 1) 2) 0
  obtain ⟨x01, x02, x10, x20⟩ := majumdarGhosh_entries_of_even hX
  simp only [majumdarGhoshTensor, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons] at x12 x22 x11 x21
  have hx12 : X 1 2 = 0 := mul_left_cancel₀ hs (by linear_combination x12)
  have hx21 : X 2 1 = 0 := mul_left_cancel₀ hs (by linear_combination -x21)
  have hx : X 2 2 = X 1 1 := mul_left_cancel₀ hs (by linear_combination x22 + x11)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majumdarGhoshGrading, hx12, hx21, x01, x02, x10, x20, hx] <;> ring

/-- On an even ring, \(\Gamma_N(\alpha\,1+\beta\,G)\) is
\((\alpha+\beta)\) times the first covering plus \((\alpha-\beta)\) times the
second. -/
private lemma majumdarGhosh_groundSpaceMap_one_grading {N : ℕ} (hN : Even N) (hNpos : 0 < N)
    (α β : ℂ) :
    groundSpaceMap majumdarGhoshTensor N (α • 1 + β • majumdarGhoshGrading) =
      (α + β) • (pairCoveringEven majumdarGhoshSinglet : NSiteSpace 2 N) +
        (α - β) • pairCoveringOdd majumdarGhoshSinglet := by
  ext σ
  have hmpv := majumdarGhosh_mpv_eq_pairCovering hN hNpos σ
  rw [mpv_eq, coeff_eq] at hmpv
  have htw := majumdarGhosh_twisted_eq hN hNpos σ
  simp only [groundSpaceMap_apply, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  rw [hmpv, htw]
  ring

/-! ### The ground space -/

/-- Project result, the two-fold dimer degeneracy of the range-three parent
Hamiltonian of `majumdarGhoshTensor`: on an even ring of \(N\ge4\) sites the
periodic three-site chain ground space is spanned by the two nearest-neighbour
singlet coverings \((1,2)(3,4)\cdots(N-1,N)\) and \((2,3)(4,5)\cdots(N,1)\).
These are the two coverings of arXiv:2011.12127,
`Papers/2011.12127/TN-Review-main.tex` lines 2399–2401; the review does not
state the dimension of the ground space. -/
theorem majumdarGhosh_chainGroundSpace_eq_span {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    chainGroundSpace majumdarGhoshTensor 3 N =
      Submodule.span ℂ {pairCoveringEven majumdarGhoshSinglet,
        pairCoveringOdd majumdarGhoshSinglet} := by
  apply le_antisymm
  · intro ψ hψ
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    obtain ⟨X, hXpar, hX⟩ :=
      majumdarGhosh_exists_parity_rep (majumdarGhosh_chainGroundSpace_le_groundSpace (by omega) hψ)
    obtain ⟨Y, -, -, hXY⟩ := majumdarGhosh_exists_intertwine (by omega) hψ hXpar hX
    rw [hN.neg_one_pow, one_smul] at hXpar
    rw [Submodule.mem_span_pair, ← hX, majumdarGhosh_eq_of_intertwine_even hXpar hXY,
      majumdarGhosh_groundSpaceMap_one_grading hN (by omega)]
    exact ⟨_, _, rfl⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨majumdarGhosh_pairCoveringEven_mem_chainGroundSpace hN (by omega) (by omega),
      majumdarGhosh_pairCoveringOdd_mem_chainGroundSpace hN (by omega) (by omega)⟩

/-- Project result: on an even ring of \(N\ge4\) sites the kernel of the
range-three parent Hamiltonian of `majumdarGhoshTensor` (arXiv:quant-ph/0608197,
Section 5) is spanned by the two nearest-neighbour singlet coverings. -/
theorem majumdarGhosh_ker_parentHamiltonian_eq_span {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    LinearMap.ker (parentHamiltonian majumdarGhoshTensor 3 N) =
      Submodule.span ℂ {pairCoveringEven majumdarGhoshSinglet,
        pairCoveringOdd majumdarGhoshSinglet} := by
  rw [ker_parentHamiltonian_eq_chainGroundSpace _ (by omega) (by omega),
    majumdarGhosh_chainGroundSpace_eq_span hN hN4]

/-- Project result: on an even ring of \(N\ge4\) sites the two singlet coverings
are linearly independent. -/
theorem majumdarGhosh_pairCovering_linearIndependent {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    LinearIndependent ℂ ![(pairCoveringEven majumdarGhoshSinglet : NSiteSpace 2 N),
      pairCoveringOdd majumdarGhoshSinglet] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  set M : Matrix (Fin 3) (Fin 3) ℂ :=
    ((a + b) / 2) • (1 : Matrix (Fin 3) (Fin 3) ℂ) + ((a - b) / 2) • majumdarGhoshGrading
  have hΓ : groundSpaceMap majumdarGhoshTensor N M = 0 := by
    rw [majumdarGhosh_groundSpaceMap_one_grading hN (by omega), ← hab]
    congr 1 <;> congr 1 <;> ring
  have hpar : majumdarGhoshGrading * M = (-1 : ℂ) ^ N • (M * majumdarGhoshGrading) := by
    rw [hN.neg_one_pow, one_smul]
    simp only [M, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hM := majumdarGhosh_eq_zero_of_groundSpaceMap_eq_zero (by omega) hpar hΓ
  have h00 := congrFun (congrFun hM 0) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp only [M, majumdarGhoshGrading, smul_of, smul_cons, smul_eq_mul, mul_one, mul_zero,
    Matrix.smul_empty, mul_neg, Fin.isValue, Matrix.add_apply, Matrix.smul_apply, one_apply_eq,
    of_apply, cons_val', cons_val_zero, cons_val_fin_one, Matrix.zero_apply,
    cons_val_one] at h00 h11
  exact ⟨by linear_combination h00, by linear_combination h11⟩

/-- Project result: on an even ring of \(N\ge4\) sites the periodic three-site
chain ground space of `majumdarGhoshTensor` is two-dimensional. -/
theorem majumdarGhosh_finrank_chainGroundSpace {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    Module.finrank ℂ (chainGroundSpace majumdarGhoshTensor 3 N) = 2 := by
  rw [majumdarGhosh_chainGroundSpace_eq_span hN hN4, ← Matrix.range_cons_cons_empty _ _ ![],
    finrank_span_eq_card (majumdarGhosh_pairCovering_linearIndependent hN hN4)]
  simp

/-- An odd boundary matrix intertwined with an odd one by both matrices of the
tensor has vanishing entries in rows `1, 2`, and its partner has vanishing
entries in row `0`. -/
private lemma majumdarGhosh_entries_of_intertwine_odd {X Y : Matrix (Fin 3) (Fin 3) ℂ}
    (h : ∀ a : Fin 2, X * majumdarGhoshTensor a = majumdarGhoshTensor a * Y) :
    X 1 0 = 0 ∧ X 2 0 = 0 ∧ Y 0 1 = 0 ∧ Y 0 2 = 0 ∧
      Y 1 0 = Complex.invSqrtTwo * X 0 2 ∧ Y 2 0 = -(Complex.invSqrtTwo * X 0 1) := by
  have hs := Complex.invSqrtTwo_ne_zero
  have a11 := congrFun (congrFun (h 0) 1) 1
  have a22 := congrFun (congrFun (h 0) 2) 2
  have a00 := congrFun (congrFun (h 0) 0) 0
  have b22 := congrFun (congrFun (h 1) 2) 2
  have b11 := congrFun (congrFun (h 1) 1) 1
  have b00 := congrFun (congrFun (h 1) 0) 0
  simp only [majumdarGhoshTensor, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons] at a11 a22 a00 b22 b11 b00
  exact ⟨by linear_combination a11, by linear_combination b22,
    mul_left_cancel₀ hs (by linear_combination b11),
    mul_left_cancel₀ hs (by linear_combination -a22),
    by linear_combination -a00, by linear_combination -b00⟩

/-- Project result: on an odd ring of \(N\ge5\) sites the periodic three-site
chain ground space of `majumdarGhoshTensor` is zero. -/
theorem majumdarGhosh_chainGroundSpace_eq_bot_of_odd {N : ℕ} (hN : Odd N) (hN5 : 5 ≤ N) :
    chainGroundSpace majumdarGhoshTensor 3 N = ⊥ := by
  rw [eq_bot_iff]
  intro ψ hψ
  rw [Submodule.mem_bot]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨X, hXpar, hX⟩ :=
    majumdarGhosh_exists_parity_rep (majumdarGhosh_chainGroundSpace_le_groundSpace (by omega) hψ)
  obtain ⟨Y, hYpar, hY, hXY⟩ := majumdarGhosh_exists_intertwine (by omega) hψ hXpar hX
  have hT := cyclicTranslateState_mem_chainGroundSpace majumdarGhoshTensor (by omega)
    (by omega) (⟨n, by omega⟩ : Fin (n + 1)) hψ
  obtain ⟨Z, -, -, hYZ⟩ := majumdarGhosh_exists_intertwine (by omega) hT hYpar hY
  rw [hN.neg_one_pow] at hXpar hYpar
  obtain ⟨-, -, hY01, hY02, hY10, hY20⟩ := majumdarGhosh_entries_of_intertwine_odd hXY
  obtain ⟨hY10', hY20', -, -, -, -⟩ := majumdarGhosh_entries_of_intertwine_odd hYZ
  obtain ⟨hX10, hX20, -, -, -, -⟩ := majumdarGhosh_entries_of_intertwine_odd hXY
  have hs := Complex.invSqrtTwo_ne_zero
  have hX02 : X 0 2 = 0 := mul_left_cancel₀ hs (by linear_combination hY10' - hY10)
  have hX01 : X 0 1 = 0 := mul_left_cancel₀ hs (by linear_combination hY20 - hY20')
  rw [neg_one_smul] at hXpar
  obtain ⟨e00, e11, e12, e21, e22⟩ := majumdarGhosh_entries_of_odd hXpar
  have hX0 : X = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e11, e12, e21, e22, hX01, hX02, hX10, hX20]
  rw [← hX, hX0, map_zero]

end MPSTensor

end
