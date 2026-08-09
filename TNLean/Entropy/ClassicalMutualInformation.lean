/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.Rank
import TNLean.Analysis.ProbabilityEntropy

/-!
# Mutual information of a finite joint distribution

For a nonnegative real matrix of total mass one, this file defines the row and column
marginals, Shannon entropy, and classical mutual information. It proves that the mutual
information is at most the logarithm of the ordinary real matrix rank.

The proof follows Riazanov--Vyalyi, Theorem 4.1. A linear dependence among the nonzero rows
gives two admissible row rescalings. For
$$
\begin{aligned}
P^{\varepsilon}_{x,y} &= (1 + \varepsilon\beta_x)P_{x,y},\\
I(P^{\varepsilon}) &= I(P) + \varepsilon S(\beta).
\end{aligned}
$$
Here
$$
S(\beta)=\sum_x\beta_x\left(h(p_x)-\sum_y h(P_{x,y})\right),
$$
where $h(t)=-t\log t$ with $h(0)=0$, and $p_x=\sum_y P_{x,y}$ is the row
marginal.
If $S(\beta)\geq 0$, the nonnegative endpoint is chosen; otherwise the nonpositive endpoint is
chosen. Thus $\varepsilon S(\beta)\geq 0$, and the selected endpoint removes a row without
decreasing mutual information. Repetition leaves at most $\operatorname{rank}_{\mathbb{R}}P$
nonzero rows, after which the Shannon entropy bound applies.

All logarithms are natural. Thus the final inequality is equivalent to the base-two form
$2^{I(X:Y)}\leq\operatorname{rank}_{\mathbb{R}}P$ in the source.

## Main definitions

* `Matrix.IsJointDistribution`: a finite nonnegative matrix of total mass one.
* `Entropy.probabilityEntropy`: Shannon entropy in natural units.
* `Entropy.classicalMutualInformation`: mutual information of a joint probability matrix.

## Main statement

* `Entropy.classicalMutualInformation_le_log_rank`: mutual information is at most the
  logarithm of the ordinary real matrix rank.

## References

* A. Riazanov and M. Vyalyi, *Exploring the bounds on the positive semidefinite rank*,
  arXiv:1704.06507, Theorem 4.1.
-/

open scoped BigOperators

namespace Matrix

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A matrix is a joint distribution if its entries are nonnegative and have total sum one.

Source: arXiv:1704.06507, Section 4.2, immediately before Theorem 4.1. -/
def IsJointDistribution (P : Matrix X Y ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ ∑ x, ∑ y, P x y = 1

/-- The marginal distribution on the row index. -/
noncomputable def rowMarginal (P : Matrix X Y ℝ) (x : X) : ℝ :=
  ∑ y, P x y

/-- The marginal distribution on the column index. -/
noncomputable def columnMarginal (P : Matrix X Y ℝ) (y : Y) : ℝ :=
  ∑ x, P x y

/-- The set of rows which are not identically zero. -/
private noncomputable def nonzeroRows (P : Matrix X Y ℝ) : Finset X :=
  Finset.univ.filter fun x ↦ P.row x ≠ 0

/-- Rescale each row of a matrix by a prescribed real number. -/
private noncomputable def scaleRows (c : X → ℝ) (P : Matrix X Y ℝ) : Matrix X Y ℝ :=
  fun x y ↦ c x * P x y

/-- The row rescaling `P^ε_x = (1 + ε β_x) P_x` used in the proof of the
Riazanov--Vyalyi bound. -/
private noncomputable def rowPerturbation
    (P : Matrix X Y ℝ) (β : X → ℝ) (ε : ℝ) : Matrix X Y ℝ :=
  scaleRows (fun x ↦ 1 + ε * β x) P

end Matrix

namespace Entropy

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Classical mutual information in the entropy form
`I(X : Y) = H(X) + H(Y) - H(X,Y)`, with natural logarithms.

Source: arXiv:1704.06507, Section 3.1 and Section 4.2. -/
noncomputable def classicalMutualInformation (P : Matrix X Y ℝ) : ℝ :=
  probabilityEntropy (Matrix.rowMarginal P) +
    probabilityEntropy (Matrix.columnMarginal P) -
      ∑ x, ∑ y, Real.negMulLog (P x y)

/-- More nonzero rows than the rank give a nontrivial linear relation supported on those
rows. -/
private theorem exists_nontrivial_row_relation
    (P : Matrix X Y ℝ) (hcard : P.rank < P.nonzeroRows.card) :
    ∃ β : X → ℝ,
      (∀ y, ∑ x, β x * P x y = 0) ∧
      (∀ x, x ∉ P.nonzeroRows → β x = 0) ∧
      ∃ x ∈ P.nonzeroRows, β x ≠ 0 := by
  classical
  let S := P.nonzeroRows
  let A : Matrix S Y ℝ := fun x y ↦ P x.1 y
  let E : Matrix S X ℝ := fun x z ↦ if x.1 = z then 1 else 0
  have hA : A = E * P := by
    ext x y
    simp [A, E, Matrix.mul_apply]
  have hnot : ¬LinearIndependent ℝ (fun x : S ↦ P.row x.1) := by
    intro hlin
    have hrankA : A.rank ≤ P.rank := by
      rw [hA]
      exact Matrix.rank_mul_le_right E P
    have hArank : A.rank = Fintype.card S := by
      apply hlin.rank_matrix
    rw [hArank] at hrankA
    exact hcard.not_ge (by simpa [S] using hrankA)
  obtain ⟨a, ha, x, hx⟩ := Fintype.not_linearIndependent_iff.mp hnot
  let β : X → ℝ := fun z ↦ if hz : z ∈ S then a ⟨z, hz⟩ else 0
  refine ⟨β, ?_, ?_, x.1, x.2, ?_⟩
  · intro y
    have hay := congr_fun ha y
    have hwithin : ∑ z ∈ S, β z * P z y = 0 := by
      rw [← S.sum_attach]
      simpa [β, Pi.smul_apply] using hay
    rw [← hwithin]
    exact (Finset.sum_subset (Finset.subset_univ S) fun z _ hz ↦ by
      simp [β, hz]).symm
  · intro z hz
    simp [β, S, hz]
  · simp [β, x.2, hx]

/-- A nontrivial relation among nonzero rows of a nonnegative matrix has coefficients of
both signs. -/
private theorem row_relation_has_both_signs
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) (β : X → ℝ)
    (hrel : ∀ y, ∑ x, β x * P x y = 0)
    (hsupp : ∀ x, x ∉ P.nonzeroRows → β x = 0)
    (hne : ∃ x ∈ P.nonzeroRows, β x ≠ 0) :
    (∃ x ∈ P.nonzeroRows, β x < 0) ∧
      ∃ x ∈ P.nonzeroRows, 0 < β x := by
  classical
  obtain ⟨x, hxrow, hx⟩ := hne
  have hrow : P.row x ≠ 0 := by
    simpa [Matrix.nonzeroRows] using hxrow
  obtain ⟨y, hy⟩ : ∃ y, P x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hrow (funext h)
  have hPxy : 0 < P x y := (hP.1 x y).lt_of_ne' hy
  have hneg : ∃ z ∈ P.nonzeroRows, β z < 0 := by
    by_contra h
    push Not at h
    have hbeta_nonneg : ∀ z, 0 ≤ β z := by
      intro z
      by_cases hz : z ∈ P.nonzeroRows
      · exact h z hz
      · rw [hsupp z hz]
    have hxpos : 0 < β x := (hbeta_nonneg x).lt_of_ne' hx
    have hsumpos : 0 < ∑ z, β z * P z y := by
      apply Finset.sum_pos'
      · intro z _
        exact mul_nonneg (hbeta_nonneg z) (hP.1 z y)
      · exact ⟨x, Finset.mem_univ x, mul_pos hxpos hPxy⟩
    exact hsumpos.ne' (hrel y)
  have hpos : ∃ z ∈ P.nonzeroRows, 0 < β z := by
    by_contra h
    push Not at h
    have hbeta_nonpos : ∀ z, β z ≤ 0 := by
      intro z
      by_cases hz : z ∈ P.nonzeroRows
      · exact h z hz
      · rw [hsupp z hz]
    have hxneg : β x < 0 := (hbeta_nonpos x).lt_of_ne hx
    have hsumneg : ∑ z, β z * P z y < 0 := by
      have hlt : ∑ z, β z * P z y < ∑ _z : X, 0 := by
        apply Finset.sum_lt_sum
        · intro z _
          exact mul_nonpos_of_nonpos_of_nonneg (hbeta_nonpos z) (hP.1 z y)
        · exact ⟨x, Finset.mem_univ x, mul_neg_of_neg_of_pos hxneg hPxy⟩
      simpa using hlt
    exact hsumneg.ne (hrel y)
  exact ⟨hneg, hpos⟩

omit [Fintype X] in
/-- A row perturbation scales the corresponding row marginal by the same factor. -/
private theorem rowMarginal_rowPerturbation
    (P : Matrix X Y ℝ) (β : X → ℝ) (ε : ℝ) (x : X) :
    Matrix.rowMarginal (Matrix.rowPerturbation P β ε) x =
      (1 + ε * β x) * Matrix.rowMarginal P x := by
  simp [Matrix.rowMarginal, Matrix.rowPerturbation, Matrix.scaleRows,
    Finset.mul_sum]

omit [Fintype Y] in
/-- A row perturbation along a linear relation preserves every column marginal. -/
private theorem columnMarginal_rowPerturbation
    (P : Matrix X Y ℝ) (β : X → ℝ) (ε : ℝ)
    (hrel : ∀ y, ∑ x, β x * P x y = 0) :
    Matrix.columnMarginal (Matrix.rowPerturbation P β ε) =
      Matrix.columnMarginal P := by
  funext y
  simp only [Matrix.columnMarginal, Matrix.rowPerturbation, Matrix.scaleRows,
    add_mul, one_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hrel,
    mul_zero, add_zero]

/-- A nonnegative row perturbation of a joint distribution along a linear relation is again
a joint distribution. -/
private theorem isJointDistribution_rowPerturbation
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) (β : X → ℝ) (ε : ℝ)
    (hrel : ∀ y, ∑ x, β x * P x y = 0)
    (hnonneg : ∀ x, 0 ≤ 1 + ε * β x) :
    (Matrix.rowPerturbation P β ε).IsJointDistribution := by
  refine ⟨fun x y ↦ mul_nonneg (hnonneg x) (hP.1 x y), ?_⟩
  calc
    ∑ x, ∑ y, Matrix.rowPerturbation P β ε x y =
        ∑ y, ∑ x, Matrix.rowPerturbation P β ε x y := Finset.sum_comm
    _ = ∑ y, ∑ x, P x y := by
      apply Finset.sum_congr rfl
      intro y _
      exact congr_fun (columnMarginal_rowPerturbation P β ε hrel) y
    _ = ∑ x, ∑ y, P x y := Finset.sum_comm
    _ = 1 := hP.2

omit [Fintype X] in
/-- Row rescaling cannot increase ordinary matrix rank. -/
private theorem rank_rowPerturbation_le
    [Finite X]
    (P : Matrix X Y ℝ) (β : X → ℝ) (ε : ℝ) :
    (Matrix.rowPerturbation P β ε).rank ≤ P.rank := by
  classical
  letI := Fintype.ofFinite X
  have hfactor : Matrix.rowPerturbation P β ε =
      Matrix.diagonal (fun x ↦ 1 + ε * β x) * P := by
    ext x y
    simp [Matrix.rowPerturbation, Matrix.scaleRows, Matrix.diagonal_mul]
  rw [hfactor]
  exact Matrix.rank_mul_le_right _ P

/-- The coefficient of the affine variation of mutual information under a row
perturbation. -/
private noncomputable def rowPerturbationSlope (P : Matrix X Y ℝ) (β : X → ℝ) : ℝ :=
  ∑ x, β x *
    (Real.negMulLog (Matrix.rowMarginal P x) - ∑ y, Real.negMulLog (P x y))

/-- Mutual information is affine along a row perturbation which preserves the column
marginal.

**Local fix (arXiv:1704.06507, Theorem 4.1, Section 4.2):** The printed proof cancels the
row factor `1 + ε * β x` inside a quotient and then evaluates at an endpoint where that
factor can vanish. Here `Real.negMulLog_mul`, which remains valid at zero, replaces that
undefined quotient cancellation. The correction is documented in
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
private theorem classicalMutualInformation_rowPerturbation
    (P : Matrix X Y ℝ) (β : X → ℝ) (ε : ℝ)
    (hrel : ∀ y, ∑ x, β x * P x y = 0) :
    classicalMutualInformation (Matrix.rowPerturbation P β ε) =
      classicalMutualInformation P + ε * rowPerturbationSlope P β := by
  classical
  have hcancel :
      ∑ x, Matrix.rowMarginal P x * Real.negMulLog (1 + ε * β x) =
        ∑ x, ∑ y, P x y * Real.negMulLog (1 + ε * β x) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Matrix.rowMarginal, Finset.sum_mul]
  have hrow_expand :
      ∑ x : X, (Real.negMulLog (Matrix.rowMarginal P x) +
        ε * β x * Real.negMulLog (Matrix.rowMarginal P x)) =
      (∑ x : X, Real.negMulLog (Matrix.rowMarginal P x)) +
        ε * (∑ x : X, β x * Real.negMulLog (Matrix.rowMarginal P x)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    calc
      ∑ x : X, ε * β x * Real.negMulLog (Matrix.rowMarginal P x) =
          ∑ x : X, ε *
            (β x * Real.negMulLog (Matrix.rowMarginal P x)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = ε * (∑ x : X, β x * Real.negMulLog (Matrix.rowMarginal P x)) :=
        (Finset.mul_sum Finset.univ
          (fun x : X ↦ β x * Real.negMulLog (Matrix.rowMarginal P x)) ε).symm
  have hjoint_expand :
      ∑ x : X, ∑ y : Y,
        (Real.negMulLog (P x y) + ε * β x * Real.negMulLog (P x y)) =
      (∑ x : X, ∑ y : Y, Real.negMulLog (P x y)) +
        ε * (∑ x : X, ∑ y : Y, β x * Real.negMulLog (P x y)) := by
    calc
      ∑ x : X, ∑ y : Y,
          (Real.negMulLog (P x y) + ε * β x * Real.negMulLog (P x y)) =
          ∑ x : X, ((∑ y : Y, Real.negMulLog (P x y)) +
            ∑ y : Y, ε * β x * Real.negMulLog (P x y)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_add_distrib]
      _ = (∑ x : X, ∑ y : Y, Real.negMulLog (P x y)) +
          ∑ x : X, ∑ y : Y, ε * β x * Real.negMulLog (P x y) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ x : X, ∑ y : Y, Real.negMulLog (P x y)) +
          ε * (∑ x : X, ∑ y : Y, β x * Real.negMulLog (P x y)) := by
        congr 1
        calc
          ∑ x : X, ∑ y : Y, ε * β x * Real.negMulLog (P x y) =
              ∑ x : X, ε * (∑ y : Y, β x * Real.negMulLog (P x y)) := by
            apply Finset.sum_congr rfl
            intro x _
            simpa only [mul_comm, mul_left_comm, mul_assoc] using
              (Fintype.sum_mul_mul_eq_mul_sum_mul (R := ℝ) _ _ _)
          _ = ε * (∑ x : X, ∑ y : Y, β x * Real.negMulLog (P x y)) :=
            (Finset.mul_sum Finset.univ
              (fun x : X ↦ ∑ y : Y, β x * Real.negMulLog (P x y)) ε).symm
  have hjoint_split :
      ∑ x : X, ∑ y : Y,
        (P x y * Real.negMulLog (1 + ε * β x) +
          (1 + ε * β x) * Real.negMulLog (P x y)) =
      (∑ x : X, ∑ y : Y, P x y * Real.negMulLog (1 + ε * β x)) +
        ∑ x : X, ∑ y : Y,
          (1 + ε * β x) * Real.negMulLog (P x y) := by
    calc
      ∑ x : X, ∑ y : Y,
          (P x y * Real.negMulLog (1 + ε * β x) +
            (1 + ε * β x) * Real.negMulLog (P x y)) =
          ∑ x : X, ((∑ y : Y, P x y * Real.negMulLog (1 + ε * β x)) +
            ∑ y : Y, (1 + ε * β x) * Real.negMulLog (P x y)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_add_distrib]
      _ = (∑ x : X, ∑ y : Y, P x y * Real.negMulLog (1 + ε * β x)) +
          ∑ x : X, ∑ y : Y, (1 + ε * β x) * Real.negMulLog (P x y) := by
        rw [Finset.sum_add_distrib]
  have hbeta_sum :
      (∑ x : X, ∑ y : Y, β x * Real.negMulLog (P x y)) =
        ∑ x : X, β x * (∑ y : Y, Real.negMulLog (P x y)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
  rw [classicalMutualInformation, classicalMutualInformation,
    columnMarginal_rowPerturbation P β ε hrel]
  simp_rw [probabilityEntropy, rowMarginal_rowPerturbation,
    Matrix.rowPerturbation, Matrix.scaleRows, Real.negMulLog_mul]
  rw [Finset.sum_add_distrib, hjoint_split, hcancel]
  simp_rw [add_mul, one_mul]
  rw [hrow_expand, hjoint_expand, rowPerturbationSlope]
  simp_rw [mul_sub]
  simp only [Finset.sum_sub_distrib]
  rw [hbeta_sum]
  ring

/-- An admissible endpoint which kills a specified nonzero row and does not decrease
mutual information yields the required row-eliminated distribution. -/
private theorem exists_row_elimination_at_endpoint
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) (β : X → ℝ) (ε : ℝ) (x₀ : X)
    (hrel : ∀ y, ∑ x, β x * P x y = 0)
    (hfactor : ∀ x, 0 ≤ 1 + ε * β x) (hx₀ : x₀ ∈ P.nonzeroRows)
    (hzero : 1 + ε * β x₀ = 0)
    (hinfo : 0 ≤ ε * rowPerturbationSlope P β) :
    ∃ Q : Matrix X Y ℝ,
      Q.IsJointDistribution ∧
      Matrix.columnMarginal Q = Matrix.columnMarginal P ∧
      Q.rank ≤ P.rank ∧
      Q.nonzeroRows.card < P.nonzeroRows.card ∧
      classicalMutualInformation P ≤ classicalMutualInformation Q := by
  classical
  let Q := Matrix.rowPerturbation P β ε
  have hQ : Q.IsJointDistribution :=
    isJointDistribution_rowPerturbation P hP β ε hrel hfactor
  have hQrank : Q.rank ≤ P.rank := rank_rowPerturbation_le P β ε
  have hkill : Q.row x₀ = 0 := by
    ext y
    simp [Q, Matrix.rowPerturbation, Matrix.scaleRows, hzero]
  have hsubset : Q.nonzeroRows ⊆ P.nonzeroRows := by
    intro x hx
    have hxQ : Q.row x ≠ 0 := by
      simpa [Matrix.nonzeroRows] using hx
    have hxP : P.row x ≠ 0 := by
      intro hxP
      apply hxQ
      ext y
      have hxy : P x y = 0 := by
        simpa using congr_fun hxP y
      simp [Q, Matrix.rowPerturbation, Matrix.scaleRows, hxy]
    simpa [Matrix.nonzeroRows] using hxP
  have hQcard : Q.nonzeroRows.card < P.nonzeroRows.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
    intro heq
    have hx₀Q : x₀ ∈ Q.nonzeroRows := heq.symm ▸ hx₀
    have : Q.row x₀ ≠ 0 := by
      simpa [Matrix.nonzeroRows] using hx₀Q
    exact this hkill
  have hQinfo : classicalMutualInformation P ≤ classicalMutualInformation Q := by
    rw [classicalMutualInformation_rowPerturbation P β ε hrel]
    exact le_add_of_nonneg_right hinfo
  exact ⟨Q, hQ, columnMarginal_rowPerturbation P β ε hrel, hQrank, hQcard, hQinfo⟩

/-- One Riazanov--Vyalyi row-elimination step. If the number of nonzero rows exceeds
the ordinary real rank, there is another joint distribution with the same column marginal,
no larger rank, strictly fewer nonzero rows, and no smaller mutual information.

Source: arXiv:1704.06507, Sections 4.1--4.2, proof of Theorem 4.1. -/
private theorem exists_row_elimination
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution)
    (hcard : P.rank < P.nonzeroRows.card) :
    ∃ Q : Matrix X Y ℝ,
      Q.IsJointDistribution ∧
      Matrix.columnMarginal Q = Matrix.columnMarginal P ∧
      Q.rank ≤ P.rank ∧
      Q.nonzeroRows.card < P.nonzeroRows.card ∧
      classicalMutualInformation P ≤ classicalMutualInformation Q := by
  classical
  obtain ⟨β, hrel, hsupp, hne⟩ := exists_nontrivial_row_relation P hcard
  obtain ⟨⟨xneg, hxnegS, hxneg⟩, ⟨xpos, hxposS, hxpos⟩⟩ :=
    row_relation_has_both_signs P hP β hrel hsupp hne
  let S := P.nonzeroRows
  have hS : S.Nonempty := ⟨xpos, hxposS⟩
  let V := S.image β
  have hV : V.Nonempty := hS.image β
  let m := V.min' hV
  let M := V.max' hV
  have hm_mem : m ∈ V := by
    exact V.min'_mem hV
  have hM_mem : M ∈ V := by
    exact V.max'_mem hV
  obtain ⟨xmin, hxminS, hxmin⟩ := Finset.mem_image.mp hm_mem
  obtain ⟨xmax, hxmaxS, hxmax⟩ := Finset.mem_image.mp hM_mem
  have hm_neg : m < 0 := by
    exact (V.min'_le (β xneg) (Finset.mem_image.mpr ⟨xneg, hxnegS, rfl⟩)).trans_lt
      hxneg
  have hM_pos : 0 < M := by
    exact hxpos.trans_le
      (V.le_max' (β xpos) (Finset.mem_image.mpr ⟨xpos, hxposS, rfl⟩))
  have hm_le (x : X) : m ≤ β x := by
    by_cases hx : x ∈ S
    · exact V.min'_le (β x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · rw [hsupp x (by simpa [S] using hx)]
      exact hm_neg.le
  have hle_M (x : X) : β x ≤ M := by
    by_cases hx : x ∈ S
    · exact V.le_max' (β x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · rw [hsupp x (by simpa [S] using hx)]
      exact hM_pos.le
  by_cases hslope : 0 ≤ rowPerturbationSlope P β
  · let ε := -m⁻¹
    have hfactor : ∀ x, 0 ≤ 1 + ε * β x := by
      intro x
      have hmul := mul_le_mul_of_nonpos_left (hm_le x) (inv_nonpos.mpr hm_neg.le)
      rw [inv_mul_cancel₀ hm_neg.ne] at hmul
      dsimp [ε]
      linarith
    apply exists_row_elimination_at_endpoint P hP β ε xmin hrel hfactor hxminS
    · simp [ε, hxmin, hm_neg.ne]
    · exact mul_nonneg (by simp [ε, hm_neg.le]) hslope
  · let ε := -M⁻¹
    have hfactor : ∀ x, 0 ≤ 1 + ε * β x := by
      intro x
      have hmul := mul_le_mul_of_nonneg_left (hle_M x) (inv_nonneg.mpr hM_pos.le)
      rw [inv_mul_cancel₀ hM_pos.ne'] at hmul
      dsimp [ε]
      linarith
    apply exists_row_elimination_at_endpoint P hP β ε xmax hrel hfactor hxmaxS
    · simp [ε, hxmax, hM_pos.ne']
    · exact mul_nonneg_of_nonpos_of_nonpos
        (by simp [ε, hM_pos.le]) (le_of_not_ge hslope)

omit [Fintype X] in
/-- For a nonnegative matrix, a row has zero sum exactly when it is the zero row. -/
private theorem row_eq_zero_iff_rowMarginal_eq_zero
    (P : Matrix X Y ℝ) (hP : ∀ x y, 0 ≤ P x y) (x : X) :
    P.row x = 0 ↔ Matrix.rowMarginal P x = 0 := by
  constructor
  · intro hx
    rw [Matrix.rowMarginal]
    apply Finset.sum_eq_zero
    intro y _
    simpa using congr_fun hx y
  · intro hx
    ext y
    have hle : P x y ≤ Matrix.rowMarginal P x := by
      exact Finset.single_le_sum (fun z _ ↦ hP x z) (Finset.mem_univ y)
    rw [hx] at hle
    exact le_antisymm hle (hP x y)

/-- For each column of a joint distribution, its entropy contribution is no larger than
the sum of the entropy contributions of its entries. -/
private theorem negMulLog_columnMarginal_le
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) (y : Y) :
    Real.negMulLog (Matrix.columnMarginal P y) ≤
      ∑ x, Real.negMulLog (P x y) := by
  classical
  let q := Matrix.columnMarginal P y
  have hq_nonneg : 0 ≤ q := Finset.sum_nonneg fun x _ ↦ hP.1 x y
  by_cases hq : q = 0
  · have hzero : ∀ x, P x y = 0 := by
      intro x
      have hle : P x y ≤ q := by
        exact Finset.single_le_sum (fun z _ ↦ hP.1 z y) (Finset.mem_univ x)
      rw [hq] at hle
      exact le_antisymm hle (hP.1 x y)
    simp [q, hq, hzero]
  · have hq_pos : 0 < q := hq_nonneg.lt_of_ne' hq
    have hentry_le (x : X) : P x y ≤ q := by
      exact Finset.single_le_sum (fun z _ ↦ hP.1 z y) (Finset.mem_univ x)
    have hratio_nonneg (x : X) : 0 ≤ P x y / q := div_nonneg (hP.1 x y) hq_nonneg
    have hratio_le_one (x : X) : P x y / q ≤ 1 := (div_le_one hq_pos).mpr (hentry_le x)
    have hratio_sum : ∑ x, P x y / q = 1 := by
      calc
        ∑ x, P x y / q = (∑ x, P x y) / q :=
          (Finset.sum_div Finset.univ (fun x : X ↦ P x y) q).symm
        _ = q / q := by rfl
        _ = 1 := div_self hq
    have hconditional_nonneg : 0 ≤ ∑ x, Real.negMulLog (P x y / q) := by
      exact Finset.sum_nonneg fun x _ ↦
        Real.negMulLog_nonneg (hratio_nonneg x) (hratio_le_one x)
    have hfirst :
        (∑ x, (P x y / q) * Real.negMulLog q) = Real.negMulLog q := by
      calc
        ∑ x, (P x y / q) * Real.negMulLog q =
            (∑ x, P x y / q) * Real.negMulLog q :=
          (Finset.sum_mul Finset.univ (fun x : X ↦ P x y / q) (Real.negMulLog q)).symm
        _ = Real.negMulLog q := by rw [hratio_sum, one_mul]
    have hsecond :
        (∑ x, q * Real.negMulLog (P x y / q)) =
          q * (∑ x, Real.negMulLog (P x y / q)) :=
      (Finset.mul_sum Finset.univ (fun x : X ↦ Real.negMulLog (P x y / q)) q).symm
    have hdecomp :
        (∑ x, Real.negMulLog (P x y)) =
          Real.negMulLog q + q * (∑ x, Real.negMulLog (P x y / q)) := by
      calc
        ∑ x, Real.negMulLog (P x y) =
            ∑ x, ((P x y / q) * Real.negMulLog q +
              q * Real.negMulLog (P x y / q)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← Real.negMulLog_mul]
          congr 1
          field_simp
        _ = (∑ x, (P x y / q) * Real.negMulLog q) +
            ∑ x, q * Real.negMulLog (P x y / q) := by
          rw [Finset.sum_add_distrib]
        _ = Real.negMulLog q + q * (∑ x, Real.negMulLog (P x y / q)) := by
          rw [hfirst, hsecond]
    rw [hdecomp]
    exact le_add_of_nonneg_right (mul_nonneg hq_nonneg hconditional_nonneg)

/-- The mutual information of a joint distribution is at most the entropy of its row
marginal. -/
private theorem classicalMutualInformation_le_probabilityEntropy_rowMarginal
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) :
    classicalMutualInformation P ≤ probabilityEntropy (Matrix.rowMarginal P) := by
  have hcond :
      probabilityEntropy (Matrix.columnMarginal P) ≤
        ∑ x, ∑ y, Real.negMulLog (P x y) := by
    rw [probabilityEntropy]
    calc
      ∑ y, Real.negMulLog (Matrix.columnMarginal P y) ≤
          ∑ y, ∑ x, Real.negMulLog (P x y) :=
        Finset.sum_le_sum fun y _ ↦ negMulLog_columnMarginal_le P hP y
      _ = ∑ x, ∑ y, Real.negMulLog (P x y) := Finset.sum_comm
  rw [classicalMutualInformation]
  linarith

/-- The entropy of the row marginal of a joint distribution is at most the logarithm of
the number of its nonzero rows. -/
private theorem probabilityEntropy_rowMarginal_le_log_nonzeroRows
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) :
    probabilityEntropy (Matrix.rowMarginal P) ≤ Real.log P.nonzeroRows.card := by
  have hrow_nonneg (x : X) : 0 ≤ Matrix.rowMarginal P x :=
    Finset.sum_nonneg fun y _ ↦ hP.1 x y
  have hrow_sum : ∑ x, Matrix.rowMarginal P x = 1 := by
    exact hP.2
  have hsupport :
      (Finset.univ.filter fun x ↦ Matrix.rowMarginal P x ≠ 0) = P.nonzeroRows := by
    ext x
    simp [Matrix.nonzeroRows, row_eq_zero_iff_rowMarginal_eq_zero P hP.1 x]
  rw [← hsupport]
  exact probabilityEntropy_le_log_card_support (Matrix.rowMarginal P) hrow_nonneg hrow_sum

/-- Every joint distribution has a nonzero row. -/
private theorem nonzeroRows_nonempty
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) : P.nonzeroRows.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hzero (x : X) : Matrix.rowMarginal P x = 0 := by
    rw [← row_eq_zero_iff_rowMarginal_eq_zero P hP.1 x]
    have hx : x ∉ P.nonzeroRows := by simp [h]
    simpa [Matrix.nonzeroRows] using hx
  have hsumzero : ∑ x, Matrix.rowMarginal P x = 0 :=
    Finset.sum_eq_zero fun x _ ↦ hzero x
  have hsumone : ∑ x, Matrix.rowMarginal P x = 1 := hP.2
  linarith

/-- Repeated row elimination produces a joint distribution whose number of nonzero rows
is bounded by any prescribed upper bound for the original rank. -/
private theorem exists_reduced_joint_distribution
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) (r : ℕ) (hrank : P.rank ≤ r) :
    ∃ Q : Matrix X Y ℝ,
      Q.IsJointDistribution ∧ Q.nonzeroRows.card ≤ r ∧
        classicalMutualInformation P ≤ classicalMutualInformation Q := by
  classical
  suffices hreduce : ∀ n : ℕ, ∀ P : Matrix X Y ℝ,
      P.IsJointDistribution → P.rank ≤ r → P.nonzeroRows.card = n →
        ∃ Q : Matrix X Y ℝ,
          Q.IsJointDistribution ∧ Q.nonzeroRows.card ≤ r ∧
            classicalMutualInformation P ≤ classicalMutualInformation Q by
    exact hreduce P.nonzeroRows.card P hP hrank rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro P hP hrank hn
      by_cases hcard : P.nonzeroRows.card ≤ r
      · exact ⟨P, hP, hcard, le_rfl⟩
      · have hPrank : P.rank < P.nonzeroRows.card :=
          lt_of_le_of_lt hrank (lt_of_not_ge hcard)
        obtain ⟨Q, hQ, _, hQrank, hQcard, hPQ⟩ := exists_row_elimination P hP hPrank
        obtain ⟨R, hR, hRcard, hQR⟩ :=
          ih Q.nonzeroRows.card (hn ▸ hQcard) Q hQ (hQrank.trans hrank) rfl
        exact ⟨R, hR, hRcard, hPQ.trans hQR⟩

/-- **Riazanov--Vyalyi mutual-information rank bound.** For every finite joint
probability matrix, the mutual information is at most the logarithm of its ordinary real
matrix rank.

This is Theorem 4.1 of arXiv:1704.06507. The source uses base-two logarithms and states
the equivalent inequality $2^{I(X:Y)}\leq\operatorname{rank}_{\mathbb{R}}P$; the present
statement uses the natural logarithm, as does the entropy theory in TNLean. -/
theorem classicalMutualInformation_le_log_rank
    (P : Matrix X Y ℝ) (hP : P.IsJointDistribution) :
    classicalMutualInformation P ≤ Real.log P.rank := by
  obtain ⟨Q, hQ, hQcard, hPQ⟩ :=
    exists_reduced_joint_distribution P hP P.rank le_rfl
  have hQcard_pos : 0 < Q.nonzeroRows.card := (nonzeroRows_nonempty Q hQ).card_pos
  calc
    classicalMutualInformation P ≤ classicalMutualInformation Q := hPQ
    _ ≤ probabilityEntropy (Matrix.rowMarginal Q) :=
      classicalMutualInformation_le_probabilityEntropy_rowMarginal Q hQ
    _ ≤ Real.log Q.nonzeroRows.card :=
      probabilityEntropy_rowMarginal_le_log_nonzeroRows Q hQ
    _ ≤ Real.log P.rank :=
      Real.log_le_log (by exact_mod_cast hQcard_pos) (by exact_mod_cast hQcard)

end Entropy
