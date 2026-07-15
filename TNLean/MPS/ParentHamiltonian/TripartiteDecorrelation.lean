/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.MarginalSupportAbsorption
import TNLean.Channel.Schwarz.StrongSubadditivityPosDef
import Mathlib.Data.Matrix.Basis

/-!
# Tripartite support projectors for decorrelation

This file introduces the two marginal support projectors used in the forward
direction of the decorrelation--parent-commuting-Hamiltonian equivalence for an
explicit tensor product \(H_A\otimes H_X\otimes H_B\).

## Main definitions

* `TripartiteDecorrelation.supportAX`: support projector of the \(AX\) marginal.
* `TripartiteDecorrelation.supportXB`: support projector of the \(XB\) marginal.
* `TripartiteDecorrelation.HasCommutingParentHamiltonian`: existence of local
  commuting parent projectors on \(AX\) and \(XB\).
* `TripartiteDecorrelation.liftAX` and `TripartiteDecorrelation.liftXB`: their
  local lifts to the tripartite space.

## Main results

* `TripartiteDecorrelation.liftSupportAX_mul_self` and its right-handed form.
* `TripartiteDecorrelation.liftSupportXB_mul_self` and its right-handed form.
* `TripartiteDecorrelation.IsDecorrelated.supports_mul_complement_mul_eq_zero`:
  the finite matrix-unit calculation from decorrelation.
* `TripartiteDecorrelation.supportProducts_eq`: the two support-product
  identities obtained from decorrelation.
* `TripartiteDecorrelation.parentHamiltonian_iff_decorrelated`: Proposition
  D.3 on the explicit tripartite space.

## References

* arXiv:1606.00608, Appendix D.2, lines 2187--2258.
-/

open scoped Matrix MatrixOrder ComplexOrder Kronecker
open Matrix Finset BigOperators

namespace TripartiteDecorrelation

variable {A X B : Type*} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X]
  [Fintype B] [DecidableEq B]

/-- Reassociate the tripartite index from \(A\times(X\times B)\) to
\((A\times X)\times B\). -/
private noncomputable def groupAX
    (ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ) :
    Matrix ((A × X) × B) ((A × X) × B) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc A X B).symm ρ

/-- Return from the \((A\times X)\times B\) indexing to
\(A\times(X\times B)\). -/
private noncomputable def ungroupAX
    (ρ : Matrix ((A × X) × B) ((A × X) × B) ℂ) :
    Matrix (A × (X × B)) (A × (X × B)) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc A X B) ρ

/-- Reassociation preserves positive semidefiniteness. -/
private theorem groupAX_posSemidef
    {ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ} (hρ : ρ.PosSemidef) :
    (groupAX ρ).PosSemidef := by
  simpa only [groupAX, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.posSemidef_submatrix_equiv] using
      hρ.submatrix (Equiv.prodAssoc A X B)

/-- Reassociation preserves Hermiticity. -/
private theorem groupAX_isHermitian
    {ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ} (hρ : ρ.IsHermitian) :
    (groupAX ρ).IsHermitian := by
  simpa only [groupAX, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm] using hρ.submatrix (Equiv.prodAssoc A X B)

@[simp]
private theorem ungroupAX_groupAX (ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ) :
    ungroupAX (groupAX ρ) = ρ := by
  simp [groupAX, ungroupAX]

/-- Reassociation respects matrix multiplication. -/
private theorem ungroupAX_mul
    (M N : Matrix ((A × X) × B) ((A × X) × B) ℂ) :
    ungroupAX (M * N) = ungroupAX M * ungroupAX N := by
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc A X B)) M N

/-- Lift an operator on \(A\times X\) to the tripartite space. -/
noncomputable def liftAX (M : Matrix (A × X) (A × X) ℂ) :
    Matrix (A × (X × B)) (A × (X × B)) ℂ :=
  ungroupAX (Matrix.leftKroneckerEmbed (n := B) M)

/-- Lift an operator on \(X\times B\) to the tripartite space. -/
noncomputable def liftXB (M : Matrix (X × B) (X × B) ℂ) :
    Matrix (A × (X × B)) (A × (X × B)) ℂ :=
  Matrix.rightKroneckerEmbed (m := A) M

/-- Lift an operator on the separated region \(A\) to the tripartite space. -/
noncomputable def liftA (M : Matrix A A ℂ) :
    Matrix (A × (X × B)) (A × (X × B)) ℂ :=
  Matrix.leftKroneckerEmbed (n := X × B) M

/-- Lift an operator on the separated region \(B\) to the tripartite space. -/
noncomputable def liftB (M : Matrix B B ℂ) :
    Matrix (A × (X × B)) (A × (X × B)) ℂ :=
  Matrix.rightKroneckerEmbed (m := A)
    (Matrix.rightKroneckerEmbed (m := X) M)

private theorem liftAX_mul (M N : Matrix (A × X) (A × X) ℂ) :
    liftAX (B := B) (M * N) = liftAX (B := B) M * liftAX (B := B) N := by
  rw [liftAX, liftAX, liftAX, ← ungroupAX_mul, map_mul]

private theorem liftXB_mul (M N : Matrix (X × B) (X × B) ℂ) :
    liftXB (A := A) (M * N) = liftXB (A := A) M * liftXB (A := A) N := by
  exact map_mul (Matrix.rightKroneckerEmbed (m := A) (n := X × B)) M N

private theorem liftA_comm_liftXB (OA : Matrix A A ℂ) (M : Matrix (X × B) (X × B) ℂ) :
    liftA OA * liftXB M = liftXB M * liftA OA := by
  ext ⟨a, x, b⟩ ⟨a', x', b'⟩
  simp [liftA, liftXB, Matrix.mul_apply, Matrix.leftKroneckerEmbed_apply,
    Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_comm]

private theorem liftB_comm_liftAX (OB : Matrix B B ℂ) (M : Matrix (A × X) (A × X) ℂ) :
    liftB OB * liftAX M = liftAX M * liftB OB := by
  ext ⟨a, x, b⟩ ⟨a', x', b'⟩
  simp [liftB, liftAX, ungroupAX, Matrix.mul_apply,
    Matrix.leftKroneckerEmbed_apply, Matrix.rightKroneckerEmbed_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_comm]

@[simp]
private theorem conjTranspose_liftA (M : Matrix A A ℂ) :
    (liftA (X := X) (B := B) M)ᴴ = liftA (X := X) (B := B) Mᴴ := by
  change (Matrix.leftKroneckerEmbed (n := X × B) M)ᴴ =
    Matrix.leftKroneckerEmbed (n := X × B) Mᴴ
  rw [← star_eq_conjTranspose, ← map_star, star_eq_conjTranspose]

@[simp]
private theorem conjTranspose_liftB (M : Matrix B B ℂ) :
    (liftB (A := A) (X := X) M)ᴴ = liftB (A := A) (X := X) Mᴴ := by
  change (Matrix.rightKroneckerEmbed (m := A)
      (Matrix.rightKroneckerEmbed (m := X) M))ᴴ =
    Matrix.rightKroneckerEmbed (m := A)
      (Matrix.rightKroneckerEmbed (m := X) Mᴴ)
  rw [← star_eq_conjTranspose, ← map_star, ← map_star, star_eq_conjTranspose]

/-- The reduced operator on \(AX\), obtained by tracing out \(B\). -/
noncomputable def marginalAX
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) :
    Matrix (A × X) (A × X) ℂ :=
  Matrix.partialTraceRight (groupAX P)

/-- The reduced operator on \(XB\), obtained by tracing out \(A\). -/
noncomputable def marginalXB
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) :
    Matrix (X × B) (X × B) ℂ :=
  Matrix.partialTraceLeft P

private theorem liftA_single_sandwich_apply
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) (a k a₀ a₁ : A)
    (r₀ r₁ : X × B) :
    (liftA (X := X) (B := B) (Matrix.single a k 1) * P *
        liftA (X := X) (B := B) (Matrix.single k a 1))
        (a₀, r₀) (a₁, r₁) =
      if a = a₀ ∧ a = a₁ then P (k, r₀) (k, r₁) else 0 := by
  classical
  by_cases h₀ : a = a₀ <;> by_cases h₁ : a = a₁
  · subst a₀
    subst a₁
    simp [liftA, Matrix.mul_apply, Matrix.leftKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single,
      Fintype.sum_prod_type]
  · simp [liftA, Matrix.mul_apply, Matrix.leftKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single,
      Fintype.sum_prod_type, h₁]
  · simp [liftA, Matrix.mul_apply, Matrix.leftKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single, h₀]
  · simp [liftA, Matrix.mul_apply, Matrix.leftKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single, h₀, h₁]

private theorem liftB_single_sandwich_apply
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) (b k b₀ b₁ : B)
    (a₀ a₁ : A) (x₀ x₁ : X) :
    (liftB (A := A) (X := X) (Matrix.single b k 1) * P *
        liftB (A := A) (X := X) (Matrix.single k b 1))
        (a₀, x₀, b₀) (a₁, x₁, b₁) =
      if b = b₀ ∧ b = b₁ then P (a₀, x₀, k) (a₁, x₁, k) else 0 := by
  classical
  by_cases h₀ : b = b₀ <;> by_cases h₁ : b = b₁
  · subst b₀
    subst b₁
    simp [liftB, Matrix.mul_apply, Matrix.rightKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single,
      Fintype.sum_prod_type]
  · simp [liftB, Matrix.mul_apply, Matrix.rightKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single,
      Fintype.sum_prod_type, h₁]
  · simp [liftB, Matrix.mul_apply, Matrix.rightKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single, h₀]
  · simp [liftB, Matrix.mul_apply, Matrix.rightKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.single, h₀, h₁]

/-- The lifted \(XB\) marginal is a sum of contractions of \(P\) by matrix
units on \(A\).

This is the corrected matrix-unit form of arXiv:1606.00608, Appendix D.2,
lines 2236--2250. -/
theorem lift_marginalXB_eq_sum (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) :
    liftXB (marginalXB P) =
      ∑ a : A, ∑ k : A,
        liftA (Matrix.single a k 1) * P * liftA (Matrix.single k a 1) := by
  classical
  ext ⟨a, x, b⟩ ⟨a', x', b'⟩
  by_cases haa : a = a'
  · subst a'
    simp [liftXB, marginalXB, Matrix.sum_apply, Matrix.rightKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, liftA_single_sandwich_apply]
  · simp only [liftXB, marginalXB, Matrix.rightKroneckerEmbed_apply,
      Matrix.kroneckerMap_apply, ne_eq, haa, not_false_eq_true, Matrix.one_apply_ne,
      Matrix.partialTraceLeft_apply, zero_mul, Matrix.sum_apply,
      liftA_single_sandwich_apply, Finset.sum_ite_irrel, Finset.sum_const_zero]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro h
    apply haa
    calc
      a = c := h.1.symm
      _ = a' := h.2

/-- The lifted \(AX\) marginal is a sum of contractions of \(P\) by matrix
units on \(B\).

This is the corrected matrix-unit form of arXiv:1606.00608, Appendix D.2,
lines 2236--2250. -/
theorem lift_marginalAX_eq_sum (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) :
    liftAX (marginalAX P) =
      ∑ b : B, ∑ k : B,
        liftB (Matrix.single b k 1) * P * liftB (Matrix.single k b 1) := by
  classical
  ext ⟨a, x, b⟩ ⟨a', x', b'⟩
  by_cases hbb : b = b'
  · subst b'
    simp [liftAX, marginalAX, groupAX, ungroupAX, Matrix.sum_apply,
      Matrix.leftKroneckerEmbed_apply, Matrix.kroneckerMap_apply,
      liftB_single_sandwich_apply]
  · simp only [liftAX, ungroupAX, marginalAX, groupAX, Matrix.coe_reindexAlgEquiv,
      Matrix.reindex_apply, Equiv.symm_symm, Matrix.leftKroneckerEmbed_apply,
      Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply, Matrix.kroneckerMap_apply,
      Matrix.partialTraceRight_apply, Equiv.prodAssoc_apply, ne_eq, hbb,
      not_false_eq_true, Matrix.one_apply_ne, mul_zero, Matrix.sum_apply,
      liftB_single_sandwich_apply, Finset.sum_ite_irrel, Finset.sum_const_zero]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro h
    apply hbb
    calc
      b = c := h.1.symm
      _ = b' := h.2

/-- Decorrelation of the separated regions \(A\) and \(B\) relative to a
tripartite projector \(P\).

See arXiv:1606.00608, Appendix D.2, Definition D.1, lines 2187--2191. -/
def IsDecorrelated (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) : Prop :=
  ∀ OA : Matrix A A ℂ, ∀ OB : Matrix B B ℂ,
    P * liftA OA * (1 - P) * liftB OB * P = 0

/-- The adjoint form of decorrelation, with the order of the two separated
observables reversed.

This is the second equality in arXiv:1606.00608, Appendix D.2, equation
`decorr`, lines 2194--2198. -/
theorem IsDecorrelated.reverse
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hdec : IsDecorrelated P)
    (OB : Matrix B B ℂ) (OA : Matrix A A ℂ) :
    P * liftB OB * (1 - P) * liftA OA * P = 0 := by
  have h := congrArg Matrix.conjTranspose (hdec OAᴴ OBᴴ)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, hPherm.eq,
    conjTranspose_liftA, conjTranspose_liftB, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using h

/-- Decorrelation annihilates the product of the two lifted reduced operators
through the complementary projector.

This is the matrix-unit calculation in arXiv:1606.00608, Appendix D.2,
lines 2236--2258. -/
theorem IsDecorrelated.marginals_mul_complement_mul_eq_zero
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hdec : IsDecorrelated P) :
    liftXB (marginalXB P) * (1 - P) * liftAX (marginalAX P) = 0 := by
  rw [lift_marginalXB_eq_sum, lift_marginalAX_eq_sum, Finset.sum_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro a _
  rw [Finset.sum_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro l _
  calc
    (liftA (Matrix.single a k 1) * P * liftA (Matrix.single k a 1) * (1 - P)) *
        (liftB (Matrix.single b l 1) * P * liftB (Matrix.single l b 1)) =
        liftA (Matrix.single a k 1) *
          (P * liftA (Matrix.single k a 1) * (1 - P) *
            liftB (Matrix.single b l 1) * P) *
          liftB (Matrix.single l b 1) := by noncomm_ring
    _ = 0 := by
      rw [hdec (Matrix.single k a 1) (Matrix.single b l 1), Matrix.mul_zero,
        Matrix.zero_mul]

/-- The reverse-order reduced-operator product also vanishes. -/
theorem IsDecorrelated.reverse_marginals_mul_complement_mul_eq_zero
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hdec : IsDecorrelated P) :
    liftAX (marginalAX P) * (1 - P) * liftXB (marginalXB P) = 0 := by
  rw [lift_marginalAX_eq_sum, lift_marginalXB_eq_sum, Finset.sum_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro b _
  rw [Finset.sum_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro l _
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [Matrix.mul_sum]
  apply Finset.sum_eq_zero
  intro k _
  calc
    (liftB (Matrix.single b l 1) * P * liftB (Matrix.single l b 1) * (1 - P)) *
        (liftA (Matrix.single a k 1) * P * liftA (Matrix.single k a 1)) =
        liftB (Matrix.single b l 1) *
          (P * liftB (Matrix.single l b 1) * (1 - P) *
            liftA (Matrix.single a k 1) * P) *
          liftA (Matrix.single k a 1) := by noncomm_ring
    _ = 0 := by
      rw [hdec.reverse hPherm (Matrix.single l b 1) (Matrix.single a k 1),
        Matrix.mul_zero, Matrix.zero_mul]

/-- The support projector of a Hermitian matrix also factors through the
matrix on the left. -/
private theorem supportProj_eq_mul_cfc_recip
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) :
    hM.supportProj = M * hM.cfc (fun x => if x ≠ 0 then x⁻¹ else 0) := by
  let f : ℝ → ℝ := fun x => if x ≠ 0 then x⁻¹ else 0
  calc
    hM.supportProj = hM.cfc f * M := SSAPosDef.supportProj_eq_cfc_recip_mul hM
    _ = hM.cfc f * hM.cfc id := by rw [hM.cfc_id]
    _ = hM.cfc (fun x => f x * id x) := (hM.cfc_mul f id).symm
    _ = hM.cfc (fun x => id x * f x) := by
      congr 2
      funext x
      exact mul_comm _ _
    _ = hM.cfc id * hM.cfc f := hM.cfc_mul id f
    _ = M * hM.cfc f := by rw [hM.cfc_id]

/-- The orthogonal support projector of the \(AX\) marginal.

See arXiv:1606.00608, Appendix D.2, lines 2225--2229. -/
noncomputable def supportAX
    {ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ} (hρ : ρ.IsHermitian) :
    Matrix (A × X) (A × X) ℂ :=
  (Matrix.partialTraceRight_isHermitian (groupAX_isHermitian hρ)).supportProj

/-- The orthogonal support projector of the \(XB\) marginal.

See arXiv:1606.00608, Appendix D.2, lines 2225--2229. -/
noncomputable def supportXB
    {ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ} (hρ : ρ.IsHermitian) :
    Matrix (X × B) (X × B) ℂ :=
  (Matrix.partialTraceLeft_isHermitian hρ).supportProj

/-- Decorrelation annihilates the product of the two marginal support
projectors through the orthogonal complement of \(P\).

The proof uses the matrix-unit expansions of the two reduced operators and
then factors each support projector through its reduced operator.  This
repairs the unsupported single-slice assertion in arXiv:1606.00608,
Appendix D.2, lines 2236--2252, while retaining the calculation in lines
2253--2258.

**Local fix (CPSV16 Appendix D.2):** A basis vector of a marginal support need
not be one partial contraction.  The reduced-operator expansion and
reciprocal-on-support factorization above replace that step.  Documented in
`docs/paper-gaps/cpsv16_decorrelation_slice_expansion_fix.tex`. -/
theorem IsDecorrelated.supports_mul_complement_mul_eq_zero
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hdec : IsDecorrelated P) :
    liftXB (supportXB hPherm) * (1 - P) * liftAX (supportAX hPherm) = 0 := by
  let hAX : (marginalAX P).IsHermitian := by
    exact Matrix.partialTraceRight_isHermitian (groupAX_isHermitian hPherm)
  let hXB : (marginalXB P).IsHermitian := by
    exact Matrix.partialTraceLeft_isHermitian hPherm
  let TAX := hAX.cfc (fun x => if x ≠ 0 then x⁻¹ else 0)
  let TXB := hXB.cfc (fun x => if x ≠ 0 then x⁻¹ else 0)
  have hAXfactor : supportAX hPherm = marginalAX P * TAX := by
    simpa only [supportAX, marginalAX, hAX, TAX] using
      supportProj_eq_mul_cfc_recip hAX
  have hXBfactor : supportXB hPherm = TXB * marginalXB P := by
    simpa only [supportXB, marginalXB, hXB, TXB] using
      SSAPosDef.supportProj_eq_cfc_recip_mul hXB
  rw [hXBfactor, hAXfactor, liftXB_mul, liftAX_mul]
  calc
    (liftXB TXB * liftXB (marginalXB P)) * (1 - P) *
        (liftAX (marginalAX P) * liftAX TAX) =
        liftXB TXB *
          (liftXB (marginalXB P) * (1 - P) * liftAX (marginalAX P)) *
          liftAX TAX := by noncomm_ring
    _ = 0 := by
      rw [hdec.marginals_mul_complement_mul_eq_zero, Matrix.mul_zero,
        Matrix.zero_mul]

/-- The reverse-order product of the two marginal support projectors through
the complement of \(P\) also vanishes. -/
theorem IsDecorrelated.reverse_supports_mul_complement_mul_eq_zero
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hdec : IsDecorrelated P) :
    liftAX (supportAX hPherm) * (1 - P) * liftXB (supportXB hPherm) = 0 := by
  let hAX : (marginalAX P).IsHermitian := by
    exact Matrix.partialTraceRight_isHermitian (groupAX_isHermitian hPherm)
  let hXB : (marginalXB P).IsHermitian := by
    exact Matrix.partialTraceLeft_isHermitian hPherm
  let TAX := hAX.cfc (fun x => if x ≠ 0 then x⁻¹ else 0)
  let TXB := hXB.cfc (fun x => if x ≠ 0 then x⁻¹ else 0)
  have hAXfactor : supportAX hPherm = TAX * marginalAX P := by
    simpa only [supportAX, marginalAX, hAX, TAX] using
      SSAPosDef.supportProj_eq_cfc_recip_mul hAX
  have hXBfactor : supportXB hPherm = marginalXB P * TXB := by
    simpa only [supportXB, marginalXB, hXB, TXB] using
      supportProj_eq_mul_cfc_recip hXB
  rw [hAXfactor, hXBfactor, liftAX_mul, liftXB_mul]
  calc
    (liftAX TAX * liftAX (marginalAX P)) * (1 - P) *
        (liftXB (marginalXB P) * liftXB TXB) =
        liftAX TAX *
          (liftAX (marginalAX P) * (1 - P) * liftXB (marginalXB P)) *
          liftXB TXB := by noncomm_ring
    _ = 0 := by
      rw [hdec.reverse_marginals_mul_complement_mul_eq_zero hPherm,
        Matrix.mul_zero, Matrix.zero_mul]

/-- The lifted support projector of the \(XB\) marginal fixes the tripartite
operator on the left.

This is the \(P_{XB}P_{AXB}=P_{AXB}\) identity in arXiv:1606.00608,
Appendix D.2, equation `Propproj`, lines 2228--2235. -/
theorem liftSupportXB_mul_self
    {ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ} (hρ : ρ.PosSemidef) :
    liftXB (supportXB hρ.isHermitian) * ρ = ρ := by
  exact hρ.rightKroneckerEmbed_supportProj_mul_self

/-- The lifted support projector of the \(XB\) marginal fixes the tripartite
operator on the right.

This is the \(P_{AXB}P_{XB}=P_{AXB}\) identity in arXiv:1606.00608,
Appendix D.2, equation `Propproj`, lines 2228--2235. -/
theorem mul_liftSupportXB_self
    {ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ} (hρ : ρ.PosSemidef) :
    ρ * liftXB (supportXB hρ.isHermitian) = ρ := by
  exact hρ.mul_rightKroneckerEmbed_supportProj_self

/-- The lifted support projector of the \(AX\) marginal fixes the tripartite
operator on the left.

This is the \(P_{AX}P_{AXB}=P_{AXB}\) identity in arXiv:1606.00608,
Appendix D.2, equation `Propproj`, lines 2228--2235. -/
theorem liftSupportAX_mul_self
    {ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ} (hρ : ρ.PosSemidef) :
    liftAX (supportAX hρ.isHermitian) * ρ = ρ := by
  have hgroup := (groupAX_posSemidef hρ).leftKroneckerEmbed_supportProj_mul_self
  have h := congrArg (ungroupAX (A := A) (X := X) (B := B)) hgroup
  simpa only [liftAX, supportAX, ungroupAX_mul, ungroupAX_groupAX] using h

/-- The lifted support projector of the \(AX\) marginal fixes the tripartite
operator on the right.

This is the \(P_{AXB}P_{AX}=P_{AXB}\) identity in arXiv:1606.00608,
Appendix D.2, equation `Propproj`, lines 2228--2235. -/
theorem mul_liftSupportAX_self
    {ρ : Matrix (A × (X × B)) (A × (X × B)) ℂ} (hρ : ρ.PosSemidef) :
    ρ * liftAX (supportAX hρ.isHermitian) = ρ := by
  have hgroup := (groupAX_posSemidef hρ).mul_leftKroneckerEmbed_supportProj_self
  have h := congrArg (ungroupAX (A := A) (X := X) (B := B)) hgroup
  simpa only [liftAX, supportAX, ungroupAX_mul, ungroupAX_groupAX] using h

/-- The two marginal support projectors multiply to the tripartite projector.

This is arXiv:1606.00608, Appendix D.2, equation `PXBAXetc`,
lines 2236--2258.  The proof uses reduced-operator matrix-unit expansions and
reciprocal-on-support factorization, so no commutation hypothesis is assumed. -/
theorem supportProducts_eq
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hPidem : P * P = P)
    (hdec : IsDecorrelated P) :
    liftXB (supportXB hPherm) * liftAX (supportAX hPherm) = P ∧
      liftAX (supportAX hPherm) * liftXB (supportXB hPherm) = P := by
  have hPstar : IsStarProjection P := by
    rw [isStarProjection_iff']
    exact ⟨hPidem, by simpa [Matrix.star_eq_conjTranspose] using hPherm.eq⟩
  have hPpos : P.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hPstar.nonneg
  constructor
  · calc
      liftXB (supportXB hPherm) * liftAX (supportAX hPherm) =
          liftXB (supportXB hPherm) * P * liftAX (supportAX hPherm) +
            liftXB (supportXB hPherm) * (1 - P) * liftAX (supportAX hPherm) := by
              noncomm_ring
      _ = liftXB (supportXB hPherm) * P * liftAX (supportAX hPherm) := by
        rw [hdec.supports_mul_complement_mul_eq_zero hPherm, add_zero]
      _ = P := by rw [liftSupportXB_mul_self hPpos, mul_liftSupportAX_self hPpos]
  · calc
      liftAX (supportAX hPherm) * liftXB (supportXB hPherm) =
          liftAX (supportAX hPherm) * P * liftXB (supportXB hPherm) +
            liftAX (supportAX hPherm) * (1 - P) * liftXB (supportXB hPherm) := by
              noncomm_ring
      _ = liftAX (supportAX hPherm) * P * liftXB (supportXB hPherm) := by
        rw [hdec.reverse_supports_mul_complement_mul_eq_zero hPherm, add_zero]
      _ = P := by rw [liftSupportAX_mul_self hPpos, mul_liftSupportXB_self hPpos]

/-- The parent commuting Hamiltonian condition on the explicit tripartite
space, written in terms of the local ground-space projectors.

The Hamiltonian terms of arXiv:1606.00608, Appendix D.2, Definition D.2,
lines 2205--2218, are \(Q_{AX}=1-P_{AX}\) and \(Q_{XB}=1-P_{XB}\).  For
commuting orthogonal projectors, the product identity below says exactly that
their lifted ranges intersect in the range of \(P\). -/
structure CommutingParentHamiltonian
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) where
  /-- The orthogonal projector onto \(K_{AX}\), as in arXiv:1606.00608,
  Appendix D.2, lines 2205--2215. -/
  PAX : Matrix (A × X) (A × X) ℂ
  /-- The orthogonal projector onto \(K_{XB}\), as in arXiv:1606.00608,
  Appendix D.2, lines 2205--2215. -/
  PXB : Matrix (X × B) (X × B) ℂ
  /-- The \(AX\) ground-space projector is Hermitian, corresponding to the
  projector assumption in arXiv:1606.00608, Appendix D.2, lines 2205--2208. -/
  hAXherm : PAX.IsHermitian
  /-- The \(AX\) ground-space projector is idempotent, corresponding to the
  projector assumption in arXiv:1606.00608, Appendix D.2, lines 2205--2208. -/
  hAXidem : PAX * PAX = PAX
  /-- The \(XB\) ground-space projector is Hermitian, corresponding to the
  projector assumption in arXiv:1606.00608, Appendix D.2, lines 2205--2208. -/
  hXBherm : PXB.IsHermitian
  /-- The \(XB\) ground-space projector is idempotent, corresponding to the
  projector assumption in arXiv:1606.00608, Appendix D.2, lines 2205--2208. -/
  hXBidem : PXB * PXB = PXB
  /-- The two lifted ground-space projectors commute, equivalent to equation
  `QAXQXB` in arXiv:1606.00608, Appendix D.2, lines 2207--2214. -/
  hcomm : liftAX PAX * liftXB PXB = liftXB PXB * liftAX PAX
  /-- Their product is the projector onto \(K_{AXB}\), which is the
  ground-space intersection in arXiv:1606.00608, Appendix D.2,
  lines 2212--2218. -/
  hproduct : liftAX PAX * liftXB PXB = P

/-- Existence of local commuting parent projectors for \(P\), in the sense of
arXiv:1606.00608, Appendix D.2, Definition D.2, lines 2205--2218. -/
def HasCommutingParentHamiltonian
    (P : Matrix (A × (X × B)) (A × (X × B)) ℂ) : Prop :=
  Nonempty (CommutingParentHamiltonian P)

/-- A parent commuting Hamiltonian on \(AX\) and \(XB\) implies decorrelation
of \(A\) and \(B\).

This is the only-if direction of arXiv:1606.00608, Appendix D.2,
Proposition D.3, lines 2279--2289. -/
theorem CommutingParentHamiltonian.isDecorrelated
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hparent : CommutingParentHamiltonian P) (hPidem : P * P = P) :
    IsDecorrelated P := by
  let SAX := liftAX (B := B) hparent.PAX
  let SXB := liftXB (A := A) hparent.PXB
  have hrev : SXB * SAX = P := by
    rw [← hparent.hcomm]
    exact hparent.hproduct
  have hquad : SXB * P * SAX = P * P := by
    calc
      SXB * P * SAX = SXB * (SAX * SXB) * SAX := by rw [hparent.hproduct]
      _ = (SXB * SAX) * (SXB * SAX) := by noncomm_ring
      _ = P * P := by rw [hrev]
  have hmiddle : SXB * (1 - P) * SAX = 0 := by
    calc
      SXB * (1 - P) * SAX = SXB * SAX - SXB * P * SAX := by noncomm_ring
      _ = P - P * P := by rw [hrev, hquad]
      _ = 0 := by rw [hPidem, sub_self]
  intro OA OB
  have hAcomm : SXB * liftA OA = liftA OA * SXB := by
    exact (liftA_comm_liftXB OA hparent.PXB).symm
  have hBcomm : liftB OB * SAX = SAX * liftB OB := by
    exact liftB_comm_liftAX OB hparent.PAX
  calc
    P * liftA OA * (1 - P) * liftB OB * P =
        (SAX * SXB) * liftA OA * (1 - P) * liftB OB * (SAX * SXB) := by
          rw [hparent.hproduct]
    _ = SAX * liftA OA * (SXB * (1 - P) * SAX) * liftB OB * SXB := by
      calc
        (SAX * SXB) * liftA OA * (1 - P) * liftB OB * (SAX * SXB) =
            SAX * (SXB * liftA OA) * (1 - P) *
              (liftB OB * SAX) * SXB := by noncomm_ring
        _ = SAX * (liftA OA * SXB) * (1 - P) *
              (SAX * liftB OB) * SXB := by rw [hAcomm, hBcomm]
        _ = SAX * liftA OA * (SXB * (1 - P) * SAX) * liftB OB * SXB := by
          noncomm_ring
    _ = 0 := by rw [hmiddle]; simp

/-- Decorrelation constructs a parent commuting Hamiltonian from the two
marginal support projectors.

This is the if direction of arXiv:1606.00608, Appendix D.2,
Proposition D.3, lines 2225--2277. -/
theorem IsDecorrelated.hasCommutingParentHamiltonian
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) (hdec : IsDecorrelated P) :
    HasCommutingParentHamiltonian P := by
  have hproducts := supportProducts_eq hPherm hPidem hdec
  exact ⟨
    { PAX := supportAX hPherm
      PXB := supportXB hPherm
      hAXherm := (Matrix.partialTraceRight_isHermitian
        (groupAX_isHermitian hPherm)).supportProj_isHermitian
      hAXidem := (Matrix.partialTraceRight_isHermitian
        (groupAX_isHermitian hPherm)).supportProj_idem
      hXBherm := (Matrix.partialTraceLeft_isHermitian hPherm).supportProj_isHermitian
      hXBidem := (Matrix.partialTraceLeft_isHermitian hPherm).supportProj_idem
      hcomm := hproducts.2.trans hproducts.1.symm
      hproduct := hproducts.2 }⟩

/-- **Parent commuting Hamiltonian--decorrelation equivalence.**

For an orthogonal projector \(P_{AXB}\), there are commuting parent terms on
\(AX\) and \(XB\) with ground projector \(P_{AXB}\) if and only if regions
\(A\) and \(B\) are decorrelated.  This is arXiv:1606.00608, Appendix D.2,
Proposition D.3, lines 2221--2289. -/
theorem parentHamiltonian_iff_decorrelated
    {P : Matrix (A × (X × B)) (A × (X × B)) ℂ}
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    HasCommutingParentHamiltonian P ↔ IsDecorrelated P :=
  ⟨fun hparent => hparent.elim fun parent => parent.isDecorrelated hPidem,
    fun hdec => hdec.hasCommutingParentHamiltonian hPherm hPidem⟩

end TripartiteDecorrelation
