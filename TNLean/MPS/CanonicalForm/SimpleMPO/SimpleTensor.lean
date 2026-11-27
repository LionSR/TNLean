/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.SimpleMPO.HorizontalBNT
import TNLean.MPS.Operator.Product.PhysicalBlocking
import TNLean.MPS.Operator.DensityOperator.ZCL
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Simple MPO tensors and copy-independent sector weights

This file begins the "Case II: $K$ simple" analysis of arXiv:1606.00608.  The
source views the tensor generating the MPDO as a matrix product vector whose
physical index is the ket--bra pair, writes it in canonical
form over a basis of normal tensors $M_k$, and attaches to each basis element
the single-site transfer matrix $\mathcal{B}_k$ obtained by contracting the
ket leg against the bra leg (lines 815--818).  A tensor is *simple* when no
$\mathcal{B}_k$ is nilpotent (lines 819--822).  For simple tensors, zero
correlation length forces the canonical-form weights $\mu_{j,q}$ to be
independent of the copy index $q$ (Appendix C.2, lines 1646--1661).

## Main declarations

* `MPOTensor.isNilpotent_physTraceTransfer_iff_of_gaugePhaseEquiv`: nilpotency of the
  physical-trace transfer is a gauge-phase invariant.
* `MPOTensor.physTraceTransfer_toTensor`: the physical-trace transfer
  of an assembled sector decomposition is block diagonal with blocks
  $\mu_{j,q}\,\mathcal{B}_j$.
* `MPOTensor.IsSimpleCanonicalForm`: simplicity for a tensor already in the
  blocked canonical-form setting of Appendix C.2.
* `MPOTensor.weight_copy_independent_of_isPhysicalTraceIdempotent`: literal zero
  correlation length makes the canonical-form weights independent of the copy index.
* `MPOTensor.IsSimpleCanonicalForm.
    exists_weight_copy_independent_of_isPhysicalTraceIdempotent`: the corresponding
  existential form for a simple canonical-form tensor.
* `MPOTensor.weight_copy_independent_of_isSourceZCL`: the separate scale-invariant
  generalization.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Section 4.3 and Appendix C.2
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Gauge-phase equivalence preserves nilpotency of the physical-trace transfer.

The physical contraction of a gauge-phase transform is the same nonzero scalar multiple of
the corresponding similarity transform.  This is the presentation-independence required by
the simplicity definition.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822, and the normal-tensor gauge theorem,
lines 1080--1117. -/
theorem isNilpotent_physTraceTransfer_of_gaugePhaseEquiv
    {A B : MPOTensor d D} (h : MPTensor.GaugePhaseEquiv A B)
    (hNil : IsNilpotent (physTraceTransfer A)) :
    IsNilpotent (physTraceTransfer B) := by
  classical
  obtain ⟨X, ζ, _hζ, hrel⟩ := h
  have hTransfer :
      physTraceTransfer B =
        ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * physTraceTransfer A *
          (↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ)) := by
    calc
      physTraceTransfer B =
          ∑ i : Fin d, ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A (i, i) *
              (↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ)) := by
        rw [physTraceTransfer]
        apply Finset.sum_congr rfl
        intro i _
        exact hrel (i, i)
      _ = ζ • ∑ i : Fin d, ((X : Matrix (Fin D) (Fin D) ℂ) * A (i, i) *
              (↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ)) := by
        rw [Finset.smul_sum]
      _ = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * physTraceTransfer A *
            (↑(X⁻¹) : Matrix (Fin D) (Fin D) ℂ)) := by
        rw [physTraceTransfer, Finset.mul_sum, Finset.sum_mul]
  obtain ⟨n, hn⟩ := hNil
  refine ⟨n, ?_⟩
  rw [hTransfer, smul_pow, Units.conj_pow, hn]
  simp

/-- Nilpotency of the physical-trace transfer is invariant under gauge-phase
equivalence.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822, and the normal-tensor gauge theorem,
lines 1080--1117. -/
theorem isNilpotent_physTraceTransfer_iff_of_gaugePhaseEquiv
    {A B : MPOTensor d D} (h : MPTensor.GaugePhaseEquiv A B) :
    IsNilpotent (physTraceTransfer A) ↔ IsNilpotent (physTraceTransfer B) :=
  ⟨isNilpotent_physTraceTransfer_of_gaugePhaseEquiv h,
    isNilpotent_physTraceTransfer_of_gaugePhaseEquiv
      (MPSTensor.gaugePhaseEquiv_symm_same_dim h)⟩

/-- Identifying equal bond dimensions does not change nilpotency of the
physical-trace transfer.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
theorem isNilpotent_physTraceTransfer_cast_iff
    {D₁ D₂ : ℕ} (hdim : D₁ = D₂) (A : MPOTensor d D₁) :
    IsNilpotent
        (physTraceTransfer (cast (congr_arg (fun n ↦ MPTensor (Fin d × Fin d) (Fin n)) hdim) A)) ↔
      IsNilpotent (physTraceTransfer A) := by
  subst D₂
  rfl

/-- The physical-trace transfer of an assembled sector decomposition is block
diagonal: the block of the flattened copy $s \leftrightarrow (j, q)$ is
$\mu_{j,q}\,\mathcal{B}_j$, where $\mathcal{B}_j$ is the physical-trace
transfer of the basis element $A_j$.  This is the block structure obtained by
contracting the physical legs of the canonical-form display of
arXiv:1606.00608, equation Eq19, lines 304--308, as in the proof of the
copy-independence lemma at lines 1652--1661. -/
theorem physTraceTransfer_toTensor (S : MPSTensor.SectorDecomposition (Fin d × Fin d)) :
    physTraceTransfer S.toTensor =
      (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
        (Matrix.blockDiagonal' fun s =>
          S.flatWeight s • physTraceTransfer (S.flatBasis s)) := by
  classical
  ext a b
  simp only [physTraceTransfer, MPSTensor.SectorDecomposition.toTensor,
    MPTensor.toTensorFromBlocks, Matrix.sum_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]
  by_cases h : (finSigmaFinEquiv.symm a).1 = (finSigmaFinEquiv.symm b).1
  · simp only [dite_eq_left h, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  · simp only [dite_eq_right h, Finset.sum_const_zero]

/-- **Simple MPO tensor in the chosen canonical form** (arXiv:1606.00608,
lines 815--822).  The source
writes the tensor on the pair alphabet in canonical form over a basis of normal
tensors $M_k$ and attaches to each basis element the transfer matrix
$\mathcal{B}_k$ contracting ket against bra leg (lines 815--818).  A basis
element is *nilpotent* when tracing $R \le D$ sites annihilates the generated
state: $\operatorname{tr}_R \rho^{(N)}(M_k) = 0$ after tracing $R \le D$
sites, for $N$ sufficiently large (line 819).  For the transfer matrix this
reads $\mathcal{B}_k^R = 0$ with $R \le D$, which is matrix nilpotency, since
the nilpotency index of a nilpotent $D \times D$ matrix is at most $D$.  The
definition at line 822 then reads: "A tensor generating MPDO's is simple if
none of the elements in a BNT is nilpotent."

This predicate records the simple horizontal-canonical-form data of the
already-blocked tensor $K$ in Appendix C.2, line 1628. It does not include
the separate biCF hypothesis imposed there, since the copy-independence
argument at lines 1646--1658 does not use the inverse tensor. It retains the
assumption that `M` generates MPDOs; its canonical-form witness has the shape
of `MPOTensor.IsHorizontalCF`, with the additional requirement that no basis
element have nilpotent physical-trace transfer.

**Scope restriction (fixed representative):** The BNT witness includes the
line-246 global unit-weight convention through
`MPSTensor.IsBNTCanonicalForm.weight_unit_exists`.
Thus this predicate is evaluated on the displayed tensor `M`, not modulo a
nonzero scalar rescaling. The mathematical nilpotency clause is scale invariant,
but the unit-weight normalization included in the canonical-form witness need
not be compatible with the scale fixed by Definition 4.1. See
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>. -/
def IsSimpleCanonicalForm (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧
    ∃ S : MPSTensor.SectorDecomposition (Fin d × Fin d),
      MPSTensor.IsBNTCanonicalForm S ∧
        (∀ j, ¬ IsNilpotent (physTraceTransfer (S.basis j))) ∧
        ∃ hTotal : S.totalDim = D,
          ∃ X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ,
          ∀ i : Fin d × Fin d,
            M i =
              cast (by rw [hTotal] :
                  Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
                    Matrix (Fin D) (Fin D) ℂ)
                ((MPSTensor.globalGaugeOfBlocks X :
                      Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
                  S.toTensor i *
                  (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                      GL (Fin S.totalDim) ℂ) :
                    Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))

/-- A simple canonical-form tensor is in horizontal canonical form:
simplicity is the horizontal canonical form of arXiv:1606.00608, lines
815--818, together with the nilpotency exclusion of lines 819--822. -/
theorem IsSimpleCanonicalForm.isHorizontalCF {M : MPOTensor d D}
    (hM : IsSimpleCanonicalForm M) :
    IsHorizontalCF M := by
  obtain ⟨-, S, hCF, -, hTotal, X, hEq⟩ := hM
  exact ⟨S, hCF, hTotal, X, hEq⟩

/-- The zero-correlation-length equation restricts to every copy of every
normal representative in the horizontal canonical form:
\[
  (\mu_{j,q}\mathcal B_j)^2
    =\lambda\,\mu_{j,q}\mathcal B_j,
  \qquad \lambda>0.
\]

This is the block equation used before the source compares two copy indices.

Source: arXiv:1606.00608, Appendix C.2, equation in lines 1652--1657. -/
theorem exists_weighted_basis_physTraceTransfer_sq_of_isSourceZCL
    {M : MPOTensor d D}
    (S : MPSTensor.SectorDecomposition (Fin d × Fin d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin d × Fin d,
      M i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hZCL : IsSourceZCL M) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (j : Fin S.basisCount) (q : Fin (S.copies j)),
      (S.weight j q • physTraceTransfer (S.basis j)) *
          (S.weight j q • physTraceTransfer (S.basis j)) =
        (lam : ℂ) • (S.weight j q • physTraceTransfer (S.basis j)) := by
  classical
  subst hTotal
  obtain ⟨-, lam, hlam, hsq⟩ := hZCL
  have hX' : ∀ i : Fin d × Fin d, M i =
      (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
        S.toTensor i *
        (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := fun i ↦ by
    simpa using hEq i
  have hT : physTraceTransfer M =
      (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
        physTraceTransfer S.toTensor *
        (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    simp only [physTraceTransfer]
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ hX' (i, i)
  rw [hT] at hsq
  have hRR :
      physTraceTransfer S.toTensor * physTraceTransfer S.toTensor =
        (lam : ℂ) • physTraceTransfer S.toTensor := by
    have h2 := congrArg (fun Z ↦
      (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * Z *
        (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) hsq
    simpa only [Matrix.mul_smul, Matrix.smul_mul, mul_assoc,
      Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using h2
  rw [physTraceTransfer_toTensor] at hRR
  have hfun :
      (fun s ↦ (S.flatWeight s • physTraceTransfer (S.flatBasis s)) *
          (S.flatWeight s • physTraceTransfer (S.flatBasis s))) =
        (lam : ℂ) • fun s ↦
          S.flatWeight s • physTraceTransfer (S.flatBasis s) := by
    apply Matrix.blockDiagonal'_injective
    apply (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv).injective
    simpa only [Matrix.reindex_apply, Matrix.blockDiagonal'_mul,
      Matrix.blockDiagonal'_smul, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_smul, Pi.smul_apply] using hRR
  refine ⟨lam, hlam, ?_⟩
  intro j q
  have h :
      (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          physTraceTransfer
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) *
        (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          physTraceTransfer
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) =
      (lam : ℂ) •
        (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          physTraceTransfer
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) :=
    congrFun hfun (S.flatIndexEquiv ⟨j, q⟩)
  rw [Equiv.symm_apply_apply] at h
  simpa [Pi.smul_apply] using h

/-- Literal zero correlation length restricts to every weighted canonical block:
\[
  (\mu_{j,q}\mathcal B_j)^2=\mu_{j,q}\mathcal B_j.
\]

The proof conjugates the ambient physical-trace idempotence equation through the chosen
canonical-form gauge and then reads the diagonal block indexed by `(j, q)`.

**Scope restriction (literal-ZCL inheritance):** This is only the literal-ZCL inheritance
part of Case II. It neither gives spectral normality of the absorbed tensor nor completes
`prop2to3`. The remaining Case-II boundary is recorded in
<https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_pf_rank_one.pdf>.

Source: arXiv:1606.00608, Appendix C.2, lines 1745--1782. -/
theorem weighted_basis_physTraceTransfer_sq_of_literal_ZCL
    {M : MPOTensor d D}
    (S : MPSTensor.SectorDecomposition (Fin d × Fin d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin d × Fin d,
      M i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hZCL_sq : physTraceTransfer M * physTraceTransfer M = physTraceTransfer M) :
    ∀ (j : Fin S.basisCount) (q : Fin (S.copies j)),
      (S.weight j q • physTraceTransfer (S.basis j)) *
          (S.weight j q • physTraceTransfer (S.basis j)) =
        S.weight j q • physTraceTransfer (S.basis j) := by
  classical
  subst hTotal
  have hX' : ∀ i : Fin d × Fin d, M i =
      (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
        S.toTensor i *
        (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := fun i ↦ by
    simpa using hEq i
  have hT : physTraceTransfer M =
      (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
        physTraceTransfer S.toTensor *
        (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    simp only [physTraceTransfer]
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ hX' (i, i)
  rw [hT] at hZCL_sq
  have hRR :
      physTraceTransfer S.toTensor * physTraceTransfer S.toTensor =
        physTraceTransfer S.toTensor := by
    have h2 := congrArg (fun Z ↦
      (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * Z *
        (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) hZCL_sq
    simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using h2
  rw [physTraceTransfer_toTensor] at hRR
  have hfun :
      (fun s ↦ (S.flatWeight s • physTraceTransfer (S.flatBasis s)) *
          (S.flatWeight s • physTraceTransfer (S.flatBasis s))) =
        fun s ↦ S.flatWeight s • physTraceTransfer (S.flatBasis s) := by
    apply Matrix.blockDiagonal'_injective
    apply (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv).injective
    simpa only [Matrix.reindex_apply, Matrix.blockDiagonal'_mul,
      Matrix.submatrix_mul_equiv] using hRR
  intro j q
  have h :
      (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          physTraceTransfer
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) *
        (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          physTraceTransfer
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) =
      S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
          (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
        physTraceTransfer
          (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1) :=
    congrFun hfun (S.flatIndexEquiv ⟨j, q⟩)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- **Literal zero correlation length makes the sector weights copy independent**
(CPSV16, Lemma C.10, label `lemmus`, lines 1646--1661). Let
$M$ on the pair alphabet be in canonical form over a basis of normal tensors with per-copy
weights $\mu_{j,q}$, and suppose no basis element has nilpotent physical-trace
transfer. If the literal physical-trace equation $\mathcal T_M^2=\mathcal T_M$
holds, then $\mu_{j,q}$ does not depend on $q$.

The block equation gives
$\mathcal B_j^2=\mu_{j,q}^{-1}\mathcal B_j$. Since $\mathcal B_j\ne0$, comparing
two copy indices gives $\mu_{j,q}=\mu_{j,q'}$. The nonnilpotency and canonical-form
data are the standing simplicity conditions of the source. -/
theorem weight_copy_independent_of_isPhysicalTraceIdempotent {M : MPOTensor d D}
    (S : MPSTensor.SectorDecomposition (Fin d × Fin d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin d × Fin d,
      M i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hZCL : IsPhysicalTraceIdempotent M)
    (hnonNil : ∀ j, ¬ IsNilpotent (physTraceTransfer (S.basis j)))
    (j : Fin S.basisCount) (q q' : Fin (S.copies j)) :
    S.weight j q = S.weight j q' := by
  classical
  have key := weighted_basis_physTraceTransfer_sq_of_literal_ZCL
    S hTotal X hEq ((isPhysicalTraceIdempotent_iff M).mp hZCL)
  have hTj0 : physTraceTransfer (S.basis j) ≠ 0 := by
    intro h0
    exact hnonNil j (by rw [h0]; exact IsNilpotent.zero)
  have hdiv : ∀ r : Fin (S.copies j),
      physTraceTransfer (S.basis j) * physTraceTransfer (S.basis j) =
        ((1 : ℂ) / S.weight j r) • physTraceTransfer (S.basis j) := by
    intro r
    have hμ : S.weight j r ≠ 0 := S.weight_ne_zero j r
    have hk := key j r
    rw [smul_mul_smul_comm] at hk
    have h3 := congrArg (fun Z ↦ (S.weight j r * S.weight j r)⁻¹ • Z) hk
    simp only [smul_smul] at h3
    rw [inv_mul_cancel₀ (mul_ne_zero hμ hμ), one_smul] at h3
    rw [h3]
    congr 1
    field_simp
  have hq := (hdiv q).symm.trans (hdiv q')
  have hscalar : (1 : ℂ) / S.weight j q = (1 : ℂ) / S.weight j q' := by
    by_contra hne
    have hsub : ((1 : ℂ) / S.weight j q - (1 : ℂ) / S.weight j q') •
        physTraceTransfer (S.basis j) = 0 := by
      rw [sub_smul, hq, sub_self]
    have h4 := congrArg (fun Z ↦
      ((1 : ℂ) / S.weight j q - (1 : ℂ) / S.weight j q')⁻¹ • Z) hsub
    simp only [smul_smul, smul_zero] at h4
    rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at h4
    exact hTj0 h4
  rw [div_eq_div_iff (S.weight_ne_zero j q) (S.weight_ne_zero j q')] at hscalar
  simpa using hscalar.symm

/-- **Scale-invariant generalization of copy independence.** Let
$M$ on the pair alphabet be in canonical form over a basis of normal tensors with per-copy
weights $\mu_{j,q}$, and suppose no basis element has nilpotent physical-trace
transfer. This theorem allows
$\mathcal T_M^2=\lambda\mathcal T_M$ for an arbitrary positive $\lambda$ and proves
that $\mu_{j,q}$ does not depend on $q$. The exact fixed-representative statement
of CPSV16, Lemma C.10, is
`weight_copy_independent_of_isPhysicalTraceIdempotent`. -/
theorem weight_copy_independent_of_isSourceZCL {M : MPOTensor d D}
    (S : MPSTensor.SectorDecomposition (Fin d × Fin d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin d × Fin d,
      M i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hZCL : IsSourceZCL M)
    (hnonNil : ∀ j, ¬ IsNilpotent (physTraceTransfer (S.basis j)))
    (j : Fin S.basisCount) (q q' : Fin (S.copies j)) :
    S.weight j q = S.weight j q' := by
  classical
  obtain ⟨lam, hlam, key⟩ :=
    exists_weighted_basis_physTraceTransfer_sq_of_isSourceZCL
      S hTotal X hEq hZCL
  -- The basis transfer is nonzero, so the scalars can be compared.
  have hTj0 : physTraceTransfer (S.basis j) ≠ 0 := by
    intro h0
    exact hnonNil j (by rw [h0]; exact IsNilpotent.zero)
  have hdiv : ∀ r : Fin (S.copies j),
      physTraceTransfer (S.basis j) * physTraceTransfer (S.basis j) =
        ((lam : ℂ) / S.weight j r) • physTraceTransfer (S.basis j) := by
    intro r
    have hμ : S.weight j r ≠ 0 := S.weight_ne_zero j r
    have hk := key j r
    rw [smul_mul_smul_comm, smul_smul] at hk
    have h3 := congrArg (fun Z => (S.weight j r * S.weight j r)⁻¹ • Z) hk
    simp only [smul_smul] at h3
    rw [inv_mul_cancel₀ (mul_ne_zero hμ hμ), one_smul] at h3
    rw [h3]
    congr 1
    field_simp
  have hq := (hdiv q).symm.trans (hdiv q')
  have hscalar : (lam : ℂ) / S.weight j q = (lam : ℂ) / S.weight j q' := by
    by_contra hne
    have hsub : ((lam : ℂ) / S.weight j q - (lam : ℂ) / S.weight j q') •
        physTraceTransfer (S.basis j) = 0 := by
      rw [sub_smul, hq, sub_self]
    have h4 := congrArg (fun Z =>
      ((lam : ℂ) / S.weight j q - (lam : ℂ) / S.weight j q')⁻¹ • Z) hsub
    simp only [smul_smul, smul_zero] at h4
    rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at h4
    exact hTj0 h4
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)
  rw [div_eq_div_iff (S.weight_ne_zero j q) (S.weight_ne_zero j q')] at hscalar
  exact (mul_left_cancel₀ hlam0 hscalar).symm

/-- **Literal-ZCL copy independence for a simple canonical-form tensor**
(CPSV16, Lemma C.10, label `lemmus`, lines 1628 and 1646--1661). A simplicity
witness supplies the canonical form and nonnilpotency conditions; literal
physical-trace idempotence makes every sector weight independent of its copy
index. -/
theorem IsSimpleCanonicalForm.exists_weight_copy_independent_of_isPhysicalTraceIdempotent
    {M : MPOTensor d D} (hM : IsSimpleCanonicalForm M)
    (hZCL : IsPhysicalTraceIdempotent M) :
    ∃ S : MPSTensor.SectorDecomposition (Fin d × Fin d),
      MPSTensor.IsBNTCanonicalForm S ∧
        (∃ hTotal : S.totalDim = D,
          ∃ X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ,
          ∀ i : Fin d × Fin d,
            M i =
              cast (by rw [hTotal] :
                  Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
                    Matrix (Fin D) (Fin D) ℂ)
                ((MPSTensor.globalGaugeOfBlocks X :
                      Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
                  S.toTensor i *
                  (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                      GL (Fin S.totalDim) ℂ) :
                    Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))) ∧
        (∀ j, ¬ IsNilpotent (physTraceTransfer (S.basis j))) ∧
        ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
          S.weight j q = S.weight j q' := by
  obtain ⟨-, S, hCF, hnil, hTotal, X, hEq⟩ := hM
  exact ⟨S, hCF, ⟨hTotal, X, hEq⟩, hnil, fun j q q' ↦
    weight_copy_independent_of_isPhysicalTraceIdempotent
      S hTotal X hEq hZCL hnil j q q'⟩

/-- **Scale-invariant generalization for a simple canonical-form tensor.** A
simplicity witness supplies the chosen canonical form and nilpotency exclusion;
the broader `IsSourceZCL` relation then makes the sector weights independent of
the copy index. The exact CPSV16 Lemma C.10 specialization is
`IsSimpleCanonicalForm.exists_weight_copy_independent_of_isPhysicalTraceIdempotent`. -/
theorem IsSimpleCanonicalForm.exists_weight_copy_independent_of_isSourceZCL
    {M : MPOTensor d D} (hM : IsSimpleCanonicalForm M)
    (hZCL : IsSourceZCL M) :
    ∃ S : MPSTensor.SectorDecomposition (Fin d × Fin d),
      MPSTensor.IsBNTCanonicalForm S ∧
        (∃ hTotal : S.totalDim = D,
          ∃ X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ,
          ∀ i : Fin d × Fin d,
            M i =
              cast (by rw [hTotal] :
                  Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
                    Matrix (Fin D) (Fin D) ℂ)
                ((MPSTensor.globalGaugeOfBlocks X :
                      Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
                  S.toTensor i *
                  (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                      GL (Fin S.totalDim) ℂ) :
                    Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))) ∧
        (∀ j, ¬ IsNilpotent (physTraceTransfer (S.basis j))) ∧
        ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
          S.weight j q = S.weight j q' := by
  obtain ⟨-, S, hCF, hnil, hTotal, X, hEq⟩ := hM
  exact ⟨S, hCF, ⟨hTotal, X, hEq⟩, hnil, fun j q q' =>
    weight_copy_independent_of_isSourceZCL S hTotal X hEq hZCL hnil j q q'⟩

end MPOTensor
