/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.HorizontalBNT
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.ZCL

/-!
# Simple MPO tensors and copy-independent sector weights

This file begins the "Case II: $K$ simple" analysis of arXiv:1606.00608.  The
source views the tensor generating the MPDO as a matrix product vector whose
doubled physical index carries the bra and ket legs, writes it in canonical
form over a basis of normal tensors $M_k$, and attaches to each basis element
the single-site transfer matrix $\mathcal{B}_k$ obtained by contracting the
ket leg against the bra leg (lines 815--818).  A tensor is *simple* when no
$\mathcal{B}_k$ is nilpotent (lines 819--822).  For simple tensors, zero
correlation length forces the canonical-form weights $\mu_{j,q}$ to be
independent of the copy index $q$ (Appendix C.2, lines 1646--1661).

## Main declarations

* `MPOTensor.doubledPhysTraceTransfer`: the transfer matrix $\sum_i B^{(i,i)}$
  of a doubled-index tensor.
* `MPOTensor.doubledPhysTraceTransfer_toMPSTensor`: on the doubled-index view
  of an MPO tensor this recovers `MPOTensor.physTraceTransfer`.
* `MPOTensor.doubledPhysTraceTransfer_toTensor`: the physical-trace transfer
  of an assembled sector decomposition is block diagonal with blocks
  $\mu_{j,q}\,\mathcal{B}_j$.
* `MPOTensor.IsSimpleCanonicalForm`: simplicity for a tensor already in the
  blocked canonical-form setting of Appendix C.2.
* `MPOTensor.IsSimple`: the source simplicity predicate, allowing the positive
  physical blocking required before the BNT canonical form is chosen.
* `MPOTensor.weight_copy_independent_of_isSourceZCL`: zero correlation length
  makes the canonical-form weights independent of the copy index.
* `MPOTensor.IsSimpleCanonicalForm.exists_weight_copy_independent_of_isSourceZCL`:
  the existential form for a simple canonical-form tensor.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Section 4.3 and Appendix C.2
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- The **physical-trace transfer of a doubled-index tensor**: the single bond
matrix $\sum_i B^{(i,i)}$ obtained by contracting the ket leg of one tensor
against its bra leg.  This is the transfer object of the source
zero-correlation-length condition (arXiv:1606.00608, Definition 4.2, lines
735--739), applied to a single basis-of-normal-tensors element as in the
transfer matrices $\mathcal{B}_k$ of lines 815--818. -/
noncomputable def doubledPhysTraceTransfer (d : ℕ) {D' : ℕ} (B : MPSTensor (d * d) D') :
    Matrix (Fin D') (Fin D') ℂ :=
  ∑ i : Fin d, B (finProdFinEquiv (i, i))

variable {d D : ℕ}

/-- On the doubled-index view of an MPO tensor, the doubled physical-trace
transfer is the physical-trace transfer $\mathcal{T}_M = \sum_i M^{ii}$ of the
source zero-correlation-length condition (arXiv:1606.00608, Definition 4.2,
lines 735--739). -/
theorem doubledPhysTraceTransfer_toMPSTensor (M : MPOTensor d D) :
    doubledPhysTraceTransfer d M.toMPSTensor = physTraceTransfer M := by
  simp only [doubledPhysTraceTransfer, physTraceTransfer, toMPSTensor,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- The physical-trace transfer of an assembled sector decomposition is block
diagonal: the block of the flattened copy $s \leftrightarrow (j, q)$ is
$\mu_{j,q}\,\mathcal{B}_j$, where $\mathcal{B}_j$ is the physical-trace
transfer of the basis element $A_j$.  This is the block structure obtained by
contracting the physical legs of the canonical-form display of
arXiv:1606.00608, equation Eq19, lines 304--308, as in the proof of the
copy-independence lemma at lines 1652--1661. -/
theorem doubledPhysTraceTransfer_toTensor (S : MPSTensor.SectorDecomposition (d * d)) :
    doubledPhysTraceTransfer d S.toTensor =
      (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
        (Matrix.blockDiagonal' fun s =>
          S.flatWeight s • doubledPhysTraceTransfer d (S.flatBasis s)) := by
  classical
  ext a b
  simp only [doubledPhysTraceTransfer, MPSTensor.SectorDecomposition.toTensor,
    MPSTensor.toTensorFromBlocks, Matrix.sum_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]
  by_cases h : (finSigmaFinEquiv.symm a).1 = (finSigmaFinEquiv.symm b).1
  · simp only [dif_pos h, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  · simp only [dif_neg h, Finset.sum_const_zero]

/-- **Simple MPO tensor in the chosen canonical form** (arXiv:1606.00608,
lines 815--822).  The source
writes the doubled-index tensor in canonical form over a basis of normal
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
element have nilpotent physical-trace transfer. -/
def IsSimpleCanonicalForm (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧
    ∃ S : MPSTensor.SectorDecomposition (d * d),
      MPSTensor.IsBNTCanonicalForm S ∧
        (∀ j, ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j))) ∧
        ∃ hTotal : S.totalDim = D,
          ∃ X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ,
          ∀ i : Fin (d * d),
            M.toMPSTensor i =
              cast (by rw [hTotal] :
                  Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
                    Matrix (Fin D) (Fin D) ℂ)
                ((MPSTensor.globalGaugeOfBlocks X :
                      Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
                  S.toTensor i *
                  (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                      GL (Fin S.totalDim) ℂ) :
                    Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))

/-- **Simple MPO tensor** (arXiv:1606.00608, lines 815--822). Before choosing
the BNT, the source blocks a positive number of physical sites (line 815).
A tensor is simple when one such blocked tensor is a simple canonical-form
tensor in the sense above. -/
def IsSimple (M : MPOTensor d D) : Prop :=
  IsMPDO M ∧ ∃ L : ℕ, 0 < L ∧ IsSimpleCanonicalForm (blockTensor M L)

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
    (S : MPSTensor.SectorDecomposition (d * d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin (d * d),
      M.toMPSTensor i =
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
      (S.weight j q • doubledPhysTraceTransfer d (S.basis j)) *
          (S.weight j q • doubledPhysTraceTransfer d (S.basis j)) =
        (lam : ℂ) • (S.weight j q • doubledPhysTraceTransfer d (S.basis j)) := by
  classical
  subst hTotal
  obtain ⟨-, lam, hlam, hsq⟩ := hZCL
  have hX' : ∀ i : Fin (d * d), M.toMPSTensor i =
      (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
        S.toTensor i *
        (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := fun i ↦ by
    simpa using hEq i
  have hT : physTraceTransfer M =
      (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
        doubledPhysTraceTransfer d S.toTensor *
        (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    rw [← doubledPhysTraceTransfer_toMPSTensor M]
    simp only [doubledPhysTraceTransfer]
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ hX' (finProdFinEquiv (i, i))
  rw [hT] at hsq
  have hRR :
      doubledPhysTraceTransfer d S.toTensor * doubledPhysTraceTransfer d S.toTensor =
        (lam : ℂ) • doubledPhysTraceTransfer d S.toTensor := by
    have h2 := congrArg (fun Z ↦
      (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * Z *
        (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) hsq
    simpa only [Matrix.mul_smul, Matrix.smul_mul, mul_assoc,
      Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using h2
  rw [doubledPhysTraceTransfer_toTensor] at hRR
  have hfun :
      (fun s ↦ (S.flatWeight s • doubledPhysTraceTransfer d (S.flatBasis s)) *
          (S.flatWeight s • doubledPhysTraceTransfer d (S.flatBasis s))) =
        (lam : ℂ) • fun s ↦
          S.flatWeight s • doubledPhysTraceTransfer d (S.flatBasis s) := by
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
          doubledPhysTraceTransfer d
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) *
        (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          doubledPhysTraceTransfer d
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) =
      (lam : ℂ) •
        (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          doubledPhysTraceTransfer d
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
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1745--1782. -/
theorem weighted_basis_physTraceTransfer_sq_of_literal_ZCL
    {M : MPOTensor d D}
    (S : MPSTensor.SectorDecomposition (d * d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin (d * d),
      M.toMPSTensor i =
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
      (S.weight j q • doubledPhysTraceTransfer d (S.basis j)) *
          (S.weight j q • doubledPhysTraceTransfer d (S.basis j)) =
        S.weight j q • doubledPhysTraceTransfer d (S.basis j) := by
  classical
  subst hTotal
  have hX' : ∀ i : Fin (d * d), M.toMPSTensor i =
      (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
        S.toTensor i *
        (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := fun i ↦ by
    simpa using hEq i
  have hT : physTraceTransfer M =
      (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
        doubledPhysTraceTransfer d S.toTensor *
        (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    rw [← doubledPhysTraceTransfer_toMPSTensor M]
    simp only [doubledPhysTraceTransfer]
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ hX' (finProdFinEquiv (i, i))
  rw [hT] at hZCL_sq
  have hRR :
      doubledPhysTraceTransfer d S.toTensor * doubledPhysTraceTransfer d S.toTensor =
        doubledPhysTraceTransfer d S.toTensor := by
    have h2 := congrArg (fun Z ↦
      (((MPSTensor.globalGaugeOfBlocks X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * Z *
        (MPSTensor.globalGaugeOfBlocks X :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)) hZCL_sq
    simpa only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using h2
  rw [doubledPhysTraceTransfer_toTensor] at hRR
  have hfun :
      (fun s ↦ (S.flatWeight s • doubledPhysTraceTransfer d (S.flatBasis s)) *
          (S.flatWeight s • doubledPhysTraceTransfer d (S.flatBasis s))) =
        fun s ↦ S.flatWeight s • doubledPhysTraceTransfer d (S.flatBasis s) := by
    apply Matrix.blockDiagonal'_injective
    apply (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv).injective
    simpa only [Matrix.reindex_apply, Matrix.blockDiagonal'_mul,
      Matrix.submatrix_mul_equiv] using hRR
  intro j q
  have h :
      (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          doubledPhysTraceTransfer d
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) *
        (S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
            (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
          doubledPhysTraceTransfer d
            (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1)) =
      S.weight (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1
          (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).2 •
        doubledPhysTraceTransfer d
          (S.basis (S.flatIndexEquiv.symm (S.flatIndexEquiv ⟨j, q⟩)).1) :=
    congrFun hfun (S.flatIndexEquiv ⟨j, q⟩)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- **Zero correlation length makes the sector weights copy independent**
(arXiv:1606.00608, Appendix C.2, lines 1646--1661).  Let the doubled-index
view of $M$ be in canonical form over a basis of normal tensors with per-copy
weights $\mu_{j,q}$, and suppose no basis element has nilpotent physical-trace
transfer.  If $M$ has zero correlation length, then $\mu_{j,q}$ does not
depend on $q$.

The source proof applies the zero-correlation-length equation to the
canonical-form display: with
$\mathcal{T}_M^2 = \lambda\,\mathcal{T}_M$, $\lambda > 0$, the block
decomposition gives
$\mu_{j,q}^2\,\mathcal{B}_j^2 = \lambda\,\mu_{j,q}\,\mathcal{B}_j$ on the copy
$(j, q)$, so $\mathcal{B}_j^2 = (\lambda/\mu_{j,q})\,\mathcal{B}_j$; since
$\mathcal{B}_j \ne 0$ ("this cannot be zero", line 1657), the scalar
$\lambda/\mu_{j,q}$, hence $\mu_{j,q}$, is independent of $q$. -/
theorem weight_copy_independent_of_isSourceZCL {M : MPOTensor d D}
    (S : MPSTensor.SectorDecomposition (d * d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin (d * d),
      M.toMPSTensor i =
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
    (hnonNil : ∀ j, ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (j : Fin S.basisCount) (q q' : Fin (S.copies j)) :
    S.weight j q = S.weight j q' := by
  classical
  obtain ⟨lam, hlam, key⟩ :=
    exists_weighted_basis_physTraceTransfer_sq_of_isSourceZCL
      S hTotal X hEq hZCL
  -- The basis transfer is nonzero, so the scalars can be compared.
  have hTj0 : doubledPhysTraceTransfer d (S.basis j) ≠ 0 := by
    intro h0
    exact hnonNil j (by rw [h0]; exact IsNilpotent.zero)
  have hdiv : ∀ r : Fin (S.copies j),
      doubledPhysTraceTransfer d (S.basis j) * doubledPhysTraceTransfer d (S.basis j) =
        ((lam : ℂ) / S.weight j r) • doubledPhysTraceTransfer d (S.basis j) := by
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
        doubledPhysTraceTransfer d (S.basis j) = 0 := by
      rw [sub_smul, hq, sub_self]
    have h4 := congrArg (fun Z =>
      ((lam : ℂ) / S.weight j q - (lam : ℂ) / S.weight j q')⁻¹ • Z) hsub
    simp only [smul_smul, smul_zero] at h4
    rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at h4
    exact hTj0 h4
  have hlam0 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)
  rw [div_eq_div_iff (S.weight_ne_zero j q) (S.weight_ne_zero j q')] at hscalar
  exact (mul_left_cancel₀ hlam0 hscalar).symm

/-- **Copy-independent weights for a simple canonical-form tensor with zero
correlation length** (arXiv:1606.00608, Appendix C.2, lines 1628 and
1646--1661). A simplicity witness supplies the chosen canonical form and the
nilpotency exclusion; zero correlation length then makes the sector weights
$\mu_{j,q}$ independent of the copy index $q$. -/
theorem IsSimpleCanonicalForm.exists_weight_copy_independent_of_isSourceZCL
    {M : MPOTensor d D} (hM : IsSimpleCanonicalForm M)
    (hZCL : IsSourceZCL M) :
    ∃ S : MPSTensor.SectorDecomposition (d * d),
      MPSTensor.IsBNTCanonicalForm S ∧
        (∃ hTotal : S.totalDim = D,
          ∃ X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ,
          ∀ i : Fin (d * d),
            M.toMPSTensor i =
              cast (by rw [hTotal] :
                  Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
                    Matrix (Fin D) (Fin D) ℂ)
                ((MPSTensor.globalGaugeOfBlocks X :
                      Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
                  S.toTensor i *
                  (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                      GL (Fin S.totalDim) ℂ) :
                    Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))) ∧
        (∀ j, ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j))) ∧
        ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
          S.weight j q = S.weight j q' := by
  obtain ⟨-, S, hCF, hnil, hTotal, X, hEq⟩ := hM
  exact ⟨S, hCF, ⟨hTotal, X, hEq⟩, hnil, fun j q q' =>
    weight_copy_independent_of_isSourceZCL S hTotal X hEq hZCL hnil j q q'⟩

end MPOTensor
