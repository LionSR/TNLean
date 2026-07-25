/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTFusionIsometries

/-!
# Fusion coisometries onto the active product sectors

The product of two vertically read normal sectors may have a common zero
corner. The fusion map of arXiv:1606.00608, Theorem 4.14(iii), is therefore a
coisometry from the product bond space onto the direct sum of its nonzero
canonical sectors. The forward conjugation identity describes the retained
part, while the reverse identity states that the omitted corner is zero.

The structure below records these three properties separately:
\[
  UU^\dagger=1,\qquad
  U P^{ij}U^\dagger=D^{ij},\qquad
  P^{ij}=U^\dagger D^{ij}U.
\]
It permits an empty retained sum when the product tensor is zero.

## Main definitions

* `MPOTensor.BNTFusionCoisometryFamily`: positive weighted fusion of labelled
  tensors onto their active product sectors.

## Main results

* `BNTFusionCoisometryFamily.fusionCoisometry_mul_mulTensor`: the left zipper
  identity.
* `BNTFusionCoisometryFamily.mulTensor_mul_fusionCoisometry_conjTranspose`:
  the right zipper identity.
* `BNTFusionCoisometryFamily.mpo_mul_mpo_eq_sum`: the positive-length
  closed-word product law.
* `BNTFusionCoisometryFamily.toBNTFusionIsometryFamily_of_fullSupport`: passage
  to the stronger column-isometry structure under an explicit full-support
  identity.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(iii), lines 986--993, and Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor

/-- A positive weighted fusion decomposition onto the active product sectors.

For each pair of labels, the map is a coisometry from the product bond space
onto the retained direct sum. Both the forward conjugation and reverse
reconstruction identities are included, so a common zero corner may be
discarded but no nonzero part may be lost.

Source: arXiv:1606.00608, Theorem 4.14(iii), lines 986--993, and Appendix C.4,
lines 2020--2029 of `Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Local fix (Figure-11 fusion coisometry):** The source uses the retained-row
orientation of Proposition 4.13. Thus its fusion map satisfies
$UU^\dagger=1$, while $U^\dagger U$ is the active-support projection.
Documented in `docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
structure BNTFusionCoisometryFamily (Λ : Type*) [Fintype Λ] [DecidableEq Λ]
    (p : ℕ) where
  /-- Bond dimension of the tensor carrying each label. -/
  bondDim : Λ → ℕ
  /-- The labelled tensors, with common physical dimension `p`. -/
  tensor : ∀ γ : Λ, MPOTensor p (bondDim γ)
  /-- The positive diagonal multiplicity matrices. -/
  chi : DiagonalChiFamily Λ
  /-- Every retained diagonal entry is positive. Empty multiplicity spaces are
  permitted. -/
  posEntries : chi.PosEntries
  /-- The map from a product bond space onto its retained direct sum. -/
  fusionCoisometry : ∀ α β : Λ,
    Matrix ((γ : Λ) × (Fin (chi.dim α β γ) × Fin (bondDim γ)))
      (Fin (bondDim α * bondDim β)) ℂ
  /-- Each fusion map is a coisometry onto the retained direct sum. -/
  coisometry : ∀ α β : Λ,
    fusionCoisometry α β * (fusionCoisometry α β)ᴴ = 1
  /-- Conjugation onto the retained space gives the positive weighted direct
  sum, letter by letter. -/
  fusion : ∀ (α β : Λ) (i j : Fin p),
    fusionCoisometry α β * (mulTensor (tensor α) (tensor β)) i j *
        (fusionCoisometry α β)ᴴ =
      Matrix.blockDiagonal' fun γ => chi.matrix α β γ ⊗ₖ tensor γ i j
  /-- The retained direct sum reconstructs every product letter; equivalently,
  the omitted common corner is zero. -/
  reconstruction : ∀ (α β : Λ) (i j : Fin p),
    (mulTensor (tensor α) (tensor β)) i j =
      (fusionCoisometry α β)ᴴ *
        (Matrix.blockDiagonal' fun γ => chi.matrix α β γ ⊗ₖ tensor γ i j) *
        fusionCoisometry α β

namespace BNTFusionCoisometryFamily

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionCoisometryFamily Λ p)

private theorem listProd_conj_of_conjTranspose_mul_self_fintype
    {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (W : Matrix S T ℂ) (hW : Wᴴ * W = 1)
    {n : ℕ} (F : Fin (n + 1) → Matrix T T ℂ) :
    (List.ofFn fun l => W * F l * Wᴴ).prod =
      W * (List.ofFn F).prod * Wᴴ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons,
      List.ofFn_succ (f := F), List.prod_cons]
    have ih_step := ih (F ∘ Fin.succ)
    simp only [Function.comp_def] at ih_step
    rw [ih_step]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]

/-- The fusion coisometry carries every product letter to its retained
weighted direct sum. -/
theorem fusionCoisometry_mul_mulTensor (α β : Λ) (i j : Fin p) :
    Fam.fusionCoisometry α β * mulTensor (Fam.tensor α) (Fam.tensor β) i j =
      (Matrix.blockDiagonal' fun γ =>
        Fam.chi.matrix α β γ ⊗ₖ Fam.tensor γ i j) *
        Fam.fusionCoisometry α β := by
  rw [Fam.reconstruction]
  simp only [← Matrix.mul_assoc, Fam.coisometry, Matrix.one_mul]

/-- Every product letter carries the adjoint fusion coisometry to its retained
weighted direct sum. -/
theorem mulTensor_mul_fusionCoisometry_conjTranspose
    (α β : Λ) (i j : Fin p) :
    mulTensor (Fam.tensor α) (Fam.tensor β) i j *
        (Fam.fusionCoisometry α β)ᴴ =
      (Fam.fusionCoisometry α β)ᴴ *
        Matrix.blockDiagonal' fun γ =>
          Fam.chi.matrix α β γ ⊗ₖ Fam.tensor γ i j := by
  rw [Fam.reconstruction]
  simp only [Matrix.mul_assoc, Fam.coisometry, Matrix.mul_one]

/-- For every positive chain length, the product of two labelled closed-chain
operators is the sum over retained labels with coefficients
$\operatorname{tr}(\chi_{\alpha,\beta,\gamma}^L)$.

Exact reconstruction telescopes along a nonempty word because the fusion map
is a coisometry.  Cyclicity of trace then removes the outer fusion maps, while
the retained block diagonal contributes the stated trace-power coefficients.

Source: CPSV16, Appendix C.4, lines 2020--2029. -/
theorem mpo_mul_mpo_eq_sum (L : ℕ) (hL : 0 < L) (α β : Λ) :
    mpo (Fam.tensor α) L * mpo (Fam.tensor β) L =
      ∑ γ : Λ, Fam.chi.tracePowerCoeff α β γ L • mpo (Fam.tensor γ) L := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 :=
    ⟨L - 1, (Nat.succ_pred_eq_of_pos hL).symm⟩
  rw [← mpo_mulTensor]
  ext σ τ
  rw [mpo_apply, mpoMatrixEntry, evalWord_ofFn]
  set U := Fam.fusionCoisometry α β
  have hU : U * Uᴴ = 1 := Fam.coisometry α β
  let G : Fin (n + 1) → Matrix
      ((γ : Λ) × (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ)))
      ((γ : Λ) × (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) ℂ :=
    fun l => Matrix.blockDiagonal' fun γ =>
      Fam.chi.matrix α β γ ⊗ₖ Fam.tensor γ (σ l) (τ l)
  set W := Uᴴ
  have hW : Wᴴ * W = 1 := by
    simpa [W] using hU
  have hletters : (fun l : Fin (n + 1) => W * G l * Wᴴ) =
      fun l => mulTensor (Fam.tensor α) (Fam.tensor β) (σ l) (τ l) := by
    funext l
    simpa [W, U, G] using (Fam.reconstruction α β (σ l) (τ l)).symm
  have hconj := listProd_conj_of_conjTranspose_mul_self_fintype W hW G
  have htraceP : Matrix.trace (List.ofFn fun l =>
      mulTensor (Fam.tensor α) (Fam.tensor β) (σ l) (τ l)).prod =
      Matrix.trace (List.ofFn G).prod := by
    rw [← hletters, hconj, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, hW, Matrix.one_mul]
  rw [htraceP]
  simp only [G]
  rw [listProd_blockDiagonal'_kronecker, Matrix.trace_blockDiagonal']
  simp_rw [Matrix.trace_kronecker, Fam.chi.trace_matrix_pow]
  simp only [Matrix.sum_apply, Matrix.smul_apply, mpo_apply, mpoMatrixEntry,
    evalWord_ofFn, smul_eq_mul]

/-- The concrete closed-chain operator family carried by a fusion
coisometry family.

Source: arXiv:1606.00608, lines 962--966. -/
noncomputable def toOperatorFamily :
    BNTLabelOperatorFamily Λ
      (fun L ↦ Matrix (Fin L → Fin p) (Fin L → Fin p) ℂ) :=
  ⟨fun L γ ↦ mpo (Fam.tensor γ) L⟩

@[simp] lemma toOperatorFamily_operator (L : ℕ) (γ : Λ) :
    Fam.toOperatorFamily.operator L γ = mpo (Fam.tensor γ) L := rfl

/-- A fusion coisometry family satisfies the same-length product law with
the coefficients determined by its positive diagonal chi matrices.

Source: CPSV16, Theorem 4.14(ii)--(iii), lines 976--993, and Appendix C.4,
lines 2020--2029. -/
theorem toOperatorFamily_hasSameLengthProductForm :
    Fam.toOperatorFamily.HasSameLengthProductForm
      (BNTLabelCoefficientFamily.ofChi Fam.chi) := by
  intro L hL α β
  simpa [toOperatorFamily_operator, BNTLabelCoefficientFamily.ofChi_coeff]
    using Fam.mpo_mul_mpo_eq_sum L hL α β

/-- The source-faithful active-support fusion clause, together with its
idempotent trace-scalar law, implies the BNT algebra clause.

Source: CPSV16, Theorem 4.14(ii)--(iii), lines 972--993, and Appendix C.4,
lines 1929--1947 and 2020--2046. -/
noncomputable def toBNTAlgebraClause
    (m : BNTLabelTraceScalarFamily Λ)
    (hIdempotent :
      m.HasIdempotentCoefficientForm (BNTLabelCoefficientFamily.ofChi Fam.chi)) :
    BNTAlgebraClause (BNTLabelCoefficientFamily.ofChi Fam.chi)
      Fam.toOperatorFamily m where
  positiveChi := PositiveBNTLabelChiTracePowerForm.ofChi Fam.chi Fam.posEntries
  sameLengthProduct := Fam.toOperatorFamily_hasSameLengthProductForm
  idempotent := hIdempotent

/-- Under the additional assertion that every active-support projection is the
identity, an active fusion coisometry gives the stronger full-support fusion
family. -/
noncomputable def toBNTFusionIsometryFamily_of_fullSupport
    (hfull : ∀ α β : Λ,
      (Fam.fusionCoisometry α β)ᴴ * Fam.fusionCoisometry α β = 1) :
    BNTFusionIsometryFamily Λ p where
  bondDim := Fam.bondDim
  tensor := Fam.tensor
  chi := Fam.chi
  posEntries := Fam.posEntries
  fusionIsometry := Fam.fusionCoisometry
  isometry := hfull
  fusion := Fam.fusion

end BNTFusionCoisometryFamily

end MPOTensor
