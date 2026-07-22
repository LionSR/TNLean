/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.BNTFusionCoisometries

/-!
# Fusion coisometries attached to an MPO tensor

This file attaches the active-support fusion clause of arXiv:1606.00608,
Theorem 4.14(iii), to the basis of normal tensors in a chosen vertical
canonical decomposition of the original MPO tensor. The positive diagonal
matrices in the fusion identity determine the coefficients in the algebra
clause, while the trace scalars are the traces of the multiplicity matrices
in the same vertical decomposition.

## Main results

* `BNTFusionTensorClause` is the tensor-attached form of Theorem 4.14(iii).
* `BNTFusionTensorClause.toBNTAlgebraTensorClause` proves the tensor-attached
  implication from statement (iii) to statement (ii).
* `HasBNTFusionTensorClause.to_hasBNTAlgebraTensorClause` gives the
  corresponding existential implication.

This file proves the implication from statement (iii) to statement (ii) of
Theorem 4.14. The converse construction from the renormalization fixed-point
condition is proved in `BNTFusionTensorClauseFromRFP`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(ii)--(iii), lines 972--993, and Appendix C.4, lines 1929--1947
-/

open scoped BigOperators ComplexOrder Kronecker Matrix

noncomputable section

namespace MPOTensor

/-- The active-support fusion clause of Theorem 4.14(iii), attached to a chosen
vertical canonical decomposition of the MPO tensor \(M\).

The tensors in the fusion identity are precisely the basis of normal tensors
\(M_\alpha\) in
\[
  U\widetilde M U^\dagger
    = \bigoplus_\alpha \mu_\alpha\otimes M_\alpha.
\]
The same positive diagonal matrices \(\chi_{\alpha,\beta,\gamma}\) occur in
the fusion identity and in the length-one idempotent law for
\(m_\alpha=\operatorname{tr}(\mu_\alpha)\).

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951;
Theorem 4.14(iii), lines 986--993; and Appendix C.4, lines 1929--1947 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Local fix (Figure-11 fusion coisometry):** In the retained-row orientation,
the fusion map below satisfies $U_{\alpha,\beta}U_{\alpha,\beta}^\dagger=1$.
Its adjoint reconstructs the complete product tensor, including when a common
zero corner is omitted from the retained direct sum. Documented in
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
structure BNTFusionTensorClause (M : MPOTensor d D) where
  /-- Number of BNT labels in the chosen vertical decomposition. -/
  labelCount : ℕ
  /-- Bond dimension of each vertical BNT tensor. -/
  bondDim : Fin labelCount → ℕ
  /-- Dimension of the positive diagonal matrix \(\mu_\alpha\). -/
  multiplicity : Fin labelCount → ℕ
  /-- Positive diagonal entries of \(\mu_\alpha\). -/
  weight : (α : Fin labelCount) → Fin (multiplicity α) → ℂ
  /-- The chosen vertical basis of normal tensors \(M_\alpha\). -/
  tensor : (α : Fin labelCount) → MPSTensor (D * D) (bondDim α)
  /-- The coisometry from the original physical space onto the retained
  vertical sectors. -/
  verticalCoisometry :
    Matrix
      (Fin (∑ q : Fin (∑ α : Fin labelCount, multiplicity α),
        verticalCopyDim bondDim multiplicity q)) (Fin d) ℂ
  /-- Every BNT label occurs with a nonempty multiplicity space.

  Source: arXiv:1606.00608, Proposition 4.13, lines 948--951. -/
  multiplicity_pos : ∀ α, 0 < multiplicity α
  /-- Every diagonal entry of \(\mu_\alpha\) is positive.

  Source: arXiv:1606.00608, Proposition 4.13, lines 948--951. -/
  weight_pos : ∀ α q, (0 : ℂ) < weight α q
  /-- The vertical change of basis is a coisometry onto the retained sectors.

  Source: arXiv:1606.00608, Proposition 4.13, lines 948--951. -/
  coisometry : verticalCoisometry * (verticalCoisometry)ᴴ = 1
  /-- The chosen tensors form a basis of normal tensors of the vertical tensor.

  Source: arXiv:1606.00608, Proposition 4.13, lines 948--951. -/
  isBNT : MPSTensor.IsBNT (verticalTensor M) labelCount bondDim tensor
  /-- Conjugating the vertical tensor gives the weighted BNT direct sum.

  Source: arXiv:1606.00608, Proposition 4.13, lines 948--951. -/
  forward : ∀ v : Fin (D * D),
    verticalCoisometry * verticalTensor M v * (verticalCoisometry)ᴴ =
      verticalAssembledTensor bondDim multiplicity weight tensor v
  /-- The weighted BNT direct sum reconstructs the vertical tensor, including
  the possible zero-sector complement.

  Source: arXiv:1606.00608, Proposition 4.13, lines 948--951. -/
  reconstruction : ∀ v : Fin (D * D),
    verticalTensor M v = (verticalCoisometry)ᴴ *
      verticalAssembledTensor bondDim multiplicity weight tensor v *
        verticalCoisometry
  /-- The positive diagonal matrices \(\chi_{\alpha,\beta,\gamma}\).

  Source: arXiv:1606.00608, Theorem 4.14(ii)--(iii), lines 976--993. -/
  chi : DiagonalChiFamily (Fin labelCount)
  /-- Every diagonal entry of \(\chi_{\alpha,\beta,\gamma}\) is positive.

  Source: arXiv:1606.00608, Theorem 4.14(ii)--(iii), lines 976--993. -/
  chi_pos : chi.PosEntries
  /-- The fusion coisometry \(U_{\alpha,\beta}\) onto the retained sectors for
  each pair of BNT labels.

  Source: arXiv:1606.00608, Theorem 4.14(iii), lines 986--993. -/
  fusionCoisometry : ∀ α β : Fin labelCount,
    Matrix ((γ : Fin labelCount) × (Fin (chi.dim α β γ) × Fin (bondDim γ)))
      (Fin (bondDim α * bondDim β)) ℂ
  /-- Each fusion map is a coisometry onto the retained direct sum.

  Source: arXiv:1606.00608, Appendix C.4, lines 2020--2029. -/
  fusionCoisometry_mul_conjTranspose : ∀ α β : Fin labelCount,
    fusionCoisometry α β * (fusionCoisometry α β)ᴴ = 1
  /-- The sitewise fusion identity for the concrete vertical BNT tensors.

  Source: arXiv:1606.00608, Theorem 4.14(iii), label `Ualphabeta`,
  lines 986--993. -/
  fusion : ∀ (α β : Fin labelCount) (i j : Fin D),
    fusionCoisometry α β *
        (mulTensor (verticalBNTMPO (tensor α)) (verticalBNTMPO (tensor β))) i j *
          (fusionCoisometry α β)ᴴ =
      Matrix.blockDiagonal' fun γ =>
        chi.matrix α β γ ⊗ₖ (verticalBNTMPO (tensor γ)) i j
  /-- The retained direct sum reconstructs every product letter.

  Source: arXiv:1606.00608, Theorem 4.14(iii), label `Ualphabeta`,
  lines 986--993, and Appendix C.4, lines 2020--2029. -/
  fusionReconstruction : ∀ (α β : Fin labelCount) (i j : Fin D),
    (mulTensor (verticalBNTMPO (tensor α))
        (verticalBNTMPO (tensor β))) i j =
      (fusionCoisometry α β)ᴴ *
        (Matrix.blockDiagonal' fun γ =>
          chi.matrix α β γ ⊗ₖ (verticalBNTMPO (tensor γ)) i j) *
        fusionCoisometry α β
  /-- The length-one idempotent identity for
  \(m_\alpha=\operatorname{tr}(\mu_\alpha)\).

  Source: arXiv:1606.00608, Theorem 4.14(iii), lines 986--993, referring to
  the identity in lines 981--985. -/
  idempotent :
    (verticalBNTTraceScalarFamily weight).HasIdempotentCoefficientForm
      (BNTLabelCoefficientFamily.ofChi chi)

namespace BNTFusionTensorClause

variable {M : MPOTensor d D}

/-- The fusion-coisometry family carried by a tensor-attached fusion clause. -/
def toBNTFusionCoisometryFamily (H : BNTFusionTensorClause M) :
    BNTFusionCoisometryFamily (Fin H.labelCount) D where
  bondDim := H.bondDim
  tensor := fun γ => verticalBNTMPO (H.tensor γ)
  chi := H.chi
  posEntries := H.chi_pos
  fusionCoisometry := H.fusionCoisometry
  coisometry := H.fusionCoisometry_mul_conjTranspose
  fusion := H.fusion
  reconstruction := H.fusionReconstruction

/-- **Tensor-attached implication (iii) to (ii) of Theorem 4.14.**

The fusion isometries for the BNT tensors in a chosen vertical canonical
decomposition give the algebra clause for the same decomposition. Its
coefficients are the trace powers of the same positive diagonal matrices
\(\chi_{\alpha,\beta,\gamma}\), and its trace scalars are
\(m_\alpha=\operatorname{tr}(\mu_\alpha)\) from that decomposition.

This is only the implication from statement (iii) to statement (ii); it makes
no assertion about the renormalization fixed-point condition.

Source: arXiv:1606.00608, Theorem 4.14(ii)--(iii), lines 972--993, and
Appendix C.4, lines 1929--1947 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def toBNTAlgebraTensorClause (H : BNTFusionTensorClause M) :
    BNTAlgebraTensorClause M where
  labelCount := H.labelCount
  bondDim := H.bondDim
  multiplicity := H.multiplicity
  weight := H.weight
  tensor := H.tensor
  verticalCoisometry := H.verticalCoisometry
  multiplicity_pos := H.multiplicity_pos
  weight_pos := H.weight_pos
  coisometry := H.coisometry
  isBNT := H.isBNT
  forward := H.forward
  reconstruction := H.reconstruction
  coeffs := BNTLabelCoefficientFamily.ofChi H.chi
  algebraClause := H.toBNTFusionCoisometryFamily.toBNTAlgebraClause
    (verticalBNTTraceScalarFamily H.weight) H.idempotent

/-- The chosen decomposition in a tensor-attached fusion clause is a vertical
canonical form of the underlying MPO tensor. -/
theorem isVerticalCF (H : BNTFusionTensorClause M) : IsVerticalCF M :=
  BNTAlgebraTensorClause.isVerticalCF
    (BNTFusionTensorClause.toBNTAlgebraTensorClause H)

end BNTFusionTensorClause

/-- Existence of the fusion-coisometry clause for a chosen vertical canonical
decomposition of \(M\).

Source: arXiv:1606.00608, Theorem 4.14(iii), lines 986--993, and
Appendix C.4, lines 1929--1947. -/
def HasBNTFusionTensorClause (M : MPOTensor d D) : Prop :=
  Nonempty (BNTFusionTensorClause M)

namespace HasBNTFusionTensorClause

/-- The tensor-attached fusion-coisometry clause implies the tensor-attached
algebra clause, using the same vertical decomposition and the same positive
diagonal chi matrices.

This is only implication (iii) to (ii) of arXiv:1606.00608, Theorem 4.14;
Appendix C.4, lines 1929--1947. -/
theorem to_hasBNTAlgebraTensorClause {M : MPOTensor d D}
    (h : HasBNTFusionTensorClause M) : HasBNTAlgebraTensorClause M :=
  h.map BNTFusionTensorClause.toBNTAlgebraTensorClause

end HasBNTFusionTensorClause

end MPOTensor
