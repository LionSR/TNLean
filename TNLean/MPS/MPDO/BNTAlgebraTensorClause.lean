/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.BNT.Bridge
import TNLean.MPS.MPDO.BNTTheoremData
import TNLean.MPS.MPDO.VerticalCF

/-!
# The BNT algebra clause attached to an MPO tensor

This file ties the algebra clause of arXiv:1606.00608, Theorem 4.14(ii), to a
chosen vertical canonical decomposition of an MPO tensor.  The length-
\(L\) operators are the closed MPOs of the chosen BNT tensors, and the scalar
\(m_\alpha\) is the sum of the diagonal entries of the corresponding positive
multiplicity matrix.

No comparison with the two-site vertical canonical form is included here.  In
particular, the definitions do not assume the eventual power-sum equality, a
multiplicity-spectrum comparison, fusion isometries, or renormalization maps.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(ii), lines 972--993, and Appendix C.4, lines 2046--2064
-/

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace MPOTensor

/-- Regard a tensor with doubled physical index as an MPO tensor by separating
the two factors of that index.

For a vertical BNT tensor \(M_\alpha\), this is the MPO whose closed length-
\(L\) operator is \(O_L(M_\alpha)\).

Source: arXiv:1606.00608, lines 962--967 and Theorem 4.14(ii), lines 972--985. -/
def verticalBNTMPO {D n : ℕ} (A : MPSTensor (D * D) n) : MPOTensor D n :=
  fun a b => A (finProdFinEquiv (a, b))

@[simp]
theorem verticalBNTMPO_apply {D n : ℕ} (A : MPSTensor (D * D) n)
    (a b : Fin D) :
    verticalBNTMPO A a b = A (finProdFinEquiv (a, b)) :=
  rfl

/-- Separating and then recombining the doubled physical index recovers the
original tensor. -/
@[simp]
theorem verticalBNTMPO_toMPSTensor {D n : ℕ} (A : MPSTensor (D * D) n) :
    (verticalBNTMPO A).toMPSTensor = A := by
  funext ab
  change A (finProdFinEquiv (ab.divNat, ab.modNat)) = A ab
  exact congrArg A (finProdFinEquiv.apply_symm_apply ab)

/-- The concrete operator family \(O_L(M_\alpha)\) of a chosen vertical BNT
family.

Source: arXiv:1606.00608, lines 962--978 and Appendix C.4, lines 2048--2058. -/
def verticalBNTOperatorFamily {g D : ℕ} {dim : Fin g → ℕ}
    (A : (α : Fin g) → MPSTensor (D * D) (dim α)) :
    BNTLabelOperatorFamily (Fin g)
      (fun L => Matrix (Fin L → Fin D) (Fin L → Fin D) ℂ) :=
  ⟨fun L α => mpo (verticalBNTMPO (A α)) L⟩

@[simp]
theorem verticalBNTOperatorFamily_operator {g D : ℕ} {dim : Fin g → ℕ}
    (A : (α : Fin g) → MPSTensor (D * D) (dim α)) (L : ℕ) (α : Fin g) :
    (verticalBNTOperatorFamily A).operator L α = mpo (verticalBNTMPO (A α)) L :=
  rfl

/-- The scalars \(m_\alpha=\operatorname{tr}(\mu_\alpha)\) of a chosen
vertical canonical decomposition.  Since \(\mu_\alpha\) is diagonal with
entries \(\omega_{\alpha,q}\), its trace is their sum.

Source: arXiv:1606.00608, Theorem 4.14(ii), lines 981--985, and Appendix C.4,
lines 2058--2064. -/
def verticalBNTTraceScalarFamily {g : ℕ} {mult : Fin g → ℕ}
    (ω : (α : Fin g) → Fin (mult α) → ℂ) :
    BNTLabelTraceScalarFamily (Fin g) :=
  ⟨fun α => ∑ q, ω α q⟩

@[simp]
theorem verticalBNTTraceScalarFamily_traceScalar {g : ℕ} {mult : Fin g → ℕ}
    (ω : (α : Fin g) → Fin (mult α) → ℂ) (α : Fin g) :
    (verticalBNTTraceScalarFamily ω).traceScalar α = ∑ q, ω α q :=
  rfl

/-- The algebra clause of Theorem 4.14(ii), attached to a chosen vertical
canonical decomposition of the MPO tensor \(M\).

The fields through `reconstruction` are precisely a witness of the vertical
canonical form
\[
  U\widetilde M U^\dagger
    = \bigoplus_\alpha \mu_\alpha\otimes M_\alpha,
  \qquad
  \widetilde M
    = U^\dagger\left(\bigoplus_\alpha
        \mu_\alpha\otimes M_\alpha\right)U.
\]
The final field requires the BNT algebra clause for the concrete operators
\(O_L(M_\alpha)\) and the concrete scalars
\(m_\alpha=\sum_q\omega_{\alpha,q}=\operatorname{tr}(\mu_\alpha)\).

This structure contains no one-site/two-site BNT comparison and no channel or
fusion hypothesis.  Those are conclusions of the remaining proof of the
implication (ii) to (i), not part of statement (ii).

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951; Theorem 4.14(ii),
lines 972--993; and Appendix C.4, lines 2046--2064 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure BNTAlgebraTensorClause (M : MPOTensor d D) where
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
  /-- The chosen tensors form a CPSV16 basis of normal tensors of the vertical tensor.

  Source: arXiv:1606.00608, Proposition 4.13, lines 948--951. -/
  isCPSVBNT : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
    (fun α ↦ ⟨bondDim α, tensor α⟩)
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
  /-- The coefficient family \(c^{(L)}_{\alpha,\beta,\gamma}\). -/
  coeffs : BNTLabelCoefficientFamily (Fin labelCount)
  /-- The positive chi trace-power law, the concrete same-length product law,
  and the length-one idempotent law.

  Source: arXiv:1606.00608, Theorem 4.14(ii), lines 972--985, and Appendix C.4,
  lines 2046--2064. -/
  algebraClause : BNTAlgebraClause coeffs
    (verticalBNTOperatorFamily tensor) (verticalBNTTraceScalarFamily weight)

namespace BNTAlgebraTensorClause

/-- The source BNT predicate in the tensor clause entails the algebraic BNT
predicate for its chosen vertical decomposition. -/
theorem isBNT {M : MPOTensor d D} (H : BNTAlgebraTensorClause M) :
    MPSTensor.IsBNT (verticalTensor M) H.labelCount H.bondDim H.tensor :=
  H.isCPSVBNT.isBNT

/-- The chosen decomposition in a tensor-attached BNT algebra clause is a
vertical canonical form of the underlying MPO tensor. -/
theorem isVerticalCF {M : MPOTensor d D} (H : BNTAlgebraTensorClause M) :
    IsVerticalCF M :=
  ⟨H.labelCount, H.bondDim, H.multiplicity, H.weight, H.tensor,
    H.verticalCoisometry, H.multiplicity_pos, H.weight_pos, H.coisometry,
    H.isBNT, H.forward, H.reconstruction⟩

variable {M : MPOTensor d D} (H : BNTAlgebraTensorClause M)

/-- The concrete BNT-label operator family carried by the tensor-attached
clause. -/
def operators : BNTLabelOperatorFamily (Fin H.labelCount)
    (fun L => Matrix (Fin L → Fin D) (Fin L → Fin D) ℂ) :=
  verticalBNTOperatorFamily H.tensor

/-- The concrete trace scalars carried by the tensor-attached clause. -/
def traceScalars : BNTLabelTraceScalarFamily (Fin H.labelCount) :=
  verticalBNTTraceScalarFamily H.weight

@[simp]
theorem operators_operator (L : ℕ) (α : Fin H.labelCount) :
    H.operators.operator L α = mpo (verticalBNTMPO (H.tensor α)) L :=
  rfl

@[simp]
theorem traceScalars_traceScalar (α : Fin H.labelCount) :
    H.traceScalars.traceScalar α = ∑ q, H.weight α q :=
  rfl

end BNTAlgebraTensorClause

/-- Existence of the BNT algebra clause for a chosen vertical canonical
decomposition of \(M\).

The standing hypotheses that \(M\) is in horizontal canonical form and
generates MPDOs belong to the eventual equivalence theorem; they are not
duplicated in this predicate.

Source: arXiv:1606.00608, Theorem 4.14(ii), lines 972--993, and Appendix C.4,
lines 2046--2064. -/
def HasBNTAlgebraTensorClause (M : MPOTensor d D) : Prop :=
  Nonempty (BNTAlgebraTensorClause M)

namespace HasBNTAlgebraTensorClause

/-- A tensor-attached BNT algebra clause supplies a vertical canonical form. -/
theorem isVerticalCF {M : MPOTensor d D} (h : HasBNTAlgebraTensorClause M) :
    IsVerticalCF M := by
  obtain ⟨H⟩ := h
  exact H.isVerticalCF

end HasBNTAlgebraTensorClause

end MPOTensor
