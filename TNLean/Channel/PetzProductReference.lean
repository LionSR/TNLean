/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.MaximallyMixed
import TNLean.Channel.PetzRecovery

/-!
# Product-reference Petz factorizations

This file studies partial-trace Petz maps whose reference matrix is a tensor
product $\rho_A\otimes\rho_{BC}$, after reassociating the product indices so
that the right partial trace removes $C$. For a possibly singular first factor,
TNLean's global zero-on-kernel raw extension factors through support compression
on $A$. On supported inputs, and globally when $\rho_A$ is positive definite,
this gives the identity-tensored recovery formula associated with HJPW
Theorem 3, equation (10).

The file also records the maximally mixed specialization. In that full-support
case, both the raw map and TNLean's chosen complementary completion factor as
the identity on $A$ tensored with their local counterparts. No analogous
factorization is asserted here for TNLean's generic completed channel with a
singular first-factor reference.

## Main declarations

* `Matrix.productTensorReference`: the reassociated product reference.
* `Matrix.productTensorReference_posSemidef`: positivity of the product
  reference.
* `Matrix.partialTraceRight_productTensorReference`: its retained marginal.
* `Matrix.supportProj_partialTraceRight_productTensorReference`: factorization
  of the retained marginal support projector.
* `Matrix.supportCompressionMap`: the sandwich linear map $X \mapsto PXP$.
* `Matrix.partialTraceRightPetzMap_productTensor_kronecker`: raw support
  factorization on elementary tensors.
* `Matrix.partialTraceRightPetzMap_productTensor`: global zero-on-kernel raw
  support factorization.
* `Matrix.partialTraceRightPetzMap_productTensor_apply_of_left_supported`:
  identity-tensored recovery on supported inputs.
* `Matrix.partialTraceRightPetzMap_productTensor_of_posDef_left`: global
  identity-tensored recovery for a positive-definite first factor.
* `Matrix.maximallyMixedTensorReference`: the maximally mixed product reference.
* `Matrix.partialTraceRightPetzMap_maximallyMixedTensor`: raw factorization for
  the maximally mixed reference.
* `Matrix.partialTraceRightPetzComplementMap_maximallyMixedTensor`: factorization
  of TNLean's complementary completion term in the maximally mixed case.
* `Matrix.partialTraceRightPetzChannel_maximallyMixedTensor`: completed-channel
  factorization in the maximally mixed case.
* `Matrix.partialTraceRightPetzChannel_maximallyMixedTensor_isKrausCPTP`: the
  completed map is CPTP when the local reference has trace one.

## References

* Hayden, Jozsa, Petz, and Winter, arXiv:quant-ph/0304007v2,
  Theorem 3 and equation (10).
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Kronecker

namespace Matrix

section HJPWProductReferenceFactorization

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- The product reference $\rho_A\otimes\rho_{BC}$ from HJPW Theorem 3,
equation (10), reindexed from $A\times(B\times C)$ to $(A\times B)\times C$ so
that `partialTraceRight` traces out $C$. -/
def productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ) :
    Matrix ((A × B) × C) ((A × B) × C) ℂ :=
  (ρA ⊗ₖ ρBC).submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] in
/-- The product reference in HJPW Theorem 3, equation (10), is positive
semidefinite when both factors are positive semidefinite. -/
theorem productTensorReference_posSemidef
    [Finite A] [Finite B] [Finite C]
    {ρA : Matrix A A ℂ} {ρBC : Matrix (B × C) (B × C) ℂ}
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    (productTensorReference ρA ρBC).PosSemidef := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  letI := Fintype.ofFinite C
  exact (hA.kronecker hBC).submatrix _

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq C] in
/-- The retained $AB$ marginal of the product reference from HJPW Theorem 3,
equation (10), is $\rho_A\otimes\rho_B$. -/
theorem partialTraceRight_productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ) :
    partialTraceRight (productTensorReference ρA ρBC) =
      ρA ⊗ₖ partialTraceRight ρBC := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [productTensorReference, partialTraceRight_apply,
    Matrix.kroneckerMap_apply, Finset.mul_sum]

/-- The square root of the product reference from HJPW Theorem 3, equation
(10), factors across its two positive-semidefinite factors after canonical
reassociation. -/
theorem cfcSqrt_productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    (productTensorReference_posSemidef hA hBC).isHermitian.cfc Real.sqrt =
      (hA.isHermitian.cfc Real.sqrt ⊗ₖ hBC.isHermitian.cfc Real.sqrt).submatrix
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) := by
  rw [← (productTensorReference_posSemidef hA hBC).isHermitian.cfc_eq]
  change cfc Real.sqrt
      ((ρA ⊗ₖ ρBC).submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)) = _
  have hcfc := Matrix.cfc_submatrix_equiv (hA.kronecker hBC).isHermitian Real.sqrt
    (Equiv.prodAssoc A B C).symm
  rw [show cfc Real.sqrt
      ((ρA ⊗ₖ ρBC).submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)) =
      (cfc Real.sqrt (ρA ⊗ₖ ρBC)).submatrix
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) by
      simpa only [Equiv.symm_symm] using hcfc]
  congr 1
  have hsqrt := hA.sqrt_kronecker hBC
  rw [CFC.sqrt_eq_real_sqrt (ρA ⊗ₖ ρBC) (hA.kronecker hBC).nonneg,
    CFC.sqrt_eq_real_sqrt ρA hA.nonneg,
    CFC.sqrt_eq_real_sqrt ρBC hBC.nonneg,
    cfcₙ_eq_cfc, cfcₙ_eq_cfc, cfcₙ_eq_cfc,
    hA.isHermitian.cfc_eq, hBC.isHermitian.cfc_eq] at hsqrt
  exact hsqrt

omit [DecidableEq C] in
/-- The support inverse square root of the $AB$ marginal of the product
reference in HJPW Theorem 3, equation (10), factors across $A$ and $B$. -/
theorem supportInvSqrt_partialTraceRight_productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    (PosSemidef.partialTraceRight
      (productTensorReference_posSemidef hA hBC)).supportInvSqrt =
      hA.supportInvSqrt ⊗ₖ (PosSemidef.partialTraceRight hBC).supportInvSqrt := by
  unfold PosSemidef.supportInvSqrt
  rw [← (PosSemidef.partialTraceRight
      (productTensorReference_posSemidef hA hBC)).isHermitian.cfc_eq,
    ← hA.isHermitian.cfc_eq,
    ← (PosSemidef.partialTraceRight hBC).isHermitian.cfc_eq,
    partialTraceRight_productTensorReference]
  have hfac := hA.supportInvSqrt_kronecker
    (PosSemidef.partialTraceRight hBC)
  unfold PosSemidef.supportInvSqrt at hfac
  rw [← (hA.kronecker
      (PosSemidef.partialTraceRight hBC)).isHermitian.cfc_eq,
    ← hA.isHermitian.cfc_eq,
    ← (PosSemidef.partialTraceRight hBC).isHermitian.cfc_eq] at hfac
  exact hfac

omit [DecidableEq C] in
/-- The support projector of the $AB$ marginal of the product reference in
HJPW Theorem 3, equation (10), is $P_A\otimes P_B$. -/
theorem supportProj_partialTraceRight_productTensorReference
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    (PosSemidef.partialTraceRight
      (productTensorReference_posSemidef hA hBC)).isHermitian.supportProj =
      hA.isHermitian.supportProj ⊗ₖ
        (PosSemidef.partialTraceRight hBC).isHermitian.supportProj := by
  let hτ := PosSemidef.partialTraceRight
    (productTensorReference_posSemidef hA hBC)
  rw [← hτ.supportInvSqrt_mul_self_mul_supportInvSqrt,
    supportInvSqrt_partialTraceRight_productTensorReference ρA ρBC hA hBC,
    partialTraceRight_productTensorReference ρA ρBC,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hA.supportInvSqrt_mul_self_mul_supportInvSqrt,
    (PosSemidef.partialTraceRight hBC).supportInvSqrt_mul_self_mul_supportInvSqrt]

/-- The sandwich linear map $X\mapsto PXP$. When $P$ is a support projector,
this map compresses to the corresponding support subspace. -/
def supportCompressionMap
    (P : Matrix A A ℂ) : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun X := P * X * P
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

/-- Evaluation of the sandwich linear map $X\mapsto PXP$. -/
@[simp]
theorem supportCompressionMap_apply (P X : Matrix A A ℂ) :
    supportCompressionMap P X = P * X * P := rfl

/-- **Raw support factorization underlying HJPW equation (10), elementary-tensor
form.** For an arbitrary positive-semidefinite first factor, TNLean's global
zero-on-kernel raw extension sends $A_0\otimes X$ to
$(P_AA_0P_A)\otimes\mathcal R^{\mathrm{raw}}_{\rho_{BC}}(X)$ after canonical
reassociation.

The support compression is part of the ambient-space extension: it disappears
only on supported inputs or when $\rho_A$ is positive definite. This statement
does not identify the zero-on-kernel extension itself with HJPW equation (10),
and it makes no claim about TNLean's generic completed channel. -/
theorem partialTraceRightPetzMap_productTensor_kronecker
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef)
    (A₀ : Matrix A A ℂ) (X : Matrix B B ℂ) :
    equivReindexMap (Equiv.prodAssoc A B C)
        (partialTraceRightPetzMap
          (productTensorReference ρA ρBC)
          (productTensorReference_posSemidef hA hBC)
          (A₀ ⊗ₖ X)) =
      (hA.isHermitian.supportProj * A₀ * hA.isHermitian.supportProj) ⊗ₖ
        partialTraceRightPetzMap ρBC hBC X := by
  rw [partialTraceRightPetzMap_apply, partialTraceRightPetzMap_apply]
  rw [cfcSqrt_productTensorReference ρA ρBC hA hBC,
    supportInvSqrt_partialTraceRight_productTensorReference ρA ρBC hA hBC]
  change (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc A B C)) (_ * _ * _) = _
  rw [map_mul, map_mul]
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  rw [show (((hA.isHermitian.cfc Real.sqrt ⊗ₖ
        hBC.isHermitian.cfc Real.sqrt).submatrix
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)).submatrix
        (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm) =
      hA.isHermitian.cfc Real.sqrt ⊗ₖ hBC.isHermitian.cfc Real.sqrt by
    ext i j
    rfl]
  rw [show (leftKroneckerEmbed (n := C)
        ((hA.supportInvSqrt ⊗ₖ
            (PosSemidef.partialTraceRight hBC).supportInvSqrt) *
          (A₀ ⊗ₖ X) *
          (hA.supportInvSqrt ⊗ₖ
            (PosSemidef.partialTraceRight hBC).supportInvSqrt))).submatrix
        (Equiv.prodAssoc A B C).symm (Equiv.prodAssoc A B C).symm =
      (hA.supportInvSqrt * A₀ * hA.supportInvSqrt) ⊗ₖ
        leftKroneckerEmbed (n := C)
          ((PosSemidef.partialTraceRight hBC).supportInvSqrt * X *
            (PosSemidef.partialTraceRight hBC).supportInvSqrt) by
    simp only [leftKroneckerEmbed_apply]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    ext ⟨a, bc⟩ ⟨a', bc'⟩
    simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      Equiv.prodAssoc_symm_apply]
    ring]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  have hfirst :
      hA.isHermitian.cfc Real.sqrt *
          (hA.supportInvSqrt * A₀ * hA.supportInvSqrt) *
          hA.isHermitian.cfc Real.sqrt =
        hA.isHermitian.supportProj * A₀ * hA.isHermitian.supportProj := by
    calc
      _ = (hA.isHermitian.cfc Real.sqrt * hA.supportInvSqrt) * A₀ *
          (hA.supportInvSqrt * hA.isHermitian.cfc Real.sqrt) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hA.cfc_sqrt_mul_supportInvSqrt,
          hA.supportInvSqrt_mul_cfc_sqrt]
        rfl
  rw [hfirst]

/-- **Global raw support factorization underlying HJPW equation (10).** For a
possibly singular positive-semidefinite $\rho_A$, TNLean's zero-on-kernel raw
ambient extension is the local recovery map tensored with support compression on $A$:
\[
  \mathcal R^{\mathrm{raw}}_{\rho_A\otimes\rho_{BC}}
  = \mathcal C_{P_A}\otimes
    \mathcal R^{\mathrm{raw}}_{\rho_{BC}}.
\]

This equality describes the ambient-space extension underlying the source
formula, not HJPW equation (10) itself. It deliberately does not claim a global
identity-tensored formula for singular $\rho_A$ or a factorization of TNLean's
generic completed channel. -/
theorem partialTraceRightPetzMap_productTensor
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc A B C) ∘ₗ
        partialTraceRightPetzMap
          (productTensorReference ρA ρBC)
          (productTensorReference_posSemidef hA hBC) =
      idTensorMapLM (δ := A) (partialTraceRightPetzMap ρBC hBC) ∘ₗ
        tensorMapIdLM (δ := B)
          (supportCompressionMap hA.isHermitian.supportProj) := by
  apply LinearMap.ext
  intro X
  obtain ⟨A₀, Y, hX⟩ :=
    hasOperatorSchmidtDecomposition_operatorSchmidtRank X
  rw [hX]
  simp only [LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorMapIdLM_apply, tensorMapId_kronecker,
    idTensorMapLM_apply, idTensorMap_kronecker,
    supportCompressionMap_apply]
  exact partialTraceRightPetzMap_productTensor_kronecker
    ρA ρBC hA hBC (A₀ i) (Y i)

/-- Applying support compression on the $A$ factor is the same as sandwiching
by $P_A\otimes\mathbf 1_B$. This is the support condition in the
source-compatible form of HJPW equation (10). -/
theorem tensorMapId_supportCompressionMap
    {ρA : Matrix A A ℂ} (hA : ρA.PosSemidef)
    (X : Matrix (A × B) (A × B) ℂ) :
    tensorMapIdLM (δ := B) (supportCompressionMap hA.isHermitian.supportProj) X =
      (hA.isHermitian.supportProj ⊗ₖ (1 : Matrix B B ℂ)) * X *
        (hA.isHermitian.supportProj ⊗ₖ (1 : Matrix B B ℂ)) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [tensorMapIdLM_apply, tensorMapId_apply,
    supportCompressionMap_apply, Matrix.mul_apply,
    bipartiteSlice_apply, Matrix.kroneckerMap_apply, one_apply]
  simp_rw [Fintype.sum_prod_type]
  simp

/-- **Supported-input corollary of HJPW Theorem 3, equation (10).** If an input
on $A\otimes B$ is supported by $P_A$ on its left tensor factor, then the
support compression in the raw product-reference factorization disappears,
and the map agrees with
$\operatorname{id}_A\otimes\mathcal R^{\mathrm{raw}}_{\rho_{BC}}$.

This is the source-compatible support formula. It does not assert the identity
on unsupported ambient-space inputs when $\rho_A$ is singular. -/
theorem partialTraceRightPetzMap_productTensor_apply_of_left_supported
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosSemidef) (hBC : ρBC.PosSemidef)
    (X : Matrix (A × B) (A × B) ℂ)
    (hX : (hA.isHermitian.supportProj ⊗ₖ (1 : Matrix B B ℂ)) * X *
      (hA.isHermitian.supportProj ⊗ₖ (1 : Matrix B B ℂ)) = X) :
    equivReindexMap (Equiv.prodAssoc A B C)
        (partialTraceRightPetzMap
          (productTensorReference ρA ρBC)
          (productTensorReference_posSemidef hA hBC) X) =
      idTensorMapLM (δ := A) (partialTraceRightPetzMap ρBC hBC) X := by
  have hglobal := congrArg (fun T ↦ T X)
    (partialTraceRightPetzMap_productTensor ρA ρBC hA hBC)
  simp only [LinearMap.comp_apply] at hglobal
  rw [tensorMapId_supportCompressionMap (B := B) hA X, hX] at hglobal
  exact hglobal

/-- **Full-support corollary of HJPW Theorem 3, equation (10).** If
$\rho_A$ is positive definite, then $P_A=\mathbf 1_A$ and the global raw
product-reference Petz map is literally
$\operatorname{id}_A\otimes\mathcal R^{\mathrm{raw}}_{\rho_{BC}}$ after
canonical reassociation.

Positive definiteness identifies the support space with the full ambient
matrix algebra. This statement makes no claim about the generic completed
channel for singular $\rho_A$. -/
theorem partialTraceRightPetzMap_productTensor_of_posDef_left
    (ρA : Matrix A A ℂ) (ρBC : Matrix (B × C) (B × C) ℂ)
    (hA : ρA.PosDef) (hBC : ρBC.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc A B C) ∘ₗ
        partialTraceRightPetzMap
          (productTensorReference ρA ρBC)
          (productTensorReference_posSemidef hA.posSemidef hBC) =
      idTensorMapLM (δ := A) (partialTraceRightPetzMap ρBC hBC) := by
  rw [partialTraceRightPetzMap_productTensor ρA ρBC hA.posSemidef hBC]
  have hproj : hA.posSemidef.isHermitian.supportProj = 1 :=
    hA.supportProj_eq_one
  have hcompression : supportCompressionMap hA.posSemidef.isHermitian.supportProj =
      (LinearMap.id : Matrix A A ℂ →ₗ[ℂ] Matrix A A ℂ) := by
    apply LinearMap.ext
    intro X
    change hA.posSemidef.isHermitian.supportProj * X *
      hA.posSemidef.isHermitian.supportProj = X
    rw [hproj]
    simp
  rw [hcompression, tensorMapIdLM_id, LinearMap.comp_id]

end HJPWProductReferenceFactorization

section HJPWTensorFactorization

variable {dA : ℕ} [NeZero dA]
variable {B C : Type*} [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- The reference
$\sigma_{ABC}=d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$, reindexed from
$A\times(B\times C)$ to $(A\times B)\times C$ so that `partialTraceRight`
traces out $C$.

This is the maximally mixed specialization of the reference in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, equation (10). It is
not the Hayashi--Koashi--Imoto block decomposition. -/
noncomputable def maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    Matrix ((Fin dA × B) × C) ((Fin dA × B) × C) ℂ :=
  (maximallyMixedOn (dA := dA) ⊗ₖ ρ).submatrix
    (Equiv.prodAssoc (Fin dA) B C) (Equiv.prodAssoc (Fin dA) B C)

omit [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] in
/-- The maximally mixed tensor reference is positive semidefinite whenever
$\rho_{BC}$ is positive semidefinite. -/
theorem maximallyMixedTensorReference_posSemidef
    [Finite B] [Finite C]
    {ρ : Matrix (B × C) (B × C) ℂ} (hρ : ρ.PosSemidef) :
    (maximallyMixedTensorReference (dA := dA) ρ).PosSemidef := by
  classical
  letI := Fintype.ofFinite B
  letI := Fintype.ofFinite C
  exact (maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker hρ
    |>.submatrix _

omit [NeZero dA] [Fintype B] [DecidableEq B] [DecidableEq C] in
/-- Tracing $C$ from the maximally mixed specialization of HJPW equation (10)
gives $d_A^{-1}\mathbf 1_A\otimes\rho_B$. -/
theorem partialTraceRight_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    partialTraceRight (maximallyMixedTensorReference (dA := dA) ρ) =
      maximallyMixedOn (dA := dA) ⊗ₖ partialTraceRight ρ := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [maximallyMixedTensorReference, maximallyMixedOn,
    partialTraceRight_apply, Matrix.kroneckerMap_apply,
    Matrix.smul_apply, Finset.mul_sum]

private theorem cfcSqrt_maximallyMixedOn_kronecker
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    ((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker hρ).isHermitian.cfc
        Real.sqrt =
      (Real.sqrt ((dA : ℝ)⁻¹) : ℂ) •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          hρ.isHermitian.cfc Real.sqrt) := by
  let c : ℝ := (dA : ℝ)⁻¹
  have hc : 0 ≤ c := by positivity
  have hbase : maximallyMixedOn (dA := dA) ⊗ₖ ρ =
      c • ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ ρ) := by
    ext a b
    simp [maximallyMixedOn, c, Matrix.kroneckerMap_apply,
      Matrix.smul_apply]
    ring
  have hsqrt :=
    ((Matrix.PosSemidef.one (n := Fin dA)).kronecker hρ).sqrt_smul hc
  have hleft : CFC.sqrt (maximallyMixedOn (dA := dA) ⊗ₖ ρ) =
      ((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker
        hρ).isHermitian.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt _
      ((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker hρ).nonneg,
      cfcₙ_eq_cfc,
      ((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker
        hρ).isHermitian.cfc_eq]
  have hright : CFC.sqrt
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ ρ) =
      ((Matrix.PosSemidef.one (n := Fin dA)).kronecker
        hρ).isHermitian.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt _
      ((Matrix.PosSemidef.one (n := Fin dA)).kronecker hρ).nonneg,
      cfcₙ_eq_cfc,
      ((Matrix.PosSemidef.one (n := Fin dA)).kronecker
        hρ).isHermitian.cfc_eq]
  calc
    _ = CFC.sqrt (maximallyMixedOn (dA := dA) ⊗ₖ ρ) := hleft.symm
    _ = CFC.sqrt
        (c • ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ ρ)) := by rw [← hbase]
    _ = Real.sqrt c • CFC.sqrt
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ ρ) := hsqrt
    _ = Real.sqrt c •
        ((Matrix.PosSemidef.one (n := Fin dA)).kronecker
          hρ).isHermitian.cfc Real.sqrt := by rw [hright]
    _ = Real.sqrt c • ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        hρ.isHermitian.cfc Real.sqrt) := by
      rw [← ((Matrix.PosSemidef.one (n := Fin dA)).kronecker
        hρ).isHermitian.cfc_eq,
        Matrix.cfc_one_kronecker hρ.isHermitian, hρ.isHermitian.cfc_eq]
    _ = (Real.sqrt ((dA : ℝ)⁻¹) : ℂ) •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          hρ.isHermitian.cfc Real.sqrt) := by rw [Complex.coe_smul]

/-- The square root in the maximally mixed specialization of HJPW equation
(10) factors into the dimension normalization and the square root of $\rho_{BC}$, after the
canonical product-index reassociation. -/
theorem cfcSqrt_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    (maximallyMixedTensorReference_posSemidef
      (dA := dA) hρ).isHermitian.cfc Real.sqrt =
      ((Real.sqrt ((dA : ℝ)⁻¹) : ℂ) •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          hρ.isHermitian.cfc Real.sqrt)).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C) := by
  rw [← (maximallyMixedTensorReference_posSemidef
    (dA := dA) hρ).isHermitian.cfc_eq]
  change cfc Real.sqrt
      ((maximallyMixedOn (dA := dA) ⊗ₖ ρ).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C)) = _
  have hcfc := Matrix.cfc_submatrix_equiv
    (((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker
      hρ).isHermitian) Real.sqrt (Equiv.prodAssoc (Fin dA) B C).symm
  rw [show cfc Real.sqrt
      ((maximallyMixedOn (dA := dA) ⊗ₖ ρ).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C)) =
      (cfc Real.sqrt (maximallyMixedOn (dA := dA) ⊗ₖ ρ)).submatrix
        (Equiv.prodAssoc (Fin dA) B C)
        (Equiv.prodAssoc (Fin dA) B C) by
        simpa only [Equiv.symm_symm] using hcfc]
  rw [((maximallyMixedOn_posDef (dA := dA)).posSemidef.kronecker
    hρ).isHermitian.cfc_eq, cfcSqrt_maximallyMixedOn_kronecker ρ hρ]

omit [Fintype C] [DecidableEq B] [DecidableEq C] in
/-- Tracing out the untouched $A\times B$ factors from the maximally mixed
specialization of HJPW equation (10) gives the $C$ marginal of $\rho_{BC}$. -/
theorem partialTraceLeft_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    partialTraceLeft (maximallyMixedTensorReference (dA := dA) ρ) =
      partialTraceLeft ρ := by
  ext c c'
  simp only [maximallyMixedTensorReference, maximallyMixedOn,
    partialTraceLeft_apply, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    Matrix.submatrix_apply, Equiv.prodAssoc_apply, smul_eq_mul,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [one_apply_eq, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hd : (dA : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne dA
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

omit [DecidableEq B] [DecidableEq C] in
/-- The maximally mixed tensor reference has the same trace as $\rho_{BC}$. -/
theorem trace_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) :
    Matrix.trace (maximallyMixedTensorReference (dA := dA) ρ) =
      Matrix.trace ρ := by
  rw [← trace_partialTraceLeft,
    partialTraceLeft_maximallyMixedTensorReference, trace_partialTraceLeft]

omit [DecidableEq C] in
/-- For the maximally mixed specialization of HJPW equation (10), the support
inverse square root of the $AB$ marginal is $\sqrt{d_A}\,\mathbf 1_A\otimes\rho_B^{-1/2}$ on its
support. -/
theorem supportInvSqrt_partialTraceRight_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    (PosSemidef.partialTraceRight
      (maximallyMixedTensorReference_posSemidef
        (dA := dA) hρ)).supportInvSqrt =
      (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ •
        ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          (PosSemidef.partialTraceRight hρ).supportInvSqrt) := by
  classical
  let c : ℝ := (dA : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA))
  have hmarg :
      partialTraceRight (maximallyMixedTensorReference (dA := dA) ρ) =
        c • ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
          partialTraceRight ρ) := by
    rw [partialTraceRight_maximallyMixedTensorReference]
    ext a b
    simp [maximallyMixedOn, c, Matrix.kroneckerMap_apply,
      Matrix.smul_apply]
    ring
  let hbase := (Matrix.PosSemidef.one (n := Fin dA)).kronecker
    (PosSemidef.partialTraceRight hρ)
  have hscaled := hbase.supportInvSqrt_smul hc
  unfold PosSemidef.supportInvSqrt at hscaled ⊢
  rw [← (PosSemidef.partialTraceRight
    (maximallyMixedTensorReference_posSemidef
      (dA := dA) hρ)).isHermitian.cfc_eq,
    hmarg, (hbase.smul hc.le).isHermitian.cfc_eq]
  rw [hscaled]
  congr 1
  exact Matrix.PosSemidef.supportInvSqrt_one_kronecker
    (PosSemidef.partialTraceRight hρ)

omit [DecidableEq C] in
/-- The support projector of the $AB$ marginal in the maximally mixed
specialization of HJPW equation (10) is the identity on $A$ tensored with the
support projector of $\rho_B$.

The proof uses the support-inverse sandwich
$\tau^{-1/2}\tau\tau^{-1/2}=P_{\operatorname{supp}\tau}$ together with the
specialized support-inverse factorization above. -/
theorem supportProj_partialTraceRight_maximallyMixedTensorReference
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    (PosSemidef.partialTraceRight
      (maximallyMixedTensorReference_posSemidef
        (dA := dA) hρ)).isHermitian.supportProj =
      (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ
        (PosSemidef.partialTraceRight hρ).isHermitian.supportProj := by
  let hτ := PosSemidef.partialTraceRight
    (maximallyMixedTensorReference_posSemidef (dA := dA) hρ)
  have hsupport := hτ.supportInvSqrt_mul_self_mul_supportInvSqrt
  rw [← hsupport]
  rw [supportInvSqrt_partialTraceRight_maximallyMixedTensorReference ρ hρ,
    partialTraceRight_maximallyMixedTensorReference]
  simp only [maximallyMixedOn, Matrix.smul_mul, Matrix.mul_smul]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one,
    (PosSemidef.partialTraceRight hρ).supportInvSqrt_mul_self_mul_supportInvSqrt]
  have hc : (0 : ℝ) < (dA : ℝ)⁻¹ := inv_pos.mpr (by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dA))
  have hcancelR : (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ *
      (Real.sqrt ((dA : ℝ)⁻¹))⁻¹ * (dA : ℝ)⁻¹ = 1 := by
    calc
      _ = (Real.sqrt ((dA : ℝ)⁻¹) *
          Real.sqrt ((dA : ℝ)⁻¹))⁻¹ * (dA : ℝ)⁻¹ := by
        rw [mul_inv]
      _ = ((dA : ℝ)⁻¹)⁻¹ * (dA : ℝ)⁻¹ := by
        rw [← pow_two, Real.sq_sqrt hc.le]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hc)
  have hcancelC : (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) * (dA : ℂ)⁻¹ = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.ofReal_one] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) hcancelR
  ext i j
  simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply, one_apply,
    smul_eq_mul]
  by_cases hij : i.1 = j.1
  · simp only [hij, if_pos, Complex.real_smul]
    rw [mul_one, one_mul]
    change (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) *
      ((((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) *
        ((dA : ℂ)⁻¹ *
          (PosSemidef.partialTraceRight hρ).isHermitian.supportProj i.2 j.2)) = _
    calc
      _ = ((((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt ((dA : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) * (dA : ℂ)⁻¹) *
          (PosSemidef.partialTraceRight hρ).isHermitian.supportProj i.2 j.2 := by ring
      _ = _ := by rw [hcancelC, one_mul]
  · simp [hij]

/-- **Maximally mixed specialization of HJPW equation (10), elementary-tensor
algebra.** For the reference
$\sigma_{ABC}=d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$, the raw partial-trace
Petz support formula sends every elementary tensor $A_0\otimes X_B$ to
$A_0\otimes\mathcal R_{\rho_{BC}}(X_B)$, up to the canonical reassociation
$(A\times B)\times C\simeq A\times(B\times C)$.

This is the maximally mixed specialization of the tensor-product factorization
in Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, equation (10).

**Maximally mixed specialization
(docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex):**
This theorem proves only the $d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$ case.
The general support-compressed raw identity is
`partialTraceRightPetzMap_productTensor`; its positive-definite-left corollary
recovers the literal identity-tensored formula. Neither result implies the
Koashi--Imoto/Hayashi block decomposition. -/
theorem partialTraceRightPetzMap_maximallyMixedTensor_kronecker
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef)
    (A : Matrix (Fin dA) (Fin dA) ℂ) (X : Matrix B B ℂ) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C)
        (partialTraceRightPetzMap
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ)
          (A ⊗ₖ X)) =
      A ⊗ₖ partialTraceRightPetzMap ρ hρ X := by
  have hgeneral := partialTraceRightPetzMap_productTensor_kronecker
    (maximallyMixedOn (dA := dA)) ρ
    (maximallyMixedOn_posDef (dA := dA)).posSemidef hρ A X
  have hproj :
      (maximallyMixedOn_posDef (dA := dA)).posSemidef.isHermitian.supportProj = 1 :=
    (maximallyMixedOn_posDef (dA := dA)).supportProj_eq_one
  rw [hproj, Matrix.one_mul, Matrix.mul_one] at hgeneral
  simpa only [maximallyMixedTensorReference, productTensorReference] using hgeneral

/-- **Complementary-term compatibility, elementary-tensor form.** For the
maximally mixed tensor reference, TNLean's complementary measure-and-prepare
term acts as the identity on $A$ and as the local complementary term on $B$,
after canonical reassociation.

This statement concerns TNLean's support completion; it is not part of HJPW
equation (10). -/
theorem partialTraceRightPetzComplementMap_maximallyMixedTensor_kronecker
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef)
    (A : Matrix (Fin dA) (Fin dA) ℂ) (X : Matrix B B ℂ) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C)
        (partialTraceRightPetzComplementMap
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ)
          (A ⊗ₖ X)) =
      A ⊗ₖ partialTraceRightPetzComplementMap ρ hρ X := by
  rw [partialTraceRightPetzComplementMap_apply,
    partialTraceRightPetzComplementMap_apply]
  rw [supportProj_partialTraceRight_maximallyMixedTensorReference ρ hρ,
    partialTraceLeft_maximallyMixedTensorReference]
  let P := (PosSemidef.partialTraceRight hρ).isHermitian.supportProj
  have hQ : (1 : Matrix (Fin dA × B) (Fin dA × B) ℂ) -
      (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ P =
      (1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ (1 - P) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    by_cases haa : a = a' <;> by_cases hbb : b = b' <;>
      simp [haa, hbb, Matrix.kroneckerMap_apply]
  rw [hQ, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]
  ext ⟨a, bc⟩ ⟨a', bc'⟩
  simp only [equivReindexMap, LinearEquiv.coe_toLinearMap,
    Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodAssoc_symm_apply]
  rw [Matrix.partialTraceLeft_apply, mul_assoc]

/-- **Maximally mixed specialization of HJPW equation (10), raw Petz-map
factorization.** For
$\sigma_{ABC}=d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$, the raw partial-trace
Petz map is $\operatorname{id}_A\otimes\mathcal R_{\rho_{BC}}$, after the
canonical reassociation of product indices.

This is the maximally mixed specialization of equation (10) of
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2.

**Maximally mixed specialization
(docs/paper-gaps/hjpw04_petz_factorization_maximally_mixed_scope.tex):**
This theorem proves only the $d_A^{-1}\mathbf 1_A\otimes\rho_{BC}$ case.
The general support-compressed raw identity is
`partialTraceRightPetzMap_productTensor`; its positive-definite-left corollary
recovers the literal identity-tensored formula. Neither result implies the
Koashi--Imoto/Hayashi block decomposition. -/
theorem partialTraceRightPetzMap_maximallyMixedTensor
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C) ∘ₗ
        partialTraceRightPetzMap
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ) =
      idTensorMapLM (δ := Fin dA) (partialTraceRightPetzMap ρ hρ) := by
  simpa only [maximallyMixedTensorReference, productTensorReference] using
    partialTraceRightPetzMap_productTensor_of_posDef_left
      (maximallyMixedOn (dA := dA)) ρ
      (maximallyMixedOn_posDef (dA := dA)) hρ

/-- **Complementary-term compatibility.** For the maximally mixed tensor
reference, TNLean's complementary measure-and-prepare term factors as the
identity on $A$ tensored with the local complementary term on $B$, after
canonical reassociation.

This is a compatibility property of TNLean's support completion, not a claim
from HJPW equation (10). -/
theorem partialTraceRightPetzComplementMap_maximallyMixedTensor
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C) ∘ₗ
        partialTraceRightPetzComplementMap
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ) =
      idTensorMapLM (δ := Fin dA)
        (partialTraceRightPetzComplementMap ρ hρ) := by
  apply LinearMap.ext
  intro X
  obtain ⟨A, Y, hX⟩ :=
    hasOperatorSchmidtDecomposition_operatorSchmidtRank X
  rw [hX]
  simp only [LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [idTensorMapLM_apply, idTensorMap_kronecker]
  exact partialTraceRightPetzComplementMap_maximallyMixedTensor_kronecker
    ρ hρ (A i) (Y i)

/-- **Completed-channel factorization.** For the maximally mixed tensor
reference, TNLean's completed partial-trace Petz channel is the identity on
$A$ tensored with the completed local channel on $B$, after canonical
reassociation.

The raw support-map summand is the maximally mixed specialization of HJPW
equation (10). The complementary summand is TNLean's support-completion
compatibility and is not asserted by that equation. This theorem does not
invoke or assert a Koashi--Imoto decomposition. -/
theorem partialTraceRightPetzChannel_maximallyMixedTensor
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef) :
    equivReindexMap (Equiv.prodAssoc (Fin dA) B C) ∘ₗ
        partialTraceRightPetzChannel
          (maximallyMixedTensorReference (dA := dA) ρ)
          (maximallyMixedTensorReference_posSemidef (dA := dA) hρ) =
      idTensorMapLM (δ := Fin dA) (partialTraceRightPetzChannel ρ hρ) := by
  rw [partialTraceRightPetzChannel, LinearMap.comp_add,
    partialTraceRightPetzMap_maximallyMixedTensor,
    partialTraceRightPetzComplementMap_maximallyMixedTensor,
    partialTraceRightPetzChannel, idTensorMapLM_add]

/-- The completed Petz channel for the maximally mixed tensor reference is
trace-preserving and completely positive whenever $\rho_{BC}$ has trace one. -/
theorem partialTraceRightPetzChannel_maximallyMixedTensor_isKrausCPTP
    (ρ : Matrix (B × C) (B × C) ℂ) (hρ : ρ.PosSemidef)
    (hρtrace : Matrix.trace ρ = 1) :
    IsKrausCPTP
      (partialTraceRightPetzChannel
        (maximallyMixedTensorReference (dA := dA) ρ)
        (maximallyMixedTensorReference_posSemidef (dA := dA) hρ)) := by
  apply partialTraceRightPetzChannel_isKrausCPTP
  rw [trace_maximallyMixedTensorReference, hρtrace]

end HJPWTensorFactorization

end Matrix
