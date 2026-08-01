/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.MarginalSupportAbsorption
import TNLean.Channel.PetzProductReference
import TNLean.Channel.Schwarz.SSAEqualityDPI
import TNLean.Channel.Schwarz.WeylSupportPetzRecovery

/-!
# Petz recovery from equality in strong subadditivity

For a tripartite density matrix satisfying equality in strong subadditivity,
this file specializes equality in relative-entropy data processing to the
reference matrix \(\rho_A\otimes\rho_{BC}\). The resulting Petz map recovers
\(\rho_{ABC}\), and its product-reference formula is
\(\operatorname{id}_A\otimes\mathcal R^{\mathrm{raw}}_{\rho_{BC}}\) on the
supported input \(\rho_{AB}\).

## Main results

* `Matrix.product_marginal_support` restates, for the Petz-recovery argument,
  that a bipartite positive semidefinite matrix lies in the support of the
  product of its marginals.
* `Matrix.partialTraceRightPetzMap_product_marginal_recovery_of_isSSAEquality`
  gives the recovery identity for the product reference.
* `Matrix.idTensor_partialTraceRightPetzMap_traceC_ABC_eq_of_isSSAEquality`
  gives the identity-tensored form of the recovery formula.
* `Matrix.idTensor_partialTraceRightPetzChannel_traceC_ABC_eq_of_isSSAEquality`
  supplies the identity-tensored quantum-operation form used by HJPW.

## References

* P. Hayden, R. Jozsa, D. Petz, and A. Winter,
  arXiv:quant-ph/0304007v2, Theorem 3 and equations (8), (10), and (11);
  source labels `eq:transpose:channel`, `eq:form:of:hat-T`, and
  `eq:markov:quantum`.
-/

open scoped Matrix ComplexOrder Kronecker
open Matrix

namespace Matrix

private theorem PosSemidef.supportProj_eq_of_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : A = B) :
    hA.supportProj = hB.supportProj := by
  subst B
  rfl

private theorem bipartiteBlock_support_of_right_sandwich
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B]
    {X : Matrix (A × B) (A × B) ℂ} {P : Matrix B B ℂ}
    (hX : ((1 : Matrix A A ℂ) ⊗ₖ P) * X *
      ((1 : Matrix A A ℂ) ⊗ₖ P) = X)
    (a a' : A) :
    P * bipartiteBlock X a a' * P = bipartiteBlock X a a' := by
  ext b b'
  have hentry := congrArg (fun M => M (a, b) (a', b')) hX
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply] at hentry
  simp_rw [Fintype.sum_prod_type] at hentry
  simp at hentry
  simpa only [Matrix.mul_apply, bipartiteBlock_apply] using hentry

section ProductMarginalSupport

variable {L R : Type*} [Fintype L] [Fintype R]

/-- A positive semidefinite matrix \(\rho_{LR}\) is supported on
\(\operatorname{supp}\rho_L\otimes\operatorname{supp}\rho_R\). Equivalently,
\[
  \ker(\rho_L\otimes\rho_R)\subseteq\ker\rho_{LR}.
\]
This is the support condition for the product reference used in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2,
`eq:transpose:channel`. -/
theorem product_marginal_support
    {ρ : Matrix (L × R) (L × R) ℂ} (hρ : ρ.PosSemidef) :
    ∀ v : L × R → ℂ,
      (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) *ᵥ v = 0 → ρ *ᵥ v = 0 := by
  exact hρ.productMarginals_kernel_le

end ProductMarginalSupport

section SSAEqualityRecovery

variable {dA dB dC : ℕ}

open SSAPosDef

/-- **Product-reference Petz recovery at SSA equality.** If a tripartite
density matrix saturates strong subadditivity, then the raw Petz map for the
reference \(\rho_A\otimes\rho_{BC}\), canonically reassociated so that it
traces out \(C\), recovers \(\rho_{ABC}\) from \(\rho_{AB}\).

This is Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, Theorem 3 and
equation (8), specialized to the product reference used in equations
(10)--(11). No marginal is assumed invertible. -/
theorem partialTraceRightPetzMap_product_marginal_recovery_of_isSSAEquality
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    partialTraceRightPetzMap
        (productTensorReference (partialTraceRight ρ_ABC) (traceA_ABC ρ_ABC))
        (productTensorReference_posSemidef hρ_dm.1.partialTraceRight
          (traceLeftA_posSemidef hρ_dm.1))
        (traceC_ABC ρ_ABC) =
      ρ_ABC.submatrix (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC))
        (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)) := by
  classical
  let r := Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC)
  let ρr := ρ_ABC.submatrix r r
  let ρA := partialTraceRight ρ_ABC
  let ρBC := traceA_ABC ρ_ABC
  let σ0 := ρA ⊗ₖ ρBC
  let σr := productTensorReference ρA ρBC
  have hρ := hρ_dm.1
  have hA : ρA.PosSemidef := by
    exact hρ.partialTraceRight
  have hBC : ρBC.PosSemidef := by
    exact traceLeftA_posSemidef hρ
  have hρr : ρr.PosSemidef := hρ.submatrix r
  have hσr : σr.PosSemidef := productTensorReference_posSemidef hA hBC
  have hsupp0 :
      ∀ v, σ0 *ᵥ v = 0 → ρ_ABC *ᵥ v = 0 := by
    exact product_marginal_support hρ
  have hsupp :
      ∀ v, σr *ᵥ v = 0 → ρr *ᵥ v = 0 := by
    simpa only [σ0, σr, ρr, productTensorReference, r, Equiv.symm_symm] using
      mulVec_submatrix_support r.symm hsupp0
  have hDPI :=
    (isSSAEquality_iff_product_marginal_data_processing_eq ρ_ABC hρ_dm).mp hSSA
  rw [← traceC_ABC_product_marginals ρ_ABC] at hDPI
  have heq :
      quantumRelativeEntropy ρr σr =
        quantumRelativeEntropy (partialTraceRight ρr) (partialTraceRight σr) := by
    calc
      quantumRelativeEntropy ρr σr =
          quantumRelativeEntropy ρ_ABC σ0 := by
            simpa only [ρr, σr, σ0, productTensorReference, r,
              Equiv.symm_symm] using
              quantumRelativeEntropy_submatrix_equiv hρ.isHermitian
                (hA.kronecker hBC).isHermitian r.symm
      _ = quantumRelativeEntropy (traceC_ABC ρ_ABC) (traceC_ABC σ0) := hDPI
      _ = quantumRelativeEntropy (partialTraceRight ρr)
          (partialTraceRight σr) := by
            rw [show partialTraceRight ρr = traceC_ABC ρ_ABC by
                simpa only [ρr, r] using
                  partialTraceRight_submatrix_prodAssoc ρ_ABC,
              show partialTraceRight σr = traceC_ABC σ0 by
                simpa only [σr, σ0, productTensorReference, r] using
                  partialTraceRight_submatrix_prodAssoc σ0]
  let ρIndex := Classical.choice (nonempty_of_trace_eq_one ρ_ABC hρ_dm.2)
  letI : Nonempty (Fin dC) := ⟨ρIndex.2.2⟩
  have hrec :=
    partialTraceRightPetzMap_eq_of_relativeEntropy_eq_general_support
      hρr hσr hsupp heq
  simpa only [ρr, σr, ρA, ρBC, r,
    partialTraceRight_submatrix_prodAssoc] using hrec

/-- **Identity-tensored form of HJPW equation (11).** At equality in strong
subadditivity, the raw Petz map for \(\rho_{BC}\), tensored with the identity
on \(A\), recovers \(\rho_{ABC}\) from \(\rho_{AB}\).

This is the supported-input consequence of Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, equations (10)--(11). For singular \(\rho_A\), this
does not assert a global identity-tensored factorization of the raw map or of
TNLean's chosen completed channel on unsupported inputs. -/
theorem idTensor_partialTraceRightPetzMap_traceC_ABC_eq_of_isSSAEquality
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    idTensorMapLM (δ := Fin dA)
        (partialTraceRightPetzMap (traceA_ABC ρ_ABC)
          (traceLeftA_posSemidef hρ_dm.1))
        (traceC_ABC ρ_ABC) =
      ρ_ABC := by
  classical
  have hρ := hρ_dm.1
  have hAB := traceC_ABC_posSemidef hρ
  have hA := hρ.partialTraceRight
  have hBC := traceLeftA_posSemidef hρ
  let hAAB := PosSemidef.partialTraceRight hAB
  let P := hAAB.supportProj
  have hProj : P = hA.supportProj :=
    hAAB.supportProj_eq_of_eq hA
      (partialTraceRight_traceC_ABC ρ_ABC)
  have hL :
      (P ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) *
          traceC_ABC ρ_ABC =
        traceC_ABC ρ_ABC := by
    change leftKroneckerEmbed (n := Fin dB)
        (PosSemidef.partialTraceRight hAB).isHermitian.supportProj *
          traceC_ABC ρ_ABC =
        traceC_ABC ρ_ABC
    exact hAB.leftKroneckerEmbed_supportProj_mul_self
  have hR :
      traceC_ABC ρ_ABC *
          (P ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) =
        traceC_ABC ρ_ABC := by
    change traceC_ABC ρ_ABC * leftKroneckerEmbed (n := Fin dB)
        (PosSemidef.partialTraceRight hAB).isHermitian.supportProj =
      traceC_ABC ρ_ABC
    exact hAB.mul_leftKroneckerEmbed_supportProj_self
  have hX :
      (hA.supportProj ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) * traceC_ABC ρ_ABC *
          (hA.supportProj ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) =
        traceC_ABC ρ_ABC := by
    rw [← hProj]
    rw [hL, hR]
  have hfactor :=
    partialTraceRightPetzMap_productTensor_apply_of_left_supported
      (partialTraceRight ρ_ABC) (traceA_ABC ρ_ABC) hA hBC
      (traceC_ABC ρ_ABC) hX
  have hraw :=
    partialTraceRightPetzMap_product_marginal_recovery_of_isSSAEquality
      ρ_ABC hρ_dm hSSA
  rw [hraw] at hfactor
  have hcancel :
      equivReindexMap (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC))
          (ρ_ABC.submatrix (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC))
            (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC))) =
        ρ_ABC := by
    ext i j
    change Matrix.reindex (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC))
        (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC))
          (ρ_ABC.submatrix (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC))
            (Equiv.prodAssoc (Fin dA) (Fin dB) (Fin dC))) i j =
      ρ_ABC i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]
  exact hfactor.symm.trans hcancel

/-- The local completed Petz map for \(\rho_{BC}\) is a quantum channel.

This supplies the quantum operation \(\widehat{\mathcal R}\) in
Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, equations (10)--(11),
without requiring invertibility of \(\rho_{BC}\). -/
theorem partialTraceRightPetzChannel_traceA_ABC_isKrausCPTP
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    IsKrausCPTP
      (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
        (traceLeftA_posSemidef hρ_dm.1)) := by
  apply partialTraceRightPetzChannel_isKrausCPTP
  change (partialTraceLeft ρ_ABC).trace = 1
  rw [trace_partialTraceLeft, hρ_dm.2]

/-- **Quantum-operation form of HJPW equation (11).** At equality in strong
subadditivity, the completed local Petz channel for \(\rho_{BC}\), tensored
with the identity on \(A\), recovers \(\rho_{ABC}\) from \(\rho_{AB}\).

The completed channel agrees with the raw support formula on every
\(B\)-block of \(\rho_{AB}\). This is the source-facing quantum operation
\(\widehat{\mathcal R}\) from Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, equations (10)--(11); no global factorization of
TNLean's completed product-reference channel is asserted. -/
theorem idTensor_partialTraceRightPetzChannel_traceC_ABC_eq_of_isSSAEquality
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1)
    (hSSA : IsSSAEquality ρ_ABC hρ_dm.1.isHermitian) :
    idTensorMapLM (δ := Fin dA)
        (partialTraceRightPetzChannel (traceA_ABC ρ_ABC)
          (traceLeftA_posSemidef hρ_dm.1))
        (traceC_ABC ρ_ABC) =
      ρ_ABC := by
  classical
  have hρ := hρ_dm.1
  have hAB := traceC_ABC_posSemidef hρ
  have hBC := traceLeftA_posSemidef hρ
  have hBAB := hAB.partialTraceLeft
  have hB := hBC.partialTraceRight
  let P := hBAB.supportProj
  have hProj : P = hB.supportProj :=
    hBAB.supportProj_eq_of_eq hB
      (partialTraceLeft_traceC_ABC_eq_partialTraceRight_traceA_ABC ρ_ABC)
  have hL :
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ P) * traceC_ABC ρ_ABC =
        traceC_ABC ρ_ABC := by
    change rightKroneckerEmbed (m := Fin dA)
        (PosSemidef.partialTraceLeft hAB).isHermitian.supportProj *
          traceC_ABC ρ_ABC =
        traceC_ABC ρ_ABC
    exact hAB.rightKroneckerEmbed_supportProj_mul_self
  have hR :
      traceC_ABC ρ_ABC * ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ P) =
        traceC_ABC ρ_ABC := by
    change traceC_ABC ρ_ABC * rightKroneckerEmbed (m := Fin dA)
        (PosSemidef.partialTraceLeft hAB).isHermitian.supportProj =
      traceC_ABC ρ_ABC
    exact hAB.mul_rightKroneckerEmbed_supportProj_self
  have hX :
      ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ hB.supportProj) *
          traceC_ABC ρ_ABC *
          ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ hB.supportProj) =
        traceC_ABC ρ_ABC := by
    rw [← hProj, hL, hR]
  have hraw :=
    idTensor_partialTraceRightPetzMap_traceC_ABC_eq_of_isSSAEquality
      ρ_ABC hρ_dm hSSA
  ext ⟨a, bc⟩ ⟨a', bc'⟩
  have hblock :=
    bipartiteBlock_support_of_right_sandwich hX a a'
  have hlocal :=
    partialTraceRightPetzChannel_apply_of_supported
      (traceA_ABC ρ_ABC) hBC
      (bipartiteBlock (traceC_ABC ρ_ABC) a a') hblock
  change
    (partialTraceRightPetzChannel (traceA_ABC ρ_ABC) hBC
      (bipartiteBlock (traceC_ABC ρ_ABC) a a')) bc bc' =
      ρ_ABC (a, bc) (a', bc')
  rw [hlocal]
  exact congrArg (fun M => M (a, bc) (a', bc')) hraw

end SSAEqualityRecovery

end Matrix
