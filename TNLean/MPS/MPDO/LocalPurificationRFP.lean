/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.TransferMatrix
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.MPDO.PRFP
import TNLean.MPS.MPDO.ZCL

/-!
# Consequences of purification renormalization fixed points

This file develops the one-site purification renormalization fixed-point
condition of arXiv:1606.00608
(Cirac--Perez-Garcia--Schuch--Verstraete), Definition 4.3. The definition in
`TNLean.MPS.MPDO.PRFP` follows the ancillary-contraction presentation `Psipuri`
from lines 744--747:

`M^{ij} = ∑_k A^{(i,k)} ⊗ conj(A^{(j,k)})`,

where the purifying spin-ancilla tensor `A` is a pure-state RFP. This file proves
the resulting LPDO and MPDO properties, physical-trace idempotence, and the
finite-chain equation `MPDO-Puri-1`.

**Local fix (intended presentation):** The printed Definition 4.3 names the
global equation `MPDO-Puri-1`, while the surrounding lines 744--763 continue
with the one-site presentation `Psipuri`. We adopt that standing presentation
for `IsPRFP` and retain the bare global-family reading as a separate predicate.
See `docs/paper-gaps/cpsv16_purification_rfp_definition.tex`.

Literal physical-trace idempotence is the source ZCL diagram of Definition 4.2.
The separate predicate `IsSourceZCL` is its nonzero, scale-invariant extension.
The nondegenerate PRFP predicate adds exactly the nonvanishing needed to pass
from literal idempotence to that scale-invariant relation. The doubled-index
predicate `IsZCL` concerns a different transfer object; the maximally mixed
witness below separates it from source PRFP.

## Main definitions

* `MPOTensor.IsNondegeneratePRFP`: source PRFP together with nonzero
  physical-trace transfer.

## Main results

* `MPOTensor.IsPRFP.isLPDO` and `MPOTensor.IsPRFP.isMPDO`: source PRFP gives
  locally purifiable density operators and matrix product density operators.
* `MPOTensor.exists_isPRFP_not_isZCL`: source PRFP does not imply doubled-index
  transfer-map idempotence.
* `MPOTensor.purificationTensor_isTransferIdempotent_iff_physTraceTransfer_sq`:
  for fixed purifying data, pure-state RFP is equivalent to physical-trace
  idempotence.
* `MPOTensor.IsPRFP.isPhysicalTraceIdempotent`: source PRFP implies the literal
  Definition 4.2 physical-trace equation.
* `MPOTensor.isPRFP_iff_isLPDO_and_physTraceTransfer_sq`: source PRFP is
  equivalent to LPDO form together with physical-trace idempotence.
* `MPOTensor.isSourceZCL_of_isPRFP`: a PRFP with nonzero physical-trace transfer
  satisfies the scale-invariant source-ZCL relation.
* `MPOTensor.IsPRFP.hasPurificationRFPWitness`: source PRFP yields the
  finite-chain equation `MPDO-Puri-1`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 744--786.
-/
open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- A nondegenerate purification renormalization fixed point is a source
PRFP whose physical-trace transfer is nonzero. The additional clause is exactly
what is needed to view literal physical-trace idempotence as the nonzero,
scale-invariant `IsSourceZCL` relation. It adds a project nonzero normalization
condition to the purification presentation and ZCL characterization in CPSV16,
arXiv:1606.00608, lines 744--786, not part of Definition 4.3 itself. -/
def IsNondegeneratePRFP (M : MPOTensor d D) : Prop :=
  IsPRFP M ∧ physTraceTransfer M ≠ 0

/-- A purification renormalization fixed point has the local purification
structure: its purifying data is an `IsLPDO` witness, after dropping the RFP
condition on the purifying tensor. This is the one-site presentation preceding
CPSV16 Definition 4.3, arXiv:1606.00608, lines 744--758. -/
theorem IsPRFP.isLPDO {M : MPOTensor d D}
    (h : IsPRFP M) : IsLPDO M := by
  obtain ⟨dK, D', A, e, hM, _⟩ := h
  exact ⟨dK, D', A, e, hM⟩

/-- A purification renormalization fixed point generates matrix product density
operators: tracing the ancilla of the one-site purification preceding CPSV16
Definition 4.3, arXiv:1606.00608, lines 744--758, yields a positive semidefinite
operator on every nonempty chain (via `IsLPDO.isMPDO`). -/
theorem IsPRFP.isMPDO {M : MPOTensor d D}
    (h : IsPRFP M) : IsMPDO M :=
  h.isLPDO.isMPDO

/-! ## A purification RFP tensor that is not doubled-index ZCL

The source purification-RFP condition does not imply the doubled-index
zero-correlation-length condition `MPOTensor.IsZCL`
(`E_M ∘ E_M = E_M`). The witness below is the
diagonal purification at `d = d_K = 2`, `D = D' = 1`, `A = [1/√2, 0, 0, 1/√2]`:
its purifying tensor is a pure-state renormalization fixed point, yet the ancilla
trace contraction halves the leading eigenvalue, so the induced transfer map is
`½ • id` and idempotence fails. See
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_zcl_canonical_form_normalization.pdf>. -/

/-- Scalar amplitudes of the diagonal purifying tensor: `1/√2` on the diagonal. -/
noncomputable def witnessAmplitude (i k : Fin 2) : ℂ := if i = k then (Real.sqrt 2)⁻¹ else 0

/-- The diagonal purifying tensor `A^{(i,k)}` at inner bond dimension `D' = 1`. -/
noncomputable def witnessA : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun i k => Matrix.of (fun _ _ => witnessAmplitude i k)

/-- The combined spin-ancilla MPS tensor on `Fin (2 * 2)`. -/
noncomputable def witnessAcombined : MPSTensor (2 * 2) 1 :=
  purificationTensor witnessA

/-- The ancilla-contracted MPO tensor `M^{ij}` at `D = D' = 1`. -/
noncomputable def witnessM : MPOTensor 2 1 :=
  fun i j => (∑ k : Fin 2,
    (witnessA i k) ⊗ₖ ((witnessA j k).map (starRingEnd ℂ))).submatrix
      ⇑(finProdFinEquiv (m := 1) (n := 1)).symm ⇑(finProdFinEquiv (m := 1) (n := 1)).symm

private lemma sqrt2_inv_mul_self :
    ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = (2⁻¹ : ℂ) := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The single entry of the contracted MPO tensor: `M^{ij} = ½` if `i = j`, else `0`. -/
lemma witnessM_entry (i j : Fin 2) :
    witnessM i j 0 0 = if i = j then (2⁻¹ : ℂ) else 0 := by
  have amp_mul_conj : ∀ a b c : Fin 2,
      witnessAmplitude a c * (starRingEnd ℂ) (witnessAmplitude b c)
        = if a = c ∧ b = c then (2⁻¹ : ℂ) else 0 := by
    intro a b c
    by_cases hac : a = c
    · by_cases hbc : b = c
      · rw [ite_eq_left ⟨hac, hbc⟩]
        simp only [witnessAmplitude, ite_eq_left hac, ite_eq_left hbc, map_inv₀,
          Complex.conj_ofReal]
        exact sqrt2_inv_mul_self
      · rw [ite_eq_right (fun h => hbc h.2)]
        simp only [witnessAmplitude, ite_eq_right hbc, map_zero, mul_zero]
    · rw [ite_eq_right (fun h => hac h.1)]
      simp only [witnessAmplitude, ite_eq_right hac, zero_mul]
  simp only [witnessM, Matrix.submatrix_apply, witnessA, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [amp_mul_conj]

/-- The transfer map of the witness MPO is `½ • id`: its leading eigenvalue is `½`,
not `1`, reflecting the maximally mixed reduced state. -/
lemma transferMap_witnessM :
    transferMap witnessM = (2⁻¹ : ℂ) • LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  ext a b
  obtain rfl : a = 0 := Subsingleton.elim a 0
  obtain rfl : b = 0 := Subsingleton.elim b 0
  rw [transferMap_apply]
  simp only [Matrix.sum_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.mul_apply,
    Fin.sum_univ_one, Matrix.conjTranspose_apply, witnessM_entry, LinearMap.smul_apply,
    LinearMap.id_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Fin.reduceEq, ↓reduceIte, star_zero, mul_zero, zero_mul, add_zero,
    show star (2⁻¹ : ℂ) = 2⁻¹ from by simp]
  ring

/-- The combined spin-ancilla tensor is a pure-state RFP: its transfer map is the
identity, since the amplitudes satisfy `∑ |A|² = 1`. -/
lemma witnessAcombined_isTransferIdempotent : MPSTensor.IsTransferIdempotent witnessAcombined := by
  have h : Kraus.transferMap witnessAcombined = LinearMap.id := by
    refine LinearMap.ext fun X => ?_
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim a 0
    obtain rfl : b = 0 := Subsingleton.elim b 0
    rw [Kraus.transferMap_apply, Matrix.sum_apply, Fin.sum_univ_four]
    have e0 : (0 : Fin (2 * 2)).divNat = 0 ∧ (0 : Fin (2 * 2)).modNat = 0 := by decide
    have e1 : (1 : Fin (2 * 2)).divNat = 0 ∧ (1 : Fin (2 * 2)).modNat = 1 := by decide
    have e2 : (2 : Fin (2 * 2)).divNat = 1 ∧ (2 : Fin (2 * 2)).modNat = 0 := by decide
    have e3 : (3 : Fin (2 * 2)).divNat = 1 ∧ (3 : Fin (2 * 2)).modNat = 1 := by decide
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply,
      witnessAcombined, purificationTensor, witnessA, Matrix.of_apply, LinearMap.id_apply, e0.1,
      e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, witnessAmplitude, Fin.reduceEq, ↓reduceIte,
      zero_mul, add_zero, ← starRingEnd_apply, map_inv₀, Complex.conj_ofReal]
    linear_combination (2 * X 0 0) * sqrt2_inv_mul_self
  rw [MPSTensor.IsTransferIdempotent, h, LinearMap.comp_id]

/-- **Source PRFP does not imply doubled-index zero-correlation length.**
There is an MPO tensor satisfying `IsPRFP` whose doubled-index transfer-map
idempotence `E_M ∘ E_M = E_M` fails, because the purification's trace contraction
drops the leading eigenvalue below `1`. CPSV16 Definition 4.2, lines 735--739,
uses the physical-trace transfer, and its PRFP presentation is at lines 744--760;
`IsZCL` here is the separate project doubled-index predicate, not the source's
Definition 4.2. This distinction is documented in
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_zcl_canonical_form_normalization.pdf>. -/
theorem exists_isPRFP_not_isZCL :
    ∃ M : MPOTensor 2 1, IsPRFP M ∧ ¬ IsZCL M := by
  refine ⟨witnessM, ⟨2, 1, witnessA, (finProdFinEquiv (m := 1) (n := 1)).symm, fun _ _ => rfl,
    witnessAcombined_isTransferIdempotent⟩, ?_⟩
  intro hZCL
  rw [IsZCL, transferMap_witnessM] at hZCL
  have hfun := LinearMap.congr_fun hZCL (1 : Matrix (Fin 1) (Fin 1) ℂ)
  have hc := congrFun (congrFun hfun 0) 0
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
    Matrix.smul_apply, Matrix.one_apply, ↓reduceIte] at hc
  norm_num at hc

/-- The physical-trace transfer of the witness is the identity matrix: closing
the ket and bra physical legs gives 𝒯 = M⁰⁰ + M¹¹ = ½ + ½ = 1. -/
lemma physTraceTransfer_witnessM : physTraceTransfer witnessM = 1 := by
  have hentry : physTraceTransfer witnessM 0 0 = 1 := by
    rw [show physTraceTransfer witnessM = ∑ i : Fin 2, witnessM i i from rfl,
      Matrix.sum_apply, Fin.sum_univ_two, witnessM_entry, witnessM_entry,
      ite_eq_left rfl, ite_eq_left rfl]
    norm_num
  ext a b
  obtain rfl : a = 0 := Subsingleton.elim a 0
  obtain rfl : b = 0 := Subsingleton.elim b 0
  rw [hentry, Matrix.one_apply_eq]

/-- **The maximally mixed witness has source zero correlation length**
(arXiv:1606.00608, Definition 4.2, lines 735–739). The maximally mixed
purification tensor, which is the counterexample above to literal doubled-index
idempotence, has physical-trace transfer equal to the identity. This transfer is
nonzero and idempotent, hence the tensor has source zero correlation length. The
example is recorded in
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_zcl_canonical_form_normalization.pdf>:
the physical-trace transfer correctly classifies the maximally mixed product state as having zero
correlation length, whereas the doubled-index condition wrongly excludes it. -/
theorem isSourceZCL_witnessM : IsSourceZCL witnessM :=
  isSourceZCL_of_physTraceTransfer_sq witnessM
    (by rw [physTraceTransfer_witnessM]; exact one_ne_zero)
    (by rw [physTraceTransfer_witnessM, mul_one])

/-! ## Purification RFP implies physical-trace idempotence

Definition 4.3 inherits the one-site ancillary-contraction presentation from
arXiv:1606.00608, lines 744--747. Closing the physical legs identifies the
physical-trace transfer of `M` with a reindexing of the transfer matrix of the
purifying tensor. Pure-state RFP idempotence therefore gives the literal
physical-trace idempotence of Definition 4.2.

The source theorem at lines 775--786 relates PRFP, ZCL, and preparation by a
length-independent completely positive map. Here literal physical-trace
idempotence is obtained unconditionally. Passing to the project's broader
nonzero scale-invariant predicate `IsSourceZCL` additionally requires
`physTraceTransfer M ≠ 0`. -/

/-- **Pure-state RFP is equivalent to physical-trace idempotence for fixed
purifying data.** Suppose `M` is the one-site ancillary contraction of `A`
through the bond identification `e`, as in `Psipuri` at arXiv:1606.00608,
lines 744--747. Then the purifying tensor is a pure-state RFP if and only if the
physical-trace transfer $\mathcal T_M = \sum_i M^{ii}$ is idempotent.

The purifying tensor has transfer matrix
$K' = \sum_p \overline{A_p} \otimes A_p$. Closing the physical legs of `M`
rewrites $\mathcal T_M$ as a reindexing of `K'` by `e` and the Kronecker-factor
swap. Both reindexings are equivalences, so matrix idempotence passes in both
directions. Faithfulness of `transferMatrix` then recovers transfer-map
idempotence. -/
theorem purificationTensor_isTransferIdempotent_iff_physTraceTransfer_sq
    {dK D' : ℕ} (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e) :
    MPSTensor.IsTransferIdempotent (purificationTensor A) ↔
      physTraceTransfer M * physTraceTransfer M = physTraceTransfer M := by
  set s : (Fin D' × Fin D') ≃ (Fin D' × Fin D') := Equiv.prodComm (Fin D') (Fin D')
    with hs
  set K' : Matrix (Fin D' × Fin D') (Fin D' × Fin D') ℂ :=
    transferMatrix (Kraus.transferMap (purificationTensor A)) with hK'
  set K : Matrix (Fin D' × Fin D') (Fin D' × Fin D') ℂ :=
    ∑ i : Fin d, ∑ k : Fin dK, (A i k) ⊗ₖ ((A i k).map (starRingEnd ℂ)) with hKdef
  -- Swapping the two Kronecker factors is a bond-pair reindexing.
  have kron_swap : ∀ X Y : Matrix (Fin D') (Fin D') ℂ,
      (Y ⊗ₖ X).submatrix (⇑s) (⇑s) = X ⊗ₖ Y := by
    intro X Y
    ext ⟨a, b⟩ ⟨c, d'⟩
    simp only [Matrix.submatrix_apply, hs, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Matrix.kronecker_apply]
    ring
  -- The transfer matrix, reindexed by the factor swap, has the Kronecker order of `M`.
  have step1 : K'.submatrix (⇑s) (⇑s)
      = ∑ p : Fin (d * dK),
          (purificationTensor A p) ⊗ₖ ((purificationTensor A p).map (starRingEnd ℂ)) := by
    rw [hK', MPSTensor.transferMatrix_eq]
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← kron_swap (purificationTensor A p) ((purificationTensor A p).map (starRingEnd ℂ)),
      Matrix.submatrix_apply]
  -- Reindex the spin–ancilla product index by `finProdFinEquiv`.
  have hreindex : (∑ i : Fin d, ∑ k : Fin dK, (A i k) ⊗ₖ ((A i k).map (starRingEnd ℂ)))
      = ∑ p : Fin (d * dK),
          (purificationTensor A p) ⊗ₖ ((purificationTensor A p).map (starRingEnd ℂ)) := by
    rw [← Fintype.sum_prod_type']
    exact (finProdFinEquiv.symm.sum_comp _).symm
  -- Identify `K` with the swapped transfer matrix.
  have hKK' : K = K'.submatrix (⇑s) (⇑s) := by rw [hKdef, hreindex, step1]
  -- Closing the physical legs identifies `𝒯_M` with a reindexing of `K`.
  have hPT : physTraceTransfer M = K.submatrix (⇑e) (⇑e) := by
    ext a b
    rw [show physTraceTransfer M = ∑ i : Fin d, M i i from rfl, Matrix.sum_apply,
      Matrix.submatrix_apply, hKdef, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hM i i, Matrix.submatrix_apply]
  constructor
  · intro hRFP
    have hidemK' : K' * K' = K' := by
      have h2 := congrArg transferMatrix hRFP
      rw [transferMatrix_comp] at h2
      rw [hK']
      exact h2
    have hidemK : K * K = K := by
      rw [hKK', Matrix.submatrix_mul_equiv K' K' (⇑s) s (⇑s), hidemK']
    rw [hPT, Matrix.submatrix_mul_equiv K K (⇑e) e (⇑e), hidemK]
  · intro hPTidem
    rw [hPT, Matrix.submatrix_mul_equiv K K (⇑e) e (⇑e)] at hPTidem
    have hidemK : K * K = K := (Matrix.reindex e.symm e.symm).injective hPTidem
    rw [hKK', Matrix.submatrix_mul_equiv K' K' (⇑s) s (⇑s)] at hidemK
    have hidemK' : K' * K' = K' := (Matrix.reindex s.symm s.symm).injective hidemK
    apply transferMatrix_injective
    rw [transferMatrix_comp, ← hK']
    exact hidemK'

/-- **Idempotence of the physical-trace transfer under PRFP.** If M is the
ancilla contraction of a pure-state
renormalization fixed point, then its physical-trace transfer is idempotent.

This is the forward direction of
`purificationTensor_isTransferIdempotent_iff_physTraceTransfer_sq`; source:
arXiv:1606.00608, the purification tensor formula and Definition 4.3,
lines 744--758. -/
theorem physTraceTransfer_sq_of_isPRFP (M : MPOTensor d D)
    (h : IsPRFP M) :
    physTraceTransfer M * physTraceTransfer M = physTraceTransfer M := by
  obtain ⟨dK, D', A, e, hM, hRFP⟩ := h
  exact (purificationTensor_isTransferIdempotent_iff_physTraceTransfer_sq A e hM).mp hRFP

/-- A purification renormalization fixed point satisfies the literal
physical-trace idempotence diagram of arXiv:1606.00608, Definition 4.2. -/
theorem IsPRFP.isPhysicalTraceIdempotent {M : MPOTensor d D} (h : IsPRFP M) :
    IsPhysicalTraceIdempotent M :=
  (isPhysicalTraceIdempotent_iff M).2 (physTraceTransfer_sq_of_isPRFP M h)

/-- **LPDO form and physical-trace idempotence characterize PRFP.**
An MPO tensor has a source PRFP purification exactly when it has local
purifying data and its physical-trace transfer is idempotent. For fixed
purifying data, the equivalence follows from
`purificationTensor_isTransferIdempotent_iff_physTraceTransfer_sq`.

This formalizes the equivalence of clauses (i) and (ii) in arXiv:1606.00608,
Theorem 4.4, lines 777--784, under the one-site purification presentation from
lines 744--747 that is built into `IsPRFP`. It does not address clause (iii), the
repeated-copy density formula. -/
theorem isPRFP_iff_isLPDO_and_physTraceTransfer_sq
    (M : MPOTensor d D) :
    IsPRFP M ↔
      IsLPDO M ∧ physTraceTransfer M * physTraceTransfer M = physTraceTransfer M := by
  constructor
  · intro h
    exact ⟨h.isLPDO, physTraceTransfer_sq_of_isPRFP M h⟩
  · rintro ⟨⟨dK, D', A, e, hM⟩, hT⟩
    exact ⟨dK, D', A, e, hM,
      (purificationTensor_isTransferIdempotent_iff_physTraceTransfer_sq A e hM).mpr hT⟩

/-- **Nondegenerate PRFP equivalence.** A tensor is a nondegenerate PRFP
if and only if it has local purifying data and a nonzero idempotent
physical-trace transfer. This adds the project's nonzero normalization
condition to the purification/ZCL characterization in CPSV16 Theorem 4.4,
arXiv:1606.00608, lines 775--786. -/
theorem isNondegeneratePRFP_iff (M : MPOTensor d D) :
    IsNondegeneratePRFP M ↔
      IsLPDO M ∧ physTraceTransfer M ≠ 0 ∧
        physTraceTransfer M * physTraceTransfer M = physTraceTransfer M := by
  constructor
  · rintro ⟨hLocal, h0⟩
    exact ⟨hLocal.isLPDO, h0, physTraceTransfer_sq_of_isPRFP M hLocal⟩
  · rintro ⟨hLPDO, h0, hT⟩
    exact ⟨(isPRFP_iff_isLPDO_and_physTraceTransfer_sq M).mpr
      ⟨hLPDO, hT⟩, h0⟩

/-- A purification RFP with nonzero physical-trace transfer satisfies the
scale-invariant `IsSourceZCL` relation. Literal physical-trace idempotence is
unconditional; the nonzero hypothesis belongs only to `IsSourceZCL`.

**Scope restriction (normalization):** This theorem concludes the project's
nonzero, positive-up-to-scale `IsSourceZCL` relation, not the literal
unconditional ZCL equation in CPSV16 Theorem 4.4, lines 775--786. The latter is
`IsPRFP.isPhysicalTraceIdempotent`. See
`docs/paper-gaps/cpsv16_purification_rfp_definition.tex`. -/
theorem isSourceZCL_of_isPRFP (M : MPOTensor d D)
    (h : IsPRFP M) (h0 : physTraceTransfer M ≠ 0) :
    IsSourceZCL M :=
  h.isPhysicalTraceIdempotent.isSourceZCL h0

/-- A nondegenerate purification RFP satisfies the nonzero up-to-scalar
physical-trace relation. The literal source implication PRFP to ZCL in
arXiv:1606.00608, lines 775--786, is `IsPRFP.isPhysicalTraceIdempotent`. -/
theorem IsNondegeneratePRFP.isSourceZCL {M : MPOTensor d D}
    (h : IsNondegeneratePRFP M) : IsSourceZCL M :=
  isSourceZCL_of_isPRFP M h.1 h.2

/-! ## The tensor purification identity and the source purification RFP

A tensor that is the ancilla contraction of a purifying family (the purification
graphic of arXiv:1606.00608, line 747) generates, at every system size, exactly
the ancillary trace of the pure spin-ancilla matrix product state. This is the
coefficient form of the purification equation at arXiv:1606.00608, line 751, and
it derives the finite-chain presentation `MPDO-Puri-1` from the
one-site source definition (arXiv:1606.00608, lines 744--758). -/

/-- The purifying spin-ancilla tensor recovers the original amplitude at the
encoded product index: evaluating `purificationTensor` at the spin-ancilla pair
returns the corresponding matrix of the family. -/
private theorem purificationTensor_finProdFinEquiv {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) (i : Fin d) (k : Fin dK) :
    purificationTensor A (finProdFinEquiv (i, k)) = A i k := by
  change A (finProdFinEquiv (i, k)).divNat (finProdFinEquiv (i, k)).modNat = A i k
  rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- The matrix product vector coefficient of the purifying tensor along a joined
spin-ancilla configuration is the trace of the ordered product of the
spin-ancilla amplitudes. -/
private theorem mpv_purificationTensor {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) {N : ℕ}
    (σ : Fin N → Fin d) (κ : Fin N → Fin dK) :
    MPSTensor.mpv (purificationTensor A) (fun n => finProdFinEquiv (σ n, κ n))
      = Matrix.trace ((List.ofFn fun l => A (σ l) (κ l)).prod) := by
  have hfun : (fun l : Fin N => purificationTensor A (finProdFinEquiv (σ l, κ l)))
      = fun l => A (σ l) (κ l) :=
    funext fun l => purificationTensor_finProdFinEquiv A (σ l) (κ l)
  simp only [MPSTensor.mpv_eq, MPSTensor.coeff_eq,
    MPSTensor.evalWord_ofFn_eq_prod, hfun]

/-- **The tensor purification identity propagates to the global density
operators.** If M is the ancilla contraction of a purifying family A through a
bond identification e (the purification graphic of arXiv:1606.00608, line 747),
then at every system size the matrix product operator `mpo M N` equals the
ancillary trace `purificationDensity A N` of the pure spin-ancilla matrix product
state generated by A. This is the coefficient form of the purification equation
at arXiv:1606.00608, line 751.

The N-fold product of the contracted tensor expands as a Kronecker sum over the
ancillary words (`lpdo_prod_decomp`); tracing it and conjugating the bra factor
yields the ancillary trace. The equation holds at every system size, so no
positive-length restriction is needed. -/
theorem mpo_eq_purificationDensity {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') {M : MPOTensor d D}
    (hM : ∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    (N : ℕ) :
    mpo M N = purificationDensity A N := by
  ext σ τ
  simp only [mpo_apply, mpoMatrixEntry, MPOTensor.evalWord_ofFn]
  rw [lpdo_prod_decomp A e hM σ τ, Matrix.trace_submatrix_equiv, Matrix.trace_sum]
  simp only [purificationDensity, Matrix.of_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Matrix.trace_kronecker, ← AddMonoidHom.map_trace (starRingEnd ℂ),
    mpv_purificationTensor A σ κ, mpv_purificationTensor A τ κ, starRingEnd_apply]

/-- A purification renormalization fixed point supplies the finite-chain
purification equation `MPDO-Puri-1` of arXiv:1606.00608, line 751, together
with the same pure-state RFP purifying tensor. The equation follows by
expanding the one-site ancillary contraction along the chain. -/
theorem IsPRFP.hasPurificationRFPWitness {M : MPOTensor d D}
    (h : IsPRFP M) : HasPurificationRFPWitness M := by
  obtain ⟨dK, D', A, e, hM, hRFP⟩ := h
  refine ⟨dK, D', A, ?_, hRFP⟩
  intro N _
  exact mpo_eq_purificationDensity A e hM N

end MPOTensor
