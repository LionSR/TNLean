/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.PRFP
import TNLean.MPS.MPDO.ZCL
import TNLean.Channel.TransferMatrix

/-!
# Local purification RFP condition for MPDO tensors

This file records a local tensor-level purification condition for MPDO tensors.
It is motivated by the purification tensor formula `Psipuri` in arXiv:1606.00608
(Cirac--Perez-Garcia--Schuch--Verstraete), line 747, but it is not the source
purification-RFP definition.

A tensor `M` generating MPDOs need not be a renormalization fixed point in the
transfer-map sense. Instead one writes `M` through a purifying MPS tensor `A`
whose physical leg carries a spin index together with an ancillary index, so that
`M` is the ancilla contraction of `A` with its conjugate (the `Psipuri` graphic,
line 747):

  `M^{ij} = ∑_k A^{(i,k)} ⊗ conj(A^{(j,k)})`,

and imposes the local condition that such a purification exists with `A` a
pure-state renormalization fixed point (`MPSTensor.IsRFP`, arXiv:1606.00608,
Definition 3.2).

## Scope

The predicate below is a separate local tensor condition, not the source
purification-RFP definition. The source PRFP definition is stated in
`TNLean.MPS.MPDO.PRFP` using the positive-length global purification equation
and the pure-state RFP condition on the purifying tensor. The trace-preserving
post-ancilla structure discussed after the source definition is recorded there
separately. This local condition is still useful because it pins the tensor
`M^{ij}` itself, not merely the family of density operators `M` generates.

`MPOTensor.IsLocalPurificationRFP` is exactly `MPOTensor.IsLPDO` (the local
purification structure) together with the requirement that the purifying tensor,
viewed as an MPS tensor on the combined spin-ancilla index `Fin (d * dK)`, is a
pure-state RFP.

## Main definitions

* `MPOTensor.IsLocalPurificationRFP`: the local purification condition with a
  pure-state RFP purifying tensor.

## Main results

* `MPOTensor.IsLocalPurificationRFP.isLPDO`: the local condition supplies an
  LPDO witness.
* `MPOTensor.IsLocalPurificationRFP.isMPDO`: the local condition generates
  matrix product density operators.
* `MPOTensor.exists_isLocalPurificationRFP_not_isZCL`: the local condition does
  not imply the literal zero-correlation-length condition `IsZCL`, as witnessed
  by a diagonal purification whose ancilla contraction halves the leading
  eigenvalue.
* `MPOTensor.mpo_eq_purificationDensity`: the ancilla contraction at the tensor
  level agrees, at every system size, with the ancillary trace of the pure
  spin-ancilla matrix product state.
* `MPOTensor.isPRFP_of_isLocalPurificationRFP`: the local purification condition
  implies the source purification renormalization fixed-point predicate `IsPRFP`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, `Psipuri`
  (line 747), pure-state RFP Definition 3.2.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- A tensor `M` satisfies the local purification-RFP condition when it is the
ancilla contraction of a pure-state renormalization fixed point: there are a
Kraus dimension `dK`, an inner bond dimension `D'`, a purifying family
`A^{(i,k)} ∈ M_{D'}(ℂ)`, and a bond-space identification
`e : Fin D ≃ Fin D' × Fin D'`
such that

  `M^{ij} = (∑_k A^{(i,k)} ⊗ conj(A^{(j,k)})).submatrix e e`,

and the purifying tensor `A`, viewed as an MPS tensor on the combined
spin–ancilla index `Fin (d * dK)`, is a pure-state renormalization fixed point.

**Scope restriction:** This is a local tensor condition motivated by
arXiv:1606.00608, `Psipuri` (line 747), not the source PRFP definition itself.
The positive-length global purification equation is recorded separately in
`TNLean.MPS.MPDO.PRFP`; see
`docs/paper-gaps/cpsv16_purification_rfp_definition.tex`. -/
def IsLocalPurificationRFP (M : MPOTensor d D) : Prop :=
  ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D'),
    (∀ i j : Fin d, M i j = (∑ k : Fin dK,
      (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e)
    ∧ MPSTensor.IsRFP (purificationTensor A)

/-- The local purification-RFP condition has the local purification structure:
its purifying data is an `IsLPDO` witness (the RFP condition on the purifying
tensor is dropped). -/
theorem IsLocalPurificationRFP.isLPDO {M : MPOTensor d D}
    (h : IsLocalPurificationRFP M) : IsLPDO M := by
  obtain ⟨dK, D', A, e, hM, _⟩ := h
  exact ⟨dK, D', A, e, hM⟩

/-- The local purification-RFP condition generates matrix product density
operators: tracing the ancilla of the purification yields a positive
semidefinite operator at every system size (via `IsLPDO.isMPDO`). -/
theorem IsLocalPurificationRFP.isMPDO {M : MPOTensor d D}
    (h : IsLocalPurificationRFP M) : IsMPDO M :=
  h.isLPDO.isMPDO

/-! ## A local purification-RFP tensor that is not ZCL

The local purification-RFP condition does not imply the literal zero-correlation
length condition `MPOTensor.IsZCL` (`E_M ∘ E_M = E_M`). The witness below is the
diagonal purification at `d = d_K = 2`, `D = D' = 1`, `A = [1/√2, 0, 0, 1/√2]`:
its purifying tensor is a pure-state renormalization fixed point, yet the ancilla
trace contraction halves the leading eigenvalue, so the induced transfer map is
`½ • id` and idempotence fails. See
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`. -/

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
      · rw [if_pos ⟨hac, hbc⟩]
        simp only [witnessAmplitude, if_pos hac, if_pos hbc, map_inv₀, Complex.conj_ofReal]
        exact sqrt2_inv_mul_self
      · rw [if_neg (fun h => hbc h.2)]
        simp only [witnessAmplitude, if_neg hbc, map_zero, mul_zero]
    · rw [if_neg (fun h => hac h.1)]
      simp only [witnessAmplitude, if_neg hac, zero_mul]
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
lemma witnessAcombined_isRFP : MPSTensor.IsRFP witnessAcombined := by
  have h : MPSTensor.transferMap witnessAcombined = LinearMap.id := by
    refine LinearMap.ext fun X => ?_
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim a 0
    obtain rfl : b = 0 := Subsingleton.elim b 0
    rw [MPSTensor.transferMap_apply, Matrix.sum_apply, Fin.sum_univ_four]
    have e0 : (0 : Fin (2 * 2)).divNat = 0 ∧ (0 : Fin (2 * 2)).modNat = 0 := by decide
    have e1 : (1 : Fin (2 * 2)).divNat = 0 ∧ (1 : Fin (2 * 2)).modNat = 1 := by decide
    have e2 : (2 : Fin (2 * 2)).divNat = 1 ∧ (2 : Fin (2 * 2)).modNat = 0 := by decide
    have e3 : (3 : Fin (2 * 2)).divNat = 1 ∧ (3 : Fin (2 * 2)).modNat = 1 := by decide
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply,
      witnessAcombined, purificationTensor, witnessA, Matrix.of_apply, LinearMap.id_apply, e0.1,
      e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, witnessAmplitude, Fin.reduceEq, ↓reduceIte,
      zero_mul, add_zero, ← starRingEnd_apply, map_inv₀, Complex.conj_ofReal]
    linear_combination (2 * X 0 0) * sqrt2_inv_mul_self
  rw [MPSTensor.IsRFP, h, LinearMap.comp_id]

/-- **The local purification-RFP condition does not imply literal zero-correlation
length.** There is an MPO tensor satisfying `IsLocalPurificationRFP` whose
literal transfer-map idempotence `E_M ∘ E_M = E_M` fails, because the
purification's trace contraction drops the leading eigenvalue below `1`. This is
the canonical-form deviation documented in
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`. -/
theorem exists_isLocalPurificationRFP_not_isZCL :
    ∃ M : MPOTensor 2 1, IsLocalPurificationRFP M ∧ ¬ IsZCL M := by
  refine ⟨witnessM, ⟨2, 1, witnessA, (finProdFinEquiv (m := 1) (n := 1)).symm, fun _ _ => rfl,
    witnessAcombined_isRFP⟩, ?_⟩
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
      if_pos rfl, if_pos rfl]
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
docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex: the physical-trace
transfer correctly classifies the maximally mixed product state as having zero
correlation length, whereas the doubled-index condition wrongly excludes it. -/
theorem isSourceZCL_witnessM : IsSourceZCL witnessM :=
  isSourceZCL_of_physTraceTransfer_sq witnessM
    (by rw [physTraceTransfer_witnessM]; exact one_ne_zero)
    (by rw [physTraceTransfer_witnessM, mul_one])

/-! ## Purification renormalization fixed point implies source zero correlation length

The source theorem (arXiv:1606.00608, lines 775–786) states that, for a tensor
M admitting a matrix product state purification, the three conditions

* M is a purification renormalization fixed point (the definition at
  arXiv:1606.00608, line 758),
* M has zero correlation length,
* the density operators generated by M are produced by iterating a single
  length-independent completely positive map on a fixed product input
  (arXiv:1606.00608, line 770),

are equivalent. Established here is a local, scope-restricted analogue of this
forward implication, on the physical-trace transfer object 𝒯_M = ∑_i M^{ii}
(`physTraceTransfer`, the transfer object of Definition 4.2, arXiv:1606.00608,
lines 735–739): it assumes the one-site local purification predicate
(`IsLocalPurificationRFP`), not the global purification equation, so it does not
cover a source purification renormalization fixed point known only through that
global equation. When the purifying tensor A is a pure-state renormalization
fixed point, the transfer matrix of its transfer map is idempotent, and closing
the physical legs of M transports that idempotence to 𝒯_M. -/

/-- **Idempotence of the physical-trace transfer under the local
purification-RFP condition.** If M is the ancilla contraction of a pure-state
renormalization fixed point (`IsLocalPurificationRFP`, motivated by the
purification equation at arXiv:1606.00608, line 747, and the definition at
line 758), then the physical-trace transfer 𝒯_M = ∑_i M^{ii}
is idempotent: 𝒯_M 𝒯_M = 𝒯_M.

The purifying tensor A has transfer matrix K' = ∑_p conj(A_p) ⊗ A_p
(`MPSTensor.transferMatrix_eq`); the pure-state RFP condition makes K'
idempotent (`transferMatrix_comp`). Closing the ket and bra physical legs of M
rewrites 𝒯_M as a reindexing of K' by the bond identification e together
with the Kronecker factor swap, and matrix idempotence is preserved under
reindexing by an equivalence (`Matrix.submatrix_mul_equiv`). -/
theorem physTraceTransfer_sq_of_isLocalPurificationRFP (M : MPOTensor d D)
    (h : IsLocalPurificationRFP M) :
    physTraceTransfer M * physTraceTransfer M = physTraceTransfer M := by
  obtain ⟨dK, D', A, e, hM, hRFP⟩ := h
  set s : (Fin D' × Fin D') ≃ (Fin D' × Fin D') := Equiv.prodComm (Fin D') (Fin D')
    with hs
  set K' : Matrix (Fin D' × Fin D') (Fin D' × Fin D') ℂ :=
    transferMatrix (MPSTensor.transferMap (purificationTensor A)) with hK'
  set K : Matrix (Fin D' × Fin D') (Fin D' × Fin D') ℂ :=
    ∑ i : Fin d, ∑ k : Fin dK, (A i k) ⊗ₖ ((A i k).map (starRingEnd ℂ)) with hKdef
  -- The pure-state RFP condition makes the transfer matrix idempotent.
  have hidemK' : K' * K' = K' := by
    have hRFP' : MPSTensor.transferMap (purificationTensor A) ∘ₗ
        MPSTensor.transferMap (purificationTensor A)
          = MPSTensor.transferMap (purificationTensor A) := hRFP
    have h2 := congrArg transferMatrix hRFP'
    rw [transferMatrix_comp] at h2
    rw [hK']; exact h2
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
  -- Identify `K` with the swapped transfer matrix, hence `K` is idempotent.
  have hKK' : K = K'.submatrix (⇑s) (⇑s) := by rw [hKdef, hreindex, step1]
  have hidemK : K * K = K := by
    rw [hKK', Matrix.submatrix_mul_equiv K' K' (⇑s) s (⇑s), hidemK']
  -- Closing the physical legs identifies `𝒯_M` with a reindexing of `K`.
  have hPT : physTraceTransfer M = K.submatrix (⇑e) (⇑e) := by
    ext a b
    rw [show physTraceTransfer M = ∑ i : Fin d, M i i from rfl, Matrix.sum_apply,
      Matrix.submatrix_apply, hKdef, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hM i i, Matrix.submatrix_apply]
  rw [hPT, Matrix.submatrix_mul_equiv K K (⇑e) e (⇑e), hidemK]

/-- **The local purification-RFP condition with nonzero physical-trace transfer
has source zero correlation length** (the forward implication, from PRFP to ZCL,
of arXiv:1606.00608, lines 775–786, on the source transfer object). If the ancilla
contraction of a pure-state renormalization fixed point has nonzero
physical-trace transfer 𝒯_M = ∑_i M^{ii} ≠ 0, then M has source zero
correlation length.

**Scope restriction (normalization):** the literal unconditional implication
`IsLocalPurificationRFP M → IsSourceZCL M` is false. The zero tensor
(`D = D' = dK = 1`, `A i 0 = 0`) satisfies `IsLocalPurificationRFP` — its
purifying tensor is identically zero, and `0 ∘ 0 = 0` makes that tensor a
pure-state renormalization fixed point — yet `physTraceTransfer M = 0`, so it is
not source ZCL. The hypothesis `physTraceTransfer M ≠ 0` reflects the paper's
PRFP being a *normalized* pure-state renormalization fixed point with leading
eigenvalue `1`, a condition that `IsLocalPurificationRFP` drops. See
`docs/paper-gaps/cpsv16_purification_rfp_definition.tex`. -/
theorem isSourceZCL_of_isLocalPurificationRFP (M : MPOTensor d D)
    (h : IsLocalPurificationRFP M) (h0 : physTraceTransfer M ≠ 0) :
    IsSourceZCL M :=
  isSourceZCL_of_physTraceTransfer_sq M h0
    (physTraceTransfer_sq_of_isLocalPurificationRFP M h)

/-! ## The tensor purification identity and the source purification RFP

A tensor that is the ancilla contraction of a purifying family (the purification
graphic of arXiv:1606.00608, line 747) generates, at every system size, exactly
the ancillary trace of the pure spin-ancilla matrix product state. This is the
coefficient form of the purification equation at arXiv:1606.00608, line 751, and
it carries the local purification condition to the global purification equation
of the source purification renormalization fixed point (arXiv:1606.00608,
Definition 4.4, line 758). -/

/-- Word evaluation of a matrix product state tensor on a listed configuration is
the ordered product of the per-site matrices. -/
private theorem evalWord_ofFn_prod {dphys Dbond : ℕ} (A : MPSTensor dphys Dbond) {N : ℕ}
    (σ : Fin N → Fin dphys) :
    MPSTensor.evalWord A (List.ofFn σ) = (List.ofFn fun l => A (σ l)).prod := by
  induction N with
  | zero => simp only [List.ofFn_zero, MPSTensor.evalWord_nil, List.prod_nil]
  | succ n ih =>
    simp only [List.ofFn_succ, MPSTensor.evalWord_cons, List.prod_cons]
    congr 1
    exact ih (σ ∘ Fin.succ)

/-- The purifying spin-ancilla tensor recovers the original amplitude at the
encoded product index: evaluating `purificationTensor` at the spin-ancilla pair
returns the corresponding matrix of the family. -/
private theorem purificationTensor_finProdFinEquiv {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) (i : Fin d) (k : Fin dK) :
    purificationTensor A (finProdFinEquiv (i, k)) = A i k := by
  have h : ((finProdFinEquiv (i, k) : Fin (d * dK)).divNat,
      (finProdFinEquiv (i, k) : Fin (d * dK)).modNat) = (i, k) :=
    finProdFinEquiv.symm_apply_apply (i, k)
  have hd : (finProdFinEquiv (i, k) : Fin (d * dK)).divNat = i := congrArg Prod.fst h
  have hm : (finProdFinEquiv (i, k) : Fin (d * dK)).modNat = k := congrArg Prod.snd h
  change A (finProdFinEquiv (i, k)).divNat (finProdFinEquiv (i, k)).modNat = A i k
  rw [hd, hm]

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
  simp only [MPSTensor.mpv_eq, MPSTensor.coeff_eq, evalWord_ofFn_prod, hfun]

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

/-- **The local purification condition implies the source purification
renormalization fixed point.** A tensor satisfying `IsLocalPurificationRFP`
carries a purifying family that is a pure-state renormalization fixed point
(`MPSTensor.IsRFP`) and whose ancilla contraction is the tensor; by
`mpo_eq_purificationDensity` that contraction satisfies the global purification
equation at every positive system size, so the same family witnesses `IsPRFP`
(arXiv:1606.00608, Definition 4.4, line 758).

This is the tensor-identity to global-state-equation direction and adds no
hypothesis beyond `IsLocalPurificationRFP`. Together with
`isSourceZCL_of_isLocalPurificationRFP` (under a nonzero physical-trace transfer)
it shows the local purification condition delivers both the source Definition 4.4
predicate and source zero correlation length. -/
theorem isPRFP_of_isLocalPurificationRFP {M : MPOTensor d D}
    (h : IsLocalPurificationRFP M) : IsPRFP M := by
  obtain ⟨dK, D', A, e, hM, hRFP⟩ := h
  refine ⟨dK, D', A, ?_, hRFP⟩
  intro N _
  exact mpo_eq_purificationDensity A e hM N

end MPOTensor
