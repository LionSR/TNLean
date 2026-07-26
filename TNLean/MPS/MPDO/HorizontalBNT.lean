/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.InvariantProjection
import TNLean.MPS.MPDO.PostBlockedRepresentativeSpan

/-!
# Representative-indexed horizontal canonical form

This file connects the public horizontal canonical-form predicate for an MPO
to the representative-grouped form of Lemma L.  Repeated copies of a normal
tensor are grouped by their BNT representative before the trace-separation
argument is applied.  The resulting first-site conclusion therefore holds on
every representative without a per-copy separation hypothesis.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, lines 264--301
  and Appendix C.3, Lemma L, lines 1835--1858.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1873--1887.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- First-site insertion commutes with a weighted block-diagonal direct sum.

This is the linear passage from the minimal representatives to the repeated
sectors in arXiv:1606.00608, eq. `eq:II_ABasicTensors`, lines 281--301. -/
theorem insertedTensor_toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (Y : Matrix (Fin d) (Fin d) ℂ) (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k)) :
    insertedTensor Y (toTensorFromBlocks μ A) =
      toTensorFromBlocks μ (fun k ↦ insertedTensor Y (A k)) := by
  funext i
  change (∑ j, Y i j •
      Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k ↦ μ k • A k j)) =
    Matrix.reindexLinearEquiv ℂ ℂ finSigmaFinEquiv finSigmaFinEquiv
      (Matrix.blockDiagonal' fun k ↦ μ k • insertedTensor Y (A k) i)
  simp_rw [← (Matrix.reindexLinearEquiv ℂ ℂ
    finSigmaFinEquiv finSigmaFinEquiv).map_smul]
  rw [← map_sum]
  congr 1
  funext a b
  rw [Matrix.sum_apply]
  simp_rw [Matrix.smul_apply]
  by_cases h : a.1 = b.1
  · simp_rw [Matrix.blockDiagonal'_apply, dif_pos h]
    simp only [insertedTensor, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    calc
      ∑ x, Y i x * (μ a.1 * A a.1 x a.2 (cast _ b.2)) =
          ∑ x, μ a.1 * (Y i x * A a.1 x a.2 (cast _ b.2)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = μ a.1 * ∑ x, Y i x * A a.1 x a.2 (cast _ b.2) :=
        (Finset.mul_sum ..).symm
  · simp_rw [Matrix.blockDiagonal'_apply, dif_neg h]
    simp

/-- Equality of insertions on every minimal representative gives equality on
the full sector decomposition, including all repeated weighted copies.

Source: arXiv:1606.00608, eq. `eq:II_ABasicTensors`, lines 281--301. -/
theorem SectorDecomposition.insertedTensor_toTensor_eq_of_basis
    (S : SectorDecomposition d) (Y Z : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ j, insertedTensor Y (S.basis j) = insertedTensor Z (S.basis j)) :
    insertedTensor Y S.toTensor = insertedTensor Z S.toTensor := by
  rw [S.toTensor_eq_toTensorFromBlocks_flat,
    insertedTensor_toTensorFromBlocks, insertedTensor_toTensorFromBlocks]
  congr 1
  funext s
  exact h (S.flatIndexEquiv.symm s).1

/-- An equality between two first-site insertions is preserved by a common
global gauge conjugation.

This is the gauge transport used after the direct-sum identity in
arXiv:1606.00608, eq. `eq:II_ABasicTensors`, lines 281--301. -/
theorem insertedTensor_eq_of_gauge
    {A B : MPSTensor d D} (X : GL (Fin D) ℂ)
    (hX : ∀ i, B i = (X : Matrix (Fin D) (Fin D) ℂ) * A i *
      (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (Y Z : Matrix (Fin d) (Fin d) ℂ)
    (hA : insertedTensor Y A = insertedTensor Z A) :
    insertedTensor Y B = insertedTensor Z B := by
  funext i
  simp only [insertedTensor]
  simp_rw [hX]
  calc
    ∑ j, Y i j • ((X : Matrix (Fin D) (Fin D) ℂ) * A j *
        (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) =
        (X : Matrix (Fin D) (Fin D) ℂ) *
          (∑ j, Y i j • A j) *
            (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp
    _ = (X : Matrix (Fin D) (Fin D) ℂ) *
          (∑ j, Z i j • A j) *
            (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      rw [show (∑ j, Y i j • A j) = ∑ j, Z i j • A j from congrFun hA i]
    _ = ∑ j, Z i j • ((X : Matrix (Fin D) (Fin D) ℂ) * A j *
        (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- Normalized BNT-refined horizontal form for an MPO tensor.

The doubled-index tensor is the representative-indexed BNT sector
decomposition, with one invertible gauge on each repeated copy. Thus the
global gauge is the block direct sum of the copy gauges, rather than an
arbitrary similarity that could mix distinct sectors. Repeated
gauge-equivalent copies are grouped over one representative and retain their
individual nonzero weights. There is no additional all-zero summand.

**Scope restriction (BNT-refined horizontal form):** this predicate is stronger
than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, canonical form at lines 237--244 and the BNT
decomposition `eq:II_ABasicTensors` at lines 281--301. -/
def IsHorizontalCF (M : MPOTensor d D) : Prop :=
  ∃ S : MPSTensor.SectorDecomposition (d * d),
    MPSTensor.IsBNTCanonicalForm S ∧
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

/-- Normalized BNT-refined horizontal form gives its positive-length BNT MPV
representation.

The block direct sum of the copy similarities leaves every closed
matrix-product trace invariant.

Source: arXiv:1606.00608, `eq:II_ABasicTensors` and `decBSV`, lines
281--301. -/
theorem IsHorizontalCF.hasHorizontalCFMPVRepresentation
    {M : MPOTensor d D} (hHorizontal : IsHorizontalCF M) :
    HasHorizontalCFMPVRepresentation M := by
  obtain ⟨S, hCF, hTotal, Xcopy, hX⟩ := hHorizontal
  subst D
  refine ⟨S, hCF, ?_⟩
  have hGauge : MPSTensor.GaugeEquiv S.toTensor M.toMPSTensor := by
    refine ⟨MPSTensor.globalGaugeOfBlocks Xcopy, ?_⟩
    intro i
    simpa using hX i
  intro N _hN σ
  exact (hGauge.sameMPV N σ).symm

/-- Inserting the doubled-index left action gives the doubled-index tensor of
left multiplication of the vertically viewed MPO tensor.

Source: arXiv:1606.00608, Proposition 4.13, lines 1873--1887. -/
theorem insertedTensor_ketLeftAction_toMPSTensor
    (M : MPOTensor d D) (Q : Matrix (Fin d) (Fin d) ℂ) :
    MPSTensor.insertedTensor (MPSTensor.ketLeftAction Q) M.toMPSTensor =
      (M.ketLeftMul Q).toMPSTensor := by
  funext p
  rw [MPSTensor.insertedTensor]
  change (∑ q : Fin (d * d),
      MPSTensor.ketLeftAction Q p q • M q.divNat q.modNat) =
    ∑ k : Fin d, Q p.divNat k • M k p.modNat
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [MPSTensor.ketLeftAction, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, ite_smul, zero_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_eq_single p.modNat]
  · simp
  · intro j hj
    rw [if_neg (Ne.symm hj)]

/-- Inserting the doubled-index right action gives the doubled-index tensor of
right multiplication of the vertically viewed MPO tensor.

Source: arXiv:1606.00608, Proposition 4.13, lines 1873--1887. -/
theorem insertedTensor_braRightAction_toMPSTensor
    (M : MPOTensor d D) (Q : Matrix (Fin d) (Fin d) ℂ) :
    MPSTensor.insertedTensor (MPSTensor.braRightAction Q) M.toMPSTensor =
      (M.braRightMul Q).toMPSTensor := by
  funext p
  rw [MPSTensor.insertedTensor]
  change (∑ q : Fin (d * d),
      MPSTensor.braRightAction Q p q • M q.divNat q.modNat) =
    ∑ k : Fin d, Q k p.modNat • M p.divNat k
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [MPSTensor.braRightAction, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, ite_smul, zero_smul]
  rw [Fintype.sum_eq_single p.divNat]
  · simp
  · intro i hi
    simp [hi.symm]

/-- Inserting the doubled-index two-sided action gives the doubled-index tensor
of two-sided multiplication of the vertically viewed MPO tensor.

Source: arXiv:1606.00608, Proposition 4.13, lines 1873--1887. -/
theorem insertedTensor_ketLeftBraRightAction_toMPSTensor
    (M : MPOTensor d D) (Q : Matrix (Fin d) (Fin d) ℂ) :
    MPSTensor.insertedTensor
        (MPSTensor.ketLeftBraRightAction Q) M.toMPSTensor =
      ((M.ketLeftMul Q).braRightMul Q).toMPSTensor := by
  funext p
  rw [MPSTensor.insertedTensor]
  change (∑ q : Fin (d * d),
      MPSTensor.ketLeftBraRightAction Q p q • M q.divNat q.modNat) =
    ∑ j : Fin d, Q j p.modNat • (∑ k : Fin d, Q p.divNat k • M k j)
  rw [← finProdFinEquiv.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [MPSTensor.ketLeftBraRightAction,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ring

/-- The two first-site identities in Proposition 4.13 imply equality of the
opposite-corner insertions on every BNT representative.

Positive-length MPV equality transports the first-site identities from the
doubled-index tensor of `M` to the representative-indexed sector
decomposition.  The representative-grouped Lemma L then separates the BNT
representatives while grouping all repeated copies of each representative.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858, applied to
the contractions in Proposition 4.13, lines 1873--1887. -/
theorem representative_opposite_insert_eq_of_rotated_mpo_entries
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hCF : MPSTensor.IsBNTCanonicalForm S)
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (hInv : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin (d * d)),
      (∑ i : Fin d, Q (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n => (ρ (Fin.succ n)).modNat)) =
      ∑ i : Fin d, ∑ j : Fin d, Q (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).modNat)) * Q j (ρ 0).modNat))
    (hComm : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin (d * d)),
      (∑ i : Fin d, Q (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n => (ρ (Fin.succ n)).modNat)) =
      ∑ j : Fin d,
        mpo M (N + 1)
          (Fin.cons (ρ 0).divNat (fun n => (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n => (ρ (Fin.succ n)).modNat)) * Q j (ρ 0).modNat)) :
    ∀ j, MPSTensor.insertedTensor (MPSTensor.braRightAction Q) (S.basis j) =
      MPSTensor.insertedTensor (MPSTensor.ketLeftBraRightAction Q) (S.basis j) := by
  intro j
  calc
    MPSTensor.insertedTensor (MPSTensor.braRightAction Q) (S.basis j) =
        MPSTensor.insertedTensor (MPSTensor.ketLeftAction Q) (S.basis j) :=
      (hCF.insertedTensor_basis_eq_of_firstSiteActionAgree
        ((MPSTensor.firstSiteActionAgree_ketLeft_braRight M Q hComm).of_sameMPVPos hM)
        j).symm
    _ = MPSTensor.insertedTensor
        (MPSTensor.ketLeftBraRightAction Q) (S.basis j) :=
      hCF.insertedTensor_basis_eq_of_firstSiteActionAgree
        ((MPSTensor.firstSiteActionAgree_ketLeft_ketLeftBraRight M Q hInv).of_sameMPVPos hM)
        j

/-- A one-sided invariant Hermitian matrix reduces every horizontal BNT
representative.

If `Q M = Q M Q` for the vertically viewed tensor, positivity of every MPDO
density operator gives the two first-site identities in Proposition 4.13.
The representative-grouped Lemma L then shows that the insertions of `M Q`
and `Q M Q` agree on every representative.

This is the representative-indexed form of the invariant-projection step in
arXiv:1606.00608, Proposition 4.13, lines 1873--1887. -/
theorem representative_braRight_eq_ketLeftBraRight_of_invariant
    (M : MPOTensor d D) (hMpdo : IsMPDO M)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hCF : MPSTensor.IsBNTCanonicalForm S)
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian)
    (hQM : M.ketLeftMul Q = (M.ketLeftMul Q).braRightMul Q) :
    ∀ j, MPSTensor.insertedTensor (MPSTensor.braRightAction Q) (S.basis j) =
      MPSTensor.insertedTensor (MPSTensor.ketLeftBraRightAction Q) (S.basis j) := by
  refine representative_opposite_insert_eq_of_rotated_mpo_entries M S hCF hM Q ?_ ?_
  · intro N ρ
    have h := firstSiteMatrix_mul_mpo_of_ketLeftMul_invariant M Q hQM N
    have h2 := Matrix.ext_iff.mpr h
      (Fin.cons (ρ 0).divNat fun n => (ρ (Fin.succ n)).divNat)
      (Fin.cons (ρ 0).modNat fun n => (ρ (Fin.succ n)).modNat)
    rw [mul_firstSiteMatrix_apply] at h2
    simp only [firstSiteMatrix_mul_apply] at h2
    simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ] at h2
    rw [h2]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  · intro N ρ
    have h := firstSiteMatrix_mul_mpo_comm M hMpdo hQ hQM N
    have h2 := Matrix.ext_iff.mpr h
      (Fin.cons (ρ 0).divNat fun n => (ρ (Fin.succ n)).divNat)
      (Fin.cons (ρ 0).modNat fun n => (ρ (Fin.succ n)).modNat)
    rw [mul_firstSiteMatrix_apply, firstSiteMatrix_mul_apply] at h2
    simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ] at h2
    exact h2

/-- **Lemma L on the original bond space.**

Let `M` be in normalized BNT-refined horizontal form. If two physical operators
have the same first-site action on every matrix product vector of `M`, then
their inserted tensors are equal on the original bond space:
\[
  Y_1V^{(N)}(M)=Z_1V^{(N)}(M)\quad\hbox{for every }N
  \quad\Longrightarrow\quad YM=ZM.
\]
The representative-grouped Lemma L first gives equality on each minimal BNT
representative.  Linearity extends it to all repeated weighted sectors, and
the block direct sum of the copy gauges transports it to `M`.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858, using the
horizontal BNT decomposition at lines 281--301. -/
theorem IsHorizontalCF.insertedTensor_eq_of_firstSiteActionAgree
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M)
    {Y Z : Matrix (Fin (d * d)) (Fin (d * d)) ℂ}
    (hAct : MPSTensor.FirstSiteActionAgree M.toMPSTensor Y Z) :
    MPSTensor.insertedTensor Y M.toMPSTensor =
      MPSTensor.insertedTensor Z M.toMPSTensor := by
  obtain ⟨S, hCF, hTotal, Xcopy, hX⟩ := hHorizontal
  subst D
  let X := MPSTensor.globalGaugeOfBlocks Xcopy
  have hX' : ∀ i, M.toMPSTensor i =
      (X : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (((X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    intro i
    simpa using hX i
  have hGauge : MPSTensor.GaugeEquiv S.toTensor M.toMPSTensor := ⟨X, hX'⟩
  have hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor := by
    intro N _hN σ
    exact (hGauge.sameMPV N σ).symm
  have hBasis :=
    hCF.insertedTensor_basis_eq_of_firstSiteActionAgree (hAct.of_sameMPVPos hM)
  have hSector : MPSTensor.insertedTensor Y S.toTensor =
      MPSTensor.insertedTensor Z S.toTensor :=
    S.insertedTensor_toTensor_eq_of_basis Y Z hBasis
  exact MPSTensor.insertedTensor_eq_of_gauge X hX' Y Z hSector

/-- A displaced idempotent for a tensor in normalized BNT-refined horizontal
form fails to commute with the generated density operator at some positive
chain length.

If commutation held at every positive length, idempotence would give the
one-sided first-site identities for the two-sided compression.  The literal
representative-grouped Lemma L would then give the forbidden letterwise
identity.  This is the contrapositive needed in the periodic-sector paragraph
of arXiv:1606.00608, Proposition 4.13, lines 1888--1893.

**Local fix (noncommuting length):** the source prints noncommutation at every
length, but its contradiction is pointwise and only needs the length produced
here.  Documented in
`docs/paper-gaps/cpgsv17_periodic_sector_projector.tex`. -/
theorem IsHorizontalCF.exists_not_commute_of_displaced
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQidem : IsIdempotentElem Q)
    (hdisp : M.ketLeftMul Q ≠ (M.ketLeftMul Q).braRightMul Q) :
    ∃ N : ℕ, ¬ Commute (firstSiteMatrix Q N) (mpo M (N + 1)) := by
  classical
  by_contra hnone
  simp only [not_exists, not_not] at hnone
  apply hdisp
  have hAct : MPSTensor.FirstSiteActionAgree M.toMPSTensor
      (MPSTensor.ketLeftAction Q) (MPSTensor.ketLeftBraRightAction Q) := by
    apply MPSTensor.firstSiteActionAgree_ketLeft_ketLeftBraRight M Q
    intro N ρ
    have hQ1idem : firstSiteMatrix Q N * firstSiteMatrix Q N =
        firstSiteMatrix Q N := by
      rw [firstSiteMatrix_mul_firstSiteMatrix, hQidem]
    have hOneSided : firstSiteMatrix Q N * mpo M (N + 1) =
        firstSiteMatrix Q N * mpo M (N + 1) * firstSiteMatrix Q N := by
      calc
        firstSiteMatrix Q N * mpo M (N + 1) =
            firstSiteMatrix Q N * firstSiteMatrix Q N * mpo M (N + 1) := by
              rw [hQ1idem]
        _ = firstSiteMatrix Q N *
            (firstSiteMatrix Q N * mpo M (N + 1)) := by rw [Matrix.mul_assoc]
        _ = firstSiteMatrix Q N *
            (mpo M (N + 1) * firstSiteMatrix Q N) := by rw [(hnone N).eq]
        _ = firstSiteMatrix Q N * mpo M (N + 1) *
            firstSiteMatrix Q N := by rw [Matrix.mul_assoc]
    have h2 := Matrix.ext_iff.mpr hOneSided
      (Fin.cons (ρ 0).divNat fun n => (ρ (Fin.succ n)).divNat)
      (Fin.cons (ρ 0).modNat fun n => (ρ (Fin.succ n)).modNat)
    rw [mul_firstSiteMatrix_apply] at h2
    simp only [firstSiteMatrix_mul_apply] at h2
    simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ] at h2
    rw [h2]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hInsert := hHorizontal.insertedTensor_eq_of_firstSiteActionAgree M hAct
  have hTensor : (M.ketLeftMul Q).toMPSTensor =
      ((M.ketLeftMul Q).braRightMul Q).toMPSTensor := by
    rw [← insertedTensor_ketLeftAction_toMPSTensor,
      ← insertedTensor_ketLeftBraRightAction_toMPSTensor]
    exact hInsert
  funext i j
  have hij := congrFun hTensor (finProdFinEquiv (i, j))
  simpa [toMPSTensor] using hij

/-- The normalized BNT-refined horizontal-form predicate supplies the
representative-indexed invariant-projection conclusion.

The witness is the BNT sector decomposition occurring in `IsHorizontalCF`.
Repeated copies remain grouped over their common representative; no
per-copy trace-separation hypothesis is introduced.

Source: arXiv:1606.00608, lines 264--301 and Proposition 4.13,
lines 1873--1887. -/
theorem IsHorizontalCF.exists_representative_braRight_eq_ketLeftBraRight
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hMpdo : IsMPDO M)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian)
    (hQM : M.ketLeftMul Q = (M.ketLeftMul Q).braRightMul Q) :
    ∃ S : MPSTensor.SectorDecomposition (d * d),
      MPSTensor.IsBNTCanonicalForm S ∧
      MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor ∧
      ∀ j, MPSTensor.insertedTensor (MPSTensor.braRightAction Q) (S.basis j) =
        MPSTensor.insertedTensor (MPSTensor.ketLeftBraRightAction Q) (S.basis j) := by
  obtain ⟨S, hCF, hTotal, Xcopy, hX⟩ := hHorizontal
  subst D
  have hGauge : MPSTensor.GaugeEquiv S.toTensor M.toMPSTensor := by
    refine ⟨MPSTensor.globalGaugeOfBlocks Xcopy, ?_⟩
    intro i
    simpa using hX i
  have hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor := by
    intro N _hN σ
    exact (hGauge.sameMPV N σ).symm
  exact ⟨S, hCF, hM,
    representative_braRight_eq_ketLeftBraRight_of_invariant
      M hMpdo S hCF hM hQ hQM⟩

/-- A one-sided invariant Hermitian matrix also reduces the MPO tensor from
the right.

The representative-grouped Lemma L first identifies the two insertions on
every minimal BNT representative.  Linearity gives the identity on all
repeated weighted sectors, and the direct sum of the copy gauges in
`IsHorizontalCF` transports it to the original tensor.  Thus the conclusion
is a literal equality of MPO tensors, rather than merely an equality of their
MPV families.  The source specializes `Q` to an orthogonal projector; this
implication only uses Hermiticity.

This is the equation $\widetilde M Q=Q\widetilde M Q$ in the
invariant-projection step of arXiv:1606.00608, Proposition 4.13, lines
1873--1887. -/
theorem IsHorizontalCF.braRight_eq_ketLeftBraRight_of_invariant
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hMpdo : IsMPDO M)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian)
    (hQM : M.ketLeftMul Q = (M.ketLeftMul Q).braRightMul Q) :
    M.braRightMul Q = (M.ketLeftMul Q).braRightMul Q := by
  obtain ⟨S, hCF, hTotal, Xcopy, hX⟩ := hHorizontal
  subst D
  let X := MPSTensor.globalGaugeOfBlocks Xcopy
  have hX' : ∀ i, M.toMPSTensor i =
      (X : Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) * S.toTensor i *
        (((X)⁻¹ : GL (Fin S.totalDim) ℂ) :
          Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) := by
    intro i
    simpa using hX i
  have hGauge : MPSTensor.GaugeEquiv S.toTensor M.toMPSTensor := ⟨X, hX'⟩
  have hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor := by
    intro N _hN σ
    exact (hGauge.sameMPV N σ).symm
  have hBasis := representative_braRight_eq_ketLeftBraRight_of_invariant
    M hMpdo S hCF hM hQ hQM
  have hSector :
      MPSTensor.insertedTensor (MPSTensor.braRightAction Q) S.toTensor =
        MPSTensor.insertedTensor
          (MPSTensor.ketLeftBraRightAction Q) S.toTensor :=
    S.insertedTensor_toTensor_eq_of_basis _ _ hBasis
  have hOriginal :
      MPSTensor.insertedTensor (MPSTensor.braRightAction Q) M.toMPSTensor =
        MPSTensor.insertedTensor
          (MPSTensor.ketLeftBraRightAction Q) M.toMPSTensor :=
    MPSTensor.insertedTensor_eq_of_gauge X hX' _ _ hSector
  have hTensor : (M.braRightMul Q).toMPSTensor =
      ((M.ketLeftMul Q).braRightMul Q).toMPSTensor := by
    rw [← insertedTensor_braRightAction_toMPSTensor,
      ← insertedTensor_ketLeftBraRightAction_toMPSTensor]
    exact hOriginal
  funext i j
  have hij := congrFun hTensor (finProdFinEquiv (i, j))
  simpa [toMPSTensor] using hij

end MPOTensor
