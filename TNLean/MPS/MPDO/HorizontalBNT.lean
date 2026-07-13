/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.BlockTriangularTrace
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

/-- Adjoin an all-zero block of dimension `z` to an MPS tensor.

The horizontal canonical form of arXiv:1606.00608, lines 217--219 permits
such a block: the sum of the nonzero block dimensions may be strictly smaller
than the original bond dimension. -/
noncomputable def zeroTail (A : MPSTensor d D) (z : ℕ) : MPSTensor d (z + D) :=
  MPSTensor.diagFin (fun _ ↦ 0) A

/-- An all-zero direct summand does not change any positive-length matrix
product vector.

Source: arXiv:1606.00608, lines 217--219. -/
theorem zeroTail_sameMPV₂Pos (A : MPSTensor d D) (z : ℕ) :
    MPSTensor.SameMPV₂Pos (zeroTail A z) A := by
  classical
  intro N hN σ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simp only [MPSTensor.mpv, MPSTensor.coeff, zeroTail]
  let e : (Fin z ⊕ Fin D) ≃ Fin (z + D) := finSumFinEquiv
  change Matrix.trace (MPSTensor.evalWord
      (fun i ↦ Matrix.reindex e e (MPSTensor.diagSum (fun _ ↦ 0) A i))
      (List.ofFn σ)) = _
  rw [MPSTensor.evalWord_reindex (e := e)]
  rw [Matrix.trace_reindex]
  rw [MPSTensor.evalWord_diagSum_is_fromBlocks]
  rw [MPSTensor.trace_fromBlocks_upper]
  simp [List.ofFn_succ]

/-- Positive-length matrix product vector equality transports a first-site
action identity between tensors of possibly different bond dimensions.

This is the form needed when a horizontal canonical form contains the zero
summand allowed in arXiv:1606.00608, lines 217--219: first-site identities
only involve chains of length `N + 1`, and hence never use the empty chain. -/
theorem FirstSiteActionAgree.of_sameMPVPos {D' : ℕ} {A : MPSTensor d D}
    {B : MPSTensor d D'} {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAB : MPSTensor.SameMPV₂Pos A B) (h : FirstSiteActionAgree A Y Z) :
    FirstSiteActionAgree B Y Z := by
  intro N σ
  calc
    ∑ i : Fin d, Y (σ 0) i * MPSTensor.mpv B (Fin.cons i (σ ∘ Fin.succ)) =
        ∑ i : Fin d, Y (σ 0) i * MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hAB (N + 1) (Nat.succ_pos N) (Fin.cons i (σ ∘ Fin.succ))]
    _ = ∑ i : Fin d, Z (σ 0) i *
        MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) := h N σ
    _ = ∑ i : Fin d, Z (σ 0) i *
        MPSTensor.mpv B (Fin.cons i (σ ∘ Fin.succ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hAB (N + 1) (Nat.succ_pos N) (Fin.cons i (σ ∘ Fin.succ))]

/-- First-site insertion commutes with adjoining an all-zero summand.

Source: the zero-block allowance in arXiv:1606.00608, lines 217--219. -/
theorem insertedTensor_zeroTail (Y : Matrix (Fin d) (Fin d) ℂ)
    (A : MPSTensor d D) (z : ℕ) :
    insertedTensor Y (zeroTail A z) = zeroTail (insertedTensor Y A) z := by
  funext i a b
  generalize ha : finSumFinEquiv.symm a = a'
  generalize hb : finSumFinEquiv.symm b = b'
  cases a' <;> cases b' <;>
    simp [insertedTensor, zeroTail, diagFin, diagSum, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.submatrix_apply, ha, hb]

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

/-- Horizontal canonical form for an MPO tensor.

The doubled-index tensor is literally gauge-conjugate to the direct sum of an
all-zero block and a representative-indexed BNT sector decomposition.
Repeated gauge-equivalent copies are grouped over one representative and
retain their individual nonzero weights.  This is the decomposition in
arXiv:1606.00608, lines 217--219 and eq. `eq:II_ABasicTensors`, lines 281--301. -/
def IsHorizontalCF (M : MPOTensor d D) : Prop :=
  ∃ S : MPSTensor.SectorDecomposition (d * d),
    MPSTensor.IsBNTCanonicalForm S ∧
      ∃ z : ℕ, ∃ hTotal : z + S.totalDim = D, ∃ X : GL (Fin D) ℂ,
        ∀ i : Fin (d * d),
          M.toMPSTensor i =
            (X : Matrix (Fin D) (Fin D) ℂ) *
              cast (by rw [hTotal] :
                  Matrix (Fin (z + S.totalDim)) (Fin (z + S.totalDim)) ℂ =
                    Matrix (Fin D) (Fin D) ℂ)
                (MPSTensor.zeroTail S.toTensor z i) *
              (((X)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)

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

/-- The public horizontal canonical-form predicate supplies the
representative-indexed invariant-projection conclusion.

The witness is the BNT sector decomposition occurring in `IsHorizontalCF`.
Repeated copies remain grouped over their common representative; no
per-copy trace-separation hypothesis is introduced.  The equality is stated
for positive lengths because the permitted all-zero summand changes only the
empty-chain coefficient.

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
  obtain ⟨S, hCF, z, hTotal, X, hX⟩ := hHorizontal
  subst D
  have hGauge : MPSTensor.GaugeEquiv
      (MPSTensor.zeroTail S.toTensor z) M.toMPSTensor := by
    refine ⟨X, ?_⟩
    intro i
    simpa using hX i
  have hMZero : MPSTensor.SameMPV₂Pos M.toMPSTensor
      (MPSTensor.zeroTail S.toTensor z) := by
    intro N _ σ
    exact (hGauge.sameMPV N σ).symm
  have hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor :=
    hMZero.trans (MPSTensor.zeroTail_sameMPV₂Pos S.toTensor z)
  exact ⟨S, hCF, hM,
    representative_braRight_eq_ketLeftBraRight_of_invariant
      M hMpdo S hCF hM hQ hQM⟩

/-- A one-sided invariant Hermitian matrix also reduces the MPO tensor from
the right.

The representative-grouped Lemma L first identifies the two insertions on
every minimal BNT representative.  Linearity gives the identity on all
repeated weighted sectors and the all-zero summand, and the global gauge in
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
  obtain ⟨S, hCF, z, hTotal, X, hX⟩ := hHorizontal
  subst D
  have hX' : ∀ i, M.toMPSTensor i =
      (X : Matrix (Fin (z + S.totalDim)) (Fin (z + S.totalDim)) ℂ) *
        MPSTensor.zeroTail S.toTensor z i *
        (((X)⁻¹ : GL (Fin (z + S.totalDim)) ℂ) :
          Matrix (Fin (z + S.totalDim)) (Fin (z + S.totalDim)) ℂ) := by
    intro i
    simpa using hX i
  have hGauge : MPSTensor.GaugeEquiv
      (MPSTensor.zeroTail S.toTensor z) M.toMPSTensor := ⟨X, hX'⟩
  have hMZero : MPSTensor.SameMPV₂Pos M.toMPSTensor
      (MPSTensor.zeroTail S.toTensor z) := by
    intro N _ σ
    exact (hGauge.sameMPV N σ).symm
  have hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor :=
    hMZero.trans (MPSTensor.zeroTail_sameMPV₂Pos S.toTensor z)
  have hBasis := representative_braRight_eq_ketLeftBraRight_of_invariant
    M hMpdo S hCF hM hQ hQM
  have hSector :
      MPSTensor.insertedTensor (MPSTensor.braRightAction Q) S.toTensor =
        MPSTensor.insertedTensor
          (MPSTensor.ketLeftBraRightAction Q) S.toTensor :=
    S.insertedTensor_toTensor_eq_of_basis _ _ hBasis
  have hZero :
      MPSTensor.insertedTensor (MPSTensor.braRightAction Q)
          (MPSTensor.zeroTail S.toTensor z) =
        MPSTensor.insertedTensor (MPSTensor.ketLeftBraRightAction Q)
          (MPSTensor.zeroTail S.toTensor z) := by
    rw [MPSTensor.insertedTensor_zeroTail,
      MPSTensor.insertedTensor_zeroTail, hSector]
  have hOriginal :
      MPSTensor.insertedTensor (MPSTensor.braRightAction Q) M.toMPSTensor =
        MPSTensor.insertedTensor
          (MPSTensor.ketLeftBraRightAction Q) M.toMPSTensor :=
    MPSTensor.insertedTensor_eq_of_gauge X hX' _ _ hZero
  have hTensor : (M.braRightMul Q).toMPSTensor =
      ((M.ketLeftMul Q).braRightMul Q).toMPSTensor := by
    rw [← insertedTensor_braRightAction_toMPSTensor,
      ← insertedTensor_ketLeftBraRightAction_toMPSTensor]
    exact hOriginal
  funext i j
  have hij := congrFun hTensor (finProdFinEquiv (i, j))
  simpa [toMPSTensor] using hij

end MPOTensor
