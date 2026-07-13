/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PostBlockedRepresentativeSpan

/-!
# Horizontal BNT canonical form for matrix product operators

The horizontal canonical form of an MPO is expressed through a minimal basis
of normal tensors and the repeated weighted copies lying over each basis
representative.  The associated doubled-index tensor has the same complete MPV
family as
\[
  \bigoplus_{j=1}^g\bigoplus_{q=1}^{r_j}\mu_{j,q}A_j,
\]
so its length-\(N\) vector is
\[
  \sum_{j=1}^g\left(\sum_{q=1}^{r_j}\mu_{j,q}^N\right)V^{(N)}(A_j).
\]
This is the representative-indexed form of arXiv:1606.00608,
equations `eq:II_ABasicTensors` and `decBSV`, lines 283--301.

The theorems below apply the representative-grouped Lemma L of Appendix C.3,
lines 1835--1858, to the three first-site contractions used in the proof of
Proposition 4.13.  Repeated gauge-equivalent copies are grouped before the
trace-separation argument; no per-copy separation hypothesis is imposed.

## Main definitions

* `MPOTensor.IsHorizontalCF`: horizontal BNT canonical form at the level of
  the complete MPV family.

## Main results

* `MPSTensor.IsBNTCanonicalForm.insertedTensor_basis_eq_of_two_firstSiteActionAgree`:
  two first-site identities with a common left action give equality of the
  other two insertions on every BNT representative.
* `MPOTensor.basis_opposite_insert_eq_of_rotated_mpo_entries`: the preceding
  statement for the three doubled-index contractions of Proposition 4.13.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- Horizontal canonical form of an MPO tensor at the level of its complete
matrix product vector family.

The doubled-index tensor is represented by a minimal basis of normal tensors
with nonzero weighted copies.  Copies over the same representative are grouped
by the coefficients \(\sum_q\mu_{j,q}^N\), as in arXiv:1606.00608,
equations `eq:II_ABasicTensors` and `decBSV`, lines 283--301. -/
def IsHorizontalCF (M : MPOTensor d D) : Prop :=
  ∃ P : MPSTensor.SectorDecomposition (d * d),
    MPSTensor.IsBNTCanonicalForm P ∧ MPSTensor.SameMPV₂ M.toMPSTensor P.toTensor

end MPOTensor

namespace MPSTensor.IsBNTCanonicalForm

variable {d : ℕ} {P : SectorDecomposition d}

/-- If two first-site identities have the same left action, then the other two
insertions agree on every basis-of-normal-tensors representative.

The copies over a representative contribute the grouped coefficient
\(\sum_q\mu_{j,q}^N\).  The representative-grouped Lemma L applies separately
to both identities and gives the conclusion without separating repeated
copies.  Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1858. -/
theorem insertedTensor_basis_eq_of_two_firstSiteActionAgree
    (hCF : IsBNTCanonicalForm P)
    {Yleft Ycorner Yright : Matrix (Fin d) (Fin d) ℂ}
    (hInv : FirstSiteActionAgree P.toTensor Yleft Ycorner)
    (hPos : FirstSiteActionAgree P.toTensor Yleft Yright) :
    ∀ j, insertedTensor Yright (P.basis j) = insertedTensor Ycorner (P.basis j) := by
  exact fun j ↦ (hCF.insertedTensor_basis_eq_of_firstSiteActionAgree hPos j).symm.trans
    (hCF.insertedTensor_basis_eq_of_firstSiteActionAgree hInv j)

end MPSTensor.IsBNTCanonicalForm

namespace MPOTensor

variable {d D : ℕ}

/-- The three first-site contractions in Proposition 4.13 agree on every
basis-of-normal-tensors representative.

Let \(Y_L,Y_C,Y_R\) denote the doubled-index matrices representing
\(PH^{(N)}\), \(PH^{(N)}P\), and \(H^{(N)}P\), respectively.  If the first
contraction agrees with each of the other two at every length, then
\(Y_RA_j=Y_CA_j\) for every minimal representative \(A_j\) of the horizontal
canonical form.

Source: arXiv:1606.00608, Proposition 4.13, lines 1873--1887, using the
representative-grouped Lemma L at Appendix C.3, lines 1835--1858. -/
theorem basis_opposite_insert_eq_of_rotated_mpo_entries
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hCF : MPSTensor.IsBNTCanonicalForm S)
    (hM : MPSTensor.SameMPV₂ M.toMPSTensor S.toTensor)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hInv : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin (d * d)),
      (∑ i : Fin d, P (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n ↦ (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n ↦ (ρ (Fin.succ n)).modNat)) =
      ∑ i : Fin d, ∑ j : Fin d, P (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n ↦ (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n ↦ (ρ (Fin.succ n)).modNat)) * P j (ρ 0).modNat))
    (hComm : ∀ (N : ℕ) (ρ : Fin (N + 1) → Fin (d * d)),
      (∑ i : Fin d, P (ρ 0).divNat i *
        mpo M (N + 1) (Fin.cons i (fun n ↦ (ρ (Fin.succ n)).divNat))
          (Fin.cons (ρ 0).modNat (fun n ↦ (ρ (Fin.succ n)).modNat)) =
      ∑ j : Fin d,
        mpo M (N + 1)
          (Fin.cons (ρ 0).divNat (fun n ↦ (ρ (Fin.succ n)).divNat))
          (Fin.cons j (fun n ↦ (ρ (Fin.succ n)).modNat)) * P j (ρ 0).modNat)) :
    ∀ k, MPSTensor.insertedTensor (MPSTensor.braRightAction P) (S.basis k) =
      MPSTensor.insertedTensor (MPSTensor.ketLeftBraRightAction P) (S.basis k) := by
  exact hCF.insertedTensor_basis_eq_of_two_firstSiteActionAgree
    (MPSTensor.FirstSiteActionAgree.of_sameMPV hM
      (MPSTensor.firstSiteActionAgree_ketLeft_ketLeftBraRight M P hInv))
    (MPSTensor.FirstSiteActionAgree.of_sameMPV hM
      (MPSTensor.firstSiteActionAgree_ketLeft_braRight M P hComm))

end MPOTensor
