/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.OperatorProduct

/-!
# Physical adjoint of an MPO tensor

This file defines the physical adjoint, which exchanges and conjugates the
physical indices of an MPO tensor without reversing its virtual chain, and
proves the corresponding word and periodic-operator identities.

## Main definitions

* `MPOTensor.bondPairSwap` — exchange of the two doubled virtual-bond indices.
* `MPOTensor.bondPairSwapEquiv` — the corresponding doubled-bond equivalence.
* `MPOTensor.productBondSwapEquiv` — exchange of two possibly unequal product-bond factors.
* `MPOTensor.reindexBond` — transport of an MPO tensor along a bond equivalence.
* `MPOTensor.physicalAdjointTensor` — physical adjoint without virtual reflection.

## Main results

* `MPOTensor.physicalAdjointTensor_mulTensor` — the physical adjoint reverses a product after
  exchanging the two product-bond factors.
* `MPOTensor.evalWord_physicalAdjointTensor` — word evaluation under physical adjoint.
* `MPOTensor.mpo_physicalAdjointTensor` — the periodic family is conjugate-transposed.
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Exchange the two oriented bond indices of a doubled virtual index.
For `ab = (a, b)`, this is `bondPairSwap ab = (b, a)`.

This is the bond-index exchange under adjunction in the first diagram of the
proof of Proposition 4.13 of arXiv:1606.00608, lines 1909--1913, and the
virtual-pair reflection used in the proof of Lemma III.7 in Section III.B of
arXiv:1703.09188, lines 536--557. -/
def bondPairSwap (ab : Fin (D * D)) : Fin (D * D) :=
  finProdFinEquiv (ab.modNat, ab.divNat)

@[simp] theorem bondPairSwap_finProdFinEquiv (a b : Fin D) :
    bondPairSwap (finProdFinEquiv (a, b)) = finProdFinEquiv (b, a) := by
  simp [bondPairSwap]

@[simp] theorem bondPairSwap_involutive (ab : Fin (D * D)) :
    bondPairSwap (bondPairSwap ab) = ab := by
  rw [show ab = finProdFinEquiv (ab.divNat, ab.modNat) by
    exact (finProdFinEquiv.apply_symm_apply ab).symm]
  simp

/-- The equivalence exchanging the two entries of a doubled virtual index. -/
def bondPairSwapEquiv (D : ℕ) : Fin (D * D) ≃ Fin (D * D) where
  toFun := bondPairSwap
  invFun := bondPairSwap
  left_inv := bondPairSwap_involutive
  right_inv := bondPairSwap_involutive

@[simp] theorem bondPairSwapEquiv_apply (ab : Fin (D * D)) :
    bondPairSwapEquiv D ab = bondPairSwap ab := rfl

@[simp] theorem bondPairSwapEquiv_symm :
    (bondPairSwapEquiv D).symm = bondPairSwapEquiv D := by
  rfl

/-- The canonical equivalence exchanging two possibly unequal factors of a product bond.
An index encoding `(a, b)` in `Fin (D₁ * D₂)` is sent to the index encoding `(b, a)` in
`Fin (D₂ * D₁)`. -/
def productBondSwapEquiv (D₁ D₂ : ℕ) : Fin (D₁ * D₂) ≃ Fin (D₂ * D₁) :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.prodComm (Fin D₁) (Fin D₂)).trans finProdFinEquiv)

@[simp] theorem productBondSwapEquiv_finProdFinEquiv {D₁ D₂ : ℕ}
    (a : Fin D₁) (b : Fin D₂) :
    productBondSwapEquiv D₁ D₂ (finProdFinEquiv (a, b)) =
      finProdFinEquiv (b, a) := by
  simp [productBondSwapEquiv]

@[simp] theorem productBondSwapEquiv_symm (D₁ D₂ : ℕ) :
    (productBondSwapEquiv D₁ D₂).symm = productBondSwapEquiv D₂ D₁ := by
  apply Equiv.ext
  intro x
  apply (productBondSwapEquiv D₁ D₂).injective
  rcases finProdFinEquiv.surjective x with ⟨⟨a, b⟩, rfl⟩
  simp

/-- For equal factor dimensions, the heterogeneous product-bond swap agrees with the
established doubled-bond swap. -/
theorem productBondSwapEquiv_self (D : ℕ) :
    productBondSwapEquiv D D = bondPairSwapEquiv D := by
  ext x
  rw [show x = finProdFinEquiv (x.divNat, x.modNat) by
    exact (finProdFinEquiv.apply_symm_apply x).symm]
  simp

/-- Transport both virtual indices of an MPO tensor along a bond-space equivalence. -/
def reindexBond {D D' : ℕ} (e : Fin D' ≃ Fin D) (K : MPOTensor d D) :
    MPOTensor d D' :=
  fun i j a b ↦ K i j (e a) (e b)

@[simp] theorem reindexBond_apply {D D' : ℕ} (e : Fin D' ≃ Fin D)
    (K : MPOTensor d D) (i j : Fin d) (a b : Fin D') :
    reindexBond e K i j a b = K i j (e a) (e b) := rfl

/-- The physical adjoint of an MPO tensor swaps its ket and bra indices and conjugates each
virtual matrix entry, without transposing the virtual indices:
$$(K^\sharp)^{ij}_{\beta\alpha} = \overline{K^{ji}_{\beta\alpha}}.$$

This local adjoint relates layer annihilation to the two-sided support condition in equation
`PjKiPj`; unlike `adjointTensor`, it does not reverse virtual multiplication.

Source: arXiv:1606.00608, Appendix C.2, equations `AppKxKy=0`--`PjKiPj`,
lines 1634--1689. -/
def physicalAdjointTensor (K : MPOTensor d D) : MPOTensor d D :=
  fun i j β α ↦ star (K j i β α)

/-- Evaluating the physical adjoint swaps the physical indices and conjugates the entry. -/
@[simp] theorem physicalAdjointTensor_apply (K : MPOTensor d D)
    (i j : Fin d) (β α : Fin D) :
    physicalAdjointTensor K i j β α = star (K j i β α) := rfl

/-- The physical adjoint reverses the order of an MPO tensor product. Since `mulTensor U V`
has bond coordinates ordered as `Fin D₁ × Fin D₂`, while the reversed product has coordinates
ordered as `Fin D₂ × Fin D₁`, the right-hand side is transported by `productBondSwapEquiv`:
$$(U V)^\dagger = V^\dagger U^\dagger.$$

This is the local product-adjoint identity used when taking the dagger of the fusion equations
in the proof of Proposition `prop:zetas` of arXiv:2502.20257, lines 1662--1677. -/
theorem physicalAdjointTensor_mulTensor {D₁ D₂ : ℕ}
    (U : MPOTensor d D₁) (V : MPOTensor d D₂) :
    physicalAdjointTensor (mulTensor U V) =
      reindexBond (productBondSwapEquiv D₁ D₂)
        (mulTensor (physicalAdjointTensor V) (physicalAdjointTensor U)) := by
  classical
  ext i k x y
  simp only [physicalAdjointTensor_apply, mulTensor_apply, reindexBond_apply,
    Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply]
  rcases hx : finProdFinEquiv.symm x with ⟨x₁, x₂⟩
  rcases hy : finProdFinEquiv.symm y with ⟨y₁, y₂⟩
  simp only [productBondSwapEquiv, Equiv.trans_apply, Equiv.prodComm_apply,
    Equiv.symm_apply_apply, hx, hy, Prod.swap_prod_mk]
  calc
    star (∑ j, U k j x₁ y₁ * V j i x₂ y₂) =
        ∑ j, star (U k j x₁ y₁ * V j i x₂ y₂) := by
      exact star_sum Finset.univ _
    _ = ∑ j, star (V j i x₂ y₂) * star (U k j x₁ y₁) := by
      exact Finset.sum_congr rfl fun j _ ↦ star_mul _ _

/-- Physical slices of the physical adjoint are the conjugate transposes of the original
physical slices.  Only physical indices are transposed.

Source: arXiv:1606.00608, Appendix C.2, lines 1634--1689. -/
theorem physicalSlice_physicalAdjointTensor (K : MPOTensor d D) (β α : Fin D) :
    physicalSlice (physicalAdjointTensor K) β α = (physicalSlice K β α)ᴴ := by
  ext i j
  rfl

/-- Closed words of the physical adjoint are entrywise conjugates of the words with ket and
bra configurations exchanged. -/
theorem evalWord_physicalAdjointTensor (K : MPOTensor d D)
    (is js : List (Fin d)) (hlen : is.length = js.length) :
    evalWord (physicalAdjointTensor K) is js =
      (evalWord K js is).map (starRingEnd ℂ) := by
  induction is generalizing js with
  | nil =>
      simp only [List.length_nil, eq_comm, List.length_eq_zero_iff] at hlen
      subst js
      exact (starRingEnd ℂ).mapMatrix.map_one.symm
  | cons i is ih =>
      cases js with
      | nil => simp at hlen
      | cons j js =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          simp only [evalWord_cons, ih js hlen]
          exact ((starRingEnd ℂ).mapMatrix.map_mul (K j i) (evalWord K js is)).symm

/-- The physical adjoint generates the conjugate-transposed periodic operator family without
spatial reflection.

Source: arXiv:1606.00608, Appendix C.2, lines 1634--1689. -/
theorem mpo_physicalAdjointTensor (K : MPOTensor d D) (N : ℕ)
    (σ τ : Fin N → Fin d) :
    mpo (physicalAdjointTensor K) N σ τ = star (mpo K N τ σ) := by
  rw [mpo_apply, mpoMatrixEntry, evalWord_physicalAdjointTensor K _ _ (by simp),
    ← AddMonoidHom.map_trace (starRingEnd ℂ)]
  rfl

end MPOTensor
