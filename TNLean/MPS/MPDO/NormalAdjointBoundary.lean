/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ReductionExistence
import TNLean.MPS.MPDO.BondSimilarity
import TNLean.MPS.MPDO.Boundary
import TNLean.MPS.MPDO.PhysicalAdjoint

/-!
# Arbitrary-boundary adjoints from normal periodic dual blocks

Suppose every block has positive bond dimension and is normal, and an
involution on its labels realizes the physical adjoint at every positive
periodic length. Two applications of the normal-target reduction theorem
identify the dual bond dimensions. The resulting square reduction is an exact
similarity, which transports arbitrary boundaries at every length.

The periodic adjoint identity is an explicit physical star-representation
hypothesis. Neither algebraic multiplication of boundary operators nor the
existence of fusion tensors supplies it. The transported boundary uses
entrywise complex conjugation, without transposing its virtual indices.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `algcond` and Appendix A:
  this is a sufficient criterion for the additional adjoint-closure property,
  not a derivation of a physical star representation from `algcond`.
* Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Proposition 20:
  the normal-target rectangular reduction theorem used below.
-/

open scoped Matrix

namespace MPOTensor

variable {d D E : ℕ}

/-- Adjunction of a boundary-weighted operator conjugates the boundary
entrywise and takes the physical adjoint of the tensor. Virtual order is
unchanged. This identity includes the empty chain. -/
theorem conjTranspose_mpoWithBoundary (A : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) :
    (mpoWithBoundary A X N)ᴴ =
      mpoWithBoundary (physicalAdjointTensor A) (X.map (starRingEnd ℂ)) N := by
  ext σ τ
  change star (Matrix.trace (X * evalWord A (List.ofFn τ) (List.ofFn σ))) =
    Matrix.trace (X.map (starRingEnd ℂ) *
      evalWord (physicalAdjointTensor A) (List.ofFn σ) (List.ofFn τ))
  rw [evalWord_physicalAdjointTensor A _ _ (by simp),
    ← Matrix.map_mul (f := starRingEnd ℂ), ← AddMonoidHom.map_trace (starRingEnd ℂ)]
  rfl

/-- A two-sided bond similarity moves from tensor letters to an arbitrary
boundary, independently of chain length. -/
theorem mpoWithBoundary_eq_of_conj {A : MPOTensor d D} {B : MPOTensor d E}
    {V : Matrix (Fin E) (Fin D) ℂ} {W : Matrix (Fin D) (Fin E) ℂ}
    (hVW : V * W = 1) (hWV : W * V = 1)
    (hletter : ∀ i j, V * A i j * W = B i j)
    (X : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) :
    mpoWithBoundary A X N = mpoWithBoundary B (V * X * W) N := by
  ext σ τ
  change Matrix.trace (X * evalWord A (List.ofFn σ) (List.ofFn τ)) =
    Matrix.trace ((V * X * W) * evalWord B (List.ofFn σ) (List.ofFn τ))
  rw [evalWord_eq_mul_mul_of_conj hVW hWV hletter]
  calc
    Matrix.trace (X * (W * evalWord B (List.ofFn σ) (List.ofFn τ) * V)) =
        Matrix.trace ((X * W * evalWord B (List.ofFn σ) (List.ofFn τ)) * V) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (V * (X * W * evalWord B (List.ofFn σ) (List.ofFn τ))) :=
      Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

variable {ι : Type*} {dim : ι → ℕ}

/-- A label dual realizes the physical adjoint at all positive periodic
lengths. This is a physical star-representation hypothesis, separate from
algebraic product closedness. -/
def IsPeriodicAdjointFamily (A : (a : ι) → MPOTensor d (dim a))
    (dual : ι → ι) : Prop :=
  ∀ (a : ι) (N : ℕ), 0 < N → mpo (A (dual a)) N = (mpo (A a) N)ᴴ

namespace IsPeriodicAdjointFamily

variable {A : (a : ι) → MPOTensor d (dim a)} {dual : ι → ι}

/-- Periodic physical adjoint equality is positive-length MPV equality for
the flattened physical-adjoint and dual tensors. -/
theorem sameMPV₂Pos (h : IsPeriodicAdjointFamily A dual) (a : ι) :
    MPSTensor.SameMPV₂Pos (physicalAdjointTensor (A a)).toMPSTensor
      (A (dual a)).toMPSTensor := by
  intro N hN ρ
  let σ : Fin N → Fin d := fun n ↦ (ρ n).divNat
  let τ : Fin N → Fin d := fun n ↦ (ρ n).modNat
  have hρ : (fun n ↦ finProdFinEquiv (σ n, τ n)) = ρ := by
    funext n
    exact finProdFinEquiv.apply_symm_apply (ρ n)
  rw [← hρ]
  change Matrix.trace (Kraus.evalWord (physicalAdjointTensor (A a)).toMPSTensor
      (List.ofFn (fun n ↦ finProdFinEquiv (σ n, τ n)))) =
    Matrix.trace (Kraus.evalWord (A (dual a)).toMPSTensor
      (List.ofFn (fun n ↦ finProdFinEquiv (σ n, τ n))))
  rw [evalWord_toMPSTensor_pairConfig, evalWord_toMPSTensor_pairConfig]
  change mpo (physicalAdjointTensor (A a)) N σ τ = mpo (A (dual a)) N σ τ
  rw [mpo_physicalAdjointTensor, h a N hN]
  rfl

/-- Normal positive-dimensional dual blocks have equal bond dimensions.
The two inequalities come from normal-target reductions in opposite dual
directions; no one-site injectivity or canonical normalization is assumed. -/
theorem bondDim_dual (h : IsPeriodicAdjointFamily A dual)
    (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (A a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a) (a : ι) : dim a = dim (dual a) := by
  letI : ∀ a, NeZero (dim a) := fun a ↦ ⟨Nat.ne_of_gt (hDim a)⟩
  obtain ⟨V₁, W₁, h₁⟩ :=
    MPSTensor.exists_isReduction_of_isNormal_of_sameMPV₂Pos
      (A (dual a)).toMPSTensor (physicalAdjointTensor (A a)).toMPSTensor
      (hNormal (dual a)) (h.sameMPV₂Pos a)
  obtain ⟨V₂, W₂, h₂⟩ :=
    MPSTensor.exists_isReduction_of_isNormal_of_sameMPV₂Pos
      (A (dual (dual a))).toMPSTensor
      (physicalAdjointTensor (A (dual a))).toMPSTensor
      (hNormal (dual (dual a))) (h.sameMPV₂Pos (dual a))
  exact Nat.le_antisymm (by simpa only [hdual a] using h₂.bondDim_le) h₁.bondDim_le

/-- The normal-target reduction becomes a two-sided similarity. It gives
both the exact one-letter identity and the arbitrary-boundary adjoint
formula, with the same matrices at every length, including zero.

The boundary is \(V_a\overline XW_a\); its conjugation is entrywise rather
than the virtual conjugate transpose. -/
theorem exists_boundaryGauge (h : IsPeriodicAdjointFamily A dual)
    (hdual : Function.Involutive dual)
    (hNormal : ∀ a, Kraus.IsNormal (A a).toMPSTensor)
    (hDim : ∀ a, 0 < dim a) (a : ι) :
    ∃ (V : Matrix (Fin (dim (dual a))) (Fin (dim a)) ℂ)
      (W : Matrix (Fin (dim a)) (Fin (dim (dual a))) ℂ),
      V * W = 1 ∧ W * V = 1 ∧
      (∀ i j, physicalAdjointTensor (A a) i j = W * A (dual a) i j * V) ∧
      ∀ (X : Matrix (Fin (dim a)) (Fin (dim a)) ℂ) (N : ℕ),
        (mpoWithBoundary (A a) X N)ᴴ =
          mpoWithBoundary (A (dual a)) (V * X.map (starRingEnd ℂ) * W) N := by
  letI : NeZero (dim (dual a)) := ⟨Nat.ne_of_gt (hDim (dual a))⟩
  obtain ⟨V, W, hred⟩ :=
    MPSTensor.exists_isReduction_of_isNormal_of_sameMPV₂Pos
      (A (dual a)).toMPSTensor (physicalAdjointTensor (A a)).toMPSTensor
      (hNormal (dual a)) (h.sameMPV₂Pos a)
  have hWV : W * V = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv
      (finCongr (h.bondDim_dual hdual hNormal hDim a).symm)).mp hred.mul_eq_one
  have hletter (i j : Fin d) :
      V * physicalAdjointTensor (A a) i j * W = A (dual a) i j := by
    simpa [toMPSTensor] using hred.evalWord [finProdFinEquiv (i, j)]
  refine ⟨V, W, hred.mul_eq_one, hWV, ?_, ?_⟩
  · intro i j
    rw [← hletter i j]
    simp only [Matrix.mul_assoc, hWV, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hWV, Matrix.one_mul]
  · intro X N
    rw [conjTranspose_mpoWithBoundary]
    exact mpoWithBoundary_eq_of_conj hred.mul_eq_one hWV hletter _ N

end IsPeriodicAdjointFamily

end MPOTensor
