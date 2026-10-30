/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.QuadraticPrescribedOBCWindow
import TNLean.MPS.Preparation.OBCCanonicalPhysicalRanks
import TNLean.MPS.MPU.PeriodicOperatorCutRank

/-!
# The quadratic solution for an arbitrary prescribed canonical OBC tensor

The source canonical equations force the original OBC bond dimensions
to be the actual physical cut ranks. The existing periodic cut-rank
bound then derives the squared-bond common bound. Changing that bound
retains the original bond spaces, site matrices and coefficient vector
definitionally. The quadratic supplier therefore applies to the original
prescribed canonical representation, with no supplied squared-bond bound,
canonical TI representative, nonzero-state premise or comparison gauge.

Only the source's row normalization, faithful density recursion and scalar
initial density are used from the OBC canonical conditions. Diagonality,
trace normalization and uniqueness need not be assumed separately.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal,
MPSarchive.tex lines 431--458, and the first clause of Theorem 8,
lines 1139--1169.
-/

open Matrix MPSPreparation OBCChainTensor
open scoped BigOperators ComplexOrder

namespace MPSTensor

variable {d D Q N L : ℕ} {A : MPSTensor d D}

/-- The common squared-bond bound of the original prescribed canonical
OBC representation is derived from its actual physical ranks and the
periodic TI representation. No OBC rank or bond bound is supplied.
Source: PGVWC07, lines 456--458 and 1139--1169. -/
theorem canonicalOBC_bondDim_le_of_mpv_eq (B : OBCChainTensor d Q N)
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef)
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (hcoeff : B.coeff = mpv A) (k : Fin (N + 1)) : B.bondDim k ≤ D * D := by
  rw [bondDim_eq_cutCoefficientRank_of_canonical B Λ hzero hstep hfaithful hrow k, hcoeff]
  exact MPUCircuit.cutCoefficientRank_mpv_le A (Nat.lt_succ_iff.mp k.isLt)

/-- The prescribed canonical tensor with only its derived common bound
changed. Its original rectangular tensors and coefficient sum are retained.
Source: PGVWC07, lines 456--458 and 1139--1169. -/
noncomputable def canonicalOBCWithSquaredBound (B : OBCChainTensor d Q N)
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef)
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (hcoeff : B.coeff = mpv A) : OBCChainTensor d (D * D) N :=
  B.withBondBound (canonicalOBC_bondDim_le_of_mpv_eq B Λ hzero hstep hfaithful hrow hcoeff)

/-- The original canonical OBC window in its derived doubled coordinates.
The common bound is proved internally, with all original sites retained.
Source: PGVWC07, the displayed window in lines 1139--1152. -/
noncomputable def quadraticCanonicalOBCWindow (hletter : ∃ i, A i ≠ 0)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d Q N)
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef)
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (hcoeff : B.coeff = mpv A) :
    Fin (D ^ 4) → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  quadraticPrescribedOBCWindow hletter hC1 hN
    (canonicalOBCWithSquaredBound B Λ hzero hstep hfaithful hrow hcoeff) hcoeff

/-- The reconstruction window retains the original supplied site entry
at every physical letter and both doubled virtual coordinates.
Source: PGVWC07, the original OBC window in lines 1139--1152. -/
theorem quadraticCanonicalOBCWindow_apply (hletter : ∃ i, A i ≠ 0)
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d Q N)
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef)
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (hcoeff : B.coeff = mpv A) (j : Fin (D ^ 4)) (i : Fin d)
    (a b : Fin D × Fin D) :
    quadraticCanonicalOBCWindow hletter hC1 hN B Λ hzero hstep hfaithful hrow hcoeff j i a b =
      B.tensor ⟨L + j.val, by have := j.isLt; omega⟩ i
        ((prescribedOBCWindowBondEquiv hletter hC1 hN
          (canonicalOBCWithSquaredBound B Λ hzero hstep hfaithful hrow hcoeff)
          hcoeff j.castSucc).symm a)
        ((prescribedOBCWindowBondEquiv hletter hC1 hN
          (canonicalOBCWithSquaredBound B Λ hzero hstep hfaithful hrow hcoeff)
          hcoeff j.succ).symm b) := rfl

/-- The actual prescribed canonical OBC representation has a quadratic
solution whenever its nonzero physical state admits the supplied C1 TI
representation. Nonvanishing, the Perron gauge, squared-bond bounds and
all window bond equalities are derived. No canonical TI hypothesis or
positive C1 length is added.
Source: PGVWC07, first clause of Theorem 8, MPSarchive.tex lines 1139--1169. -/
theorem exists_quadraticSolution_canonicalOBCWindow
    (hC1 : Kraus.IsNBlkInjective A L) (hN : 2 * L + D ^ 4 < N)
    (B : OBCChainTensor d Q N)
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef)
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (hcoeff : B.coeff = mpv A) :
    ∃ hletter : ∃ i, A i ≠ 0, Nonempty (QuadraticReconstructionSolution
      (quadraticCanonicalOBCWindow hletter hC1 hN B Λ hzero hstep hfaithful hrow hcoeff)) := by
  classical
  have hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0 := by
    by_contra h
    push_neg at h
    apply coeff_ne_zero_of_faithful_density B Λ hzero hstep hfaithful
    rw [hcoeff]
    exact funext h
  obtain ⟨hletter, hsolution⟩ := exists_quadraticSolution_prescribedOBCWindow_of_mpv_ne_zero
    hC1 hN (canonicalOBCWithSquaredBound B Λ hzero hstep hfaithful hrow hcoeff)
    hcoeff hnonzero
  exact ⟨hletter, hsolution⟩

end MPSTensor
