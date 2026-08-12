/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.Periodic.Overlap.SelfOverlapSetup
import TNLean.MPS.Periodic.SectorIrreducibility.ProjectionOrtho
import TNLean.MPS.Periodic.SectorLift

/-!
# Fixed-length state-vector decomposition of a periodic MPS

This file formalizes the state-vector conclusion of PGVWC07, Theorem 5.  A
period-`p` irreducible translation-invariant tensor has cyclic projectors.  Each
choice of starting projector gives a site-dependent `p`-periodic chain of the
same bond dimension, and the original fixed-length coefficient is the sum of
the component coefficients.  If the ring length is not divisible by `p`, all
component coefficients vanish.

The source counts the `p` peripheral eigenvalues of the one-block canonical
transfer operator.  The maintained equivalent surface here is `IsPeriodic p A`:
it records irreducibility, left-canonical normalization, positivity of `p`, and
that the peripheral spectrum is exactly the `p`-th roots of unity.  The theorem
claims only equality of fixed-length state vectors and does not identify the
underlying tensors.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 5, lines 849--880.
-/

open scoped Matrix BigOperators
open Matrix Finset

namespace MPSChainTensor

variable {d D p N : ℕ}

/-- Repeat a `p`-site pattern around a chain of length `N`.

The site `j` uses pattern entry `j mod p`, represented additively as
`j.val • 1 : Fin p`. -/
def repeatPeriodPattern [NeZero p] (B : MPSChainTensor d D p) (N : ℕ) :
    MPSChainTensor d D N :=
  fun j => B (j.val • (1 : Fin p))

@[simp]
theorem repeatPeriodPattern_apply [NeZero p]
    (B : MPSChainTensor d D p) (j : Fin N) :
    repeatPeriodPattern B N j = B (j.val • (1 : Fin p)) :=
  rfl

end MPSChainTensor

namespace MPSTensor

variable {d D p N : ℕ}

section Components

variable [NeZero p]

/-- The `p`-site projector pattern starting in cyclic sector `u`.

Its local matrix is the PGVWC07 component
`Q_{u+k} A^i Q_{u+k+1}` and retains the original bond dimension `D`. -/
def projectorComponentPattern (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin p) : MPSChainTensor d D p :=
  fun k i => cornerLetter Q A (u + k) i

/-- Repeat one cyclic-projector component pattern around an `N`-site ring. -/
def projectorComponentChain (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin p) (N : ℕ) : MPSChainTensor d D N :=
  MPSChainTensor.repeatPeriodPattern (projectorComponentPattern Q A u) N

@[simp]
theorem projectorComponentChain_apply
    (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin p) (j : Fin N) (i : Fin d) :
    projectorComponentChain Q A u N j i =
      cornerLetter Q A (u + j.val • (1 : Fin p)) i :=
  rfl

/-- A nonempty projector-component chain evaluates to the corresponding cyclic
corner product. -/
theorem projectorComponentChain_eval
    (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (hQproj : ∀ k, IsOrthogonalProjection (Q k))
    (u : Fin p) (σ : Fin (N + 1) → Fin d) :
    MPSChainTensor.eval (projectorComponentChain Q A u (N + 1)) σ =
      cornerProd Q A u (List.ofFn σ) := by
  induction N generalizing u with
  | zero =>
      simp [MPSChainTensor.eval, projectorComponentChain, projectorComponentPattern,
        MPSChainTensor.repeatPeriodPattern, cornerProd_single]
  | succ n ih =>
      rw [MPSChainTensor.eval_succ, List.ofFn_succ, cornerProd_cons]
      change
        cornerLetter Q A u (σ 0) *
            MPSChainTensor.eval (projectorComponentChain Q A (u + 1) (n + 1))
              (σ ∘ Fin.succ) =
          Q u * A (σ 0) * cornerProd Q A (u + 1) (List.ofFn (σ ∘ Fin.succ))
      rw [ih (u + 1) (σ ∘ Fin.succ)]
      simp only [cornerLetter, Matrix.mul_assoc,
        corner_mul_cornerProd Q A (u + 1) _ (hQproj (u + 1))]

/-- The paper-oriented cyclic shift transports an entire word from its starting
projector to its ending projector. -/
theorem projector_mul_evalWord_eq_evalWord_mul_projector
    (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (hshift : ∀ k i, Q k * A i = A i * Q (k + 1))
    (u : Fin p) (w : List (Fin d)) :
    Q u * evalWord A w = evalWord A w * Q (u + w.length • (1 : Fin p)) := by
  induction w generalizing u with
  | nil => simp
  | cons i w ih =>
      simp only [evalWord_cons, List.length_cons, add_smul, one_smul]
      rw [← Matrix.mul_assoc, hshift u i, Matrix.mul_assoc, ih (u + 1)]
      congr 2
      abel

/-- Under the cyclic shift, the corner product is simply the word product with
its starting projector inserted on the left. -/
theorem cornerProd_eq_projector_mul_evalWord
    (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (hQproj : ∀ k, IsOrthogonalProjection (Q k))
    (hshift : ∀ k i, Q k * A i = A i * Q (k + 1))
    (u : Fin p) (w : List (Fin d)) :
    cornerProd Q A u w = Q u * evalWord A w := by
  rw [cornerProd_eq_conj_evalWord Q A hQproj hshift]
  have htransport := projector_mul_evalWord_eq_evalWord_mul_projector Q A hshift u w
  calc
    Q u * evalWord A w * Q (u + w.length • (1 : Fin p)) =
        evalWord A w * Q (u + w.length • (1 : Fin p)) *
          Q (u + w.length • (1 : Fin p)) := by rw [htransport]
    _ = evalWord A w * Q (u + w.length • (1 : Fin p)) := by
      rw [(hQproj _).2]
    _ = Q u * evalWord A w := htransport.symm

/-- At every positive length, inserting the cyclic resolution of the identity
splits an MPS coefficient into the sum of the explicit projector-component
chain coefficients. -/
theorem mpv_eq_sum_projectorComponentChain_coeff
    (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (hQproj : ∀ k, IsOrthogonalProjection (Q k))
    (hQsum : ∑ k, Q k = 1)
    (hshift : ∀ k i, Q k * A i = A i * Q (k + 1))
    (σ : Fin (N + 1) → Fin d) :
    mpv A σ =
      ∑ u : Fin p, MPSChainTensor.coeff
        (projectorComponentChain Q A u (N + 1)) σ := by
  simp only [mpv, coeff, MPSChainTensor.coeff, projectorComponentChain_eval Q A hQproj,
    cornerProd_eq_projector_mul_evalWord Q A hQproj hshift]
  calc
    (evalWord A (List.ofFn σ)).trace =
        ((∑ u : Fin p, Q u) * evalWord A (List.ofFn σ)).trace := by rw [hQsum, one_mul]
    _ = ∑ u : Fin p, (Q u * evalWord A (List.ofFn σ)).trace := by
      rw [Finset.sum_mul, Matrix.trace_sum]

/-- If the chain length does not close the cyclic sector, every component
coefficient vanishes by projector orthogonality. -/
theorem projectorComponentChain_coeff_eq_zero_of_not_dvd
    (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (hQproj : ∀ k, IsOrthogonalProjection (Q k))
    (hQsum : ∑ k, Q k = 1)
    (hshift : ∀ k i, Q k * A i = A i * Q (k + 1))
    {N : ℕ} (hN : ¬p ∣ N) (u : Fin p) (σ : Fin N → Fin d) :
    MPSChainTensor.coeff (projectorComponentChain Q A u N) σ = 0 := by
  have hNpos : 0 < N := by
    by_contra h
    have : N = 0 := Nat.eq_zero_of_not_pos h
    exact hN (this ▸ dvd_zero p)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
  rw [MPSChainTensor.coeff, projectorComponentChain_eval Q A hQproj,
    cornerProd_eq_conj_evalWord Q A hQproj hshift]
  have hstep : ((n + 1) • (1 : Fin p)) ≠ 0 := by
    simpa only [← Nat.cast_eq_nsmul_one, Fin.natCast_eq_zero] using hN
  have hne : u + (n + 1) • (1 : Fin p) ≠ u := by
    intro h
    exact hstep (add_left_cancel h)
  rw [Matrix.trace_mul_cycle]
  rw [orthogonalProjection_mul_eq_zero_of_sum_eq_one Q hQproj hQsum hne, zero_mul,
    Matrix.trace_zero]

end Components

end MPSTensor
