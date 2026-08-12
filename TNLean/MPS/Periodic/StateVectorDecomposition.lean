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

This file formalizes a normalized form of the state-vector conclusion in
PGVWC07, Theorem 5. A period-\(p\) irreducible translation-invariant tensor has
cyclic projectors. Each starting projector gives a site-dependent
\(p\)-periodic chain of the same bond dimension, and the original fixed-length
coefficient is the sum of the component coefficients. If the ring length is
not divisible by \(p\), all component coefficients vanish.

The source counts the \(p\) peripheral eigenvalues of the one-block canonical
transfer operator. The maintained surface here is `IsPeriodic p A`: it records
irreducibility, left-canonical normalization, positivity of \(p\), and an exact
\(p\)-th-root peripheral spectrum. The theorem
claims only equality of fixed-length state vectors and does not identify the
underlying tensors.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 5, lines 849--880.
-/

open scoped Matrix BigOperators
open Matrix Finset

namespace MPSChainTensor

variable {d D p N : ℕ}

/-- Repeat a \(p\)-site pattern around a chain of length \(N\).

Site \(j\) uses the pattern entry represented additively by
`j.val • (1 : Fin p)`. -/
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

/-- The \(p\)-site projector pattern starting in cyclic sector \(u\).

Its local matrix is the PGVWC07 component
\(Q_{u+k} A^i Q_{u+k+1}\) and retains the original bond dimension \(D\). -/
def projectorComponentPattern (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (u : Fin p) : MPSChainTensor d D p :=
  fun k i => cornerLetter Q A (u + k) i

/-- Repeat one cyclic-projector component pattern around an \(N\)-site ring. -/
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
private theorem projectorComponentChain_eval
    (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (hQproj : ∀ k, IsOrthogonalProjection (Q k))
    (u : Fin p) (σ : Fin (N + 1) → Fin d) :
    MPSChainTensor.eval (projectorComponentChain Q A u (N + 1)) σ =
      cornerProd Q A u (List.ofFn σ) := by
  induction N generalizing u with
  | zero =>
      rw [MPSChainTensor.eval_succ]
      simp [projectorComponentChain, projectorComponentPattern,
        MPSChainTensor.repeatPeriodPattern, cornerProd, cornerLetter]
  | succ n ih =>
      rw [MPSChainTensor.eval_succ, List.ofFn_succ, cornerProd_cons]
      have hzero :
          projectorComponentChain Q A u (n + 1 + 1) 0 =
            projectorComponentPattern Q A u 0 := by
        rfl
      have htail :
          (fun k : Fin (n + 1) =>
            projectorComponentChain Q A u (n + 1 + 1) k.succ) =
              projectorComponentChain Q A (u + 1) (n + 1) := by
        funext k i
        simp only [projectorComponentChain_apply]
        congr 1
        simp only [Fin.val_succ, add_nsmul, one_smul]
        abel
      rw [hzero, htail, ih (u + 1) (fun k => σ k.succ)]
      simp only [projectorComponentPattern, cornerLetter, add_zero, Matrix.mul_assoc]
      rw [corner_mul_cornerProd Q A (u + 1) _ (hQproj (u + 1))]

/-- The paper-oriented cyclic shift transports an entire word from its starting
projector to its ending projector. -/
private theorem projector_mul_evalWord_eq_evalWord_mul_projector
    (Q : Fin p → MatrixAlg D) (A : MPSTensor d D)
    (hshift : ∀ k i, Q k * A i = A i * Q (k + 1))
    (u : Fin p) (w : List (Fin d)) :
    Q u * evalWord A w = evalWord A w * Q (u + w.length • (1 : Fin p)) := by
  induction w generalizing u with
  | nil => simp
  | cons i w ih =>
      simp only [evalWord_cons, List.length_cons, add_smul, one_smul]
      rw [← Matrix.mul_assoc, hshift u i, Matrix.mul_assoc, ih (u + 1)]
      have hindex :
          u + 1 + w.length • (1 : Fin p) =
            u + (w.length + 1) • (1 : Fin p) := by
        rw [add_nsmul, one_nsmul]
        abel
      rw [hindex]
      have hindex' :
          u + (w.length + 1) • (1 : Fin p) =
            u + (w.length • (1 : Fin p) + 1) := by
        rw [add_nsmul, one_nsmul]
      rw [Matrix.mul_assoc, hindex']

/-- Under the cyclic shift, the corner product is simply the word product with
its starting projector inserted on the left. -/
private theorem cornerProd_eq_projector_mul_evalWord
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
      rw [Matrix.mul_assoc, (hQproj _).2]
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
    intro hzero
    apply hN
    have hnsmul_val : ∀ t : ℕ, ((t • (1 : Fin p)) : Fin p).val = t % p := by
      intro t
      induction t with
      | zero => simp
      | succ k ih => rw [succ_nsmul, Fin.val_add, ih]; simp
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hval := congrArg Fin.val hzero
    simpa only [hnsmul_val, Fin.val_zero] using hval
  have hne : u + (n + 1) • (1 : Fin p) ≠ u := by
    intro h
    exact hstep (add_left_cancel (h.trans (add_zero u).symm))
  simp only [List.length_ofFn]
  rw [Matrix.trace_mul_cycle]
  rw [orthogonalProjection_mul_eq_zero_of_sum_eq_one Q hQproj hQsum hne, zero_mul,
    Matrix.trace_zero]

end Components

section IsPeriodic

/-- A periodic tensor supplies the inverse-reindexed cyclic projectors in the
orientation used by PGVWC07, Theorem 5:
`Q_k A^i = A^i Q_{k+1}`.

The projectors act on the original \(D\)-dimensional virtual space; no
bond-dimension compression occurs. -/
theorem exists_paper_cyclic_projectors_of_isPeriodic
    (A : MPSTensor d D) (hA : IsPeriodic p A) :
    let _ : NeZero p := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ Q : Fin p → MatrixAlg D,
      (∀ k, IsOrthogonalProjection (Q k)) ∧
      (∑ k, Q k = 1) ∧
      (∀ k i, Q k * A i = A i * Q (k + 1)) := by
  letI : NeZero D := ⟨hA.bondDim_ne_zero⟩
  letI : NeZero p := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨_dim, _blocks, P, _φ, _V, _hLC, _hMPV, hPproj, hPsum, hCyclic,
    _hComm, _hTrace, _hIntertwine, _hMul, _hStar, _hNondeg, _hLetter,
    _hV_iso, _hV_range, _hEmbed⟩ :=
    exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic A hA
  have hCyclic' :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k := by
    intro k
    simpa [cyclicNextOfPos, Fin.add_def] using hCyclic k
  let Q : Fin p → MatrixAlg D := fun k => P (-k)
  refine ⟨Q, fun k => hPproj (-k), ?_, ?_⟩
  · change (∑ k, P (-k)) = 1
    (convert (Equiv.sum_comp (Equiv.neg (Fin p)) P).trans hPsum using 1; rfl)
  · intro k i
    exact negReindex_paper_shift A hA.leftCanonical hPproj hCyclic' k i

/-- **PGVWC07 Theorem 5, periodic branch.**

If \(p\mid N\), a period-\(p\) tensor generates at length \(N\) the sum of
\(p\) explicit \(p\)-periodic component chains. Component \(u\) has local
matrices \(Q_{u+j} A^i Q_{u+j+1}\), uses the original bond dimension \(D\), and
closes its virtual sector after \(N\) sites.

The source phrases the hypothesis as a one-block canonical transfer operator
with \(p\) peripheral eigenvalues. Here `IsPeriodic p A` is the maintained
normalized surface: it states irreducibility, left-canonical form, positive
period, and peripheral spectrum equal to the \(p\)-th roots of unity.
Only the fixed-length state-vector equality is asserted.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 5, lines 849--880. -/
theorem pgvwc07_periodic_stateVector_decomposition_of_dvd
    (A : MPSTensor d D) (hA : IsPeriodic p A)
    {N : ℕ} (hN : 0 < N) (hdiv : p ∣ N) :
    let _ : NeZero p := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ Q : Fin p → MatrixAlg D,
      (∀ k, IsOrthogonalProjection (Q k)) ∧
      (∑ k, Q k = 1) ∧
      (∀ k i, Q k * A i = A i * Q (k + 1)) ∧
      (∀ (u : Fin p) (j : Fin N) (i : Fin d),
        projectorComponentChain Q A u N j i =
          Q (u + j.val • (1 : Fin p)) * A i *
            Q (u + j.val • (1 : Fin p) + 1)) ∧
      (∀ u : Fin p, u + N • (1 : Fin p) = u) ∧
      (∀ σ : Fin N → Fin d,
        mpv A σ = ∑ u : Fin p,
          MPSChainTensor.coeff (projectorComponentChain Q A u N) σ) := by
  letI : NeZero p := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨Q, hQproj, hQsum, hshift⟩ := exists_paper_cyclic_projectors_of_isPeriodic A hA
  refine ⟨Q, hQproj, hQsum, hshift, ?_, ?_, ?_⟩
  · intro u j i
    rfl
  · obtain ⟨k, rfl⟩ := hdiv
    intro u
    have hpzero : p • (1 : Fin p) = 0 := by
      simpa only [Fintype.card_fin] using
        (card_nsmul_eq_zero (x := (1 : Fin p)))
    have hcycle : (p * k) • (1 : Fin p) = 0 := by
      calc
        (p * k) • (1 : Fin p) = k • (p • (1 : Fin p)) := by
          rw [mul_comm, mul_nsmul']
        _ = k • 0 := by rw [hpzero]
        _ = 0 := nsmul_zero k
    rw [hcycle, add_zero]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    exact mpv_eq_sum_projectorComponentChain_coeff Q A hQproj hQsum hshift

/-- **PGVWC07 Theorem 5, vanishing branch.**

If the period does not divide the ring length, every explicit cyclic-projector
component has zero coefficient, and therefore the original fixed-length state
vector is zero.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 5, lines 849--880. -/
theorem pgvwc07_stateVector_eq_zero_of_not_dvd
    (A : MPSTensor d D) (hA : IsPeriodic p A)
    {N : ℕ} (hN : ¬p ∣ N) :
    ∀ σ : Fin N → Fin d, mpv A σ = 0 := by
  letI : NeZero p := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨Q, hQproj, hQsum, hshift⟩ := exists_paper_cyclic_projectors_of_isPeriodic A hA
  have hNpos : 0 < N := by
    by_contra h
    have : N = 0 := Nat.eq_zero_of_not_pos h
    exact hN (this ▸ dvd_zero p)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
  intro σ
  rw [mpv_eq_sum_projectorComponentChain_coeff Q A hQproj hQsum hshift]
  exact Finset.sum_eq_zero fun u _ =>
    projectorComponentChain_coeff_eq_zero_of_not_dvd
      Q A hQproj hQsum hshift hN u σ

end IsPeriodic

end MPSTensor
