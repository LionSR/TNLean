/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Trace
import TNLean.MPS.MPDO.Defs

/-!
# First-site actions on matrix product density operators

This file defines multiplication of an MPO tensor or density operator on its
first physical site.  These identities are common to the invariant-projection
and sector-trace arguments and require no canonical-form hypotheses.

## Main definitions

* `MPOTensor.ketLeftMul` and `MPOTensor.braRightMul`: multiplication on the two
  physical legs of a vertically viewed MPO tensor.
* `MPOTensor.firstSiteMatrix`: a one-site matrix acting on the first site of a chain.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1874--1902.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- The vertically viewed product $P\widetilde M$.  Viewing the MPO tensor as
the family of physical-space operators $(\widetilde M_{ab})_{ij}=M^{ij}_{ab}$
indexed by the virtual indices, multiply each operator by `P` on the left:
$(P\widetilde M)^{ij}=\sum_kP_{ik}M^{kj}$.

The invariant-projection step in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1874--1887, considers an orthogonal projector $P$ with
$P\widetilde M=P\widetilde M P$ in this sense. -/
noncomputable def ketLeftMul (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ) :
    MPOTensor d D :=
  fun i j => ∑ k : Fin d, P i k • M k j

/-- The vertically viewed product $\widetilde M P$: multiply each
physical-space operator $\widetilde M_{ab}$ by `P` on the right,
$(\widetilde M P)^{ij}=\sum_kP_{kj}M^{ik}$.

Together with `ketLeftMul` this expresses the hypothesis
$P\widetilde M=P\widetilde M P$ in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1874--1887. -/
noncomputable def braRightMul (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ) :
    MPOTensor d D :=
  fun i j => ∑ k : Fin d, P k j • M i k

/-- Splitting off the first site of a density-operator entry:
$H^{(N+1)}_{(i,\sigma),(j,\tau)}
=\tr(M^{ij}M^{\sigma_0\tau_0}\cdots M^{\sigma_{N-1}\tau_{N-1}})$. -/
theorem mpo_cons_cons (M : MPOTensor d D) {N : ℕ} (i j : Fin d)
    (σ τ : Fin N → Fin d) :
    mpo M (N + 1) (Fin.cons i σ) (Fin.cons j τ) =
      Matrix.trace (M i j * evalWord M (List.ofFn σ) (List.ofFn τ)) := by
  simp only [mpo_apply, mpoMatrixEntry]
  congr 1
  rw [List.ofFn_succ, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, evalWord_cons]

/-- The one-site matrix `P` acting on the first spin of an $(N+1)$-site chain,
$P_1=P\otimes\Id^{\otimes N}$.  The products $P_1H^{(N+1)}$,
$P_1H^{(N+1)}P_1$, and $H^{(N+1)}P_1$ in the displayed chain
eq1:proof.IV.12 of arXiv:1606.00608, lines 1874--1887, are formed with this
operator. -/
noncomputable def firstSiteMatrix (P : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin (N + 1) → Fin d) (Fin (N + 1) → Fin d) ℂ :=
  fun σ τ => P (σ 0) (τ 0) * (if σ ∘ Fin.succ = τ ∘ Fin.succ then 1 else 0)

/-- Acting by the identity on the first site gives the identity on the full
chain. -/
@[simp] theorem firstSiteMatrix_one (N : ℕ) :
    firstSiteMatrix (1 : Matrix (Fin d) (Fin d) ℂ) N = 1 := by
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    simp [firstSiteMatrix]
  · have hne : σ 0 ≠ τ 0 ∨ σ ∘ Fin.succ ≠ τ ∘ Fin.succ := by
      by_contra h
      push Not at h
      apply hστ
      funext i
      refine Fin.cases h.1 (fun j ↦ ?_) i
      exact congrFun h.2 j
    rcases hne with hhead | htail
    · simp [firstSiteMatrix, hστ, hhead]
    · simp [firstSiteMatrix, Matrix.one_apply, hστ, htail]

/-- The first-spin action of a Hermitian matrix is Hermitian. -/
theorem firstSiteMatrix_isHermitian {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.IsHermitian) (N : ℕ) : (firstSiteMatrix P N).IsHermitian := by
  refine Matrix.ext fun σ τ => ?_
  simp only [Matrix.conjTranspose_apply, firstSiteMatrix]
  by_cases h : σ ∘ Fin.succ = τ ∘ Fin.succ
  · rw [if_pos h, if_pos h.symm, mul_one, mul_one]
    exact hP.apply _ _
  · rw [if_neg h, if_neg fun hh => h hh.symm, mul_zero, mul_zero, star_zero]

/-- Reindex a sum over an $(N+1)$-site configuration by its first value and
its remaining $N$ values. -/
theorem sum_fin_succ_eq_sum_cons {β : Type*} [AddCommMonoid β] {N : ℕ}
    (F : (Fin (N + 1) → Fin d) → β) :
    ∑ σ : Fin (N + 1) → Fin d, F σ =
      ∑ i : Fin d, ∑ ρ : Fin N → Fin d, F (Fin.cons i ρ) := by
  rw [← Fintype.sum_prod_type']
  exact ((Fin.consEquiv fun _ : Fin (N + 1) => Fin d).sum_comp F).symm

/-- Left multiplication by the first-spin action, entrywise:
$(P_1G)_{\sigma\tau}=\sum_iP_{\sigma_0i}G_{(i,\sigma'),\tau}$, where
$\sigma'$ is the tail of $\sigma$. -/
theorem firstSiteMatrix_mul_apply (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ}
    (G : Matrix (Fin (N + 1) → Fin d) (Fin (N + 1) → Fin d) ℂ)
    (σ τ : Fin (N + 1) → Fin d) :
    (firstSiteMatrix P N * G) σ τ =
      ∑ i : Fin d, P (σ 0) i * G (Fin.cons i (σ ∘ Fin.succ)) τ := by
  rw [Matrix.mul_apply, sum_fin_succ_eq_sum_cons]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [firstSiteMatrix, Fin.cons_zero, Function.comp_def, Fin.cons_succ]
  rw [Fintype.sum_eq_single (fun n : Fin N => σ (Fin.succ n))]
  · rw [if_pos rfl, mul_one]
  · intro ρ hρ
    rw [if_neg fun hh => hρ hh.symm, mul_zero, zero_mul]

/-- Right multiplication by the first-spin action, entrywise:
$(GP_1)_{\sigma\tau}=\sum_jG_{\sigma,(j,\tau')}P_{j\tau_0}$, where
$\tau'$ is the tail of $\tau$. -/
theorem mul_firstSiteMatrix_apply (P : Matrix (Fin d) (Fin d) ℂ) {N : ℕ}
    (G : Matrix (Fin (N + 1) → Fin d) (Fin (N + 1) → Fin d) ℂ)
    (σ τ : Fin (N + 1) → Fin d) :
    (G * firstSiteMatrix P N) σ τ =
      ∑ j : Fin d, G σ (Fin.cons j (τ ∘ Fin.succ)) * P j (τ 0) := by
  rw [Matrix.mul_apply, sum_fin_succ_eq_sum_cons]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [firstSiteMatrix, Fin.cons_zero, Function.comp_def, Fin.cons_succ]
  rw [Fintype.sum_eq_single (fun n : Fin N => τ (Fin.succ n))]
  · rw [if_pos rfl, mul_one]
  · intro ρ hρ
    rw [if_neg hρ, mul_zero, mul_zero]

/-- First-site actions compose site by site:
$P_1Q_1 = (PQ)_1$ on an $(N+1)$-site chain. -/
theorem firstSiteMatrix_mul_firstSiteMatrix
    (P Q : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    firstSiteMatrix P N * firstSiteMatrix Q N = firstSiteMatrix (P * Q) N := by
  refine Matrix.ext fun σ τ => ?_
  rw [firstSiteMatrix_mul_apply]
  have hcons : ∀ i : Fin d,
      (Fin.cons i (σ ∘ Fin.succ) : Fin (N + 1) → Fin d) ∘ Fin.succ =
        σ ∘ Fin.succ := by
    intro i
    funext n
    simp [Fin.cons_succ]
  by_cases hcond : σ ∘ Fin.succ = τ ∘ Fin.succ
  · simp only [firstSiteMatrix, Fin.cons_zero, hcons, if_pos hcond, mul_one,
      Matrix.mul_apply]
  · simp only [firstSiteMatrix, Fin.cons_zero, hcons, if_neg hcond, mul_zero,
      Finset.sum_const_zero]

/-- Move a finite scalar-weighted sum inside a trace pairing. -/
theorem sum_mul_trace_eq_trace_sum_smul (c : Fin d → ℂ)
    (B : Fin d → Matrix (Fin D) (Fin D) ℂ) (W : Matrix (Fin D) (Fin D) ℂ) :
    ∑ i : Fin d, c i * Matrix.trace (B i * W) =
      Matrix.trace ((∑ i : Fin d, c i • B i) * W) := by
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end MPOTensor
