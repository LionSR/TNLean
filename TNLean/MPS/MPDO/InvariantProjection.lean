/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.VerticalCF

/-!
# One-sided invariant matrices for matrix product density operators

This file formalizes the first operator step in the proof of Proposition 4.13
of arXiv:1606.00608, lines 1874--1887.  If a Hermitian matrix $P$ satisfies
$P\widetilde M=P\widetilde M P$ on the vertically viewed tensor, positivity of
the density operators gives
$$
  P_1H^{(N+1)}=P_1H^{(N+1)}P_1=H^{(N+1)}P_1,
$$
where $P_1=P\otimes\Id^{\otimes N}$.  Lemma L then transfers these identities
to every horizontal canonical-form block, where they say
$(\Id-P)MP=0$.

The file also specializes the positive-semidefinite power-commutation theorem
to matrix product density operators.  This is only the final operator
implication in source lines 1888--1893.  The passage from a nontrivial vertical
period to an orthogonal projector $Q$ satisfying the required all-length
commutation identities remains open.

## Main definitions

* `ketLeftMul` and `braRightMul`: the vertically viewed products
  $P\widetilde M$ and $\widetilde M P$.
* `firstSiteMatrix`: the operator $P\otimes\Id^{\otimes N}$ on an
  $(N+1)$-site chain; these operators compose site by site,
  $P_1Q_1=(PQ)_1$.

## Main results

* `firstSiteMatrix_mul_mpo_of_ketLeftMul_invariant`: one-sided tensor
  invariance gives $P_1H^{(N+1)}=P_1H^{(N+1)}P_1$.
* `firstSiteMatrix_mul_mpo_comm`: positivity and Hermiticity give
  $P_1H^{(N+1)}=H^{(N+1)}P_1$.
* `blockwise_braRight_eq_ketLeftBraRight_of_invariant`: the blockwise form of
  $(\Id-P)MP=0$.
* `mpo_commute_of_commute_pow`: commutation with a nonzero power of an MPDO
  density operator implies commutation with that density operator.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13 and the auxiliary Lemma L in the appendix
-/

open scoped Matrix BigOperators ComplexOrder

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

/-- The letters of $P\widetilde M$ are the letters of $\widetilde M$
multiplied by `P` on the left.  This identifies the one-site action
`ketLeftMul` with left multiplication on the vertically viewed tensor of
arXiv:1606.00608, line 943. -/
theorem verticalTensor_ketLeftMul (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) (v : Fin (D * D)) :
    verticalTensor (M.ketLeftMul P) v = P * verticalTensor M v := by
  ext i j
  simp [verticalTensor, ketLeftMul, Matrix.mul_apply, Matrix.sum_apply]

/-- The letters of $\widetilde M P$ are the letters of $\widetilde M$
multiplied by `P` on the right.  This identifies the one-site action
`braRightMul` with right multiplication on the vertically viewed tensor of
arXiv:1606.00608, line 943. -/
theorem verticalTensor_braRightMul (M : MPOTensor d D)
    (P : Matrix (Fin d) (Fin d) ℂ) (v : Fin (D * D)) :
    verticalTensor (M.braRightMul P) v = verticalTensor M v * P := by
  ext i j
  simp [verticalTensor, braRightMul, Matrix.mul_apply, Matrix.sum_apply,
    mul_comm]

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
  rw [Finset.sum_eq_single (fun n : Fin N => σ (Fin.succ n))]
  · rw [if_pos rfl, mul_one]
  · intro ρ _ hρ
    rw [if_neg fun hh => hρ hh.symm, mul_zero, zero_mul]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

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
  rw [Finset.sum_eq_single (fun n : Fin N => τ (Fin.succ n))]
  · rw [if_pos rfl, mul_one]
  · intro ρ _ hρ
    rw [if_neg hρ, mul_zero, mul_zero]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

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

/-- If the vertically viewed tensor satisfies $P\widetilde M=P\widetilde M P$,
then for every tail length $N$ the density operator satisfies
$P_1H^{(N+1)}=P_1H^{(N+1)}P_1$, with $P_1$ acting on the first spin.

This is the first equality of the displayed chain eq1:proof.IV.12 in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1874--1887. -/
theorem firstSiteMatrix_mul_mpo_of_ketLeftMul_invariant
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (hPM : M.ketLeftMul P = (M.ketLeftMul P).braRightMul P) (N : ℕ) :
    firstSiteMatrix P N * mpo M (N + 1) =
      firstSiteMatrix P N * mpo M (N + 1) * firstSiteMatrix P N := by
  refine Matrix.ext fun σ τ => ?_
  obtain ⟨a, σ', rfl⟩ : ∃ a σ'', σ = Fin.cons a σ'' :=
    ⟨σ 0, Fin.tail σ, (Fin.cons_self_tail σ).symm⟩
  obtain ⟨b, τ', rfl⟩ : ∃ b τ'', τ = Fin.cons b τ'' :=
    ⟨τ 0, Fin.tail τ, (Fin.cons_self_tail τ).symm⟩
  have hPM' := congrFun (congrFun hPM a) b
  simp only [ketLeftMul, braRightMul] at hPM'
  rw [mul_firstSiteMatrix_apply]
  simp only [firstSiteMatrix_mul_apply]
  simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ, mpo_cons_cons]
  calc
    ∑ i : Fin d, P a i *
        Matrix.trace (M i b * evalWord M (List.ofFn σ') (List.ofFn τ'))
        = Matrix.trace ((∑ i : Fin d, P a i • M i b) *
            evalWord M (List.ofFn σ') (List.ofFn τ')) :=
          sum_mul_trace_eq_trace_sum_smul _ _ _
    _ = Matrix.trace ((∑ j : Fin d, P j b • ∑ i : Fin d, P a i • M i j) *
            evalWord M (List.ofFn σ') (List.ofFn τ')) := by rw [hPM']
    _ = ∑ j : Fin d, P j b *
          Matrix.trace ((∑ i : Fin d, P a i • M i j) *
            evalWord M (List.ofFn σ') (List.ofFn τ')) :=
          (sum_mul_trace_eq_trace_sum_smul _ _ _).symm
    _ = ∑ j : Fin d,
          (∑ i : Fin d, P a i *
            Matrix.trace (M i j * evalWord M (List.ofFn σ') (List.ofFn τ'))) *
            P j b := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [sum_mul_trace_eq_trace_sum_smul, mul_comm]

/-- For an MPDO satisfying $P\widetilde M=P\widetilde M P$ with $P$
Hermitian, the first-spin action $P_1$ commutes with the density operator at
every tail length $N$:
$P_1H^{(N+1)}=P_1H^{(N+1)}P_1=(P_1H^{(N+1)}P_1)^\dagger=H^{(N+1)}P_1$.

This is eq1:proof.IV.12 in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1874--1887.  The paper takes $P$ to be an orthogonal
projector; this implication uses only Hermiticity of $P$. -/
theorem firstSiteMatrix_mul_mpo_comm
    (M : MPOTensor d D) (hMpdo : IsMPDO M)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian)
    (hPM : M.ketLeftMul P = (M.ketLeftMul P).braRightMul P) (N : ℕ) :
    firstSiteMatrix P N * mpo M (N + 1) = mpo M (N + 1) * firstSiteMatrix P N := by
  have hInv := firstSiteMatrix_mul_mpo_of_ketLeftMul_invariant M P hPM N
  have hcorner := mpo_opposite_corner_eq_zero M hMpdo (N + 1) (firstSiteMatrix P N)
    (firstSiteMatrix_isHermitian hP N) hInv
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul] at hcorner
  rw [hInv]
  exact (sub_eq_zero.mp hcorner).symm

/-- Let the doubled-index tensor of an MPDO have a horizontal block-injective
canonical-form decomposition, and let $P$ be Hermitian with
$P\widetilde M=P\widetilde M P$.  On every canonical-form block, the
insertions of $\widetilde M P$ and $P\widetilde M P$ agree.  Equivalently,
$(\Id-P)MP=0$ blockwise.

This is the algebraic conclusion of the invariant-projection step in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1874--1887.  The source takes
$P$ to be an orthogonal projector and writes $P^\perp MP=0$; under the weaker
Hermiticity hypothesis used here, the precise expression is $(\Id-P)MP=0$. -/
theorem blockwise_braRight_eq_ketLeftBraRight_of_invariant
    {r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (M : MPOTensor d D) (hMpdo : IsMPDO M)
    (A : (k : Fin r) → MPSTensor (d * d) (dim k))
    (hCF : HorizontalCFData (d := d * d) μ A)
    (hM : MPSTensor.SameMPV₂ M.toMPSTensor
      (MPSTensor.toTensorFromBlocks (d := d * d) (μ := μ) A))
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian)
    (hPM : M.ketLeftMul P = (M.ketLeftMul P).braRightMul P) :
    ∀ k, MPSTensor.insertedTensor (MPSTensor.braRightAction P) (A k) =
      MPSTensor.insertedTensor (MPSTensor.ketLeftBraRightAction P) (A k) := by
  refine blockwise_opposite_insert_eq_of_rotated_mpo_entries M A hCF hM P ?_ ?_
  · intro N ρ
    have h := firstSiteMatrix_mul_mpo_of_ketLeftMul_invariant M P hPM N
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
    have h := firstSiteMatrix_mul_mpo_comm M hMpdo hP hPM N
    have h2 := Matrix.ext_iff.mpr h
      (Fin.cons (ρ 0).divNat fun n => (ρ (Fin.succ n)).divNat)
      (Fin.cons (ρ 0).modNat fun n => (ρ (Fin.succ n)).modNat)
    rw [mul_firstSiteMatrix_apply, firstSiteMatrix_mul_apply] at h2
    simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ] at h2
    exact h2

/-- For an MPDO, any matrix commuting with a nonzero power of the $N$-site
density operator commutes with the density operator itself.

This is the final operator implication in the contradiction at
arXiv:1606.00608, lines 1888--1893 (equation eq2:proof.IV.12).  It does not
construct the orthogonal projector $Q$ associated with a nontrivial vertical
period or establish its commutation with $[H^{(N)}]^p$ for every $N$; that
connection remains open. -/
theorem mpo_commute_of_commute_pow (M : MPOTensor d D) (hM : IsMPDO M) (N : ℕ)
    {p : ℕ} (hp : p ≠ 0) {Q : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hQ : Commute Q (mpo M N ^ p)) : Commute Q (mpo M N) :=
  Matrix.PosSemidef.commute_of_commute_pow (hM N) hp hQ

end MPOTensor
