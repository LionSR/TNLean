/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.HorizontalCFMPVRepresentation
import TNLean.MPS.MPDO.PerCopyHorizontalCF
import TNLean.Algebra.TracePairing

/-!
# One-sided invariant matrices for matrix product density operators

This file formalizes the first operator step in the proof of Proposition 4.13
of arXiv:1606.00608, lines 1874--1887.  If a Hermitian matrix $P$ satisfies
$P\widetilde M=P\widetilde M P$ on the vertically viewed tensor, positivity of
the density operators gives
$$
  P_1H^{(N+1)}=P_1H^{(N+1)}P_1=H^{(N+1)}P_1,
$$
where $P_1=P\otimes\Id^{\otimes N}$.  Given an MPV-level BNT representation,
Lemma L transfers these identities to every minimal representative, where they
say $(\Id-P)MP=0$. The further transport to the original MPO letters uses the
literal horizontal canonical form and is carried out in
`TNLean.MPS.MPDO.HorizontalBNT`.

The file also specializes the positive-semidefinite power-commutation theorem
to matrix product density operators.  This is only the final operator
implication in source lines 1888--1893.  The cyclic projector and its word
invariance are constructed in `TNLean/MPS/MPDO/CyclicProjector.lean`; for a
tensor in literal horizontal canonical form, one noncommuting length suffices
for the periodic-sector contradiction, so the stronger all-length condition is
not required.

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
* `basis_braRight_eq_ketLeftBraRight_of_invariant`: $(\Id-P)MP=0$ on every
  representative in an MPV-level BNT representation.
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

/-- Let the doubled-index tensor of an MPDO have the same complete MPV family
as a BNT sector decomposition, and let \(P\) be Hermitian with
\(P\widetilde M=P\widetilde M P\).  On every minimal BNT representative, the
insertions of \(\widetilde M P\) and
\(P\widetilde M P\) agree.  Equivalently, \((\Id-P)MP=0\) on every
representative.

Repeated gauge-equivalent copies are grouped through their power-sum
coefficient before Lemma L is applied.  Thus the theorem uses the MPV-level
consequence `decBSV` of the horizontal canonical form in arXiv:1606.00608 and
does not assume per-copy trace separation.  It does not include the literal
bond-space gauge in equation `eq:II_ABasicTensors`.

Source: arXiv:1606.00608, Proposition 4.13, lines 1873--1887, and Appendix
C.3, Lemma L, lines 1835--1858. -/
theorem basis_braRight_eq_ketLeftBraRight_of_invariant
    (M : MPOTensor d D) (hMpdo : IsMPDO M)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hCF : MPSTensor.IsBNTCanonicalForm S)
    (hM : MPSTensor.SameMPV₂ M.toMPSTensor S.toTensor)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian)
    (hPM : M.ketLeftMul P = (M.ketLeftMul P).braRightMul P) :
    ∀ k, MPSTensor.insertedTensor (MPSTensor.braRightAction P) (S.basis k) =
      MPSTensor.insertedTensor (MPSTensor.ketLeftBraRightAction P) (S.basis k) := by
  refine basis_opposite_insert_eq_of_rotated_mpo_entries M S hCF hM P ?_ ?_
  · intro N ρ
    have h := firstSiteMatrix_mul_mpo_of_ketLeftMul_invariant M P hPM N
    have h2 := Matrix.ext_iff.mpr h
      (Fin.cons (ρ 0).divNat fun n ↦ (ρ (Fin.succ n)).divNat)
      (Fin.cons (ρ 0).modNat fun n ↦ (ρ (Fin.succ n)).modNat)
    rw [mul_firstSiteMatrix_apply] at h2
    simp only [firstSiteMatrix_mul_apply] at h2
    simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ] at h2
    rw [h2]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  · intro N ρ
    have h := firstSiteMatrix_mul_mpo_comm M hMpdo hP hPM N
    have h2 := Matrix.ext_iff.mpr h
      (Fin.cons (ρ 0).divNat fun n ↦ (ρ (Fin.succ n)).divNat)
      (Fin.cons (ρ 0).modNat fun n ↦ (ρ (Fin.succ n)).modNat)
    rw [mul_firstSiteMatrix_apply, firstSiteMatrix_mul_apply] at h2
    simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ] at h2
    exact h2

/-- Let the doubled-index tensor of an MPDO have a horizontal block-injective
canonical-form decomposition, and let $P$ be Hermitian with
$P\widetilde M=P\widetilde M P$.  On every canonical-form block, the
insertions of $\widetilde M P$ and $P\widetilde M P$ agree.  Equivalently,
$(\Id-P)MP=0$ blockwise.

This is the algebraic conclusion of the invariant-projection step in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1874--1887.  The source takes
$P$ to be an orthogonal projector and writes $P^\perp MP=0$; under the weaker
Hermiticity hypothesis used here, the precise expression is $(\Id-P)MP=0$.

**Scope restriction (per-block separation):** inherited from
`MPOTensor.blockwise_opposite_insert_eq_of_rotated_mpo_entries`
(`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`). -/
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

/-- **Commutation at a two-site chain forces letter-level invariance, for a
single-letter injective tensor.**

If `M`'s doubled-index tensor `M.toMPSTensor` is (single-letter) injective —
its `d * d` many matrices `M i j` already span the full `D × D` matrix
algebra — then commutation of the first-site action of an idempotent `Q`
with the two-site density operator `mpo M 2` alone forces the letter-level
invariance `M.ketLeftMul Q = (M.ketLeftMul Q).braRightMul Q`.  Hermiticity of
`Q` is not needed: only idempotence and the commutation itself enter the
argument (in the application to orthogonal projectors, `Q` happens to be
Hermitian, but that is not used here).

This is a single-instantiation converse of the invariant-projection step
(arXiv:1606.00608, lines 1874--1887): idempotence of `Q` upgrades the full
commutation `Q_1 H = H Q_1` to the one-sided reduction `Q_1 H = Q_1 H Q_1`
(the reverse of `firstSiteMatrix_mul_mpo_of_ketLeftMul_invariant`'s
conclusion); unfolding *that* identity against every trailing letter `M c c'`
gives `d * d` many trace identities pairing `(M.ketLeftMul Q) a b` against
`((M.ketLeftMul Q).braRightMul Q) a b`, for every physical index pair `a, b`,
over every letter of `M.toMPSTensor`. Injectivity's spanning property and
nondegeneracy of the trace pairing (`MPSTensor.traceMulRightPi_ker_eq_bot`)
then force the two matrices to agree.

Unlike the representative-grouped Lemma L in
`HorizontalCFMPVRepresentation.lean` (which uses an MPV-level BNT
representation and the commutation family at *every* length, but does not
transport its conclusion back to `M`'s own letters), this theorem needs only
the commutation hypothesis at chain length `2`, applies to `M`'s own tensor
directly, and does not extend to chain length `1` (`mpo M 1`).  The missing
literal-gauge transport for the general case is supplied in
`TNLean/MPS/MPDO/HorizontalBNT.lean`.  At chain length `1`,
the single trailing letter is the identity matrix, giving only a
trace-level identity, not enough to separate the opposite-corner difference. -/
theorem ketLeftMul_eq_braRightMul_of_commute_of_isInjective
    (M : MPOTensor d D) (hInj : MPSTensor.IsInjective M.toMPSTensor)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQidem : IsIdempotentElem Q)
    (hComm : Commute (firstSiteMatrix Q 1) (mpo M 2)) :
    M.ketLeftMul Q = (M.ketLeftMul Q).braRightMul Q := by
  classical
  have hQ1idem : firstSiteMatrix Q 1 * firstSiteMatrix Q 1 = firstSiteMatrix Q 1 := by
    rw [firstSiteMatrix_mul_firstSiteMatrix, hQidem]
  have hOneSided : firstSiteMatrix Q 1 * mpo M 2 =
      firstSiteMatrix Q 1 * mpo M 2 * firstSiteMatrix Q 1 := by
    calc firstSiteMatrix Q 1 * mpo M 2
        = firstSiteMatrix Q 1 * firstSiteMatrix Q 1 * mpo M 2 := by rw [hQ1idem]
      _ = firstSiteMatrix Q 1 * (firstSiteMatrix Q 1 * mpo M 2) := by rw [Matrix.mul_assoc]
      _ = firstSiteMatrix Q 1 * (mpo M 2 * firstSiteMatrix Q 1) := by rw [hComm.eq]
      _ = firstSiteMatrix Q 1 * mpo M 2 * firstSiteMatrix Q 1 := by rw [Matrix.mul_assoc]
  funext a b
  show (M.ketLeftMul Q) a b = ((M.ketLeftMul Q).braRightMul Q) a b
  refine sub_eq_zero.mp
    ((LinearMap.ker_eq_bot'.1 (MPSTensor.traceMulRightPi_ker_eq_bot hInj))
      ((M.ketLeftMul Q) a b - ((M.ketLeftMul Q).braRightMul Q) a b) ?_)
  funext p
  rw [MPSTensor.traceMulRightPi_apply, Pi.zero_apply]
  change Matrix.trace
    (((M.ketLeftMul Q) a b - ((M.ketLeftMul Q).braRightMul Q) a b) * M p.divNat p.modNat) = 0
  set c := p.divNat
  set c' := p.modNat
  have h2 := Matrix.ext_iff.mpr hOneSided
      (Fin.cons a (fun _ : Fin 1 => c)) (Fin.cons b (fun _ : Fin 1 => c'))
  rw [mul_firstSiteMatrix_apply] at h2
  simp only [firstSiteMatrix_mul_apply] at h2
  simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ] at h2
  simp only [mpo_cons_cons, List.ofFn_succ, List.ofFn_zero, evalWord_cons,
    evalWord_nil, mul_one] at h2
  rw [Matrix.sub_mul, Matrix.trace_sub, sub_eq_zero]
  calc Matrix.trace ((M.ketLeftMul Q) a b * M c c')
      = ∑ i : Fin d, Q a i * Matrix.trace (M i b * M c c') :=
        (sum_mul_trace_eq_trace_sum_smul (fun i => Q a i) (fun i => M i b) (M c c')).symm
    _ = ∑ j : Fin d, (∑ i : Fin d, Q a i * Matrix.trace (M i j * M c c')) * Q j b := h2
    _ = ∑ j : Fin d, Q j b * ∑ i : Fin d, Q a i * Matrix.trace (M i j * M c c') :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = ∑ j : Fin d, Q j b * Matrix.trace ((M.ketLeftMul Q) a j * M c c') := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        exact sum_mul_trace_eq_trace_sum_smul (fun i => Q a i) (fun i => M i j) (M c c')
    _ = Matrix.trace (((M.ketLeftMul Q).braRightMul Q) a b * M c c') :=
        sum_mul_trace_eq_trace_sum_smul (fun j => Q j b) (fun j => (M.ketLeftMul Q) a j) (M c c')

/-- For an MPDO, any matrix commuting with a nonzero power of the $N$-site
density operator commutes with the density operator itself.

This is the final operator implication in the contradiction at
arXiv:1606.00608, lines 1888--1893 (equation eq2:proof.IV.12).  It does not
construct the orthogonal projector $Q$ associated with a nontrivial vertical
period or establish its commutation with $[H^{(N)}]^p$.  Those ingredients are
combined in `TNLean/MPS/MPDO/CyclicProjector.lean`, where one noncommuting
length gives the contradiction for a tensor in literal horizontal canonical
form. -/
theorem mpo_commute_of_commute_pow (M : MPOTensor d D) (hM : IsMPDO M) (N : ℕ)
    {p : ℕ} (hp : p ≠ 0) {Q : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hQ : Commute Q (mpo M N ^ p)) : Commute Q (mpo M N) :=
  Matrix.PosSemidef.commute_of_commute_pow (hM N) hp hQ

end MPOTensor
