/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.FirstSite
import TNLean.MPS.MPDO.HorizontalCFMPVRepresentation
import TNLean.MPS.MPDO.PerCopyHorizontalCF

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
  have hcorner := mpo_opposite_corner_eq_zero M hMpdo (N + 1) (by omega)
    (firstSiteMatrix P N)
    (firstSiteMatrix_isHermitian hP N) hInv
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul] at hcorner
  rw [hInv]
  exact (sub_eq_zero.mp hcorner).symm

/-- Let the doubled-index tensor of an MPDO have the same positive-length MPV
family as a BNT sector decomposition, and let \(P\) be Hermitian with
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
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
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
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor
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
    (hN : 0 < N) {p : ℕ} (hp : p ≠ 0)
    {Q : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (hQ : Commute Q (mpo M N ^ p)) : Commute Q (mpo M N) :=
  Matrix.PosSemidef.commute_of_commute_pow (hM N hN) hp hQ

end MPOTensor
