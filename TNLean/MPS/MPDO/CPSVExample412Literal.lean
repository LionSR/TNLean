/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.KroneckerFactorPositivity
import QICLean.Algebra.SpinCover.Basic
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.RFPViaTS

/-!
# The literal tensor printed in CPSV16 Example 4.12

CPSV16 Example 4.12 prints a tensor $M$ with $d=D=2$ whose only nonzero
components are
\[
  1=M_{00}^{00}=M_{00}^{11}=M_{11}^{00}=-M_{11}^{11}.
\]
Thus $M^{00}=I$ and $M^{11}=\sigma_z$, with the off-diagonal physical letters
zero.  At every positive length it generates
\[
  \rho^{(N)}(M)=I^{\otimes N}+\sigma_z^{\otimes N}.
\]

The printed tensor is not normalized in the convention used by
`MPOTensor.IsRFPViaTS`: its physical-trace transfer is $I+\sigma_z$, whose
square is twice itself rather than itself.  Consequently the literal tensor
satisfies the project's scale-invariant `IsSourceZCL` relation with scale $2$,
but it fails the paper's literal ZCL equation and is not an RFP via
trace-preserving physical maps. The separate likely normalized representative
$(1/2)\,M$ is discussed in
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex` and is not treated here.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Example 4.12,
  lines 932--939.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.CPSVExample412Literal

/-- The paper's $\sigma_z=|0\rangle\langle0|-|1\rangle\langle1|$, using the
public Pauli matrix construction.

Source: CPSV16, arXiv:1606.00608, Example 4.12, lines 935--937. -/
noncomputable def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ :=
  SpinCover.pauli 2

@[simp] private lemma sigmaZ_apply_ne {i j : Fin 2} (h : i ≠ j) : sigmaZ i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [sigmaZ, SpinCover.pauli]

/-- The literal $d=D=2$ tensor $M$ printed in CPSV16 Example 4.12:
$M^{00}=I$, $M^{11}=\sigma_z$, and $M^{01}=M^{10}=0$.

Source: CPSV16, arXiv:1606.00608, Example 4.12, lines 932--935. -/
noncomputable def M : MPOTensor 2 2 :=
  fun i j => if i = j then Matrix.diagonal ![(1 : ℂ), sigmaZ i i] else 0

@[simp] private lemma M_zero_zero : M 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [M, sigmaZ, SpinCover.pauli]

@[simp] private lemma M_one_one : M 1 1 = sigmaZ := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [M, sigmaZ, SpinCover.pauli]

@[simp] private lemma M_zero_one : M 0 1 = 0 := by simp [M]
@[simp] private lemma M_one_zero : M 1 0 = 0 := by simp [M]

/-- The $\sigma_z$ eigenvalue at one physical letter. -/
noncomputable def siteSign (i : Fin 2) : ℂ := sigmaZ i i

/-- The eigenvalue of $\sigma_z^{\otimes N}$ on a binary configuration. -/
noncomputable def configurationSign {N : ℕ} (σ : Fin N → Fin 2) : ℂ :=
  ∏ k, siteSign (σ k)

private lemma siteSign_eq_one_or_neg_one (i : Fin 2) :
    siteSign i = 1 ∨ siteSign i = -1 := by
  fin_cases i <;> simp [siteSign, sigmaZ, SpinCover.pauli]

private lemma prod_M_diagonal :
    ∀ {N : ℕ} (σ : Fin N → Fin 2),
      (List.ofFn fun k => M (σ k) (σ k)).prod =
        Matrix.diagonal ![(1 : ℂ), configurationSign σ] := by
  intro N
  induction N with
  | zero =>
      intro σ
      ext a b
      fin_cases a <;> fin_cases b <;> simp [configurationSign]
  | succ N ih =>
      intro σ
      rw [List.ofFn_succ, List.prod_cons, M, ite_eq_left rfl,
        ih (fun i => σ i.succ), Matrix.diagonal_mul_diagonal]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [configurationSign, Fin.prod_univ_succ, siteSign]

private lemma prod_M_off_diagonal {N : ℕ} {σ τ : Fin N → Fin 2}
    (hστ : σ ≠ τ) :
    (List.ofFn fun k => M (σ k) (τ k)).prod = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hστ
  apply List.prod_eq_zero
  exact List.mem_ofFn.mpr ⟨k, by simp [M, hk]⟩

/-- The exact entrywise version of
$\rho^{(N)}(M)=I^{\otimes N}+\sigma_z^{\otimes N}$.

Source: CPSV16, arXiv:1606.00608, Example 4.12, equations at lines 933--936. -/
theorem rho_eq_diagonal (N : ℕ) :
    mpo M N = Matrix.diagonal fun σ => 1 + configurationSign σ := by
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    rw [Matrix.diagonal_apply_eq, mpo_apply, mpoMatrixEntry, evalWord_ofFn,
      prod_M_diagonal, Matrix.trace_diagonal]
    simp [Fin.sum_univ_two]
  · rw [Matrix.diagonal_apply_ne _ hστ, mpo_apply, mpoMatrixEntry,
      evalWord_ofFn, prod_M_off_diagonal hστ, Matrix.trace_zero]

/-- Formula-driven form of the source identity using the public finite
Kronecker product: for every positive $N$,
$\rho^{(N)}(M)=I^{\otimes N}+\sigma_z^{\otimes N}$.

Source: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--936. -/
theorem rho_eq_finKronecker (N : ℕ) (_hN : 0 < N) :
    mpo M N =
      Matrix.finKronecker (fun _ : Fin N => (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
      Matrix.finKronecker (fun _ : Fin N => sigmaZ) := by
  rw [rho_eq_diagonal]
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    simp [Matrix.finKronecker_apply, configurationSign, siteSign,
      Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hστ]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hστ
    simp only [Matrix.add_apply, Matrix.finKronecker_apply]
    have hone : ∏ n, (1 : Matrix (Fin 2) (Fin 2) ℂ) (σ n) (τ n) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      exact Matrix.one_apply_ne hk
    have hz : ∏ n, sigmaZ (σ n) (τ n) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      exact sigmaZ_apply_ne hk
    rw [hone, hz, add_zero]

private lemma configurationSign_eq_one_or_neg_one {N : ℕ} (σ : Fin N → Fin 2) :
    configurationSign σ = 1 ∨ configurationSign σ = -1 := by
  induction N with
  | zero =>
      left
      simp [configurationSign]
  | succ N ih =>
      have hprod : configurationSign σ =
          siteSign (σ 0) * configurationSign (σ ∘ Fin.succ) := by
        rw [configurationSign, Fin.prod_univ_succ]
        rfl
      rw [hprod]
      rcases siteSign_eq_one_or_neg_one (σ 0) with hhead | hhead
      · rcases ih (σ ∘ Fin.succ) with htail | htail
        · left; rw [hhead, htail, one_mul]
        · right; rw [hhead, htail, one_mul]
      · rcases ih (σ ∘ Fin.succ) with htail | htail
        · right; rw [hhead, htail, neg_one_mul]
        · left; rw [hhead, htail]; norm_num

/-- The literal tensor generates positive semidefinite operators at every
positive chain length, hence is an MPDO tensor in the project convention.

Source: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--937. -/
theorem M_isMPDO : IsMPDO M := by
  intro N _
  rw [rho_eq_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro σ
  rcases configurationSign_eq_one_or_neg_one σ with h | h <;>
    change (0 : ℂ) ≤ 1 + configurationSign σ <;> rw [h] <;> norm_num


/-! ### Trace, one-site loss, and saturation of the area law -/

private lemma sum_siteSign_eq_zero : (∑ a : Fin 2, siteSign a) = (0 : ℂ) := by
  rw [Fin.sum_univ_two]
  norm_num [siteSign, sigmaZ, SpinCover.pauli]

private lemma sum_configurationSign_eq_zero {n : ℕ} (hn : 0 < n) :
    ∑ w : Fin n → Fin 2, configurationSign w = 0 := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  calc
    ∑ w : Fin n → Fin 2, configurationSign w =
        ∑ w : Fin n → Fin 2, (∏ k : Fin n, siteSign (w k)) := rfl
    _ = ∑ w ∈ (Fintype.piFinset fun (_ : Fin n) => (Finset.univ : Finset (Fin 2))),
        (∏ k : Fin n, siteSign (w k)) := by simp [Fintype.piFinset_univ]
    _ = ∏ k : Fin n, (∑ a ∈ (Finset.univ : Finset (Fin 2)), siteSign a) := by
      rw [← Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (Fin 2)))
        (fun (_ : Fin n) a => siteSign a)]
    _ = ∏ _k : Fin n, (∑ a : Fin 2, siteSign a) := by simp
    _ = ∏ _k : Fin n, (0 : ℂ) := by rw [sum_siteSign_eq_zero]
    _ = 0 := by
      rw [Finset.prod_const, Finset.card_univ, hcard]
      exact zero_pow hn.ne'

/-- The trace of the literal positive-length operator is $2^N$.

Source formula: CPSV16, arXiv:1606.00608, Example 4.12, lines 933--936. -/
theorem trace_rho (N : ℕ) (hN : 0 < N) :
    Matrix.trace (mpo M N) = (2 : ℂ) ^ N := by
  rw [rho_eq_diagonal, Matrix.trace_diagonal, Finset.sum_add_distrib,
    sum_configurationSign_eq_zero hN, add_zero]
  simp

private lemma normalizedMPO_M_eq (N : ℕ) (hN : 0 < N) :
    normalizedMPO M N = ((2 : ℂ)⁻¹ ^ N) • mpo M N := by
  rw [normalizedMPO, trace_rho N hN, inv_pow]

private lemma configurationSign_append {L K : ℕ}
    (u : Fin L → Fin 2) (w : Fin K → Fin 2) :
    configurationSign (Fin.append u w) = configurationSign u * configurationSign w := by
  rw [configurationSign, configurationSign, configurationSign, Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

private lemma configurationSign_append_cast {L K N : ℕ} (hN : N = L + K)
    (u : Fin L → Fin 2) (w : Fin K → Fin 2) :
    configurationSign (Fin.append u w ∘ Fin.cast hN) =
      configurationSign u * configurationSign w := by
  subst hN
  simp [configurationSign_append]

private lemma reducedBlockState_M_apply {N L : ℕ} (hL : L ≤ N) (hN : 0 < N)
    (u v : Fin L → Fin 2) :
    reducedBlockState M N L hL u v =
      if u = v then ((2 : ℂ)⁻¹ ^ N) *
        ((2 : ℂ) ^ (N - L) + configurationSign u *
          (∑ w : Fin (N - L) → Fin 2, configurationSign w))
      else 0 := by
  set K := N - L with hK
  have hNK : N = L + K := by omega
  have hcard : Fintype.card (Fin K → Fin 2) = 2 ^ K := by simp
  rw [reducedBlockState_eq_sum M hL u v, normalizedMPO_M_eq N hN,
    rho_eq_diagonal N]
  by_cases huv : u = v
  · subst v
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq]
    rw [ite_true]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_const, Finset.card_univ, hcard]
      simp [nsmul_eq_mul]
      ring
    · calc
        ∑ w : Fin K → Fin 2,
            (2 : ℂ)⁻¹ ^ N * configurationSign (Fin.append u w ∘ Fin.cast hNK) =
            ∑ w : Fin K → Fin 2,
              (2 : ℂ)⁻¹ ^ N * (configurationSign u * configurationSign w) := by
              refine Finset.sum_congr rfl (fun w _ => ?_)
              rw [configurationSign_append_cast hNK u w]
        _ = (2 : ℂ)⁻¹ ^ N *
            (configurationSign u * ∑ w : Fin K → Fin 2, configurationSign w) := by
              simp [Finset.mul_sum]
  · have hterm : ∀ w : Fin K → Fin 2,
        (Matrix.diagonal fun σ : Fin N → Fin 2 => 1 + configurationSign σ)
          (Fin.append u w ∘ Fin.cast hNK) (Fin.append v w ∘ Fin.cast hNK) = 0 := by
      intro w
      apply Matrix.diagonal_apply_ne
      intro heq
      apply huv
      funext i
      have hi := congrFun heq (Fin.cast hNK.symm (Fin.castAdd K i))
      simpa [Fin.append_left] using hi
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [ite_eq_right huv]
    apply Finset.sum_eq_zero
    intro w _
    rw [hterm w, mul_zero]

/-- Tracing any nonempty complement removes the entire
$\sigma_z^{\otimes N}$ contribution.  The normalized reduced state on $L<N$
sites is the maximally mixed state $2^{-L}I^{\otimes L}$.

In particular, taking $N=L+1$ is the one-site trace loss stated in the source.

Source: CPSV16, arXiv:1606.00608, Example 4.12, line 937. -/
theorem reducedBlockState_M_eq_scaled_one {N L : ℕ}
    (hLpos : 1 ≤ L) (hLN : L < N) (hL : L ≤ N := Nat.le_of_lt hLN) :
    reducedBlockState M N L hL =
      ((2 : ℂ)⁻¹ ^ L) •
        (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ) := by
  ext u v
  rw [reducedBlockState_M_apply hL (by omega) u v]
  by_cases huv : u = v
  · subst v
    rw [ite_eq_left rfl, sum_configurationSign_eq_zero (Nat.sub_pos_of_lt hLN)]
    simp only [mul_zero, add_zero, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply_eq]
    simp only [mul_one, inv_pow]
    field_simp
    rw [← pow_add]
    congr 1
    omega
  · rw [ite_eq_right huv, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne huv, mul_zero]

/-- The source's one-site-loss statement in its literal normalization:
a one-site partial trace of $\rho^{(L+1)}(M)$ is proportional to the identity.
The reduced-state construction normalizes first, giving exactly $2^{-L}I$.

Source: CPSV16, arXiv:1606.00608, Example 4.12, line 937. -/
theorem one_site_trace_loses_sigmaZ (L : ℕ) (hL : 1 ≤ L) :
    reducedBlockState M (L + 1) L (by omega) =
      ((2 : ℂ)⁻¹ ^ L) •
        (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ) :=
  reducedBlockState_M_eq_scaled_one hL (by omega)

private lemma blockEntropy_M_eq {N L : ℕ} (hLpos : 1 ≤ L) (hLN : L < N)
    (hL : L ≤ N) (hM : (mpo M N).PosSemidef) :
    blockEntropy M N L hL hM = L * Real.log 2 := by
  rw [blockEntropy]
  have hrho_herm := reducedBlockState_isHermitian M N L hL hM
  have hrho_eq := reducedBlockState_M_eq_scaled_one hLpos hLN
  have hc_selfadj : IsSelfAdjoint ((2 : ℂ)⁻¹ ^ L : ℂ) := by simp [IsSelfAdjoint]
  have hscaled : (((2 : ℂ)⁻¹ ^ L : ℂ) •
      (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ)).IsHermitian :=
    (Matrix.isHermitian_one (n := Fin L → Fin 2) (α := ℂ)).smul hc_selfadj
  rw [vonNeumannEntropy_congr hrho_eq hrho_herm hscaled,
    vonNeumannEntropy_eq_charpoly_roots _ hscaled]
  have hcard : Fintype.card (Fin L → Fin 2) = 2 ^ L := by simp
  have hchar : (((2 : ℂ)⁻¹ ^ L : ℂ) •
      (1 : Matrix (Fin L → Fin 2) (Fin L → Fin 2) ℂ)).charpoly =
      (Polynomial.X - Polynomial.C ((2 : ℂ)⁻¹ ^ L : ℂ)) ^
        Fintype.card (Fin L → Fin 2) := by
    calc
      _ = (Matrix.diagonal fun _ : Fin L → Fin 2 => ((2 : ℂ)⁻¹ ^ L : ℂ)).charpoly := by
        rw [Matrix.smul_one_eq_diagonal]
      _ = ∏ _i : Fin L → Fin 2,
          (Polynomial.X - Polynomial.C ((2 : ℂ)⁻¹ ^ L : ℂ)) :=
        Matrix.charpoly_diagonal _
      _ = _ := by simp
  rw [hchar, Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  simp only [Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton,
    Multiset.sum_singleton, nsmul_eq_mul, hcard]
  have hre : (((2 : ℂ)⁻¹ ^ L : ℂ).re : ℝ) = ((2⁻¹ : ℝ) ^ L) := by
    calc
      (((2 : ℂ)⁻¹ ^ L : ℂ).re : ℝ) =
          ((((2⁻¹ : ℝ) : ℂ) ^ L : ℂ).re : ℝ) := by norm_num
      _ = ((((2⁻¹ : ℝ) ^ L : ℝ) : ℂ).re : ℝ) := by rw [Complex.ofReal_pow]
      _ = ((2⁻¹ : ℝ) ^ L : ℝ) := by rw [Complex.ofReal_re]
  rw [hre, show ((2⁻¹ : ℝ) ^ L) = ((2 ^ L : ℝ)⁻¹) by simp [inv_pow]]
  push_cast
  rw [Real.mul_negMulLog_inv ((2 : ℝ) ^ L) (pow_ne_zero L (by norm_num)), Real.log_pow]

/-- The literal tensor satisfies saturation of the area law: every nonempty proper
reduced block is maximally mixed, so $S_L=L\log 2$ and the mutual information
is independent of $L$.

Source claim: CPSV16, arXiv:1606.00608, Example 4.12, line 937; the entropy
calculation is the direct derivation from the printed formula at lines 933--936. -/
theorem M_isSAL : IsSAL M := by
  refine ⟨M_isMPDO, ?_, ?_⟩
  · intro N hN
    rw [trace_rho N hN]
    exact pow_ne_zero N (by norm_num)
  · intro N L hLpos hLhalf
    have hM : (mpo M N).PosSemidef := M_isMPDO N (by omega)
    simp only [mutualInfoChain]
    have hLval : blockEntropy M N L
        (Nat.le_of_lt (hLhalf.trans_le (Nat.div_le_self N 2))) hM =
        (L : ℝ) * Real.log 2 := by
      apply blockEntropy_M_eq hLpos (by omega) _ hM
    have hNLval : blockEntropy M N (N - L) (Nat.sub_le N L) hM =
        ((N - L : ℕ) : ℝ) * Real.log 2 := by
      apply blockEntropy_M_eq (by omega) (by omega) _ hM
    have hL1val : blockEntropy M N (L + 1)
        (hLhalf.trans_le (Nat.div_le_self N 2)) hM =
        ((L + 1 : ℕ) : ℝ) * Real.log 2 := by
      apply blockEntropy_M_eq (by omega) (by omega) _ hM
    have hNL1val : blockEntropy M N (N - (L + 1))
        (Nat.sub_le N (L + 1)) hM =
        ((N - (L + 1) : ℕ) : ℝ) * Real.log 2 := by
      apply blockEntropy_M_eq (by omega) (by omega) _ hM
    rw [hLval, hNLval, hL1val, hNL1val]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring

/-- The physical-trace transfer of the literal printed tensor is
$I+\sigma_z=\operatorname{diag}(2,0)$.

Source tensor: CPSV16, arXiv:1606.00608, Example 4.12, lines 932--937. -/
theorem physTraceTransfer_M :
    physTraceTransfer M = !![(2 : ℂ), 0; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [physTraceTransfer, M, sigmaZ, SpinCover.pauli, Fin.sum_univ_two]

/-- The project's scale-invariant `IsSourceZCL` relation for the literal
representative has scale $\lambda=2$:
$(I+\sigma_z)^2=2(I+\sigma_z)$.

**Local fix (normalization):** Definition 4.2 of the source requires literal
idempotence, whereas the tensor printed in Example 4.12 satisfies only this
scale-two relation. See
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Example 4.12, line 937. -/
theorem physTraceTransfer_M_sq :
    physTraceTransfer M * physTraceTransfer M =
      (2 : ℂ) • physTraceTransfer M := by
  rw [physTraceTransfer_M]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The literal tensor satisfies the project's scale-invariant `IsSourceZCL`
relation with the explicit positive scale $\lambda=2$.

**Local fix (normalization):** `IsSourceZCL` allows a positive scale and is
therefore broader than the literal idempotence in CPSV16 Definition 4.2. This
theorem records the corrected scale-two relation for the printed tensor, not
the paper's literal ZCL assertion. See
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Example 4.12, line 937. -/
theorem M_isSourceZCL : IsSourceZCL M := by
  refine ⟨?_, 2, by norm_num, physTraceTransfer_M_sq⟩
  rw [physTraceTransfer_M]
  intro h
  have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  norm_num at this

/-- The transfer of the literal printed tensor is not idempotent.  This is the
normalization mismatch hidden by the source's statement that the same printed
representative is an RFP.

**Local fix (normalization):** see
`docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Example 4.12, lines 937--938. -/
theorem physTraceTransfer_M_not_idempotent :
    physTraceTransfer M * physTraceTransfer M ≠ physTraceTransfer M := by
  rw [physTraceTransfer_M]
  intro h
  have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at this

/-- The literal printed representative cannot satisfy Definition 4.1 with
trace-preserving physical maps, since that condition forces literal transfer
idempotence.

**Local fix (normalization):** the likely $(1/2)\,M$ representative is separate;
see `docs/paper-gaps/cpsv16_example_4_12_normalization.tex`.

Source comparison: CPSV16, arXiv:1606.00608, Example 4.12, lines 937--938. -/
theorem M_not_isRFPViaTS : ¬ IsRFPViaTS M := by
  intro h
  exact physTraceTransfer_M_not_idempotent
    (physTraceTransfer_sq_of_isRFPViaTS M h)

end MPOTensor.CPSVExample412Literal
