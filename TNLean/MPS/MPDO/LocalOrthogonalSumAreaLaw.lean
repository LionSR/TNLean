/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.EntropyDecomposition
import TNLean.Algebra.HermitianHelpers
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.FirstSite

/-!
# Saturated area law for local orthogonal sums

A finite sum of matrix product density operators supported on pairwise
orthogonal one-site subspaces satisfies the saturated area law whenever every
summand does.  The sector label remains visible in every nonempty marginal, so
the entropy of each marginal is the Shannon entropy of the sector weights plus
the probability-weighted sector entropies.  The Shannon term is independent of
the marginal length and cancels in the comparison of mutual informations.

This is the final local direct-sum argument in Appendix C.2 of
arXiv:1606.00608.  It is separate from the assertion that a commuting
nearest-neighbor form and zero correlation length imply the saturated area
law for each normal sector.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, Proposition `prop4to2`, lines 1801--1808.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D g : ℕ} {dim : Fin g → ℕ}

private theorem mul_eq_self_of_isHermitian_of_mul_eq_self
    {n : Type*} [Fintype n]
    {A P : Matrix n n ℂ} (hA : A.IsHermitian) (hP : P.IsHermitian)
    (hleft : P * A = A) :
    A * P = A := by
  classical
  have hstar := congrArg Matrix.conjTranspose hleft
  simpa only [Matrix.conjTranspose_mul, hA.eq, hP.eq] using hstar

/-- Support of the first site of a normalized chain is preserved by every
nonempty prefix marginal.

This is the elementary marginalization step used in CPSV16, Appendix C.2,
lines 1760--1770 and 1801--1808. -/
theorem firstSiteMatrix_mul_reducedBlockState_of_mul_normalizedMPO
    (M : MPOTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    {N' L : ℕ} (hL : L + 1 ≤ N' + 1)
    (hfull : firstSiteMatrix P N' * normalizedMPO M (N' + 1) =
      normalizedMPO M (N' + 1)) :
    firstSiteMatrix P L * reducedBlockState M (N' + 1) (L + 1) hL =
      reducedBlockState M (N' + 1) (L + 1) hL := by
  ext u v
  obtain ⟨a, u', rfl⟩ : ∃ a u', u = Fin.cons a u' :=
    ⟨u 0, u ∘ Fin.succ, (Fin.cons_self_tail u).symm⟩
  obtain ⟨b, v', rfl⟩ : ∃ b v', v = Fin.cons b v' :=
    ⟨v 0, v ∘ Fin.succ, (Fin.cons_self_tail v).symm⟩
  rw [firstSiteMatrix_mul_apply]
  simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ]
  simp_rw [reducedBlockState_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  let z : Fin N' → Fin d :=
    Fin.append u' w ∘ Fin.cast (show N' = L + (N' + 1 - (L + 1)) by omega)
  let full (x : Fin d) : Fin (N' + 1) → Fin d :=
    Fin.append (Fin.cons x u') w ∘
      Fin.cast (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega)
  let full' : Fin (N' + 1) → Fin d :=
    Fin.append (Fin.cons b v') w ∘
      Fin.cast (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega)
  change (∑ x : Fin d, P a x * normalizedMPO M (N' + 1) (full x) full') =
    normalizedMPO M (N' + 1) (full a) full'
  have htail (x : Fin d) : full x ∘ Fin.succ = z := by
    funext i
    simp only [full, z, Function.comp_apply]
    by_cases hi : i.val < L
    · have hleft : Fin.cast
          (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega) i.succ =
          Fin.castAdd (N' + 1 - (L + 1)) (Fin.succ ⟨i.val, hi⟩) := by
        apply Fin.ext
        simp
      have hright : Fin.cast
          (show N' = L + (N' + 1 - (L + 1)) by omega) i =
          Fin.castAdd (N' + 1 - (L + 1)) ⟨i.val, hi⟩ := by
        apply Fin.ext
        simp
      rw [hleft, hright, Fin.append_left, Fin.append_left, Fin.cons_succ]
    · let k : Fin (N' + 1 - (L + 1)) := ⟨i.val - L, by omega⟩
      have hleft : Fin.cast
          (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega) i.succ =
          Fin.natAdd (L + 1) k := by
        apply Fin.ext
        simp [k]
        omega
      have hright : Fin.cast
          (show N' = L + (N' + 1 - (L + 1)) by omega) i =
          Fin.natAdd L k := by
        apply Fin.ext
        simp [k]
        omega
      rw [hleft, hright, Fin.append_right, Fin.append_right]
  have hfull_eq (x : Fin d) : full x = Fin.cons x z := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [full, Function.comp_apply]
      have hzero : Fin.cast
          (show N' + 1 = L + 1 + (N' + 1 - (L + 1)) by omega) 0 =
          Fin.castAdd (N' + 1 - (L + 1)) (0 : Fin (L + 1)) := by
        apply Fin.ext
        simp
      rw [hzero, Fin.append_left, Fin.cons_zero]
      simp
    · exact congrFun (htail x) j
  have hentry := congrFun (congrFun hfull (full a)) full'
  rw [firstSiteMatrix_mul_apply] at hentry
  simpa only [hfull_eq, Fin.cons_zero, Function.comp_def, Fin.cons_succ] using hentry

/-- The probability of a local orthogonal sector in the normalized
length-`N` state.

Source: arXiv:1606.00608, Appendix C.2, lines 1753--1770 and 1791--1808. -/
noncomputable def localOrthogonalSectorProbability
    (M : MPOTensor d D) (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) (N : ℕ) (s : Fin g) : ℝ :=
  (multiplicity s : ℝ) * (Matrix.trace (mpo (K s) N)).re /
    (Matrix.trace (mpo M N)).re

/-- Every local orthogonal sector has positive probability when its
multiplicity and the full and sector normalizations are positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1753--1770 and 1791--1808. -/
theorem localOrthogonalSectorProbability_pos
    (M : MPOTensor d D) (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) (hmultiplicity : ∀ s, 0 < multiplicity s)
    {N : ℕ} (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace (mpo (K s) N)) (s : Fin g) :
    0 < localOrthogonalSectorProbability M K multiplicity N s := by
  rw [localOrthogonalSectorProbability]
  have hMre : 0 < (Matrix.trace (mpo M N)).re :=
    (RCLike.pos_iff.mp hMtrace).1
  have hSre : 0 < (Matrix.trace (mpo (K s) N)).re :=
    (RCLike.pos_iff.mp (hSectorTrace s)).1
  exact div_pos (mul_pos (by exact_mod_cast hmultiplicity s) hSre) hMre

/-- The normalized full chain is the probability-weighted sum of its local
orthogonal sectors.

Source: arXiv:1606.00608, Appendix C.2, lines 1753--1770 and 1791--1808. -/
theorem normalizedMPO_eq_sum_localOrthogonalSectorProbability_smul
    (M : MPOTensor d D) (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) {N : ℕ}
    (hM : mpo M N = ∑ s : Fin g, (multiplicity s : ℂ) • mpo (K s) N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace (mpo (K s) N)) :
    normalizedMPO M N = ∑ s : Fin g,
      (localOrthogonalSectorProbability M K multiplicity N s : ℂ) •
        normalizedMPO (K s) N := by
  classical
  have hMtraceEq : Matrix.trace (mpo M N) =
      ((Matrix.trace (mpo M N)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (RCLike.pos_iff.mp hMtrace).2
  have hSectorTraceEq : ∀ s,
      Matrix.trace (mpo (K s) N) = ((Matrix.trace (mpo (K s) N)).re : ℂ) :=
    fun s ↦ by
      apply Complex.ext
      · rfl
      · simpa using (RCLike.pos_iff.mp (hSectorTrace s)).2
  have hpComplex (s : Fin g) :
      (localOrthogonalSectorProbability M K multiplicity N s : ℂ) =
        (multiplicity s : ℂ) * Matrix.trace (mpo (K s) N) /
          Matrix.trace (mpo M N) := by
    rw [localOrthogonalSectorProbability, hMtraceEq, hSectorTraceEq s]
    norm_num
  rw [normalizedMPO]
  nth_rewrite 2 [hM]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [normalizedMPO, hpComplex]
  simp only [smul_smul]
  congr 1
  field_simp [(ne_of_gt hMtrace), (ne_of_gt (hSectorTrace s))]

/-- Every nonempty marginal has the same local-sector probabilities as the
normalized full chain.

Source: arXiv:1606.00608, Appendix C.2, lines 1753--1770 and 1791--1808. -/
theorem reducedBlockState_eq_sum_localOrthogonalSectorProbability_smul
    (M : MPOTensor d D) (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) {N L : ℕ} (hL : L ≤ N)
    (hM : mpo M N = ∑ s : Fin g, (multiplicity s : ℂ) • mpo (K s) N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace (mpo (K s) N)) :
    reducedBlockState M N L hL = ∑ s : Fin g,
      (localOrthogonalSectorProbability M K multiplicity N s : ℂ) •
        reducedBlockState (K s) N L hL := by
  classical
  have hfull := normalizedMPO_eq_sum_localOrthogonalSectorProbability_smul
    M K multiplicity hM hMtrace hSectorTrace
  ext u v
  rw [reducedBlockState_eq_sum]
  simp_rw [hfull, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [reducedBlockState_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]

/-- Entropy of a nonempty marginal of a local orthogonal sum is the Shannon
entropy of the sector probabilities plus the probability-weighted sector
entropies.

Source: arXiv:1606.00608, Appendix C.2, lines 1760--1780 and 1806--1808. -/
theorem blockEntropy_eq_sum_localOrthogonalSectorProbability
    (M : MPOTensor d D) (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) (P : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (hmultiplicity : ∀ s, 0 < multiplicity s)
    (hP : ∀ s, IsOrthogonalProjection (P s))
    (hPorthogonal : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hMpdo : IsMPDO M) (hSectorMpdo : ∀ s, IsMPDO (K s))
    {N L : ℕ} (hN : 0 < N) (hL : L + 1 ≤ N)
    (hM : mpo M N = ∑ s : Fin g, (multiplicity s : ℂ) • mpo (K s) N)
    (hMtrace : 0 < Matrix.trace (mpo M N))
    (hSectorTrace : ∀ s, 0 < Matrix.trace (mpo (K s) N))
    (hsupport : ∀ s,
      firstSiteMatrix (P s) L * reducedBlockState (K s) N (L + 1) hL =
        reducedBlockState (K s) N (L + 1) hL) :
    blockEntropy M N (L + 1) hL (hMpdo N hN) =
      ∑ s : Fin g,
        (Real.negMulLog
            (localOrthogonalSectorProbability M K multiplicity N s) +
          localOrthogonalSectorProbability M K multiplicity N s *
            blockEntropy (K s) N (L + 1) hL (hSectorMpdo s N hN)) := by
  classical
  let p : Fin g → ℝ := fun s ↦
    localOrthogonalSectorProbability M K multiplicity N s
  let ρ : Fin g → Matrix (Fin (L + 1) → Fin d) (Fin (L + 1) → Fin d) ℂ :=
    fun s ↦ reducedBlockState (K s) N (L + 1) hL
  let Q : Fin g → Matrix (Fin (L + 1) → Fin d) (Fin (L + 1) → Fin d) ℂ :=
    fun s ↦ firstSiteMatrix (P s) L
  have hp : ∀ s, 0 < p s := fun s ↦
    localOrthogonalSectorProbability_pos M K multiplicity hmultiplicity
      hMtrace hSectorTrace s
  have hρpos : ∀ s, (ρ s).PosSemidef := fun s ↦
    reducedBlockState_posSemidef (K s) N (L + 1) hL (hSectorMpdo s N hN)
  have hρtrace : ∀ s, Matrix.trace (ρ s) = 1 := fun s ↦
    reducedBlockState_trace (K s) N (L + 1) hL (ne_of_gt (hSectorTrace s))
  have hQherm : ∀ s, (Q s).IsHermitian := fun s ↦
    firstSiteMatrix_isHermitian (hP s).1 L
  have hQρ : ∀ s, Q s * ρ s = ρ s := by
    intro s
    simpa only [Q, ρ] using hsupport s
  have hρQ : ∀ s, ρ s * Q s = ρ s := fun s ↦
    mul_eq_self_of_isHermitian_of_mul_eq_self (hρpos s).isHermitian
      (hQherm s) (hQρ s)
  have hQorthogonal : ∀ s t, s ≠ t → Q s * Q t = 0 := by
    intro s t hst
    change firstSiteMatrix (P s) L * firstSiteMatrix (P t) L = 0
    rw [firstSiteMatrix_mul_firstSiteMatrix, hPorthogonal hst]
    ext u v
    simp [firstSiteMatrix]
  have hsum : reducedBlockState M N (L + 1) hL =
      ∑ s, (p s : ℂ) • ρ s := by
    exact reducedBlockState_eq_sum_localOrthogonalSectorProbability_smul
      M K multiplicity hL hM hMtrace hSectorTrace
  have hadd := vonNeumannEntropy_eq_sum_of_pairwise_annihilating_supports
    (reducedBlockState M N (L + 1) hL)
    (reducedBlockState_isHermitian M N (L + 1) hL (hMpdo N hN))
    (fun s ↦ (p s : ℂ) • ρ s) Q
    (fun s ↦ ((hρpos s).smul (a := (p s : ℂ))
      (by exact_mod_cast (hp s).le)).isHermitian)
    hsum (fun s ↦ ⟨by rw [Matrix.mul_smul, hQρ],
      by rw [Matrix.smul_mul, hρQ]⟩) hQorthogonal
  calc
    blockEntropy M N (L + 1) hL (hMpdo N hN) =
        ∑ s, vonNeumannEntropy ((p s : ℂ) • ρ s)
          (((hρpos s).smul (a := (p s : ℂ))
            (by exact_mod_cast (hp s).le)).isHermitian) := hadd
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simpa only [p, ρ, blockEntropy, add_comm] using
        vonNeumannEntropy_smul (hρpos s) (hρtrace s) (p s)

/-- A finite local orthogonal sum of saturated-area-law sectors satisfies the
saturated area law.

This is the conditional final sentence of CPSV16, Appendix C.2, Proposition
`prop4to2`, lines 1806--1808.  It does not formalize the printed assertion that
the GSNNCH form alone implies SAL: the proof there applies the single-sector
Proposition `4to2`, whose hypotheses include ZCL.  The omission and the later
conditional statement are recorded in
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`.

The support hypothesis states the mathematical content of locality needed in
the entropy argument.  In particular, it is independent of the BNT projectors
whose present construction assumes SAL.

The support condition starts at chain length two.  This is sufficient because
the mutual-information comparison in `IsSAL` has `1 ≤ L < N / 2`, and hence
only invokes marginal support when `N ≥ 4`.

**Scope restriction (exact local sum):** The theorem assumes the exact local
orthogonal-sum equality at every positive chain length and is supplied with
one-site projections whose tensor extensions support every nonempty normalized
sector marginal on chains of length at least two.  This restriction is
documented in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem isSAL_of_localOrthogonalSum
    (M : MPOTensor d D) (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) (P : Fin g → Matrix (Fin d) (Fin d) ℂ)
    [Nonempty (Fin g)]
    (hmultiplicity : ∀ s, 0 < multiplicity s)
    (hP : ∀ s, IsOrthogonalProjection (P s))
    (hPorthogonal : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hM : ∀ (N : ℕ), 0 < N →
      mpo M N = ∑ s : Fin g, (multiplicity s : ℂ) • mpo (K s) N)
    (hsupport : ∀ (s : Fin g) (N L : ℕ), 2 ≤ N → (hL : L + 1 ≤ N) →
      firstSiteMatrix (P s) L * reducedBlockState (K s) N (L + 1) hL =
        reducedBlockState (K s) N (L + 1) hL)
    (hSectorSAL : ∀ s, IsSAL (K s)) :
    IsSAL M := by
  classical
  let hSectorMpdo : ∀ s, IsMPDO (K s) := fun s ↦ Classical.choose (hSectorSAL s)
  have hSectorTrace : ∀ (N : ℕ), 0 < N → ∀ s,
      0 < Matrix.trace (mpo (K s) N) := by
    intro N hN s
    apply Matrix.PosSemidef.trace_pos_of_ne_zero (hSectorMpdo s N hN)
    intro hzero
    exact (Classical.choose_spec (hSectorSAL s)).1 N hN (by
      rw [hzero, Matrix.trace_zero])
  let hMpdo : IsMPDO M := by
    intro N hN
    rw [hM N hN]
    refine Finset.sum_induction _ Matrix.PosSemidef (fun A B hA hB ↦ hA.add hB)
      Matrix.PosSemidef.zero (fun s _ ↦ ?_)
    exact (hSectorMpdo s N hN).smul
      (by exact_mod_cast Nat.zero_le (multiplicity s))
  have hMtrace : ∀ (N : ℕ), 0 < N → 0 < Matrix.trace (mpo M N) := by
    intro N hN
    have hre : 0 < (Matrix.trace (mpo M N)).re := by
      rw [hM N hN, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_pos'
      · intro s _
        rw [Matrix.trace_smul]
        norm_num
        exact mul_nonneg (by exact_mod_cast Nat.zero_le (multiplicity s))
          (RCLike.nonneg_iff.mp (hSectorMpdo s N hN).trace_nonneg).1
      · let s : Fin g := Classical.choice inferInstance
        refine ⟨s, Finset.mem_univ s, ?_⟩
        rw [Matrix.trace_smul]
        norm_num
        exact mul_pos (by exact_mod_cast hmultiplicity s)
          (RCLike.pos_iff.mp (hSectorTrace N hN s)).1
    apply RCLike.pos_iff.mpr
    exact ⟨hre, (RCLike.nonneg_iff.mp (hMpdo N hN).trace_nonneg).2⟩
  refine ⟨hMpdo, fun N hN ↦ ne_of_gt (hMtrace N hN), ?_⟩
  intro N L hL hLN
  let p : Fin g → ℝ := fun s ↦
    localOrthogonalSectorProbability M K multiplicity N s
  have hMI (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N / 2) :
      mutualInfoChain M N m (hmN.trans (Nat.div_le_self N 2))
          (hMpdo N (by omega)) =
        ∑ s : Fin g, Real.negMulLog (p s) +
          ∑ s : Fin g, p s *
            mutualInfoChain (K s) N m (hmN.trans (Nat.div_le_self N 2))
              (hSectorMpdo s N (by omega)) := by
    have hEntropy (l : ℕ) (hlpos : 0 < l) (hlN : l ≤ N) :
        blockEntropy M N l hlN (hMpdo N (by omega)) =
          ∑ s : Fin g,
            (Real.negMulLog
                (localOrthogonalSectorProbability M K multiplicity N s) +
              localOrthogonalSectorProbability M K multiplicity N s *
                blockEntropy (K s) N l hlN (hSectorMpdo s N (by omega))) := by
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlpos)
      exact blockEntropy_eq_sum_localOrthogonalSectorProbability
        M K multiplicity P hmultiplicity hP hPorthogonal hMpdo hSectorMpdo
        (N := N) (L := l) (by omega) hlN (hM N (by omega))
        (hMtrace N (by omega)) (hSectorTrace N (by omega))
        (fun s ↦ hsupport s N l (by omega) hlN)
    have hEm := hEntropy m (by omega) (hmN.trans (Nat.div_le_self N 2))
    have hEcomp := hEntropy (N - m) (by omega) (Nat.sub_le N m)
    have hEN := hEntropy N (by omega) (le_refl N)
    simp only [mutualInfoChain]
    rw [hEm, hEcomp, hEN]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    simp only [p]
    ring
  rw [hMI L hL (Nat.le_of_lt hLN), hMI (L + 1) (by omega) (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact (Classical.choose_spec (hSectorSAL s)).2 N L hL hLN

end MPOTensor
