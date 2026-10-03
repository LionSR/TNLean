/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Equivalence
import TNLean.MPS.MPU.KetLeftMul
import TNLean.MPS.MPU.KetLeftMulCanonicalForm
import TNLean.MPS.Core.Blocking

/-!
# Physical left actions on symmetry-preserving MPU paths

An involutive one-site unitary acts continuously on local tensors. If this
action carries one operator symmetry to another, it also carries continuous
paths satisfying the first symmetry to paths satisfying the second.

**Scope restriction (fixed virtual dimension):** These results concern paths
in one fixed ambient virtual dimension, as in the current strict-equivalence
definition. They do not compare unequal raw virtual dimensions. See
`docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-- A fixed one-site left action is continuous on local MPO tensors.

Source: arXiv:1703.09188, proof of Lemma `lemma:sym-trafo-swap`, lines 2076--2084. -/
theorem continuous_ketLeftMul (Q : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun W : MPOTensor d D => W.ketLeftMul Q) := by
  unfold ketLeftMul
  fun_prop

private theorem ketLeftMul_comp (W : MPOTensor d D)
    (P Q : Matrix (Fin d) (Fin d) ℂ) :
    (W.ketLeftMul P).ketLeftMul Q = W.ketLeftMul (Q * P) := by
  ext i j a b
  simp only [ketLeftMul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- An involutive one-site left action is an involution on local tensors.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem ketLeftMul_involutive (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q * Q = 1) :
    Function.Involutive (fun W : MPOTensor d D => W.ketLeftMul Q) := by
  intro W
  change (W.ketLeftMul Q).ketLeftMul Q = W
  rw [ketLeftMul_comp, hQ]
  ext i j a b
  simp [ketLeftMul, Matrix.one_apply]

private theorem joinedIn_ketLeftMul
    (S T : FiniteChainOperatorSymmetry d)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hST : ∀ W : MPOTensor d D,
      IsInvariantUnderSymmetry S W → IsInvariantUnderSymmetry T (W.ketLeftMul Q))
    {U V : MPOTensor d D}
    (h : JoinedIn {W : MPOTensor d D | IsMPU W ∧ IsInvariantUnderSymmetry S W} U V) :
    JoinedIn {W : MPOTensor d D | IsMPU W ∧ IsInvariantUnderSymmetry T W}
      (U.ketLeftMul Q) (V.ketLeftMul Q) := by
  refine (h.map (continuous_ketLeftMul Q).continuousOn).mono ?_
  rintro _ ⟨W, hW, rfl⟩
  exact ⟨hW.1.ketLeftMul hQ, hST W hW.2⟩

/-- An involutive unitary left action identifies the two symmetry-preserving
path relations whenever it identifies their invariant tensors.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem joinedIn_isMPU_isInvariantUnderSymmetry_iff_ketLeftMul
    (S T : FiniteChainOperatorSymmetry d)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1)
    (hST : ∀ W : MPOTensor d D,
      IsInvariantUnderSymmetry S W ↔ IsInvariantUnderSymmetry T (W.ketLeftMul Q))
    (U V : MPOTensor d D) :
    JoinedIn {W : MPOTensor d D | IsMPU W ∧ IsInvariantUnderSymmetry S W} U V ↔
      JoinedIn {W : MPOTensor d D | IsMPU W ∧ IsInvariantUnderSymmetry T W}
        (U.ketLeftMul Q) (V.ketLeftMul Q) := by
  constructor
  · exact joinedIn_ketLeftMul S T Q hQ (fun W => (hST W).mp)
  · intro h
    have hTS : ∀ W : MPOTensor d D,
        IsInvariantUnderSymmetry T W → IsInvariantUnderSymmetry S (W.ketLeftMul Q) := by
      intro W hW
      apply (hST (W.ketLeftMul Q)).mpr
      simpa only [ketLeftMul_involutive Q hQQ W] using hW
    simpa only [ketLeftMul_involutive Q hQQ U, ketLeftMul_involutive Q hQQ V] using
      joinedIn_ketLeftMul T S Q hQ hTS h

/-- An involutive one-site unitary identifies strict symmetry-preserving
equivalence for two symmetries whose invariant tensors it identifies.
Canonical form is preserved at both endpoints; intermediate tensors need
only generate MPUs and satisfy the corresponding symmetry.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_iff_ketLeftMul
    (S T : FiniteChainOperatorSymmetry d)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1)
    (hST : ∀ W : MPOTensor d D,
      IsInvariantUnderSymmetry S W ↔ IsInvariantUnderSymmetry T (W.ketLeftMul Q))
    (U V : MPOTensor d D) :
    StrictlyEquivalentUnderSymmetry S U V rfl ↔
      StrictlyEquivalentUnderSymmetry T (U.ketLeftMul Q) (V.ketLeftMul Q) rfl := by
  change (MPSTensor.IsMPUCanonicalForm U.toMPSTensor ∧
    MPSTensor.IsMPUCanonicalForm V.toMPSTensor ∧
    JoinedIn {W : MPOTensor d D | IsMPU W ∧ IsInvariantUnderSymmetry S W} U V) ↔ _
  constructor
  · intro h
    refine ⟨isMPUCanonicalForm_ketLeftMul U h.1 Q hQ,
      isMPUCanonicalForm_ketLeftMul V h.2.1 Q hQ, ?_⟩
    exact (joinedIn_isMPU_isInvariantUnderSymmetry_iff_ketLeftMul S T Q hQ hQQ hST U V).mp
      h.2.2
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ketLeftMul_involutive Q hQQ U] using
        isMPUCanonicalForm_ketLeftMul (U.ketLeftMul Q) h.1 Q hQ
    · simpa only [ketLeftMul_involutive Q hQQ V] using
        isMPUCanonicalForm_ketLeftMul (V.ketLeftMul Q) h.2.1 Q hQ
    · exact (joinedIn_isMPU_isInvariantUnderSymmetry_iff_ketLeftMul S T Q hQ hQQ hST U V).mpr
        h.2.2

private theorem evalWord_ketLeftMul_ofFn
    (W : MPOTensor d D) (Q : Matrix (Fin d) (Fin d) ℂ) :
    ∀ (N : ℕ) (s t : Fin N → Fin d),
      evalWord (W.ketLeftMul Q) (List.ofFn s) (List.ofFn t) =
        ∑ r : Fin N → Fin d,
          (∏ n : Fin N, Q (s n) (r n)) • evalWord W (List.ofFn r) (List.ofFn t) := by
  intro N
  induction N with
  | zero =>
      intro s t
      simp
  | succ N ih =>
      intro s t
      rw [List.ofFn_succ, List.ofFn_succ, evalWord_cons, ketLeftMul,
        ih (fun n => s n.succ) (fun n => t n.succ)]
      rw [Finset.sum_mul_sum]
      rw [← (Fin.consEquiv fun _ : Fin (N + 1) => Fin d).sum_comp
        (fun r : Fin (N + 1) → Fin d =>
          (∏ n : Fin (N + 1), Q (s n) (r n)) •
            evalWord W (List.ofFn r) (t 0 :: List.ofFn fun n => t n.succ))]
      simp [← Fintype.sum_prod_type', Fin.consEquiv, Fin.prod_univ_succ,
        List.ofFn_succ, evalWord_cons, smul_smul, mul_comm]

/-- Blocking a tensor after a one-site ket action is the ket action of the
corresponding tensor power on the blocked tensor. This includes length zero.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085,
and Definition `def:equivalent-symmetry`, lines 1356--1366. -/
theorem blockTensor_ketLeftMul (W : MPOTensor d D)
    (Q : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    blockTensor (W.ketLeftMul Q) k = (blockTensor W k).ketLeftMul (MPSTensor.blockKron k Q) := by
  funext i j
  change evalWord (W.ketLeftMul Q)
    (List.ofFn (MPSTensor.decodeBlock d k i)) (List.ofFn (MPSTensor.decodeBlock d k j)) =
      ∑ l : Fin (MPSTensor.blockPhysDim d k),
        MPSTensor.blockKron k Q i l •
          evalWord W (List.ofFn (MPSTensor.decodeBlock d k l))
            (List.ofFn (MPSTensor.decodeBlock d k j))
  rw [evalWord_ketLeftMul_ofFn]
  exact (Fintype.sum_equiv (MPSTensor.decodeBlockEquiv d k) _ _ fun l => rfl).symm

/-- The one-site involution also identifies strict symmetry-preserving
equivalence after some common positive blocking length. The symmetry
correspondence is required on all tensors in each blocked physical space.
No ancilla action or unequal-bond comparison is asserted.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085,
and Definition `def:equivalent-symmetry`, lines 1356--1366. -/
theorem exists_strictlyEquivalentUnderSymmetry_blockTensor_iff_ketLeftMul
    (S T : FiniteChainOperatorSymmetry d)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1)
    (hST : ∀ k : ℕ, 0 < k → ∀ W : MPOTensor (MPSTensor.blockPhysDim d k) D,
      IsInvariantUnderSymmetry (S.block k) W ↔
        IsInvariantUnderSymmetry (T.block k) (W.ketLeftMul (MPSTensor.blockKron k Q)))
    (U V : MPOTensor d D) :
    (∃ k > 0, StrictlyEquivalentUnderSymmetry (S.block k)
      (blockTensor U k) (blockTensor V k) rfl) ↔
      (∃ k > 0, StrictlyEquivalentUnderSymmetry (T.block k)
        (blockTensor (U.ketLeftMul Q) k) (blockTensor (V.ketLeftMul Q) k) rfl) := by
  refine exists_congr fun k => and_congr_right fun hk => ?_
  have hQk : MPSTensor.blockKron k Q ∈
      Matrix.unitaryGroup (Fin (MPSTensor.blockPhysDim d k)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact MPSTensor.blockKron_mul_conjTranspose k Q
      (by simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hQ)
  have hQQk : MPSTensor.blockKron k Q * MPSTensor.blockKron k Q = 1 := by
    rw [← MPSTensor.blockKron_mul, hQQ, MPSTensor.blockKron_one]
  simpa only [blockTensor_ketLeftMul] using
    strictlyEquivalentUnderSymmetry_iff_ketLeftMul (S.block k) (T.block k)
      (MPSTensor.blockKron k Q) hQk hQQk (hST k hk) (blockTensor U k) (blockTensor V k)

end MPOTensor
