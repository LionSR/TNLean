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

**Scope restriction (shared ambient virtual dimension):** The strict-equivalence
definition connects padded tensors in a common ambient virtual dimension. The
symmetry correspondence transported here is therefore required at every bond
dimension, not only the raw one. See
`docs/paper-gaps/mpu_equivalence_fixed_bond.tex`.

**Scope restriction (no identity ancillas):** The equivalence comparisons
`strictlyEquivalentUnderSymmetry_iff_ketLeftMul` and
`exists_strictlyEquivalentUnderSymmetry_blockTensor_iff_ketLeftMul` compare
strict equivalence, before and after common positive blocking, without
adjoining identity ancillas. The source definition of equivalence under a
symmetry also permits identity ancillas (arXiv:1703.09188, Definition
`def:equivalent-symmetry`, lines 1356--1366), and transporting the symmetry
action to the enlarged physical dimension is not determined by the source.
See `docs/paper-gaps/mpu_symmetry_ancilla_transport.tex`.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D Da Db : ℕ}

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
    (hST : ∀ {E : ℕ} (W : MPOTensor d E),
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

/-- The one-site ket action commutes with adjoining unused bond directions:
both sides left-multiply every physical slice by `Q` inside the same bond
block. -/
private theorem ketLeftMul_padBond (U : MPOTensor d D)
    (Q : Matrix (Fin d) (Fin d) ℂ) (D' : ℕ) (h : D ≤ D') :
    (padBond U D' h).ketLeftMul Q = padBond (U.ketLeftMul Q) D' h := by
  funext i j
  simp only [ketLeftMul, padBond]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Reindexing both physical legs by the trivial equivalence `(finCongr rfl).symm`
is the identity. -/
private theorem reindexPhysical_finCongr_rfl (U : MPOTensor d D) :
    reindexPhysical (finCongr (rfl : d = d)).symm U = U := by
  funext i j
  simp [reindexPhysical, finCongr_refl]

/-- An involutive one-site unitary identifies strict symmetry-preserving
equivalence for two symmetries whose invariant tensors it identifies at every
bond dimension. Canonical form is preserved at both endpoints; intermediate
tensors need only generate MPUs and satisfy the corresponding symmetry.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_iff_ketLeftMul
    (S T : FiniteChainOperatorSymmetry d)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1)
    (hST : ∀ {E : ℕ} (W : MPOTensor d E),
      IsInvariantUnderSymmetry S W ↔ IsInvariantUnderSymmetry T (W.ketLeftMul Q))
    (U : MPOTensor d Da) (V : MPOTensor d Db) :
    StrictlyEquivalentUnderSymmetry S U V rfl ↔
      StrictlyEquivalentUnderSymmetry T (U.ketLeftMul Q) (V.ketLeftMul Q) rfl := by
  unfold StrictlyEquivalentUnderSymmetry
  constructor
  · rintro ⟨hU, hV, D', ha, hb, hpath⟩
    rw [reindexPhysical_finCongr_rfl] at hpath
    refine ⟨isMPUCanonicalForm_ketLeftMul U hU Q hQ,
      isMPUCanonicalForm_ketLeftMul V hV Q hQ, D', ha, hb, ?_⟩
    rw [reindexPhysical_finCongr_rfl, ← ketLeftMul_padBond, ← ketLeftMul_padBond]
    exact (joinedIn_isMPU_isInvariantUnderSymmetry_iff_ketLeftMul S T Q hQ hQQ hST
      (padBond U D' ha) (padBond V D' hb)).mp hpath
  · rintro ⟨hU', hV', D', ha, hb, hpath⟩
    rw [reindexPhysical_finCongr_rfl, ← ketLeftMul_padBond, ← ketLeftMul_padBond] at hpath
    refine ⟨?_, ?_, D', ha, hb, ?_⟩
    · simpa only [ketLeftMul_involutive Q hQQ U] using
        isMPUCanonicalForm_ketLeftMul (U.ketLeftMul Q) hU' Q hQ
    · simpa only [ketLeftMul_involutive Q hQQ V] using
        isMPUCanonicalForm_ketLeftMul (V.ketLeftMul Q) hV' Q hQ
    · rw [reindexPhysical_finCongr_rfl]
      exact (joinedIn_isMPU_isInvariantUnderSymmetry_iff_ketLeftMul S T Q hQ hQQ hST
        (padBond U D' ha) (padBond V D' hb)).mpr hpath

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
No ancilla action is asserted.

Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085,
and Definition `def:equivalent-symmetry`, lines 1356--1366. -/
theorem exists_strictlyEquivalentUnderSymmetry_blockTensor_iff_ketLeftMul
    (S T : FiniteChainOperatorSymmetry d)
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1)
    (hST : ∀ k : ℕ, 0 < k → ∀ {E : ℕ} (W : MPOTensor (MPSTensor.blockPhysDim d k) E),
      IsInvariantUnderSymmetry (S.block k) W ↔
        IsInvariantUnderSymmetry (T.block k) (W.ketLeftMul (MPSTensor.blockKron k Q)))
    (U : MPOTensor d Da) (V : MPOTensor d Db) :
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
