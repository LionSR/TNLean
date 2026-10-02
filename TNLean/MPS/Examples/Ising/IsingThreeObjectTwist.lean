/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.Examples.Ising.IsingFusionAlgebraOneSigma
import TNLean.MPS.Examples.Ising.IsingFusionAlgebraPsiSigma
import TNLean.MPS.Examples.Ising.IsingFusionAlgebraSigma
import TNLean.MPS.Examples.Ising.IsingSectorAction

/-!
# The full three-object Ising bond object

The project construction recorded in
`Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1.4, inserts
`Θ₃ = 5 A₁ ⊕ 3 Aψ ⊕ 2 Aσ` before the strand `√2 Aσ`. Its fusion has four
weighted normal blocks, not three: `5 (√2 Aσ)`, `3 (√2 Aσ)`, `2 (√2 A₁)`,
and `2 (√2 Aψ)`. The last two blocks come from `σ × σ = 1 + ψ`, the Ising
fusion rule of arXiv:1511.08090, Appendix D.2, lines 1305–1323 in the local
source. This is a project-derived application of those tensors; the weighted
bond object is not a theorem of that paper.

The periodic operator identity follows from the three existing fusion rules.
Every nonempty pair-alphabet word is a pair of physical configurations, so
that identity gives the word-trace identity. The multi-block asymmetric
compression theorem then provides the four-block compression, with
`40 = 4 + 4 + 3 + 3 + 26`.

**Scope restriction (sitewise bond-object calculation):** these results concern
`Θ₃ ⋆ (√2 Aσ)` of bond dimension forty, not the full round-45B boundary
tensors of bond dimensions forty-eight and sixty-four. The distinction and
the remaining full-tensor proof are recorded in
`docs/paper-gaps/tnlean_ising_three_object_twist_scope.tex`. No vanishing-remainder
claim is made for the compression chosen here.

## References

* Bultinck, Mariën, Williamson, Şahinoğlu, Haegeman and Verstraete,
  *Anyons and matrix product operator algebras*, arXiv:1511.08090,
  Appendix D.2 (the Ising fusion data).
* Cirac, Pérez-García, Schuch and Verstraete,
  *Matrix product density operators: Renormalization fixed points and boundary theories*,
  arXiv:1606.00608, Theorem 4.14 and the question following it, lines 995–1010
  (the motivation for the project construction).
* Project construction record: `Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §1.4.
-/

open scoped Matrix Kronecker

namespace IsingTwist

open MPSTensor

/-- The three weighted summands in the bond ordering of data file §1.4. -/
theorem thetaThree_eq_directSum : thetaThree = MPOTensor.directSum ((5 : ℂ) • isingOne)
    (MPOTensor.directSum ((3 : ℂ) • isingPsi) ((Real.sqrt 2 : ℂ) • isingSigma)) := by
  ext h h' i j
  simp only [thetaThree, thetaThreeZ, complexOfZsqrt2_apply, MPOTensor.directSum,
    Matrix.submatrix_apply, Equiv.trans_apply, Equiv.sumCongr_apply,
    Pi.smul_apply]
  rcases (finSumFinEquiv (m := 3) (n := 7)).symm i with a | a <;>
    rcases (finSumFinEquiv (m := 3) (n := 7)).symm j with b | b
  · simp [isingOne, map_ofNat]
  · simp
  · simp
  · simp only [Matrix.fromBlocks_apply₂₂]
    rcases ha : (finSumFinEquiv (m := 3) (n := 4)).symm a with a | a <;>
      rcases hb : (finSumFinEquiv (m := 3) (n := 4)).symm b with b | b <;>
      simp [ha, hb, isingPsi, isingSigma, map_ofNat]

/-- The full three-object operator fusion (data file §1.4): the hidden `σ` object
feeds the `1` and `ψ` channels, while the other two objects both feed `σ`. -/
theorem thetaThree_mpo_mul_isingSigma {L : ℕ} (hL : 0 < L) :
    MPOTensor.mpo thetaThree L * MPOTensor.mpo isingSigma L =
      ((5 : ℂ) ^ L + 3 ^ L) • MPOTensor.mpo isingSigma L +
        (2 * (Real.sqrt 2 : ℂ)) ^ L •
          (MPOTensor.mpo isingOne L + MPOTensor.mpo isingPsi L) := by
  rw [thetaThree_eq_directSum, MPOTensor.mpo_directSum, MPOTensor.mpo_directSum,
    MPOTensor.mpo_smul, MPOTensor.mpo_smul, MPOTensor.mpo_smul,
    add_mul, add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
    isingOne_mul_isingSigma hL, isingPsi_mul_isingSigma hL, isingSigma_mul_isingSigma hL]
  rw [← add_assoc, ← add_smul, smul_smul, ← mul_pow, mul_comm (Real.sqrt 2 : ℂ) 2]

/-- The hundred-letter tensor of `Θ₃ ⋆ (√2 Aσ)` (data file §1.4). -/
noncomputable def isingBondObjectThree : MPSTensor 100 40 :=
  (MPOTensor.mulTensor thetaThree isingSigma).toMPSTensor

/-- The four-channel word-trace identity of data file §1.4, at every positive length. -/
theorem isingBondObjectThree_trace_evalWord (w : List (Fin 100)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord isingBondObjectThree w) =
      ((5 : ℂ) ^ w.length + 3 ^ w.length) *
          Matrix.trace (Kraus.evalWord isingSigma.toMPSTensor w) +
        (2 * (Real.sqrt 2 : ℂ)) ^ w.length *
          (Matrix.trace (Kraus.evalWord isingOne.toMPSTensor w) +
            Matrix.trace (Kraus.evalWord isingPsi.toMPSTensor w)) := by
  let p : Fin w.length → Fin 10 × Fin 10 := fun i => finProdFinEquiv.symm (w.get i)
  have hp : (List.ofFn fun i => finProdFinEquiv ((p i).1, (p i).2)) = w := by
    simpa only [p, Prod.mk.eta, Equiv.apply_symm_apply] using List.ofFn_get w
  have h := thetaThree_mpo_mul_isingSigma (List.length_pos_of_ne_nil hw)
  rw [← MPOTensor.mpo_mulTensor] at h
  have he := congrFun (congrFun h (fun i => (p i).1)) (fun i => (p i).2)
  simpa only [isingBondObjectThree, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    MPOTensor.mpo_apply_toMPSTensor, hp] using he

/-- Dimensions of the two `σ` slots and the `1, ψ` slots (data file §1.4). -/
def isingThreeBlockDim : Fin 4 → ℕ := ![4, 4, 3, 3]

/-- The four weighted targets of the three-object fusion (data file §1.4). -/
noncomputable def isingThreeTargets : (s : Fin 4) → MPSTensor 100 (isingThreeBlockDim s)
  | 0 => (5 : ℂ) • isingSigma.toMPSTensor
  | 1 => (3 : ℂ) • isingSigma.toMPSTensor
  | 2 => (2 * (Real.sqrt 2 : ℂ)) • isingOne.toMPSTensor
  | 3 => (2 * (Real.sqrt 2 : ℂ)) • isingPsi.toMPSTensor

/-- Four-block asymmetric compression of the full bond-object product.
This applies the P5 note, Theorem 7.7, to the word identity of data file §1.4. -/
theorem isingBondObjectThree_compression_exists :
    Nonempty (MultiBlockCompression isingBondObjectThree Finset.univ isingThreeTargets) := by
  apply exists_multiBlockCompression_of_isNormal
  · intro s _
    fin_cases s <;> dsimp [isingThreeTargets]
    · exact (isNormal_smul_iff (by norm_num) _).2 isingSigma_isNormal
    · exact (isNormal_smul_iff (by norm_num) _).2 isingSigma_isNormal
    · apply (isNormal_smul_iff _ _).2 isingOne_isNormal
      exact mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num)))
    · apply (isNormal_smul_iff _ _).2 isingPsi_isNormal
      exact mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by norm_num)))
  · intro s _
    fin_cases s <;> decide
  · intro w hw
    have hscale {D : ℕ} (c : ℂ) (A : MPSTensor 100 D) :
        Matrix.trace (Kraus.evalWord (c • A) w) =
          c ^ w.length * Matrix.trace (Kraus.evalWord A w) := by
      rw [show c • A = (fun i => c • A i) from rfl,
        Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
    rw [isingBondObjectThree_trace_evalWord w hw]
    simp only [Nat.reduceMul, isingThreeTargets, Fin.sum_univ_succ, Fin.isValue,
      Fin.succ, Nat.reduceAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.mk_one,
      Fin.reduceFinMk, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    dsimp +instances [isingThreeBlockDim]
    rw [hscale 5 isingSigma.toMPSTensor, hscale 3 isingSigma.toMPSTensor,
      hscale (2 * (Real.sqrt 2 : ℂ)) isingOne.toMPSTensor,
      hscale (2 * (Real.sqrt 2 : ℂ)) isingPsi.toMPSTensor]
    ring

/-- A four-block compression supplied by the asymmetric compression theorem. -/
noncomputable def isingThreeCompression :
    MultiBlockCompression isingBondObjectThree Finset.univ isingThreeTargets :=
  Classical.choice isingBondObjectThree_compression_exists

/-- The active targets occupy fourteen of the forty auxiliary dimensions. -/
theorem isingBondObjectThree_dim_eq : (40 : ℕ) = 14 + isingThreeCompression.z := by
  simpa [isingThreeBlockDim, Fin.sum_univ_succ, Fin.succ] using isingThreeCompression.dim_eq

/-- The compression has twenty-six one-dimensional zero diagonal slots. -/
theorem isingBondObjectThree_z_eq : isingThreeCompression.z = 26 := by
  have h := isingBondObjectThree_dim_eq
  omega

end IsingTwist
