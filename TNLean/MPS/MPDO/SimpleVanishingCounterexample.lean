/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Examples
import TNLean.MPS.MPDO.SourceSimpleTensor

/-!
# Normalized simplicity with a vanishing positive-length MPO

The one-letter tensor whose sole local matrix is $\operatorname{diag}(1,-1)$
generates the scalar closed MPO $1+(-1)^N$. It is positive semidefinite at every
positive length but vanishes at odd lengths. After blocking two sites, both
virtual phases become $1$, and the resulting tensor has an explicit normalized
BNT canonical form with a nonnilpotent scalar representative.

This tensor satisfies both normalized simplicity and the source-faithful
Definition 4.7 predicate. It separates those predicates from the explicitly
stronger `MPOTensor.IsNonvanishingSourceSimple` interface because its one-site
closed MPO vanishes.

## Main results

* `MPOTensor.SimpleVanishingCounterexample.mpo_eq`: the exact closed-MPO formula.
* `MPOTensor.SimpleVanishingCounterexample.M_isMPDO`: positivity at every positive length.
* `MPOTensor.SimpleVanishingCounterexample.mpo_one_eq_zero`: the one-site MPO vanishes.
* `MPOTensor.SimpleVanishingCounterexample.M_isSimple`: normalized simplicity after blocking
  two sites.
* `MPOTensor.SimpleVanishingCounterexample.M_isSourceSimple`: source-faithful Definition 4.7
  simplicity.
* `MPOTensor.SimpleVanishingCounterexample.M_not_isNonvanishingSourceSimple`: failure of the
  strengthened positive-length nonvanishing interface.
* `M_isSimple_and_isSourceSimple_and_not_isNonvanishingSourceSimple`: deprecated
  transition theorem stating the three preceding conclusions together.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.SimpleVanishingCounterexample

/-- The one-letter MPO whose sole local matrix is $\operatorname{diag}(1,-1)$.
It reuses the phase-flip tensor from the repeated-phase counterexample. -/
def M : MPOTensor 1 2 := fun _ _ => MPSTensor.phaseFlipTensor 0

/-- The unique local matrix of `M` is the diagonal sign-flip matrix. -/
theorem M_apply (i j : Fin 1) :
    M i j = !![1, 0; 0, -1] := by
  fin_cases i
  fin_cases j
  rfl

private lemma evalWord_M (is js : List (Fin 1)) (h : is.length = js.length) :
    evalWord M is js = !![1, 0; 0, (-1 : ℂ) ^ is.length] := by
  induction is generalizing js with
  | nil =>
      rw [List.length_nil, eq_comm, List.length_eq_zero_iff] at h
      subst js
      ext a b
      fin_cases a <;> fin_cases b <;> simp [evalWord]
  | cons i is ih =>
      cases js with
      | nil => simp at h
      | cons j js =>
          have hlen : is.length = js.length := by simpa using h
          rw [evalWord_cons, ih js hlen]
          ext a b
          fin_cases i
          fin_cases j
          fin_cases a <;> fin_cases b <;>
            simp [M, MPSTensor.phaseFlipTensor, Matrix.mul_apply, pow_succ]

/-- The exact finite-chain formula for the phase-cancelling example:
$\rho^{(N)}(M)=(1+(-1)^N)I$ on the one-dimensional physical Hilbert space. -/
theorem mpo_eq (N : ℕ) :
    mpo M N = (1 + (-1 : ℂ) ^ N) • (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ) := by
  ext σ τ
  have hστ : σ = τ := Subsingleton.elim _ _
  subst τ
  simp only [mpo_apply, mpoMatrixEntry]
  rw [evalWord_M _ _ (by simp)]
  simp [Matrix.trace]

/-- The phase-cancelling tensor generates positive semidefinite closed MPOs at
every positive length; even lengths give $2I$ and odd lengths give $0$. -/
theorem M_isMPDO : IsMPDO M := by
  intro N _hN
  rw [mpo_eq]
  rcases neg_one_pow_eq_or ℂ N with h | h
  · rw [h, show (1 + 1 : ℂ) = 2 by norm_num]
    have hOne : (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ).PosSemidef :=
      Matrix.PosSemidef.one
    exact hOne.smul (α := ℂ) (by norm_num)
  · rw [h, show (1 + -1 : ℂ) = 0 by norm_num]
    simpa only [zero_smul] using
      (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ).PosSemidef)

/-- The generated MPO already vanishes at the positive chain length $N=1$. -/
theorem mpo_one_eq_zero : mpo M 1 = 0 := by
  rw [mpo_eq]
  norm_num

private lemma scalarUnitTensor_evalWord (w : List (Fin 1)) :
    MPSTensor.evalWord MPSTensor.scalarUnitTensor w = 1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [MPSTensor.evalWord_cons, ih]
      simp [MPSTensor.scalarUnitTensor]

private theorem signFlip_isBNTCanonicalForm :
    MPSTensor.IsBNTCanonicalForm
      (MPSTensor.SectorBNT.Examples.signFlipDecomp MPSTensor.scalarUnitTensor) := by
  refine {
    basis_dim_pos := by simp
    basis_irreducible := fun _ =>
      MPSTensor.isIrreducibleTensor_of_bondDim_one MPSTensor.scalarUnitTensor
    basis_left_canonical := by
      intro j
      simp [MPSTensor.IsLeftCanonical, MPSTensor.scalarUnitTensor]
    basis_normalized_self_overlap := by
      intro j
      simp [MPSTensor.mpvOverlap, MPSTensor.mpv, scalarUnitTensor_evalWord, Matrix.trace]
    bnt_data := by
      refine ⟨0, ?_⟩
      intro N hN
      apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
      intro hzero
      have h := congrArg
        (fun v : MPSTensor.MPVSpace 1 N => v (fun _ : Fin N => (0 : Fin 1))) hzero
      simp [MPSTensor.mpvState_apply, MPSTensor.mpv, scalarUnitTensor_evalWord,
        Matrix.trace] at h
    basis_distinct := by
      intro j k hjk
      exact absurd (Subsingleton.elim j k) hjk
    weight_norm_le_one := by
      intro j q
      change ‖(if q = 0 then (1 : ℂ) else -1)‖ ≤ 1
      split_ifs <;> simp
    weight_unit_exists := by
      refine ⟨0, 0, ?_⟩
      change ‖(if (0 : Fin 2) = 0 then (1 : ℂ) else -1)‖ = 1
      simp }

private noncomputable def S : MPSTensor.SectorDecomposition
    (MPSTensor.blockPhysDim 1 2 * MPSTensor.blockPhysDim 1 2) where
  basisCount := 1
  basisDim := fun _ => 1
  basis := fun _ => MPSTensor.scalarUnitTensor
  sectors :=
    { copies := fun _ => 2
      copies_pos := fun _ => by norm_num
      weight := fun _ _ => 1
      weight_ne_zero := fun _ _ => one_ne_zero }

private theorem S_isBNTCanonicalForm : MPSTensor.IsBNTCanonicalForm S := by
  refine {
    basis_dim_pos := by simp [S]
    basis_irreducible := fun _ =>
      MPSTensor.isIrreducibleTensor_of_bondDim_one MPSTensor.scalarUnitTensor
    basis_left_canonical := by
      intro j
      change ∑ _ : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * 1 = 1
      simp only [Matrix.conjTranspose_one, Fin.sum_univ_one]
      exact Matrix.one_mul 1
    basis_normalized_self_overlap :=
      signFlip_isBNTCanonicalForm.basis_normalized_self_overlap
    bnt_data := signFlip_isBNTCanonicalForm.bnt_data
    basis_distinct := by
      change ∀ j k : Fin 1, j ≠ k → _
      intro j k hjk
      exact absurd (Subsingleton.elim j k) hjk
    weight_norm_le_one := by
      change ∀ (_ : Fin 1) (_ : Fin 2), ‖(1 : ℂ)‖ ≤ 1
      simp
    weight_unit_exists := by
      change ∃ (_ : Fin 1) (_ : Fin 2), ‖(1 : ℂ)‖ = 1
      exact ⟨0, 0, by simp⟩ }

private theorem blockTensor_M_two_eq_one
    (i : Fin (MPSTensor.blockPhysDim 1 2 * MPSTensor.blockPhysDim 1 2)) :
    (blockTensor M 2).toMPSTensor i = 1 := by
  fin_cases i
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [M, MPOTensor.blockTensor, MPOTensor.toMPSTensor,
      MPSTensor.phaseFlipTensor, MPSTensor.wordOfBlock, MPOTensor.evalWord,
      Matrix.mul_apply]

private theorem S_toTensor_eq_one
    (i : Fin (MPSTensor.blockPhysDim 1 2 * MPSTensor.blockPhysDim 1 2)) :
    S.toTensor i = 1 := by
  change (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
    (Matrix.blockDiagonal' fun s => S.flatWeight s • S.flatBasis s i) = 1
  have hBlocks : (fun s => S.flatWeight s • S.flatBasis s i) = fun _ => 1 := by
    funext s
    change (1 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1
    simp
  rw [hBlocks]
  change (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
    (Matrix.blockDiagonal' (1 : (s : Fin S.totalCopies) →
      Matrix (Fin (S.flatDim s)) (Fin (S.flatDim s)) ℂ)) = 1
  rw [Matrix.blockDiagonal'_one]
  simp [Matrix.reindex_apply]

private theorem S_basis_transfer_not_nilpotent (j : Fin S.basisCount) :
    ¬ IsNilpotent (doubledPhysTraceTransfer 1 (S.basis j)) := by
  let T := doubledPhysTraceTransfer 1 (S.basis j)
  change ¬ IsNilpotent T
  have hT : T = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    dsimp [T, S]
    ext a b
    fin_cases a
    fin_cases b
    norm_num [doubledPhysTraceTransfer, MPSTensor.scalarUnitTensor,
      Matrix.mul_apply, Matrix.smul_apply]
  rw [hT]
  let : Nonempty (Fin (S.basisDim j)) :=
    ⟨⟨0, S_isBNTCanonicalForm.basis_dim_pos j⟩⟩
  exact not_isNilpotent_one

private theorem blockTensor_M_two_isSimpleCanonicalForm :
    IsSimpleCanonicalForm (blockTensor M 2) := by
  refine ⟨M_isMPDO.blockTensor 2 (by norm_num), S, S_isBNTCanonicalForm,
    S_basis_transfer_not_nilpotent, ?_⟩
  have hTotal : S.totalDim = 2 := by
    change (∑ _ : Fin 2, 1) = 2
    simp
  let X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ := fun _ => 1
  refine ⟨hTotal, X, ?_⟩
  have hGauge : MPSTensor.globalGaugeOfBlocks X = 1 := by
    change Units.map _ (Units.map _ ((MulEquiv.piUnits).symm X)) = 1
    rw [show X = 1 by rfl]
    simp
  intro i
  have hBlock : (blockTensor M 2).toMPSTensor i = 1 :=
    blockTensor_M_two_eq_one i
  have hS : S.toTensor i = 1 := S_toTensor_eq_one i
  rw [hBlock, hS]
  simp only [hGauge, Units.val_one, inv_one, mul_one]
  exact (cast_eq _ _).symm

/-- The tensor is simple in the normalized fixed-representative sense, with
blocking length two and the explicitly blocked sign-flip BNT witness.

Source: arXiv:1606.00608, normalized canonical form at lines 237--246, together
with blocking and BNT decomposition at lines 227--231 and 271--301. -/
theorem M_isSimple : IsSimple M :=
  ⟨M_isMPDO, 2, by norm_num, blockTensor_M_two_isSimpleCanonicalForm⟩

/-- The sign-flip tensor satisfies the source-faithful Definition 4.7 predicate.
Its exact closed-MPO formula supplies the nonzero length `N = 2`; normalized
simplicity supplies the blocked BNT and nonnilpotency witness.

Source: arXiv:1606.00608, canonical-block convention at lines 217--246 and
Definition 4.7 at lines 815--822. -/
theorem M_isSourceSimple : IsSourceSimple M := by
  obtain ⟨hMPDO, -, hBNT⟩ := M_isSimple.isSourceSimple
  have hMpoTwo : mpo M 2 ≠ 0 := by
    intro hzero
    rw [mpo_eq] at hzero
    have hentry := congrFun (congrFun hzero (fun _ => 0)) (fun _ => 0)
    norm_num at hentry
  exact ⟨hMPDO, ⟨2, by norm_num, hMpoTwo⟩, hBNT⟩

/-- The sign-flip tensor fails the strengthened source-simple interface because
its one-site closed MPO vanishes. The nonvanishing condition is additional to
CPSV16 Definition 4.7. -/
theorem M_not_isNonvanishingSourceSimple : ¬ IsNonvanishingSourceSimple M := by
  intro hSource
  exact hSource.mpo_ne_zero 1 (by norm_num) mpo_one_eq_zero

/-- The sign-flip tensor is normalized-simple and source-simple, but it does not
satisfy the additional positive-length nonvanishing condition.

Source predicate: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
@[deprecated
  "Use `M_isSimple`, `M_isSourceSimple`, and `M_not_isNonvanishingSourceSimple`."
  (since := "2026-08-20")]
theorem M_isSimple_and_isSourceSimple_and_not_isNonvanishingSourceSimple :
    IsSimple M ∧ IsSourceSimple M ∧ ¬ IsNonvanishingSourceSimple M :=
  ⟨M_isSimple, M_isSourceSimple, M_not_isNonvanishingSourceSimple⟩

end MPOTensor.SimpleVanishingCounterexample
