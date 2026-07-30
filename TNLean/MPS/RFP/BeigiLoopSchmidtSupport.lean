/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.SchmidtRank
import TNLean.MPS.RFP.BeigiLoopTensor

/-!
# Schmidt-support realization of a positive Beigi loop

A positive loop in Beigi's sector graph carries a nonzero vector in a tensor
product of right and left sector factors.  Its coefficient matrix need not
have full rank in either ambient factor.  Factoring this matrix through its
Schmidt rank gives a matrix product tensor whose virtual dimension is that
rank.  The resulting tensor has the same periodic vectors as the ambient
realization at every positive length.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
  Section IV, equation (10) and the paragraph following it.
-/

open scoped BigOperators Kronecker Matrix

namespace MPSTensor.BeigiSectorGraphData

open FiniteWeightedDigraph

variable {d D : ℕ} {A : MPSTensor d D}

/-- The Schmidt rank of the bond vector carried by a positive loop.

**Local fix (Schmidt support):** Beigi chooses a nonzero vector in the loop
edge ground space, but does not assume that it has full Schmidt rank in the
ambient left and right factors.  The minimal virtual space is therefore its
Schmidt support.  This point is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it. -/
noncomputable def loopSchmidtRank (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : ℕ :=
  Matrix.schmidtRank (F.loopBondVector l)

/-- A rank factorization of the coefficient matrix of the loop bond vector
through its Schmidt support.

**Local fix (Schmidt support):** The intermediate dimension is the Schmidt
rank rather than either ambient tensor-factor dimension.  This removes
unused virtual directions when the chosen loop vector has deficient Schmidt
rank; see `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it. -/
structure LoopSchmidtFactorization (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) where
  /-- The right/Schmidt-indexed factor of the loop bond coefficient matrix.

  Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
  Section IV, equation (10) and the paragraph following it. -/
  rightFactor :
    Matrix (Fin (F.rightDim l.1)) (Fin (F.loopSchmidtRank l)) ℂ
  /-- The Schmidt/left-indexed factor of the loop bond coefficient matrix.

  Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
  Section IV, equation (10) and the paragraph following it. -/
  leftFactor :
    Matrix (Fin (F.loopSchmidtRank l)) (Fin (F.leftDim l.1)) ℂ
  /-- The two factors multiply to the loop bond coefficient matrix.

  Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
  Section IV, equation (10) and the paragraph following it. -/
  mul_eq : rightFactor * leftFactor =
    Matrix.schmidtCoeffMatrix (F.loopBondVector l)

/-- The chosen rank factorization of the loop bond vector through its
Schmidt support.

**Local fix (Schmidt support):** The factorization passes through the Schmidt
rank rather than an ambient tensor-factor dimension; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it. -/
noncomputable def loopSchmidtFactorization (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : LoopSchmidtFactorization F l := by
  let h := Matrix.exists_mul_eq_of_rank_le
    (Matrix.schmidtCoeffMatrix (F.loopBondVector l))
    (show (Matrix.schmidtCoeffMatrix (F.loopBondVector l)).rank ≤
      F.loopSchmidtRank l from le_rfl)
  exact {
    rightFactor := Classical.choose h
    leftFactor := Classical.choose (Classical.choose_spec h)
    mul_eq := Classical.choose_spec (Classical.choose_spec h)
  }

/-- The Schmidt support of a nonzero loop bond vector has positive
dimension.

**Local fix (Schmidt support):** Positivity follows from Beigi's nonzero loop
bond vector after restricting to its Schmidt support; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it. -/
theorem loopSchmidtRank_pos (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : 0 < F.loopSchmidtRank l := by
  rw [Nat.pos_iff_ne_zero]
  intro hrank
  have hmul :
      (F.loopSchmidtFactorization l).rightFactor *
          (F.loopSchmidtFactorization l).leftFactor = 0 := by
    ext q a
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro j _
    exact Fin.elim0 (Fin.cast hrank j)
  apply F.loopBondVector_ne_zero l
  funext qa
  have hcoeff := congrArg (fun M ↦ M qa.1 qa.2)
    (hmul.symm.trans (F.loopSchmidtFactorization l).mul_eq)
  simpa using hcoeff.symm

/-- The rectangular letter whose product with the left Schmidt factor gives
the ambient loop tensor letter.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it, with the
Schmidt-support refinement recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
private noncomputable def loopSchmidtBridge (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) (i : Fin d) :
    Matrix (Fin (F.leftDim l.1)) (Fin (F.loopSchmidtRank l)) ℂ :=
  fun a α ↦
    if hq : (F.sectorEquiv.symm i).1 = l.1 then
      if a = Fin.cast (congrArg F.leftDim hq)
          (F.sectorEquiv.symm i).2.2 then
        (F.loopSchmidtFactorization l).rightFactor
          (Fin.cast (congrArg F.rightDim hq)
            (F.sectorEquiv.symm i).2.1) α
      else 0
    else 0

/-- The loop tensor in sector coordinates on the minimal Schmidt support.

Its letter at a loop-sector coordinate is the outer product of the
corresponding row of the left factor with the corresponding column of the
right factor.  Coordinates in other sectors give zero.

**Local fix (Schmidt support):** The virtual dimension is the Schmidt rank of
the chosen bond vector, not the full left-factor dimension.  This is the
minimal realization compatible with Beigi's product-of-pairs state; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it. -/
noncomputable def minimalLoopCoordinateTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : MPSTensor d (F.loopSchmidtRank l) :=
  fun i ↦ (F.loopSchmidtFactorization l).leftFactor *
    F.loopSchmidtBridge l i

/-- Applying the spatial-decomposition unitary gives the physical loop
tensor on the minimal Schmidt support.

**Local fix (Schmidt support):** The virtual space is restricted to the
Schmidt support as documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it. -/
noncomputable def minimalLoopTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : MPSTensor d (F.loopSchmidtRank l) :=
  rotatePhysical F.unitary (F.minimalLoopCoordinateTensor l)

/-- At a coordinate in the loop sector, the minimal tensor letter is the
outer product of a column of the left rank factor and a row of the right rank
factor.

Source context: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation),
and Section IV, equation (10) and the paragraph following it.  The
Schmidt-support refinement is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem minimalLoopCoordinateTensor_sector_apply
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    (q : Fin (F.rightDim l.1)) (a : Fin (F.leftDim l.1)) :
    F.minimalLoopCoordinateTensor l
        (F.sectorEquiv ⟨l.1, (q, a)⟩) =
      Matrix.vecMulVec
        ((F.loopSchmidtFactorization l).leftFactor.col a)
        ((F.loopSchmidtFactorization l).rightFactor.row q) := by
  classical
  have hsite :
      F.sectorEquiv.symm (F.sectorEquiv ⟨l.1, (q, a)⟩) =
        ⟨l.1, (q, a)⟩ :=
    Equiv.symm_apply_apply F.sectorEquiv _
  have hq :
      (F.sectorEquiv.symm (F.sectorEquiv ⟨l.1, (q, a)⟩)).1 = l.1 :=
    congrArg Sigma.fst hsite
  have hright :
      Fin.cast (congrArg F.rightDim hq)
          (F.sectorEquiv.symm (F.sectorEquiv ⟨l.1, (q, a)⟩)).2.1 = q := by
    apply Fin.ext
    simpa only [Fin.val_cast] using congrArg (fun z ↦ z.2.1.val) hsite
  have hleft :
      Fin.cast (congrArg F.leftDim hq)
          (F.sectorEquiv.symm (F.sectorEquiv ⟨l.1, (q, a)⟩)).2.2 = a := by
    apply Fin.ext
    simpa only [Fin.val_cast] using congrArg (fun z ↦ z.2.2.val) hsite
  ext α β
  simp [minimalLoopCoordinateTensor, Matrix.mul_apply, loopSchmidtBridge,
    hright, hleft, Matrix.vecMulVec_apply]

/-- Outside the chosen loop sector, every letter of the minimal coordinate
tensor vanishes.

Source context: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (10) and the
paragraph following it.  The Schmidt-support refinement is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem minimalLoopCoordinateTensor_sector_ne
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    (k : Fin F.sectorCount) (hk : k ≠ l.1)
    (q : Fin (F.rightDim k)) (a : Fin (F.leftDim k)) :
    F.minimalLoopCoordinateTensor l (F.sectorEquiv ⟨k, (q, a)⟩) = 0 := by
  classical
  ext α β
  simp [minimalLoopCoordinateTensor, Matrix.mul_apply, loopSchmidtBridge, hk]

/-- Each ambient loop letter is the rectangular Schmidt-support letter
followed by the left factor of the bond coefficient matrix.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it, with the
Schmidt-support refinement recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
private theorem loopCoordinateTensor_eq_bridge_mul_leftFactor
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    F.loopCoordinateTensor l = fun i ↦
      F.loopSchmidtBridge l i *
        (F.loopSchmidtFactorization l).leftFactor := by
  classical
  ext i a b
  by_cases hq : (F.sectorEquiv.symm i).1 = l.1
  · by_cases ha : a = Fin.cast (congrArg F.leftDim hq)
        (F.sectorEquiv.symm i).2.2
    · have hentry := congrArg
          (fun M ↦ M
            (Fin.cast (congrArg F.rightDim hq)
              (F.sectorEquiv.symm i).2.1) b)
          (F.loopSchmidtFactorization l).mul_eq
      simpa [loopCoordinateTensor, loopSchmidtBridge, Matrix.mul_apply,
        hq, ha] using hentry.symm
    · simp [loopCoordinateTensor, loopSchmidtBridge, Matrix.mul_apply,
        hq, ha]
  · simp [loopCoordinateTensor, loopSchmidtBridge, Matrix.mul_apply, hq]

/-- A nonempty word in the products \(S_iY\) and \(YS_i\) factors as
\(RY\) and \(YR\), respectively, for a common rectangular matrix \(R\). -/
private theorem exists_schmidtWordCore {r L : ℕ}
    (Y : Matrix (Fin r) (Fin L) ℂ)
    (S : Fin d → Matrix (Fin L) (Fin r) ℂ)
    (w : List (Fin d)) (hw : w ≠ []) :
    ∃ R : Matrix (Fin L) (Fin r) ℂ,
      evalWord (fun i ↦ S i * Y) w = R * Y ∧
        evalWord (fun i ↦ Y * S i) w = Y * R := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons i w ih =>
      by_cases htail : w = []
      · subst w
        exact ⟨S i, by simp, by simp⟩
      · obtain ⟨R, hraw, hminimal⟩ := ih htail
        refine ⟨S i * Y * R, ?_, ?_⟩
        · simp only [evalWord_cons, hraw, Matrix.mul_assoc]
        · simp only [evalWord_cons, hminimal, Matrix.mul_assoc]

/-- The ambient and Schmidt-support loop tensors have equal traces on every
nonempty word.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it, with the
Schmidt-support refinement recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
private theorem trace_evalWord_loopCoordinateTensor_eq_minimal
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    (w : List (Fin d)) (hw : w ≠ []) :
    Matrix.trace (evalWord (F.loopCoordinateTensor l) w) =
      Matrix.trace (evalWord (F.minimalLoopCoordinateTensor l) w) := by
  rw [F.loopCoordinateTensor_eq_bridge_mul_leftFactor l]
  obtain ⟨R, hraw, hminimal⟩ := exists_schmidtWordCore
    (F.loopSchmidtFactorization l).leftFactor
    (F.loopSchmidtBridge l) w hw
  rw [hraw]
  change Matrix.trace (R * (F.loopSchmidtFactorization l).leftFactor) =
    Matrix.trace (evalWord
      (fun i ↦ (F.loopSchmidtFactorization l).leftFactor *
        F.loopSchmidtBridge l i) w)
  rw [hminimal]
  exact Matrix.trace_mul_comm _ _

/-- The periodic matrix product vector of the minimal Schmidt-support tensor
is the cyclic product of loop bond vectors at every positive length.

**Local fix (Schmidt support):** Restricting the virtual space to the Schmidt
support leaves every positive-length periodic vector unchanged.  The role of
this restriction is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it. -/
theorem mpv_minimalLoopCoordinateTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] (s : Fin N → Fin d) :
    mpv (F.minimalLoopCoordinateTensor l) s = F.loopCyclicProduct l s := by
  rw [← F.mpv_loopCoordinateTensor l s]
  unfold mpv coeff
  have hw : List.ofFn s ≠ [] :=
    List.length_pos_iff_ne_nil.mp
      (by simpa only [List.length_ofFn] using NeZero.pos N)
  exact (F.trace_evalWord_loopCoordinateTensor_eq_minimal l
    (List.ofFn s) hw).symm

/-- The physical tensor on the minimal Schmidt support has exactly Beigi's
product-of-pairs state as its periodic vector at every positive chain length.

**Local fix (Schmidt support):** The equality shows that removing the unused
virtual directions does not alter the physical loop state; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section III, p. 4 (MPS observation), and
Section IV, equation (10) and the paragraph following it. -/
theorem mpv_minimalLoopTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] (s : Fin N → Fin d) :
    mpv (F.minimalLoopTensor l) s = F.loopProductState l s := by
  rw [minimalLoopTensor, MPSTensor.mpv_rotatePhysical]
  simp only [loopProductState]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  exact F.mpv_minimalLoopCoordinateTensor l t

end MPSTensor.BeigiSectorGraphData
