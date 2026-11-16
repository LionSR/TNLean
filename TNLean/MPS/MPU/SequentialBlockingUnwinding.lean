/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.PrintedBlockingGates
import TNLean.MPS.MPU.BlockingUnwinding

/-!
# Sequential unwinding on the ordered original spins

Each matrix in the sequence `Y_s` is defined on the same `2k`-spin chain.
The four-spin local equation is placed at the moving pair of cells; the
remaining factors commute with it because their original-spin supports are
disjoint.

Source: arXiv:1703.09188, `eq:unwind-dagger-trick` and the sequence `Y_s`,
lines 1682--1733.
-/

open scoped Matrix Kronecker BigOperators
open Matrix QuantumCircuit

namespace MPOTensor

private def fourSpinEquiv (d : ℕ) :
    (Fin 4 → Fin d) ≃ ((Fin d × Fin d) × (Fin d × Fin d)) :=
  (Fin.appendEquiv 2 2).symm.trans
    ((finTwoArrowEquiv (Fin d)).prodCongr (finTwoArrowEquiv (Fin d)))

private theorem pairGate_four_left {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.reindex (fourSpinEquiv d) (fourSpinEquiv d)
      (printedPairGate 4 0 (by decide) A) =
      A ⊗ₖ (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  simp [Matrix.reindex_apply, printedPairGate_apply, fourSpinEquiv,
    Fin.appendEquiv, Fin.append, Fin.addCases, finTwoArrowEquiv, Fin.forall_fin_succ,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]

private theorem pairGate_four_right {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.reindex (fourSpinEquiv d) (fourSpinEquiv d)
      (printedPairGate 4 2 (by decide) A) =
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ A := by
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  simp [Matrix.reindex_apply, printedPairGate_apply, fourSpinEquiv,
    Fin.appendEquiv, Fin.append, Fin.addCases, finTwoArrowEquiv, Fin.forall_fin_succ,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]

private theorem pairGate_four_middle {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.reindex (fourSpinEquiv d) (fourSpinEquiv d)
      (printedPairGate 4 1 (by decide) A) =
      staircaseMiddle (A := Fin d) (E := Fin d) A := by
  ext ⟨⟨a, b⟩, c, e⟩ ⟨⟨a', b'⟩, c', e'⟩
  simp [Matrix.reindex_apply, printedPairGate_apply, fourSpinEquiv,
    Fin.appendEquiv, Fin.append, Fin.addCases, finTwoArrowEquiv, Fin.forall_fin_succ,
    staircaseMiddle, Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp_all

private theorem local_unwind_four {d : ℕ}
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (ζ : ℂ)
    (hlocal : ζ • (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ x))ᴴ =
      staircaseMiddle (A := Fin d) (E := Fin d) v * (xᴴ ⊗ₖ u)) :
    printedPairGate 4 1 (by decide) v * printedPairGate 4 0 (by decide) xᴴ *
        printedPairGate 4 2 (by decide) u =
      ζ • (printedPairGate 4 0 (by decide) uᴴ *
        printedPairGate 4 2 (by decide) xᴴ) *
          (printedPairGate 4 1 (by decide) v)ᴴ := by
  let E := fourSpinEquiv d
  apply (Matrix.reindexLinearEquiv ℂ ℂ E E).injective
  simp only [← Matrix.reindexLinearEquiv_mul ℂ ℂ E E E, map_smul,
    Matrix.coe_reindexLinearEquiv]
  simp only [E, ← Matrix.conjTranspose_reindex, pairGate_four_left,
    pairGate_four_right, pairGate_four_middle, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul]
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul] using hlocal.symm

/-- The source four-spin equation holds at any consecutive four-spin window
of the actual chain, with identity spectators outside that window.
Source: arXiv:1703.09188, `eq:unwind-dagger-trick`, lines 1682--1687 and 1727--1729. -/
theorem printedPairGate_unwind {d n p : ℕ} (hp : p + 4 ≤ n)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (ζ : ℂ)
    (hlocal : ζ • (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ x))ᴴ =
      staircaseMiddle (A := Fin d) (E := Fin d) v * (xᴴ ⊗ₖ u)) :
    printedPairGate n (p + 1) (by omega) v * printedPairGate n p (by omega) xᴴ *
        printedPairGate n (p + 2) (by omega) u =
      ζ • (printedPairGate n p (by omega) uᴴ *
        printedPairGate n (p + 2) (by omega) xᴴ) *
          (printedPairGate n (p + 1) (by omega) v)ᴴ := by
  let f : Fin 4 ↪ Fin n := (Fin.natAddEmb p).trans (Fin.castLEEmb hp)
  have hf (i : Fin 4) : (f i).val = p + i.val := rfl
  have hshift (q : ℕ) (hq : q + 2 ≤ 4)
      (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
      embedOp f (printedPairGate 4 q hq A) = printedPairGate n (p + q) (by omega) A :=
    printedPairGate_embed hq (by omega) f f.injective hf A
  have h := congrArg (embedOp f) (local_unwind_four u v x ζ hlocal)
  simp only [← embedOp_mul f.injective, embedOp_smul, ← embedOp_conjTranspose,
    hshift, Nat.add_zero] at h
  exact h

/-- The matrices `Y_s` on the common chain of `2k` original spins.
The left shifted layer has `k-1-s` gates, the middle cell layer has
`s` adjoint gates, the boundary `xᴴ`, and `k-1-s` forward gates; the final
factor is the adjoint of the first `s` shifted gates.
Source: arXiv:1703.09188, lines 1718--1726. -/
noncomputable def printedUnwindingSequence {d : ℕ} (k s : ℕ) (hs : s < k)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (σ ζ : ℂ) :
    Matrix (Fin (2 * k) → Fin d) (Fin (2 * k) → Fin d) ℂ :=
  (σ * ζ ^ s) • (printedLinkLayer k s (k - 1 - s) (by omega) v *
    printedCellLayer k 0 s (by omega) uᴴ *
    printedPairGate (2 * k) (2 * s) (by omega) xᴴ *
    printedCellLayer k (s + 1) (k - 1 - s) (by omega) u *
    (printedLinkLayer k 0 s (by omega) v)ᴴ)

private theorem sweep_step
    {ι : Type*} [Fintype ι] (V L P X U R T A B : Matrix ι ι ℂ) (ζ : ℂ)
    (hVL : Commute L V) (hLP : Commute L P) (hLR : Commute Lᴴ R)
    (hlocal : L * X * U = ζ • (A * B) * Lᴴ) :
    (L * V) * P * X * (U * R) * T = ζ • (V * (P * A) * B * R * (Lᴴ * T)) := by
  calc
    _ = V * P * (L * X * U) * R * T := by
      simp only [Matrix.mul_assoc]
      rw [hVL.left_comm, hLP.left_comm]
    _ = ζ • (V * (P * A) * B * R * (Lᴴ * T)) := by
      rw [hlocal]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [hLR.left_comm]

/-- Consecutive matrices in the actual source sequence are equal. All
commutations are consequences of disjoint original-spin supports.
Source: arXiv:1703.09188, lines 1718--1729. -/
theorem printedUnwindingSequence_step {d k s : ℕ} (hs : s + 1 < k)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (σ ζ : ℂ)
    (hlocal : ζ • (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ x))ᴴ =
      staircaseMiddle (A := Fin d) (E := Fin d) v * (xᴴ ⊗ₖ u)) :
    printedUnwindingSequence k s (by omega) u v x σ ζ =
      printedUnwindingSequence k (s + 1) hs u v x σ ζ := by
  let m := k - 2 - s
  have hm : k - 1 - s = m + 1 := by omega
  have hn : k - 1 - (s + 1) = m := by omega
  let V := printedLinkLayer k (s + 1) m (by omega) v
  let L := printedPairGate (2 * k) (2 * s + 1) (by omega) v
  let P := printedCellLayer k 0 s (by omega) uᴴ
  let X := printedPairGate (2 * k) (2 * s) (by omega) xᴴ
  let U := printedPairGate (2 * k) (2 * (s + 1)) (by omega) u
  let R := printedCellLayer k (s + 2) m (by omega) u
  let T := (printedLinkLayer k 0 s (by omega) v)ᴴ
  let A := printedPairGate (2 * k) (2 * s) (by omega) uᴴ
  let B := printedPairGate (2 * k) (2 * (s + 1)) (by omega) xᴴ
  have hVL : Commute L V := printedPairGate_commute_linkLayer
    (by omega) (by omega) (Or.inl (by omega)) v v
  have hLP : Commute L P := printedPairGate_commute_cellLayer
    (by omega) (by omega) (Or.inr (by omega)) v uᴴ
  have hLR : Commute Lᴴ R := by
    dsimp only [L, R]
    rw [printedPairGate_conjTranspose]
    exact printedPairGate_commute_cellLayer
      (by omega) (by omega) (Or.inl (by omega)) vᴴ u
  have hloc : L * X * U = ζ • (A * B) * Lᴴ := by
    dsimp only [L, X, U, A, B]
    have h := printedPairGate_unwind
      (n := 2 * k) (p := 2 * s) (by omega) u v x ζ hlocal
    convert h using 1
  have hleft : printedUnwindingSequence k s (by omega) u v x σ ζ =
      (σ * ζ ^ s) • ((L * V) * P * X * (U * R) * T) := by
    have hV : printedLinkLayer k s (k - 1 - s) (by omega) v = L * V := by
      convert printedLinkLayer_succ k s m (by omega) v using 1
      congr 1
    have hU : printedCellLayer k (s + 1) (k - 1 - s) (by omega) u = U * R := by
      convert printedCellLayer_succ k (s + 1) m (by omega) u using 1
      congr 1
    unfold printedUnwindingSequence
    rw [hV, hU]
  have hright : printedUnwindingSequence k (s + 1) hs u v x σ ζ =
      (σ * ζ ^ (s + 1)) • (V * (P * A) * B * R * (Lᴴ * T)) := by
    have hV : printedLinkLayer k (s + 1) (k - 1 - (s + 1)) (by omega) v = V := by
      dsimp only [V]
      congr 1
    have hR : printedCellLayer k (s + 2) (k - 1 - (s + 1)) (by omega) u = R := by
      dsimp only [R]
      congr 1
    unfold printedUnwindingSequence
    rw [hV, hR, printedCellLayer_succ_last k 0 s (by omega) uᴴ,
      printedLinkLayer_succ_last k 0 s (by omega) v, Matrix.conjTranspose_mul]
    dsimp only [P, A, B, R, T, L]
    simp only [Matrix.mul_assoc]
    congr <;> omega
  rw [hleft, hright, sweep_step V L P X U R T A B ζ hVL hLP hLR hloc, smul_smul]
  rw [pow_succ, mul_assoc]

/-- Every member of the concrete source sequence equals its first member.
Source: arXiv:1703.09188, lines 1727--1732. -/
theorem printedUnwindingSequence_eq_zero {d k s : ℕ} (hs : s < k)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (σ ζ : ℂ)
    (hlocal : ζ • (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ x))ᴴ =
      staircaseMiddle (A := Fin d) (E := Fin d) v * (xᴴ ⊗ₖ u)) :
    printedUnwindingSequence k 0 (by omega) u v x σ ζ =
      printedUnwindingSequence k s hs u v x σ ζ := by
  induction s with
  | zero => rfl
  | succ s ih =>
    exact (ih (by omega)).trans (printedUnwindingSequence_step hs u v x σ ζ hlocal)

/-- The source's left tensor factor `X` on `2k` original spins.
Source: arXiv:1703.09188, lines 1707--1714. -/
noncomputable def printedUnwindingFactor {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin (2 * k) → Fin d) (Fin (2 * k) → Fin d) ℂ :=
  printedLinkLayer k 0 (k - 1) (by omega) v *
    printedCellLayer k 0 (k - 1) (by omega) u *
    printedPairGate (2 * k) (2 * (k - 1)) (by omega) x

/-- The initial matrix in the source's sequence is the displayed right
tensor factor `Y`.
Source: arXiv:1703.09188, lines 1711--1726. -/
theorem printedUnwindingSequence_zero {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (σ ζ : ℂ) :
    printedUnwindingSequence k 0 hk u v x σ ζ =
      σ • (printedLinkLayer k 0 (k - 1) (by omega) v *
        printedPairGate (2 * k) 0 (by omega) xᴴ *
        printedCellLayer k 1 (k - 1) (by omega) u) := by
  simp [printedUnwindingSequence]

/-- The last matrix in the source's sequence is the adjoint of its left
tensor factor, with the accumulated phase.
Source: arXiv:1703.09188, lines 1727--1732. -/
theorem printedUnwindingSequence_last {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (σ ζ : ℂ) :
    printedUnwindingSequence k (k - 1) (by omega) u v x σ ζ =
      (σ * ζ ^ (k - 1)) • (printedUnwindingFactor k hk u v x)ᴴ := by
  have hcomm := printedPairGate_commute_cellLayer
    (k := k) (p := 2 * (k - 1)) (a := 0) (m := k - 1)
    (by omega) (by omega) (Or.inr (by omega)) xᴴ uᴴ
  have hV : printedLinkLayer k (k - 1) (k - 1 - (k - 1)) (by omega) v = 1 := by
    convert printedLinkLayer_zero k (k - 1) (by omega) v using 1
    congr 1
    omega
  have hU : printedCellLayer k (k - 1 + 1) (k - 1 - (k - 1)) (by omega) u = 1 := by
    convert printedCellLayer_zero k (k - 1 + 1) (by omega) u using 1
    congr 1
    omega
  unfold printedUnwindingSequence printedUnwindingFactor
  rw [hV, hU]
  simp only [Matrix.one_mul, Matrix.mul_one,
    Matrix.conjTranspose_mul, printedPairGate_conjTranspose,
    printedCellLayer_conjTranspose]
  simpa only [Matrix.mul_assoc] using congrArg (fun A ↦ (σ * ζ ^ (k - 1)) •
    (A * (printedLinkLayer k 0 (k - 1) (by omega) v)ᴴ)) hcomm.eq.symm

/-- Full sequential unwinding of the printed finite-spin matrices. The
one local four-spin relation gives the accumulated phase `σ ζ^(k-1)`;
no parity, symmetry, canonical-form or blocked-gate conclusion is assumed.
Source: arXiv:1703.09188, lines 1707--1733. -/
theorem printed_sequential_unwinding {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (σ ζ : ℂ)
    (hlocal : ζ • (staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ x))ᴴ =
      staircaseMiddle (A := Fin d) (E := Fin d) v * (xᴴ ⊗ₖ u)) :
    σ • (printedLinkLayer k 0 (k - 1) (by omega) v *
        printedPairGate (2 * k) 0 (by omega) xᴴ *
        printedCellLayer k 1 (k - 1) (by omega) u) =
      (σ * ζ ^ (k - 1)) • (printedUnwindingFactor k hk u v x)ᴴ := by
  have h := printedUnwindingSequence_eq_zero (k := k) (s := k - 1)
    (by omega) u v x σ ζ hlocal
  rw [printedUnwindingSequence_zero, printedUnwindingSequence_last] at h
  exact h

/-- The left tensor factor in the sequential unwinding is unitary when
its constituent gates are unitary.
Source: arXiv:1703.09188, lines 1707--1714. -/
theorem printedUnwindingFactor_mem_unitaryGroup {d : ℕ} (k : ℕ) (hk : 0 < k)
    (u v x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hv : v ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    (hx : x ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ) :
    printedUnwindingFactor k hk u v x ∈ Matrix.unitaryGroup (Fin (2 * k) → Fin d) ℂ :=
  Submonoid.mul_mem _
    (Submonoid.mul_mem _ (printedLinkLayer_mem_unitaryGroup _ _ _ _ v hv)
      (printedCellLayer_mem_unitaryGroup _ _ _ _ u hu))
    (printedPairGate_mem_unitaryGroup _ _ _ x hx)

/-- Actual even-ring adjoint symmetry supplies one local unitary that
unwinds all positive lengths, with the actual one- and two-block trace
signs. The finite-spin conclusion does not identify the displayed circuits
with the standard form of the actual `k`-blocked tensor.

Source: arXiv:1703.09188, lines 1657--1733.
The canonical ambient restriction is the same as in
`TwoSiteStandardFormData.exists_unwind_dagger_trick`; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem TwoSiteStandardFormData.exists_printed_sequential_unwinding
    {d D : ℕ} {W : MPOTensor (d * d) D}
    {u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (S : TwoSiteStandardFormData W u v) (hW : IsMPUCanonicalFormII W)
    (hTR : ∀ N : ℕ, 1 < N → Even N → mpo W N = (mpo W N)ᴴ) :
    ∃ x : Matrix.unitaryGroup (Fin d × Fin d) ℂ, ∀ k : ℕ, ∀ hk : 0 < k,
      timeReversalSign u v •
        (printedLinkLayer k 0 (k - 1) (by omega) v *
          printedPairGate (2 * k) 0 (by omega) (x : Matrix _ _ ℂ)ᴴ *
          printedCellLayer k 1 (k - 1) (by omega) u) =
        (timeReversalSign u v *
          (timeReversalSign u v *
            timeReversalSign (twoBlockInputGate u v) (twoBlockOutputGate v)) ^ (k - 1)) •
          (printedUnwindingFactor k hk u v (x : Matrix _ _ ℂ))ᴴ := by
  obtain ⟨x, hx⟩ := S.exists_unwind_dagger_trick hW hTR
  exact ⟨x, fun k hk ↦ printed_sequential_unwinding k hk u v x _ _ hx⟩

end MPOTensor
