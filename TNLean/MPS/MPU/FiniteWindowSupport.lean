/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteBufferedAction
import TNLean.MPS.Preparation.WindowOperatorSupport

/-!
# Actual finite MPU windows in the supported-operator algebra

The identity-tensor inclusions used in the original-site standard-form
formula are the existing chain-window operators. Their actual matrices
therefore belong to the existing finite supported-operator algebra. This
connects the standard-form window identity to cyclic transport of support,
without replacing either notion by a new support predicate.

Source: arXiv:1703.09188, Appendix identity-tensor inclusions and
finite conjugation eq:appendix-1, lines 2292–2306.
-/

open scoped Matrix

namespace MPOTensor

private theorem intervalCoordinates_localInclusion_eq_chainWindowOperator
    (d n p s : ℕ) (hn : 0 < n) (a : ℤ)
    (A : SpinChain.LocalAlgebra d (SpinChain.finiteChainRegion a n)) :
    SpinChain.intervalCoordinates d (a - p) ((p + n) + s)
      (SpinChain.localInclusion (SpinChain.finiteChainRegion_subset_expanded a n p s) A) =
      MPSTensor.chainWindowOperator ((p + n) + s) p
        (SpinChain.intervalCoordinates d a n A) := by
  classical
  ext row col
  rw [MPSTensor.chainWindowOperator_apply (by omega) (by omega)]
  have h := SpinChain.intervalCoordinates_localInclusion_apply d a n p s A row col
  by_cases hOutside : ∀ i : Fin ((p + n) + s),
      ¬ (p ≤ i.val ∧ i.val < p + n) → row i = col i
  · simpa only [hOutside, ite_true, mul_one] using h
  · simpa only [hOutside, ite_false, mul_zero] using h

/-- The actual buffered window matrix is the existing finite chain-window
inclusion, with every exterior site carrying the identity.
Source: arXiv:1703.09188, Appendix, lines 2292–2295. -/
theorem bufferedWindowMatrix_eq_chainWindowOperator
    (d n p s : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    bufferedWindowMatrix d n p s A = MPSTensor.chainWindowOperator (p + (n + s)) p A := by
  let B := (SpinChain.intervalCoordinates d 0 n).symm A
  have hA : SpinChain.intervalCoordinates d 0 n B = A := by
    exact StarAlgEquiv.apply_symm_apply _ A
  have hBuffer := SpinChain.intervalCoordinates_localInclusion_eq_bufferedWindowMatrix
    d n p s 0 B
  rw [hA] at hBuffer
  have hWindow := intervalCoordinates_localInclusion_eq_chainWindowOperator d n p s hn 0 B
  simp only [Nat.add_assoc] at hWindow
  rw [hBuffer, hA] at hWindow
  exact hWindow

/-- The buffered actual window acts only on its indicated finite interval.
Source: arXiv:1703.09188, Appendix, lines 2292–2295. -/
theorem bufferedWindowMatrix_mem_supportedOperators
    (d n p s : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    bufferedWindowMatrix d n p s A ∈ QuantumCircuit.supportedOperators d
      {i : Fin (p + (n + s)) | p ≤ i.val ∧ i.val < p + n} := by
  rw [bufferedWindowMatrix_eq_chainWindowOperator d n p s hn]
  exact MPSTensor.chainWindowOperator_mem_supportedOperators (by omega) (by omega) A

/-- The actual forward finite MPU conjugation has the standard-form
window support in the existing supported-operator algebra. This is the
base finite support bound transported cyclically to address the seam.
Source: arXiv:1703.09188, StandardForm/SF and eq:appendix-1,
lines 603–622 and 2300–2306. -/
theorem mpo_bufferedWindow_conjugation_mem_supportedOperators
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    (k p s : ℕ) (hk : 0 < k) (hN : 1 < p + (3 * (2 * k) + s))
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    mpo U (p + (3 * (2 * k) + s)) *
        bufferedWindowMatrix d (3 * (2 * k)) p s (originalSiteHeisenbergInputWindow d k A) *
        (mpo U (p + (3 * (2 * k) + s)))ᴴ ∈
      QuantumCircuit.supportedOperators d
        {i : Fin (p + (3 * (2 * k) + s)) | p ≤ i.val ∧ i.val < p + 3 * (2 * k)} := by
  rw [mpo_bufferedWindow_conjugation hU k p s hN S A]
  exact bufferedWindowMatrix_mem_supportedOperators d (3 * (2 * k)) p s (by omega)
    (originalSiteHeisenbergOutputWindow k u v A)

/-- The source input window is exactly the existing chain-window
inclusion of its complete central interval. Source: arXiv:1703.09188,
StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem originalSiteHeisenbergInputWindow_eq_chainWindowOperator
    (d k : ℕ) (hk : 0 < k)
    (A : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    originalSiteHeisenbergInputWindow d k A =
      MPSTensor.chainWindowOperator (3 * (2 * k)) (2 * k)
        (Matrix.reindex (originalSiteHeisenbergCentreEquiv d k)
          (originalSiteHeisenbergCentreEquiv d k) A) := by
  let C := Matrix.reindex (originalSiteHeisenbergCentreEquiv d k)
    (originalSiteHeisenbergCentreEquiv d k) A
  let B := (SpinChain.intervalCoordinates d (2 * k : ℕ) (2 * k)).symm C
  have hWindow := intervalCoordinates_localInclusion_eq_chainWindowOperator
    d (2 * k) (2 * k) (2 * k) (by omega) (2 * k : ℕ) B
  have hB : SpinChain.intervalCoordinates d (2 * k : ℕ) (2 * k) B = C :=
    StarAlgEquiv.apply_symm_apply _ C
  rw [hB, sub_self, show (2 * k + 2 * k) + 2 * k = 3 * (2 * k) by omega] at hWindow
  have hSource := SpinChain.intervalCoordinates_centralInclusion_originalSiteHeisenbergInputWindow
    d k 0 A
  simp only [zero_add] at hSource
  exact hSource.symm.trans hWindow

/-- Every observable on the complete central `2k`-site interval has the
actual standard-form forward support bound in the finite supported-operator
algebra. Its input is arbitrary; no source-coordinate restriction or
support conclusion is assumed. Source: arXiv:1703.09188, StandardForm/SF
and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem mpo_chainWindow_conjugation_mem_supportedOperators
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    (k p s : ℕ) (hk : 0 < k)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (MPSTensor.blockPhysDim d k) × Fin (MPSTensor.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (C : Matrix (Fin (2 * k) → Fin d) (Fin (2 * k) → Fin d) ℂ) :
    mpo U (p + (3 * (2 * k) + s)) *
        MPSTensor.chainWindowOperator (p + (3 * (2 * k) + s)) (p + 2 * k) C *
        (mpo U (p + (3 * (2 * k) + s)))ᴴ ∈
      QuantumCircuit.supportedOperators d
        {i : Fin (p + (3 * (2 * k) + s)) | p ≤ i.val ∧ i.val < p + 3 * (2 * k)} := by
  classical
  let E := originalSiteHeisenbergCentreEquiv d k
  let A := Matrix.reindex E.symm E.symm C
  have hA : Matrix.reindex E E A = C := by
    ext row col
    simp [A, Matrix.reindex_apply]
  have hPlaced : bufferedWindowMatrix d (3 * (2 * k)) p s
      (originalSiteHeisenbergInputWindow d k A) =
      MPSTensor.chainWindowOperator (p + (3 * (2 * k) + s)) (p + 2 * k) C := by
    rw [bufferedWindowMatrix_eq_chainWindowOperator d (3 * (2 * k)) p s (by omega),
      originalSiteHeisenbergInputWindow_eq_chainWindowOperator d k hk,
      MPSTensor.chainWindowOperator_chainWindowOperator (by omega) (by omega)
        (by omega) (by omega)]
    exact congrArg (MPSTensor.chainWindowOperator (p + (3 * (2 * k) + s)) (p + 2 * k)) hA
  have h := mpo_bufferedWindow_conjugation_mem_supportedOperators hU k p s hk
    (by omega) S A
  rw [hPlaced] at h
  exact h

end MPOTensor
