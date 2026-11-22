/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.QuasiLocal.TwoSiteBufferedAction
import TNLean.MPS.CanonicalForm.Correlation.WindowCorrelator
import QICLean.ManyBody.Sites.PlaceAlong
import QICLean.ManyBody.Sites.Lattice.Chain

/-!
# Actual finite MPU windows in the supported-operator algebra

The identity-tensor inclusions used in the original-site standard-form
formula are placements along windows of consecutive sites of the chain
(`ManyBody.placeAlong` along `ManyBody.chainWindow`). Their actual matrices
therefore belong to the existing finite supported-operator algebra. This
connects the standard-form window identity to cyclic transport of support,
without replacing either notion by a new support predicate.

Source: arXiv:1703.09188, Appendix identity-tensor inclusions and
finite conjugation eq:appendix-1, lines 2292–2306.

**Scope restriction (supplied standard form):** The three conjugation
results `mpo_bufferedWindow_conjugation_mem_supportedOperators`,
`mpo_chainWindow_conjugation_mem_supportedOperators` and
`mpo_conjugation_mem_supportedOperators_central` consume actual MPU
unitarity, supplied two-site standard-form data and, for the last two, a
positive block length; their windows are measured in that block length. The window
identifications carry no restriction. The standard-form construction
from bare MPU data and the source bond-dimension radius remain
separate. See
`docs/paper-gaps/mpu_qca_complete_block_heisenberg_scope.tex`.

## The actual middle four-half-block output window

The fixed six-half-block output of the supplied standard-form action is
exactly the placement (`ManyBody.placeAlong` along `ManyBody.chainWindow`) of its
four-half-block two-link observable at offset one half block. Both exterior
half blocks carry identities. This is a coordinate contraction of the actual output, with no support
or factor-presentation premise.

Source: arXiv:1703.09188, StandardForm and eq:appendix-1,
lines 603–622 and 2292–2306; the four-site output in the Appendix index
comparison, lines 2313–2334.
-/

section

open scoped Matrix

namespace MPOTensor

private theorem intervalCoordinates_localInclusion_eq_placeAlong_chainWindow
    (d n p s : ℕ) (a : ℤ)
    (A : SpinChain.LocalAlgebra d (SpinChain.finiteChainRegion a n)) :
    SpinChain.intervalCoordinates d (a - p) ((p + n) + s)
      (SpinChain.localInclusion (SpinChain.finiteChainRegion_subset_expanded a n p s) A) =
      ManyBody.placeAlong (X := fun _ ↦ Fin d)
        (ManyBody.chainWindow p (by omega : p + n ≤ (p + n) + s))
        (SpinChain.intervalCoordinates d a n A) := by
  classical
  ext row col
  rw [MPSTensor.placeAlong_chainWindow_apply]
  have h := SpinChain.intervalCoordinates_localInclusion_apply d a n p s A row col
  by_cases hOutside : ∀ i : Fin ((p + n) + s),
      ¬ (p ≤ i.val ∧ i.val < p + n) → row i = col i
  · simpa only [eq_true hOutside, ite_true, mul_one] using h
  · simpa only [eq_false hOutside, ite_false, mul_zero] using h

/-- The actual buffered window matrix is the matrix placed on the window of the `n`
consecutive sites starting at `p`, with every exterior site carrying the identity.
Source: arXiv:1703.09188, Appendix, lines 2292–2295. -/
theorem bufferedWindowMatrix_eq_placeAlong_chainWindow
    (d n p s : ℕ) (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    bufferedWindowMatrix d n p s A =
      ManyBody.placeAlong (X := fun _ ↦ Fin d)
        (ManyBody.chainWindow p (by omega : p + n ≤ p + (n + s))) A := by
  let B := (SpinChain.intervalCoordinates d 0 n).symm A
  have hA : SpinChain.intervalCoordinates d 0 n B = A := by
    exact StarAlgEquiv.apply_symm_apply _ A
  have hBuffer := SpinChain.intervalCoordinates_localInclusion_eq_bufferedWindowMatrix
    d n p s 0 B
  rw [hA] at hBuffer
  have hWindow := intervalCoordinates_localInclusion_eq_placeAlong_chainWindow d n p s 0 B
  rw! (castMode := .all) [Nat.add_assoc] at hWindow
  rw [hBuffer, hA] at hWindow
  exact hWindow

/-- The buffered actual window acts only on its indicated finite interval.
Source: arXiv:1703.09188, Appendix, lines 2292–2295. -/
theorem bufferedWindowMatrix_mem_supportedOperators
    (d n p s : ℕ)
    (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    bufferedWindowMatrix d n p s A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (Finset.univ.filter fun (i : Fin (p + (n + s))) ↦ p ≤ i.val ∧ i.val < p + n) := by
  rw [bufferedWindowMatrix_eq_placeAlong_chainWindow d n p s]
  have hmem := ManyBody.placeAlong_mem_supportedOperators (X := fun _ ↦ Fin d)
    (ManyBody.chainWindow p (by omega : p + n ≤ p + (n + s))) A
  rw [ManyBody.map_chainWindow] at hmem
  exact hmem

/-- The actual forward finite MPU conjugation has the standard-form
window support in the existing supported-operator algebra. This is the
base finite support bound transported cyclically to address the seam.
Source: arXiv:1703.09188, StandardForm/SF and eq:appendix-1,
lines 603–622 and 2300–2306. -/
theorem mpo_bufferedWindow_conjugation_mem_supportedOperators
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    (k p s : ℕ) (hN : 1 < p + (3 * (2 * k) + s))
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (A : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ) :
    mpo U (p + (3 * (2 * k) + s)) *
        bufferedWindowMatrix d (3 * (2 * k)) p s (originalSiteHeisenbergInputWindow d k A) *
        (mpo U (p + (3 * (2 * k) + s)))ᴴ ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d)
        (Finset.univ.filter fun (i : Fin (p + (3 * (2 * k) + s))) ↦
            p ≤ i.val ∧ i.val < p + 3 * (2 * k)) := by
  rw [mpo_bufferedWindow_conjugation hU k p s hN S A]
  exact bufferedWindowMatrix_mem_supportedOperators d (3 * (2 * k)) p s
    (originalSiteHeisenbergOutputWindow k u v A)

/-- The source input window is exactly the placement on its complete central
interval of `2k` consecutive sites. Source: arXiv:1703.09188,
StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem originalSiteHeisenbergInputWindow_eq_placeAlong_chainWindow
    (d k : ℕ)
    (A : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ) :
    originalSiteHeisenbergInputWindow d k A =
      ManyBody.placeAlong (X := fun _ ↦ Fin d)
        (ManyBody.chainWindow (2 * k) (by omega : 2 * k + 2 * k ≤ 3 * (2 * k)))
        (Matrix.reindex (originalSiteHeisenbergCentreEquiv d k)
          (originalSiteHeisenbergCentreEquiv d k) A) := by
  let C := Matrix.reindex (originalSiteHeisenbergCentreEquiv d k)
    (originalSiteHeisenbergCentreEquiv d k) A
  let B := (SpinChain.intervalCoordinates d (2 * k : ℕ) (2 * k)).symm C
  have hWindow := intervalCoordinates_localInclusion_eq_placeAlong_chainWindow
    d (2 * k) (2 * k) (2 * k) (2 * k : ℕ) B
  have hB : SpinChain.intervalCoordinates d (2 * k : ℕ) (2 * k) B = C :=
    StarAlgEquiv.apply_symm_apply _ C
  rw [hB] at hWindow
  rw! (castMode := .all) [sub_self,
    show (2 * k + 2 * k) + 2 * k = 3 * (2 * k) by omega] at hWindow
  have hSource := SpinChain.intervalCoordinates_centralInclusion_originalSiteHeisenbergInputWindow
    d k 0 A
  rw! (castMode := .all) [zero_add] at hSource
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
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    (C : Matrix (Fin (2 * k) → Fin d) (Fin (2 * k) → Fin d) ℂ) :
    mpo U (p + (3 * (2 * k) + s)) *
        ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow (p + 2 * k)
          (by omega : p + 2 * k + 2 * k ≤ p + (3 * (2 * k) + s))) C *
        (mpo U (p + (3 * (2 * k) + s)))ᴴ ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d)
        (Finset.univ.filter fun (i : Fin (p + (3 * (2 * k) + s))) ↦
            p ≤ i.val ∧ i.val < p + 3 * (2 * k)) := by
  classical
  let E := originalSiteHeisenbergCentreEquiv d k
  let A := Matrix.reindex E.symm E.symm C
  have hA : Matrix.reindex E E A = C := by
    ext row col
    simp [A, Matrix.reindex_apply]
  have hPlaced : bufferedWindowMatrix d (3 * (2 * k)) p s
      (originalSiteHeisenbergInputWindow d k A) =
      ManyBody.placeAlong (X := fun _ ↦ Fin d) (ManyBody.chainWindow (p + 2 * k)
        (by omega : p + 2 * k + 2 * k ≤ p + (3 * (2 * k) + s))) C := by
    rw [bufferedWindowMatrix_eq_placeAlong_chainWindow d (3 * (2 * k)) p s,
      originalSiteHeisenbergInputWindow_eq_placeAlong_chainWindow d k,
      ManyBody.placeAlong_placeAlong, ManyBody.chainWindow_trans_chainWindow, hA]
  have h := mpo_bufferedWindow_conjugation_mem_supportedOperators hU k p s
    (by omega) S A
  rw [hPlaced] at h
  exact h

/-- Every finite operator supported on the central interval has the
actual standard-form forward bound; a window matrix is recovered from
support membership rather than supplied as a separate premise.
Source: arXiv:1703.09188, StandardForm/SF and eq:appendix-1,
lines 603–622 and 2300–2306. -/
theorem mpo_conjugation_mem_supportedOperators_central
    {d D ℓ r : ℕ} {U : MPOTensor d D} (hU : U.IsMPU)
    (k p s : ℕ) (hk : 0 < k)
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo (blockTensor U k)) u v)
    {A : Matrix (Fin (p + (3 * (2 * k) + s)) → Fin d)
      (Fin (p + (3 * (2 * k) + s)) → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (Finset.univ.filter fun (i : Fin (p + (3 * (2 * k) + s))) ↦
          p + 2 * k ≤ i.val ∧ i.val < (p + 2 * k) + 2 * k)) :
    mpo U (p + (3 * (2 * k) + s)) * A * (mpo U (p + (3 * (2 * k) + s)))ᴴ ∈
      ManyBody.supportedOperators (fun _ ↦ Fin d)
        (Finset.univ.filter fun (i : Fin (p + (3 * (2 * k) + s))) ↦
            p ≤ i.val ∧ i.val < p + 3 * (2 * k)) := by
  have hA' : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (Finset.univ.map
      (ManyBody.chainWindow (p + 2 * k)
        (by omega : (p + 2 * k) + 2 * k ≤ p + (3 * (2 * k) + s)))) := by
    rw [ManyBody.map_chainWindow]
    exact hA
  obtain ⟨C, rfl⟩ := ManyBody.exists_eq_placeAlong_of_mem_supportedOperators _ hA'
  exact mpo_chainWindow_conjugation_mem_supportedOperators hU k p s hk S C

end MPOTensor

end

section

open scoped Matrix Kronecker

namespace MPOTensor

/-- The actual six-half-block output is the placement on its four consecutive
middle half blocks, with identity exterior half blocks.
Source: CPSV17, StandardForm and Appendix, lines 603–622 and 2300–2334. -/
theorem originalSiteHeisenbergOutputWindow_eq_placeAlong_chainWindow
    {d ℓ r : ℕ} (k : ℕ)
    (u : Matrix (Fin ℓ × Fin r)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ)
    (v : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ)
    (A : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ) :
    originalSiteHeisenbergOutputWindow k u v A =
      ManyBody.placeAlong (X := fun _ ↦ Fin d)
        (ManyBody.chainWindow k (by omega : k + 4 * k ≤ 3 * (2 * k)))
        (Matrix.reindex (originalSiteHeisenbergOutputCentreEquiv d k)
          (originalSiteHeisenbergOutputCentreEquiv d k) (twoLinkOutputObservable u v A)) := by
  classical
  ext row col
  obtain ⟨⟨e, c⟩, rfl⟩ := (originalSiteHeisenbergOutputWindowEquiv d k).surjective row
  obtain ⟨⟨e', c'⟩, rfl⟩ := (originalSiteHeisenbergOutputWindowEquiv d k).surjective col
  rw [MPSTensor.placeAlong_chainWindow_apply]
  simp only [originalSiteHeisenbergOutputWindow, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, originalSiteHeisenbergOutputWindowEquiv_middle,
    originalSiteHeisenbergOutputWindowEquiv_outside_eq_iff]
  by_cases he : e = e' <;> simp [he]

/-- The actual fixed output acts only on the four middle half blocks,
namely the original-site interval from k through 5k−1. No support conclusion
is supplied as a hypothesis. Source: CPSV17, Appendix, lines 2300–2334. -/
theorem originalSiteHeisenbergOutputWindow_mem_supportedOperators
    {d ℓ r : ℕ} (k : ℕ)
    (u : Matrix (Fin ℓ × Fin r)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ)
    (v : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ)
    (A : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ) :
    originalSiteHeisenbergOutputWindow k u v A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
      (Finset.univ.filter fun (i : Fin (3 * (2 * k))) ↦ k ≤ i.val ∧ i.val < k + 4 * k) := by
  rw [originalSiteHeisenbergOutputWindow_eq_placeAlong_chainWindow k u v A]
  have hmem := ManyBody.placeAlong_mem_supportedOperators (X := fun _ ↦ Fin d)
    (ManyBody.chainWindow k (by omega : k + 4 * k ≤ 3 * (2 * k)))
    (Matrix.reindex (originalSiteHeisenbergOutputCentreEquiv d k)
      (originalSiteHeisenbergOutputCentreEquiv d k) (twoLinkOutputObservable u v A))
  rw [ManyBody.map_chainWindow] at hmem
  exact hmem

end MPOTensor

end
