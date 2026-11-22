/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Shift.SwapSymmetryTransport
import TNLean.MPS.MPU.CanonicalForm.PhysicalAncillaLeftMul

/-!
# Obstructions to dimension-only swap stabilization

The flattened swap at physical dimension four does not preserve the image
of the identity-ancilla embedding from dimension two. Thus no action at
dimension two can be semiconjugate to this swap-combined action through
that embedding. Separately, the canonical flattened swaps at dimensions
four and sixteen do not intertwine the embedding from four to sixteen.
The witnesses are first-coordinate projections, independently of any
canonical-form or path construction.

For equal positive physical dimensions, balanced coprime ancillas are both
one. This explains separately why the current coprime-ancilla predicate
cannot express arbitrary common ancillary factors.

These are obstructions to two proposed interpretations, not refutations
of the source's symmetry-comparison lemma. Source: arXiv:1703.09188,
`def:equivalent-symmetry`, lines 1356--1366, and `lemma:sym-trafo-swap`,
lines 2065--2085; see `docs/paper-gaps/mpu_symmetry_ancilla_transport.tex`.
-/

open scoped Matrix

namespace MPOTensor

private theorem shiftSwap_sandwich_apply (d : ℕ)
    (X : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) (i j : Fin (d * d)) :
    (shiftPhysicalSwap d * X * shiftPhysicalSwap d) i j =
      X (bondPairSwap i) (bondPairSwap j) := by
  simp only [shiftPhysicalSwap, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, bondPairSwapEquiv_symm, bondPairSwapEquiv_apply, id_eq]

private theorem chainShiftSwap_sandwich_apply (d N : ℕ)
    (X : Matrix (Fin N → Fin (d * d)) (Fin N → Fin (d * d)) ℂ)
    (σ τ : Fin N → Fin (d * d)) :
    ((Matrix.piKronecker fun _ : Fin N ↦ (shiftPhysicalSwap d)) * X *
      (Matrix.piKronecker fun _ : Fin N ↦ (shiftPhysicalSwap d))) σ τ =
        X (fun n => bondPairSwap (σ n)) (fun n => bondPairSwap (τ n)) := by
  classical
  let e : Equiv.Perm (Fin N → Fin (d * d)) :=
    Equiv.piCongrRight (fun _ => bondPairSwapEquiv d)
  have hC : (Matrix.piKronecker fun _ : Fin N ↦ (shiftPhysicalSwap d)) =
      Equiv.Perm.permMatrix ℂ e := by
    ext s t
    simp only [Matrix.piKronecker_apply, shiftPhysicalSwap, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply]
    rw [Fintype.prod_boole]
    simp [e, funext_iff]
  rw [hC]
  simp only [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply]
  rfl

/-- A globally coherent family cannot have swap-combined adjunction at
physical dimension \(d^2\) when the original species has two distinct basis
states. Compatibility from dimension \(d\) would require a swapped ancillary
projection to stay in the identity-ancilla image.
Source context: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366. -/
theorem symmetryFamily_at_ne_shiftSwapDagger
    (S : FiniteChainOperatorSymmetryFamily) {d : ℕ} (a b : Fin d) (hab : a ≠ b) :
    S.at (d * d) ≠ shiftSwapDaggerSymmetry d := by
  intro hS
  let P : Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ :=
    fun σ τ => if σ 0 = a ∧ τ 0 = a then 1 else 0
  let Y : Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ := S.action P
  have hcompat := S.tensorPhysicalId_semiconj d d 1 P
  change tensorPhysicalIdOperator Y d =
    (S.at (d * d)).action (tensorPhysicalIdOperator P d) at hcompat
  rw [hS] at hcompat
  change tensorPhysicalIdOperator Y d =
    (Matrix.piKronecker fun _ : Fin 1 ↦ (shiftPhysicalSwap d)) * (tensorPhysicalIdOperator P d)ᴴ *
      (Matrix.piKronecker fun _ : Fin 1 ↦ (shiftPhysicalSwap d)) at hcompat
  have hzero := congrFun (congrFun hcompat (fun _ => finProdFinEquiv (a, a)))
    (fun _ => finProdFinEquiv (a, a))
  have hone := congrFun (congrFun hcompat (fun _ => finProdFinEquiv (a, b)))
    (fun _ => finProdFinEquiv (a, b))
  simp only [chainShiftSwap_sandwich_apply, Matrix.conjTranspose_apply] at hzero hone
  have hbad : (1 : ℂ) = 0 := by
    simp [tensorPhysicalIdOperator, Matrix.reindex_apply, finTupleProdEquiv,
      Equiv.arrowCongr, Function.comp_def, bondPairSwap] at hzero hone
    simpa [P, Ne.symm hab] using hzero.symm.trans hone
  norm_num at hbad

/-- A globally coherent family cannot have swap-combined transposition at
physical dimension \(d^2\) for a species with two distinct basis states,
already at chain length one.
Source context: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366. -/
theorem symmetryFamily_at_ne_shiftSwapTranspose
    (S : FiniteChainOperatorSymmetryFamily) {d : ℕ} (a b : Fin d) (hab : a ≠ b) :
    S.at (d * d) ≠ shiftSwapTransposeSymmetry d := by
  intro hS
  let P : Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ :=
    fun σ τ => if σ 0 = a ∧ τ 0 = a then 1 else 0
  let Y : Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ := S.action P
  have hcompat := S.tensorPhysicalId_semiconj d d 1 P
  change tensorPhysicalIdOperator Y d =
    (S.at (d * d)).action (tensorPhysicalIdOperator P d) at hcompat
  rw [hS] at hcompat
  change tensorPhysicalIdOperator Y d =
    (Matrix.piKronecker fun _ : Fin 1 ↦ (shiftPhysicalSwap d)) * (tensorPhysicalIdOperator P d)ᵀ *
      (Matrix.piKronecker fun _ : Fin 1 ↦ (shiftPhysicalSwap d)) at hcompat
  have hzero := congrFun (congrFun hcompat (fun _ => finProdFinEquiv (a, a)))
    (fun _ => finProdFinEquiv (a, a))
  have hone := congrFun (congrFun hcompat (fun _ => finProdFinEquiv (a, b)))
    (fun _ => finProdFinEquiv (a, b))
  simp only [chainShiftSwap_sandwich_apply, Matrix.transpose_apply] at hzero hone
  have hbad : (1 : ℂ) = 0 := by
    simp [tensorPhysicalIdOperator, Matrix.reindex_apply, finTupleProdEquiv,
      Equiv.arrowCongr, Function.comp_def, bondPairSwap] at hzero hone
    simpa [P, Ne.symm hab] using hzero.symm.trans hone
  norm_num at hbad

/-- The flattened swap takes a two-dimensional matrix tensored with an
identity outside that embedding image. The two diagonal entries over the
same original coordinate become one and zero.
This obstructs realizing the swap-combined source symmetry as a component
of a family compatible with every identity-ancilla embedding. Source
context: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366. -/
theorem shiftSwap_sandwich_not_mem_range_physicalIdMatrix :
    let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 0 1
    shiftPhysicalSwap 2 * physicalIdMatrix P 2 * shiftPhysicalSwap 2 ∉
      Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℂ => physicalIdMatrix Y 2) := by
  dsimp only
  rintro ⟨Y, h⟩
  have hzero := congrFun (congrFun h (0 : Fin 4)) (0 : Fin 4)
  have hone := congrFun (congrFun h (1 : Fin 4)) (1 : Fin 4)
  norm_num [physicalIdMatrix, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, shiftSwap_sandwich_apply, Matrix.single, bondPairSwap,
    finProdFinEquiv] at hzero hone
  have hbad : (1 : ℂ) = 0 := hzero.symm.trans hone
  norm_num at hbad

/-- No action at physical dimension two can be semiconjugate through an
identity ancilla to canonical swap-combined adjunction at dimension four.
This is a necessary-condition obstruction for the dimension-only family,
not a counterexample to the labelled-spin source interpretation.
Source context: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366. -/
theorem not_semiconj_physicalIdMatrix_to_shiftSwapDagger
    (f : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :
    ¬Function.Semiconj (fun X : Matrix (Fin 2) (Fin 2) ℂ => physicalIdMatrix X 2)
      f (fun X => shiftPhysicalSwap 2 * Xᴴ * shiftPhysicalSwap 2) := by
  intro h
  let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 0 1
  have hP : Pᴴ = P := by simp [P, Matrix.conjTranspose_single]
  have hPx : (physicalIdMatrix P 2)ᴴ = physicalIdMatrix P 2 := by
    rw [physicalIdMatrix_conjTranspose, hP]
  have hcompat : physicalIdMatrix (f P) 2 =
      shiftPhysicalSwap 2 * (physicalIdMatrix P 2)ᴴ * shiftPhysicalSwap 2 := h P
  rw [hPx] at hcompat
  exact shiftSwap_sandwich_not_mem_range_physicalIdMatrix ⟨f P, hcompat⟩

/-- No action at dimension two can be semiconjugate through an identity
ancilla to canonical swap-combined transposition at dimension four.
Source context: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366. -/
theorem not_semiconj_physicalIdMatrix_to_shiftSwapTranspose
    (f : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :
    ¬Function.Semiconj (fun X : Matrix (Fin 2) (Fin 2) ℂ => physicalIdMatrix X 2)
      f (fun X => shiftPhysicalSwap 2 * Xᵀ * shiftPhysicalSwap 2) := by
  intro h
  let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 0 1
  have hP : Pᵀ = P := by
    ext i j
    simp [P, Matrix.transpose_apply, Matrix.single, and_comm]
  have hPx : (physicalIdMatrix P 2)ᵀ = physicalIdMatrix P 2 := by
    rw [physicalIdMatrix_transpose, hP]
  have hcompat : physicalIdMatrix (f P) 2 =
      shiftPhysicalSwap 2 * (physicalIdMatrix P 2)ᵀ * shiftPhysicalSwap 2 := h P
  rw [hPx] at hcompat
  exact shiftSwap_sandwich_not_mem_range_physicalIdMatrix ⟨f P, hcompat⟩

/-- Enlarging a four-dimensional site by a four-dimensional identity does
not intertwine conjugation by the original flattened swap with conjugation
by the flattened swap at dimension sixteen. At coordinate one the two
diagonal entries are respectively one and zero.
This is an obstruction to a dimension-only interpretation of the swap in
arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366. -/
theorem physicalIdMatrix_shiftSwap_sandwich_ne :
    let P : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 0 1
    physicalIdMatrix (shiftPhysicalSwap 2 * P * shiftPhysicalSwap 2) 4 ≠
      shiftPhysicalSwap 4 * physicalIdMatrix P 4 * shiftPhysicalSwap 4 := by
  dsimp only
  intro h
  have hentry := congrFun (congrFun h (1 : Fin 16)) (1 : Fin 16)
  norm_num [physicalIdMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
    shiftPhysicalSwap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.single, bondPairSwapEquiv, bondPairSwap, finProdFinEquiv,
    Fin.divNat, Fin.modNat] at hentry

/-- Canonical flattened-swap adjunction at dimensions four and sixteen
fails the identity-ancilla semiconjugacy required of a coherent family.
Source context: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366. -/
theorem not_semiconj_physicalIdMatrix_shiftSwapDagger :
    ¬Function.Semiconj
      (fun X : Matrix (Fin 4) (Fin 4) ℂ => physicalIdMatrix X 4)
      (fun X => shiftPhysicalSwap 2 * Xᴴ * shiftPhysicalSwap 2)
      (fun X => shiftPhysicalSwap 4 * Xᴴ * shiftPhysicalSwap 4) := by
  intro h
  let P : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 0 1
  have hP : Pᴴ = P := by simp [P, Matrix.conjTranspose_single]
  have hPx : (physicalIdMatrix P 4)ᴴ = physicalIdMatrix P 4 := by
    rw [physicalIdMatrix_conjTranspose, hP]
  have hcompat : physicalIdMatrix (shiftPhysicalSwap 2 * Pᴴ * shiftPhysicalSwap 2) 4 =
      shiftPhysicalSwap 4 * (physicalIdMatrix P 4)ᴴ * shiftPhysicalSwap 4 := h P
  rw [hP, hPx] at hcompat
  exact physicalIdMatrix_shiftSwap_sandwich_ne hcompat

/-- Canonical flattened-swap transposition at dimensions four and sixteen
fails the identity-ancilla semiconjugacy required of a coherent family.
Source context: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366. -/
theorem not_semiconj_physicalIdMatrix_shiftSwapTranspose :
    ¬Function.Semiconj
      (fun X : Matrix (Fin 4) (Fin 4) ℂ => physicalIdMatrix X 4)
      (fun X => shiftPhysicalSwap 2 * Xᵀ * shiftPhysicalSwap 2)
      (fun X => shiftPhysicalSwap 4 * Xᵀ * shiftPhysicalSwap 4) := by
  intro h
  let P : Matrix (Fin 4) (Fin 4) ℂ := Matrix.single 0 0 1
  have hP : Pᵀ = P := by
    ext i j
    simp [P, Matrix.transpose_apply, Matrix.single, and_comm]
  have hPx : (physicalIdMatrix P 4)ᵀ = physicalIdMatrix P 4 := by
    rw [physicalIdMatrix_transpose, hP]
  have hcompat : physicalIdMatrix (shiftPhysicalSwap 2 * Pᵀ * shiftPhysicalSwap 2) 4 =
      shiftPhysicalSwap 4 * (physicalIdMatrix P 4)ᵀ * shiftPhysicalSwap 4 := h P
  rw [hP, hPx] at hcompat
  exact physicalIdMatrix_shiftSwap_sandwich_ne hcompat

/-- Equal positive physical dimensions force balanced coprime ancillary
sizes to be one. The later common-ancilla construction in the source is
therefore outside a definition restricted to the minimal coprime pair.
Source: arXiv:1703.09188, lines 706--724 and 2210--2215. -/
theorem balanced_coprime_ancilla_eq_one {d pa pb : ℕ} (hd : 0 < d)
    (hbalance : pa * d = pb * d) (hcoprime : Nat.Coprime pa pb) :
    pa = 1 ∧ pb = 1 := by
  have hab : pa = pb := mul_right_cancel₀ hd.ne' hbalance
  subst pb
  have hpa : pa = 1 := by simpa using hcoprime
  exact ⟨hpa, hpa⟩

end MPOTensor
