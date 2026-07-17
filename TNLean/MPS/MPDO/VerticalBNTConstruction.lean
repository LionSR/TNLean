/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RetainedClass

/-!
# Algebraic BNT construction for grouped vertical sectors

The representatives selected by the vertical grouping theorem form an
algebraic basis of normal tensors for the vertically viewed
tensor itself.  At positive chain length, the intertwining and literal
reconstruction identities identify its matrix product vector with that of the
weighted sector sum.

## Main result

* `IsHorizontalCF.isBNT_verticalTensor_of_grouping`: the grouped sector
  decomposition furnishes an `IsBNT` witness for the vertical tensor.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608,
  Proposition 4.13, lines 1863--1921.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Word evaluation respects a left intertwining by the adjoint of a sector
isometry. -/
private lemma conjTranspose_mul_evalWord_of_intertwining
    {s n : ℕ} (T : MPSTensor s d) (B : MPSTensor s n)
    (V : Matrix (Fin d) (Fin n) ℂ)
    (hinter : ∀ v, Vᴴ * T v = B v * Vᴴ) :
    ∀ w, Vᴴ * MPSTensor.evalWord T w = MPSTensor.evalWord B w * Vᴴ := by
  intro w
  induction w with
  | nil => simp
  | cons v w ih =>
      rw [MPSTensor.evalWord_cons, MPSTensor.evalWord_cons, ← Matrix.mul_assoc,
        hinter v, Matrix.mul_assoc, ih]
      exact (Matrix.mul_assoc _ _ _).symm

/-- A literal reconstruction by isometric intertwined sectors gives the
positive-length matrix product vector of their weighted block sum. -/
private lemma sameMPV₂Pos_toTensorFromBlocks_of_reconstruction
    {s r : ℕ} {dim : Fin r → ℕ}
    (T : MPSTensor s d) (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor s (dim k))
    (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hiso : ∀ k, (V k)ᴴ * V k = 1)
    (hinter : ∀ k v, (V k)ᴴ * T v = (μ k • blocks k v) * (V k)ᴴ)
    (hreconstruct : ∀ v, T v = ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ) :
    MPSTensor.SameMPV₂Pos T
      (MPSTensor.toTensorFromBlocks (d := s) (μ := μ) blocks) := by
  intro N hN σ
  rw [MPSTensor.mpv_toTensorFromBlocks_eq_sum]
  simp only [MPSTensor.mpv, MPSTensor.coeff]
  have hword : List.ofFn σ ≠ [] := by
    intro hzero
    have hlength := congrArg List.length hzero
    simp only [List.length_ofFn, List.length_nil] at hlength
    omega
  obtain ⟨v, w, hw⟩ := List.exists_cons_of_ne_nil hword
  rw [hw, MPSTensor.evalWord_cons, hreconstruct v, Finset.sum_mul,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hinterWord := conjTranspose_mul_evalWord_of_intertwining
    T (fun x => μ k • blocks k x) (V k) (hinter k) w
  calc
    Matrix.trace ((V k * (μ k • blocks k v) * (V k)ᴴ) *
        MPSTensor.evalWord T w) =
        Matrix.trace ((V k * (μ k • blocks k v)) *
          ((V k)ᴴ * MPSTensor.evalWord T w)) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = Matrix.trace (((V k)ᴴ * MPSTensor.evalWord T w) *
          (V k * (μ k • blocks k v))) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((MPSTensor.evalWord (fun x => μ k • blocks k x) w *
          (V k)ᴴ) * (V k * (μ k • blocks k v))) := by rw [hinterWord]
    _ = Matrix.trace (MPSTensor.evalWord (fun x => μ k • blocks k x) w *
          (μ k • blocks k v)) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V k)ᴴ (V k)
              (μ k • blocks k v), hiso k, Matrix.one_mul]
    _ = Matrix.trace ((μ k • blocks k v) *
          MPSTensor.evalWord (fun x => μ k • blocks k x) w) :=
            Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (MPSTensor.evalWord (fun x => μ k • blocks k x) (v :: w)) := by
            rfl
    _ = (μ k) ^ N * Matrix.trace (MPSTensor.evalWord (blocks k) (v :: w)) := by
      rw [MPSTensor.evalWord_smul, Matrix.trace_smul]
      simp only [smul_eq_mul]
      have hlength := congrArg List.length hw
      simp only [List.length_ofFn, List.length_cons] at hlength
      simp only [List.length_cons, hlength]

/-- The BNT representatives in a particular grouped vertical decomposition
form an algebraic BNT for the vertical tensor.

The hypotheses are precisely the dimension, isometry, intertwining,
reconstruction, and spectral-BNT clauses returned by
`IsHorizontalCF.exists_verticalBNTGrouping_with_isometry`.  The proof uses
those same witnesses to establish nonemptiness; it does not choose a second
vertical grouping.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1921. -/
theorem IsHorizontalCF.isBNT_verticalTensor_of_grouping
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M)
    {r : ℕ} {dim : Fin r → ℕ} (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
    (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hdimPos : ∀ k, 0 < dim k)
    (hiso : ∀ k, (V k)ᴴ * V k = 1)
    (hinter : ∀ k v,
      (V k)ᴴ * verticalTensor M v = (μ k • blocks k v) * (V k)ᴴ)
    (hreconstruct : ∀ v,
      verticalTensor M v = ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ)
    (hBNT : let C := MPSTensor.mpvPhaseClassData blocks
      MPSTensor.IsCPSVBasisOfNormalTensors
        (MPSTensor.toTensorFromBlocks (d := D * D) (μ := μ) blocks)
        (fun j => ⟨dim (C.repr j), blocks (C.repr j)⟩)) :
    let C := MPSTensor.mpvPhaseClassData blocks
    MPSTensor.IsBNT (verticalTensor M) C.g
      (fun j => dim (C.repr j)) (fun j => blocks (C.repr j)) := by
  classical
  let C := MPSTensor.mpvPhaseClassData blocks
  have hr : 0 < r := by
    by_contra hr
    have hrzero : r = 0 := Nat.eq_zero_of_not_pos hr
    apply hHorizontal.verticalTensor_ne_zero M
    funext v
    rw [hreconstruct v]
    subst r
    simp
  have hPositive : MPSTensor.SameMPV₂Pos (verticalTensor M)
      (MPSTensor.toTensorFromBlocks (d := D * D) (μ := μ) blocks) :=
    sameMPV₂Pos_toTensorFromBlocks_of_reconstruction
      (verticalTensor M) μ blocks V hiso hinter hreconstruct
  change MPSTensor.IsBNT (verticalTensor M) C.g
    (fun j => dim (C.repr j)) (fun j => blocks (C.repr j))
  refine ⟨?_, ?_, hBNT.eventually_li⟩
  · intro j
    letI : NeZero (dim (C.repr j)) := ⟨(hdimPos (C.repr j)).ne'⟩
    exact (hBNT.blocks_normal j).isNormal
  · intro N hN
    obtain ⟨c, hc⟩ := hBNT.spans_mpv N hN
    refine ⟨c, fun σ => ?_⟩
    rw [hPositive N hN σ]
    exact hc σ

end MPOTensor
