import TNLean.Channel.Peripheral.CyclicDecomposition
import TNLean.Channel.Peripheral.Conjugation
import TNLean.MPS.Irreducible.FormII
import TNLean.MPS.Structure.InvariantSubspaceDecomp
import TNLean.MPS.Core.BlockingInfrastructure

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.NoncommRing

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex KadisonSchwarz

namespace MPSTensor

variable {d D : ℕ}

/-!
# Cyclic sector decomposition for blocked periodic tensors

This file develops the tensor-side part of the cyclic decomposition story from
arXiv:1708.00029.  The current implementation focuses on the honest MPS-level
block decomposition step:

* if a blocked tensor commutes with a family of orthogonal projections summing to
  `1`, then it decomposes into compressed sectors whose direct-sum tensor is
  `SameMPV₂`-equivalent to the original blocked tensor;
* if the original tensor is left-canonical, then each compressed sector is also
  left-canonical;
* cyclic projections coming from the channel-side decomposition give the needed
  commuting projections after blocking by a multiple of the period.

The deeper sector properties (primitive / irreducible) are handled later by
transporting the channel-side corner results to these compressed tensors.
-/

section BasicProjectionWordLemmas

/-- Left-multiply every letter by `P`. -/
noncomputable def leftSectorTensor (P : MatrixAlg D) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => P * A i

/-- If `P` commutes with every letter of `A`, then it commutes with every evaluated word. -/
lemma commutes_evalWord_of_commutes_letters
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d), P * evalWord A w = evalWord A w * P := by
  intro w
  induction w with
  | nil => simp [evalWord]
  | cons i w ih =>
      calc
        P * evalWord A (i :: w)
            = P * (A i * evalWord A w) := by simp [evalWord]
        _ = (P * A i) * evalWord A w := by simp [Matrix.mul_assoc]
        _ = (A i * P) * evalWord A w := by rw [hComm i]
        _ = A i * (P * evalWord A w) := by simp [Matrix.mul_assoc]
        _ = A i * (evalWord A w * P) := by rw [ih]
        _ = (A i * evalWord A w) * P := by simp [Matrix.mul_assoc]
        _ = evalWord A (i :: w) * P := by simp [evalWord]

/-- If `P` is idempotent and commutes with the letters of `A`, then sandwiching the evaluated
word of the left-sector tensor by `P` recovers `P * evalWord A w`.  This version is valid even
for the empty word. -/
lemma left_mul_evalWord_leftSectorTensor_of_commutes
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d),
      P * evalWord (leftSectorTensor P A) w = P * evalWord A w := by
  intro w
  induction w with
  | nil => simp [evalWord]
  | cons i w ih =>
      calc
        P * evalWord (leftSectorTensor P A) (i :: w)
            = P * ((P * A i) * evalWord (leftSectorTensor P A) w) := by
                simp [leftSectorTensor, evalWord]
        _ = (P * P) * A i * evalWord (leftSectorTensor P A) w := by
                simp [Matrix.mul_assoc]
        _ = P * A i * evalWord (leftSectorTensor P A) w := by rw [hPidem]
        _ = A i * (P * evalWord (leftSectorTensor P A) w) := by
                rw [hComm i]
                simp [Matrix.mul_assoc]
        _ = A i * (P * evalWord A w) := by rw [ih]
        _ = P * A i * evalWord A w := by
                rw [hComm i]
                simp [Matrix.mul_assoc]
        _ = P * evalWord A (i :: w) := by simp [evalWord, Matrix.mul_assoc]

/-- A left-sector tensor is supported on the sector projection. -/
lemma leftSectorTensor_supported
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ i : Fin d, P * leftSectorTensor P A i * P = leftSectorTensor P A i := by
  intro i
  calc
    P * leftSectorTensor P A i * P = P * (P * A i) * P := by simp [leftSectorTensor]
    _ = (P * P) * A i * P := by simp [Matrix.mul_assoc]
    _ = P * A i * P := by rw [hPidem]
    _ = P * A i := by rw [hComm i, Matrix.mul_assoc, hPidem]
    _ = leftSectorTensor P A i := by simp [leftSectorTensor]

end BasicProjectionWordLemmas

section Compression

variable {P : MatrixAlg D}

/-- Word evaluation of the unitary-conjugated tensor. -/
private lemma evalWord_conj_unitary
    (A : MPSTensor d D) (U : Matrix.unitaryGroup (Fin D) ℂ) :
    ∀ w : List (Fin d),
      evalWord (fun i => (↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D)) w =
        (↑U : MatrixAlg D)ᴴ * evalWord A w * (↑U : MatrixAlg D) := by
  intro w
  induction w with
  | nil =>
      have hUU : (↑U : MatrixAlg D)ᴴ * (↑U : MatrixAlg D) = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
      simp [evalWord, hUU]
  | cons i w ih =>
      have hUU : (↑U : MatrixAlg D) * (↑U : MatrixAlg D)ᴴ = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem U.prop
      calc
        evalWord (fun i => (↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D)) (i :: w)
            = ((↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D)) *
                evalWord (fun i => (↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D)) w := by
                  simp [evalWord]
        _ = ((↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D)) *
              ((↑U : MatrixAlg D)ᴴ * evalWord A w * (↑U : MatrixAlg D)) := by rw [ih]
        _ = (↑U : MatrixAlg D)ᴴ * A i * ((↑U : MatrixAlg D) * (↑U : MatrixAlg D)ᴴ) *
              evalWord A w * (↑U : MatrixAlg D) := by
                noncomm_ring
        _ = (↑U : MatrixAlg D)ᴴ * evalWord A (i :: w) * (↑U : MatrixAlg D) := by
                simp [evalWord, Matrix.mul_assoc, hUU]

/-- Compress a tensor supported on an orthogonal projection to the corresponding sector bond
space.  The compressed tensor has the same sector MPVs and inherits the left-canonical equation.
-/
theorem exists_compressedTensor_of_supported_projection
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv C σ = Matrix.trace (P * evalWord A (List.ofFn σ))) := by
  /-
  Main remaining proof obligation for the tensor-side cyclic sector construction:

  * diagonalize the orthogonal projection `P` as in
    `InvariantSubspaceDecomp.exists_twoBlock_decomp_of_lowerZero`;
  * extract the `1`-eigenspace block of a tensor supported on `P`;
  * identify its MPV with `trace (P * evalWord A w)`;
  * transport the left-canonical equation `∑ Aᵢ† Aᵢ = P` to the compressed block.

  This is the core basis-compression lemma needed to turn padded sectors into
  honest smaller-bond tensors.  The surrounding API in this file is already set
  up to consume exactly this statement.
  -/
  sorry

end Compression

section CommutingProjectionDecomposition

variable {m : ℕ}

/-- If a left-canonical tensor commutes with a family of orthogonal projections summing to `1`,
then it decomposes into compressed sectors whose direct-sum tensor is `SameMPV₂`-equivalent to the
original tensor. -/
theorem exists_blockDecomp_of_commuting_projections
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) := by
  /-
  The intended proof is now short from
  `exists_compressedTensor_of_supported_projection`:

  1. replace each sector by the padded tensor `i ↦ Pₖ * Aᵢ`;
  2. use commutation with `Pₖ` to show support on `Pₖ` and the local TP equation
     `∑ (Pₖ Aᵢ)† (Pₖ Aᵢ) = Pₖ`;
  3. compress each padded sector with the previous theorem;
  4. sum the trace identities using `∑ₖ Pₖ = 1` to obtain `SameMPV₂`.

  This is precisely the honest `N = 0`-aware direct-sum decomposition step.
  -/
  sorry

end CommutingProjectionDecomposition

section FixedAdjointProjection

/-- A fixed orthogonal projection for the adjoint blocked map commutes with every Kraus operator
of the blocked tensor. -/
theorem commutes_letters_of_adjoint_fixed_projection
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : MatrixAlg D} (hP : IsOrthogonalProjection P)
    (hFix : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) P = P) :
    ∀ i : Fin d, P * A i = A i * P := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hTPK : IsTPKraus (d := d) (D := D) A := by simpa [IsTPKraus] using hLeft
  have hUnitalK : IsUnitalKraus (d := d) (D := D) K :=
    KadisonSchwarz.isUnitalKraus_conjTranspose (d := d) (D := D) (K := A) hTPK
  have hKFix : krausMap K P = P := by
    simpa [K, KadisonSchwarz.krausMap, MPSTensor.transferMap_apply] using hFix
  have hEq : krausMap K (Pᴴ * P) = (krausMap K P)ᴴ * krausMap K P := by
    calc
      krausMap K (Pᴴ * P) = krausMap K P := by simp [(hP.1.eq), (hP.2)]
      _ = P := hKFix
      _ = Pᴴ * P := by simp [(hP.1.eq), (hP.2)]
      _ = (krausMap K P)ᴴ * krausMap K P := by simp [hKFix]
  intro i
  have hComm := KadisonSchwarz.kraus_commute_of_ks_equality (K := K) hUnitalK P hEq i
  simpa [K, hKFix] using hComm

theorem exists_blockDecomp_of_adjoint_fixed_projections
    {m : ℕ}
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hFix : ∀ k : Fin m, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) = P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) := by
  have hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k := by
    intro k i
    exact
      commutes_letters_of_adjoint_fixed_projection
        (A := A) hLeft (hP := hPproj k) (hFix := hFix k) i
  exact exists_blockDecomp_of_commuting_projections A P hPproj hPsum hLeft hComm

end FixedAdjointProjection

end MPSTensor
