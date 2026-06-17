/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.CyclicSectors.CommutingProj

/-!
# Cyclic-sector decompositions from fixed adjoint projections

This file derives commuting-projection decompositions from orthogonal
projections fixed by the adjoint transfer map.

## Main declarations

* `commutes_letters_of_adjoint_fixed_projection`
* `exists_blockDecomp_of_adjoint_fixed_projections`
* `exists_blockDecomp_of_adjoint_fixed_projections_with_letter`
* `offDiag_shift_of_adjoint_cyclic_shift`
* `eq_sum_offDiag_of_adjoint_cyclic_shift`
* `offDiag_shift_evalWord_of_adjoint_cyclic_shift`

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
* [De las Cuevas–Cirac–Schuch–Pérez-García, arXiv:1708.00029, eq:Aoffdiag/eq:Auprop]
* [Wolf, *Quantum Channels & Operations*, Chapter 6]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex KadisonSchwarz

namespace MPSTensor

variable {d D : ℕ}

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
      krausMap K (Pᴴ * P) = krausMap K P := by
        simp only [hP.1.eq, hP.2]
      _ = P := hKFix
      _ = Pᴴ * P := by
        simp only [hP.1.eq, hP.2]
      _ = (krausMap K P)ᴴ * krausMap K P := by
        simp only [hKFix]
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
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (transferMap (d := d) (D := dim k)
            (fun i => (blocks k i)ᴴ) X)).1 =
          transferMap (d := d) (D := D)
            (fun i => (P k * A i)ᴴ) ((φ k X).1)) ∧
      (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) := by
  have hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k := by
    intro k i
    exact commutes_letters_of_adjoint_fixed_projection
        (A := A) hLeft (hP := hPproj k) (hFix := hFix k) i
  exact exists_blockDecomp_of_commuting_projections A P hPproj hPsum hLeft hComm

/-- Adjoint-fixed projections give compressed blocks, and the compression maps
send each compressed letter to the corresponding ambient corner.

This is the letter-level refinement of
`exists_blockDecomp_of_adjoint_fixed_projections`. -/
theorem exists_blockDecomp_of_adjoint_fixed_projections_with_letter
    {m : ℕ}
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hFix : ∀ k : Fin m, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) = P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (transferMap (d := d) (D := dim k)
            (fun i => (blocks k i)ᴴ) X)).1 =
          transferMap (d := d) (D := D)
            (fun i => (P k * A i)ᴴ) ((φ k X).1)) ∧
      (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) ∧
      (∀ k (i : Fin d), (φ k (blocks k i)).1 = P k * A i * P k) := by
  have hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k := by
    intro k i
    exact commutes_letters_of_adjoint_fixed_projection
        (A := A) hLeft (hP := hPproj k) (hFix := hFix k) i
  exact exists_blockDecomp_of_commuting_projections_with_letter A P hPproj hPsum hLeft hComm

/-- Adjoint-fixed projections give compressed blocks, corner-letter identities, and support
isometries realizing the compression maps. -/
theorem exists_blockDecomp_of_adjoint_fixed_projections_with_letter_and_isometry
    {m : ℕ}
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hFix : ∀ k : Fin m, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P k) = P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
      (V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (transferMap (d := d) (D := dim k)
            (fun i => (blocks k i)ᴴ) X)).1 =
          transferMap (d := d) (D := D)
            (fun i => (P k * A i)ᴴ) ((φ k X).1)) ∧
      (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) ∧
      (∀ k (i : Fin d), (φ k (blocks k i)).1 = P k * A i * P k) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k, V k * (V k)ᴴ = P k) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k X).1 = V k * X * (V k)ᴴ) := by
  have hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k := by
    intro k i
    exact commutes_letters_of_adjoint_fixed_projection
        (A := A) hLeft (hP := hPproj k) (hFix := hFix k) i
  exact exists_blockDecomp_of_commuting_projections_with_letter_and_isometry
    A P hPproj hPsum hLeft hComm

end FixedAdjointProjection

section CyclicShiftOffDiagonal

/-!
## Off-diagonal grading from the adjoint cyclic shift

For a family of orthogonal projections `P : Fin m → M_D(ℂ)` summing to `1` and
shifted by the adjoint transfer map, `𝓔^*(P_{k+1}) = P_k`, the Kraus operators
`A_i` carry index `k` to index `k+1`:
`P_{k+1} · A_i = A_i · P_k`.  Summing over the orthogonal grading then gives the
off-diagonal reconstruction `A_i = ∑_u P_{u+1} · A_i · P_u`.  This is the
single-site off-diagonal decomposition of a periodic block in arXiv:1708.00029,
eq:Aoffdiag/eq:Auprop: the compressed-to-global bridge that the cyclic transport
step contracts.
-/

variable {m : ℕ}

/-- **Single-site off-diagonal grading from the adjoint cyclic shift.**

If the orthogonal projections `P` are shifted by the adjoint transfer map,
`𝓔^*(P_{k+1}) = P_k`, then each Kraus operator carries index `k` to `k+1`:
`P_{k+1} · A_i = A_i · P_k`.  This is the single-site analogue of the
fixed-projection commutation `commutes_letters_of_adjoint_fixed_projection`;
see arXiv:1708.00029, eq:Auprop. -/
theorem offDiag_shift_of_adjoint_cyclic_shift [NeZero m]
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hShift : ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (k : Fin m) (i : Fin d) :
    P (k + 1) * A i = A i * P k := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hTPK : IsTPKraus (d := d) (D := D) A := by simpa [IsTPKraus] using hLeft
  have hUnitalK : IsUnitalKraus (d := d) (D := D) K :=
    KadisonSchwarz.isUnitalKraus_conjTranspose (d := d) (D := D) (K := A) hTPK
  -- The adjoint transfer map agrees with the Kraus map of `K = Aᴴ`.
  have hKshift : krausMap K (P (k + 1)) = P k := by
    simpa [K, KadisonSchwarz.krausMap, MPSTensor.transferMap_apply] using hShift k
  -- `P (k + 1)` is fixed by `Xᴴ * X = X`, and `𝓔^*(P (k + 1)) = P k` is itself a
  -- projection, so the Kadison–Schwarz gap vanishes at `P (k + 1)`.
  have hEq : krausMap K ((P (k + 1))ᴴ * P (k + 1)) =
      (krausMap K (P (k + 1)))ᴴ * krausMap K (P (k + 1)) := by
    calc
      krausMap K ((P (k + 1))ᴴ * P (k + 1)) = krausMap K (P (k + 1)) := by
        simp only [(hPproj (k + 1)).1.eq, (hPproj (k + 1)).2]
      _ = P k := hKshift
      _ = (P k)ᴴ * P k := by
        simp only [(hPproj k).1.eq, (hPproj k).2]
      _ = (krausMap K (P (k + 1)))ᴴ * krausMap K (P (k + 1)) := by
        simp only [hKshift]
  have hComm :=
    KadisonSchwarz.kraus_commute_of_ks_equality (K := K) hUnitalK (P (k + 1)) hEq i
  -- `kraus_commute_of_ks_equality` yields `P (k+1) * (Aᵢ)ᴴ ᴴ = (Aᵢ)ᴴ ᴴ * 𝓔^*(P (k+1))`.
  simpa [K, hKshift] using hComm

/-- **Off-diagonal reconstruction** `A_i = ∑_u P_{u+1} · A_i · P_u`.

With the projections summing to `1` and shifted by the adjoint transfer map, the
identity is graded into its single-site off-diagonal pieces.  See
arXiv:1708.00029, eq:Aoffdiag. -/
theorem eq_sum_offDiag_of_adjoint_cyclic_shift [NeZero m]
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hShift : ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (i : Fin d) :
    A i = ∑ u : Fin m, P (u + 1) * A i * P u := by
  have hShiftLetter := offDiag_shift_of_adjoint_cyclic_shift A hLeft hPproj hShift
  calc
    A i = A i * ∑ u : Fin m, P u := by rw [hPsum, Matrix.mul_one]
    _ = ∑ u : Fin m, A i * P u := by rw [Finset.mul_sum]
    -- Each summand carries index `u` to `u + 1` via the cyclic shift, and the
    -- right projector is recovered by idempotence: `P_{u+1}·Aᵢ·P_u = Aᵢ·P_u`.
    _ = ∑ u : Fin m, P (u + 1) * A i * P u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hShiftLetter u i, Matrix.mul_assoc, (hPproj u).2]

/-- **Telescoped off-diagonal shift across a word.**

The single-site grading `offDiag_shift_of_adjoint_cyclic_shift` accumulates one
step per letter: evaluating a word of length `ℓ` carries index `k` to
`k + ℓ·1` in `Fin m`.  This is the form contracted by the cyclic-transport step
of arXiv:1708.00029 (eq:Aoffdiag iterated across a block): for a length-`m`
word `ℓ·1 = 0`, recovering the same-index blocked commutation
`commutes_letters_of_adjoint_fixed_projection` for `blockTensor A m`. -/
theorem offDiag_shift_evalWord_of_adjoint_cyclic_shift [NeZero m]
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hShift : ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (k : Fin m) (w : List (Fin d)) :
    P (k + w.length • (1 : Fin m)) * evalWord A w = evalWord A w * P k := by
  induction w generalizing k with
  | nil => simp
  | cons a w ih =>
    have hShiftLetter := offDiag_shift_of_adjoint_cyclic_shift A hLeft hPproj hShift
    rw [evalWord_cons, List.length_cons, add_smul, one_smul, ← add_assoc,
      ← Matrix.mul_assoc, hShiftLetter (k + w.length • (1 : Fin m)) a,
      Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

end CyclicShiftOffDiagonal

end MPSTensor
