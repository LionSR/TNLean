/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Irreducible.DiagonalFixedPoint
import TNLean.MPS.Tensor.DirectSum.InvariantSubspaceDecomp
import TNLean.MPS.Transfer.Irreducible.BlockingInfrastructure
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.Compression
import QICLean.Algebra.Matrix.MatrixAux
import TNLean.MPS.Transfer.Irreducible.PeriodicBlocking
import QICLean.Channel.Semigroup.CPClosure
import QICLean.Algebra.Hermitian.CornerCompression

/-!
# Cyclic-sector decompositions from fixed adjoint projections

This file derives commuting-projection decompositions from orthogonal
projections fixed by the adjoint transfer map.

## Main declarations

* `commutes_letters_of_adjoint_fixed_projection`
* `exists_blockDecomp_of_adjoint_fixed_projections_with_letter_and_isometry`
* `offDiag_shift_of_adjoint_cyclic_shift`
* `eq_sum_offDiag_of_adjoint_cyclic_shift`
* `offDiag_shift_evalWord_of_adjoint_cyclic_shift`
* `MPSTensor.leftSectorTensor`, `MPSTensor.left_mul_evalWord_leftSectorTensor_of_commutes`: basic
  projection word lemmas for cyclic-sector decompositions.
* `MPSTensor.exists_blockDecomp_of_commuting_projections_with_letter_and_isometry`,
  `MPSTensor.exists_blockDecomp_of_commuting_projections_with_letter`: cyclic-sector decompositions
  from commuting projections.
* `pairwise_mul_zero_of_orthogonalProjection_sum_one`,
  `TNLean.MPS.CanonicalForm.preservesCorner_of_adjoint_fixed_projection`: sector irreducibility:
  projection orthogonality and
  corner preservation.

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
* [De las Cuevas–Cirac–Schuch–Pérez-García, arXiv:1708.00029, eq:Aoffdiag]
* [Wolf, *Quantum Channels & Operations*, Chapter 6]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

section Basic

/-!
## Basic projection word lemmas for cyclic-sector decompositions

This file contains the projection-word identities used throughout the
cyclic-sector normalization argument.

### Main declarations

* `leftSectorTensor`
* `left_mul_evalWord_leftSectorTensor_of_commutes`

### References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
-/

open Matrix Finset Complex

namespace MPSTensor

variable {d D : ℕ}

section BasicProjectionWordLemmas

/-- Left-multiply every letter by `P`. -/
noncomputable def leftSectorTensor (P : MatrixAlg D) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => P * A i

lemma left_mul_evalWord_leftSectorTensor_of_commutes
    (P : MatrixAlg D) (A : MPSTensor d D)
    (hPidem : P * P = P)
    (hComm : ∀ i : Fin d, P * A i = A i * P) :
    ∀ w : List (Fin d),
      P * Kraus.evalWord (leftSectorTensor P A) w = P * Kraus.evalWord A w := by
  intro w
  induction w with
  | nil =>
      simp only [Kraus.evalWord]
  | cons i w ih =>
      simp only [leftSectorTensor, Kraus.evalWord]
      calc P * (P * A i * Kraus.evalWord (leftSectorTensor P A) w)
          = P * P * A i * Kraus.evalWord (leftSectorTensor P A) w := by
            simp only [Matrix.mul_assoc]
        _ = P * A i * Kraus.evalWord (leftSectorTensor P A) w := by rw [hPidem]
        _ = A i * (P * Kraus.evalWord (leftSectorTensor P A) w) := by
            rw [← Matrix.mul_assoc, hComm i, Matrix.mul_assoc]
        _ = A i * (P * Kraus.evalWord A w) := by rw [ih]
        _ = P * (A i * Kraus.evalWord A w) := by
            rw [← Matrix.mul_assoc, ← hComm i, Matrix.mul_assoc]

end BasicProjectionWordLemmas

end MPSTensor

end Basic

section CommutingProj

/-!
## Cyclic-sector decompositions from commuting projections

This file assembles the per-sector compression theorem into a direct-sum
decomposition when a left-canonical tensor commutes with a family of
orthogonal projections.

### Main declarations

* `exists_blockDecomp_of_commuting_projections_with_letter_and_isometry`
* `exists_blockDecomp_of_commuting_projections_with_letter`

### References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
-/

open Matrix Finset Complex

namespace MPSTensor

variable {d D : ℕ}

section CommutingProjectionDecomposition

variable {m : ℕ}

/-- If a left-canonical tensor commutes with a family of orthogonal projections summing to `1`,
then it decomposes into compressed sectors whose direct-sum tensor is `SameMPV₂`-equivalent to the
original tensor. The compression isomorphism also sends each compressed sector
letter to the corresponding ambient corner P_k A_i P_k.

For each sector k, the compression isomorphism φ_k identifies the compressed
matrix algebra with the corner of P_k. Its intertwining identity identifies
the compressed adjoint transfer map with the sector adjoint transfer map on
that corner, so irreducibility and primitivity are preserved across the
compression. -/
theorem exists_blockDecomp_of_commuting_projections_with_letter_and_isometry
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
      (V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * Kraus.evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (Kraus.transferMap (ι := Fin d) (n := Fin (dim k))
            (fun i => (blocks k i)ᴴ) X)).1 =
          Kraus.transferMap (ι := Fin d) (n := Fin D)
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
  -- For each k, sector tensor P_k * A_i is P_k-supported
  have hSectorSupp : ∀ k i, P k * (P k * A i) * P k = P k * A i := by
    intro k i
    rw [← Matrix.mul_assoc (P k) (P k) _, (hPproj k).2,
      hComm k i, Matrix.mul_assoc, (hPproj k).2]
  -- TP condition for each sector
  have hSectorTP : ∀ k, ∑ i : Fin d, (P k * A i)ᴴ * (P k * A i) = P k := by
    intro k
    have hterm : ∀ i, (P k * A i)ᴴ * (P k * A i) = (A i)ᴴ * A i * P k := by
      intro i
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P k)ᴴ (P k) (A i), (hPproj k).1.eq, (hPproj k).2]
      rw [hComm k i, ← Matrix.mul_assoc]
    simp_rw [hterm, ← Finset.sum_mul, hLeft, Matrix.one_mul]
  -- Apply compression to each sector
  choose dim blocks φ V hDim hTPblocks hMPVblocks hIntertwine hMul hStar hLetterRaw
    hV_iso hV_range hEmbed using fun k =>
    exists_compressedTensor_of_supported_projection_with_letter_and_isometry
      (fun i => P k * A i) (P k) (hPproj k) (hSectorSupp k) (hSectorTP k)
  -- Per-sector trace relation: mpv(blocks k) σ = tr(P_k · Kraus.evalWord A σ)
  have hSectorTrace : ∀ k (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks k) σ = (P k * Kraus.evalWord A (List.ofFn σ)).trace := by
    intro k N σ
    rw [hMPVblocks k N σ]
    congr 1
    exact left_mul_evalWord_leftSectorTensor_of_commutes (P k) A (hPproj k).2 (hComm k) _
  have hLetter : ∀ k (i : Fin d), (φ k (blocks k i)).1 = P k * A i * P k := by
    intro k i
    calc
      (φ k (blocks k i)).1 = P k * A i := hLetterRaw k i
      _ = P k * A i * P k := by
          calc
            P k * A i = A i * P k := hComm k i
            _ = A i * (P k * P k) := by rw [(hPproj k).2]
            _ = (A i * P k) * P k := by rw [Matrix.mul_assoc]
            _ = (P k * A i) * P k := by rw [← hComm k i]
  refine ⟨dim, blocks, φ, V, hTPblocks, ?_, hSectorTrace, hIntertwine, hMul, hStar,
    hLetter, hV_iso, hV_range, hEmbed⟩
  -- SameMPV₂ follows from summing per-sector traces over the projection partition
  intro N σ
  rw [mpv_toTensorFromBlocks_eq_sum]; simp only [one_pow, one_smul]
  simp only [mpv, coeff]
  conv_lhs => rw [show Kraus.evalWord A (List.ofFn σ) = 1 * Kraus.evalWord A (List.ofFn σ) from by
    rw [Matrix.one_mul]]
  rw [show (1 : MatrixAlg D) = ∑ k : Fin m, P k from hPsum.symm]
  rw [Finset.sum_mul, Matrix.trace_sum]
  congr 1; ext k
  exact (hSectorTrace k N σ).symm

/-- If a left-canonical tensor commutes with a family of orthogonal projections summing to `1`,
then it decomposes into compressed sectors whose direct-sum tensor is `SameMPV₂`-equivalent to the
original tensor. The compression isomorphism also sends each compressed sector
letter to the corresponding ambient corner P_k A_i P_k.

This is the projection of
`exists_blockDecomp_of_commuting_projections_with_letter_and_isometry` that forgets
the support isometries. -/
theorem exists_blockDecomp_of_commuting_projections_with_letter
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hComm : ∀ k : Fin m, ∀ i : Fin d, P k * A i = A i * P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * Kraus.evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (Kraus.transferMap (ι := Fin d) (n := Fin (dim k))
            (fun i => (blocks k i)ᴴ) X)).1 =
          Kraus.transferMap (ι := Fin d) (n := Fin D)
            (fun i => (P k * A i)ᴴ) ((φ k X).1)) ∧
      (∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k Xᴴ).1 = ((φ k X).1)ᴴ) ∧
      (∀ k (i : Fin d), (φ k (blocks k i)).1 = P k * A i * P k) := by
  obtain ⟨dim, blocks, φ, _V, hTPblocks, hMPV, hSectorTrace, hIntertwine, hMul,
    hStar, hLetter, _hV_iso, _hV_range, _hEmbed⟩ :=
    exists_blockDecomp_of_commuting_projections_with_letter_and_isometry
      A P hPproj hPsum hLeft hComm
  exact ⟨dim, blocks, φ, hTPblocks, hMPV, hSectorTrace, hIntertwine, hMul, hStar,
    hLetter⟩

end CommutingProjectionDecomposition

end MPSTensor

end CommutingProj

section FixedAdjoint

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
    (hFix : Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) P = P) :
    ∀ i : Fin d, P * A i = A i * P := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hTPK : Kraus.IsTP A := hLeft
  have hUnitalK : IsUnitalKraus (d := d) (D := D) K :=
    KadisonSchwarz.isUnitalKraus_conjTranspose (d := d) (D := D) (K := A) hTPK
  have hKFix : krausMap K P = P := by
    simpa [K, KadisonSchwarz.krausMap, Kraus.transferMap_apply] using hFix
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

/-- Adjoint-fixed projections give compressed blocks, corner-letter identities, and support
isometries realizing the compression maps. -/
theorem exists_blockDecomp_of_adjoint_fixed_projections_with_letter_and_isometry
    {m : ℕ}
    (A : MPSTensor d D)
    (P : Fin m → MatrixAlg D)
    (hPproj : ∀ k : Fin m, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hFix : ∀ k : Fin m,
      Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P k) = P k) :
    ∃ (dim : Fin m → ℕ) (blocks : (k : Fin m) → MPSTensor d (dim k))
      (φ : (k : Fin m) →
        Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k))
      (V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ),
      (∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1) ∧
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := fun _ : Fin m => (1 : ℂ)) blocks) ∧
      (∀ k (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks k) σ = (P k * Kraus.evalWord A (List.ofFn σ)).trace) ∧
      (∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
        (φ k (Kraus.transferMap (ι := Fin d) (n := Fin (dim k))
            (fun i => (blocks k i)ᴴ) X)).1 =
          Kraus.transferMap (ι := Fin d) (n := Fin D)
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
eq:Aoffdiag, in inverse-indexed form: the compressed-to-global bridge that the
cyclic transport step contracts.
-/

variable {m : ℕ}

/-- **Single-site off-diagonal grading from the adjoint cyclic shift.**

If the orthogonal projections `P` are shifted by the adjoint transfer map,
`𝓔^*(P_{k+1}) = P_k`, then each Kraus operator carries index `k` to `k+1`:
`P_{k+1} · A_i = A_i · P_k`.  This is the single-site analogue of the
fixed-projection commutation `commutes_letters_of_adjoint_fixed_projection`;
see arXiv:1708.00029, eq:Aoffdiag, in inverse-indexed form.

The companion statement `kraus_mul_cyclicProj` in
`TNLean/Channel/Peripheral/CyclicDecomposition/LetterShift.lean` derives the
same shift for the direct orientation from the resolution of the identity
$\sum_kP_k=1$ instead of the unitality used here; the two hypothesis sets
are incomparable, so the two statements coexist. -/
theorem offDiag_shift_of_adjoint_cyclic_shift [NeZero m]
    (A : MPSTensor d D)
    (hLeft : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hShift : ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (k : Fin m) (i : Fin d) :
    P (k + 1) * A i = A i * P k := by
  let K : Fin d → MatrixAlg D := fun i => (A i)ᴴ
  have hTPK : Kraus.IsTP A := hLeft
  have hUnitalK : IsUnitalKraus (d := d) (D := D) K :=
    KadisonSchwarz.isUnitalKraus_conjTranspose (d := d) (D := D) (K := A) hTPK
  -- The adjoint transfer map agrees with the Kraus map of `K = Aᴴ`.
  have hKshift : krausMap K (P (k + 1)) = P k := by
    simpa [K, KadisonSchwarz.krausMap, Kraus.transferMap_apply] using hShift k
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
    (hShift : ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
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
    (hShift : ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (k : Fin m) (w : List (Fin d)) :
    P (k + w.length • (1 : Fin m)) * Kraus.evalWord A w = Kraus.evalWord A w * P k := by
  induction w generalizing k with
  | nil => simp
  | cons a w ih =>
    have hShiftLetter := offDiag_shift_of_adjoint_cyclic_shift A hLeft hPproj hShift
    rw [Kraus.evalWord_cons, List.length_cons, add_smul, one_smul, ← add_assoc,
      ← Matrix.mul_assoc, hShiftLetter (k + w.length • (1 : Fin m)) a,
      Matrix.mul_assoc, ih, ← Matrix.mul_assoc]

end CyclicShiftOffDiagonal

end MPSTensor

end FixedAdjoint

section ProjectionOrtho

/-!
## Sector irreducibility: projection orthogonality and corner preservation

This file contains the general linear-algebra input for the
sector-irreducibility development. It proves pairwise orthogonality for
orthogonal projections summing to `1`, and it shows that an adjoint-fixed
orthogonal projection for a trace-preserving tensor yields an invariant corner
algebra.

### Main statements

* `pairwise_mul_zero_of_orthogonalProjection_sum_one` — orthogonal projections
  summing to `1` are pairwise orthogonal.
* `TNLean.MPS.CanonicalForm.preservesCorner_of_adjoint_fixed_projection` — an adjoint-fixed
  orthogonal
  projection yields a preserved corner algebra.

### Tags

matrix product states, orthogonal projections, invariant corners
-/

open Matrix Finset Complex

/-! ### Orthogonal-projection pairwise orthogonality -/

variable {D m : ℕ}

/-! ### Corner preservation from adjoint fixed projections -/

variable {d : ℕ}

/-- If an orthogonal projection `P` is fixed by the adjoint transfer map
`T†(·) = ∑ᵢ Aᵢ† · Aᵢ` of a TP tensor, then `T†` preserves the corner
algebra `P · M_D(ℂ) · P`.

The proof derives `[P, Aᵢ] = 0` from
`MPSTensor.commutes_letters_of_adjoint_fixed_projection`, then threads the
idempotent relation `P² = P` through the corner sandwich. -/
theorem TNLean.MPS.CanonicalForm.preservesCorner_of_adjoint_fixed_projection
    (A : MPSTensor d D)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    {P : MatrixAlg D}
    (hP : IsOrthogonalProjection P)
    (hFix : Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) P = P) :
    PreservesCorner P (Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ)) := by
  have hComm : ∀ i : Fin d, P * A i = A i * P :=
    MPSTensor.commutes_letters_of_adjoint_fixed_projection (A := A) hTP (hP := hP) hFix
  have hCommAdj : ∀ i : Fin d, P * (A i)ᴴ = (A i)ᴴ * P := by
    intro i
    have h := congrArg Matrix.conjTranspose (hComm i)
    simpa [Matrix.conjTranspose_mul, hP.1.eq] using h.symm
  intro X
  simp only [Kraus.transferMap_apply, Finset.mul_sum, Finset.sum_mul,
    Matrix.conjTranspose_conjTranspose]
  refine Finset.sum_congr rfl ?_
  intro i _
  calc
    P * ((A i)ᴴ * (P * X * P) * A i) * P
        = (P * (A i)ᴴ) * (P * X * P) * (A i * P) := by
            simp only [Matrix.mul_assoc]
    _ = ((A i)ᴴ * P) * (P * X * P) * (P * A i) := by
          rw [hCommAdj i, ← hComm i]
    _ = (A i)ᴴ * ((P * P) * X * P) * (P * A i) := by
          simp only [Matrix.mul_assoc]
    _ = (A i)ᴴ * (P * X * P) * (P * A i) := by
          simp only [Matrix.mul_assoc, hP.2]
    _ = (A i)ᴴ * (P * X * P) * A i := by
          calc
            (A i)ᴴ * (P * X * P) * (P * A i)
                = (A i)ᴴ * ((P * X * P) * P) * A i := by
                    simp only [Matrix.mul_assoc]
            _ = (A i)ᴴ * (P * X * P) * A i := by
                    simp only [Matrix.mul_assoc, hP.2]

end ProjectionOrtho
