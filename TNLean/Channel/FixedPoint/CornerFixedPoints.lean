/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.Algebra
import TNLean.Channel.FixedPoint.CornerAlgebra
import TNLean.Channel.Spectral.Support
import TNLean.MPS.CanonicalForm.CyclicSectors.Compression

/-!
# Corner-restricted fixed points form a `*`-algebra (Wolf Corollary 6.6)

This file formalizes Wolf Corollary 6.6. Let `T*(Y) = ∑ᵢ Kᵢ† Y Kᵢ` be a
trace-preserving Schwarz map (here represented by a Kraus family `K`, so that
`T* = adjointMap K` and unitality of `T*` is `IsTP K`). Let `ρ` be the
maximum-rank fixed point of the Schrödinger map `T(X) = ∑ᵢ Kᵢ X Kᵢ†` and let
`Q := supportProj ρ` be its support projection. Then the corner-restricted
fixed-point set
`{Y ∈ Q M_D(ℂ) Q | Q T*(Y) Q = Y}`
is a `*`-subalgebra of the corner algebra `Q M_D(ℂ) Q`.

The proof follows Wolf: the stated set is exactly the fixed-point set of the
compressed adjoint map on the support sector. The compressed Kraus family is
trace-preserving on the sector and the compressed Schrödinger map has a
positive-definite (full-rank) fixed point, so Wolf Theorem 6.12 applies.
The `*`-algebra structure is then transported back to the ambient corner along
the compression isomorphism `φ : M_n(ℂ) ≃ Q M_D(ℂ) Q`.

## Main declarations

* `Kraus.cornerCompressionKraus`: the compressed Kraus family `Q Kᵢ Q`.
* `Kraus.cornerFixedPointsStarSubalgebra`: Wolf Corollary 6.6 — the
  corner-restricted fixed points form a `StarSubalgebra` of the corner algebra.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 6.6, Section 6.4]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The compressed Kraus family `Q Kᵢ Q` attached to a projection `Q`. -/
noncomputable def cornerCompressionKraus (K : Fin d → Mat) (Q : Mat) : Fin d → Mat :=
  fun i => Q * K i * Q

section Hypotheses

/-- For an orthogonal projection `Q`, the compressed family `Q Kᵢ Q` is supported
on the corner: `Q (Q Kᵢ Q) Q = Q Kᵢ Q`. -/
theorem cornerCompressionKraus_supported
    (K : Fin d → Mat) {Q : Mat} (hQ : IsOrthogonalProjection Q) :
    ∀ i : Fin d, Q * cornerCompressionKraus K Q i * Q = cornerCompressionKraus K Q i := by
  intro i
  have hQidem : Q * Q = Q := hQ.2
  simp only [cornerCompressionKraus]
  rw [show Q * (Q * K i * Q) * Q = (Q * Q) * K i * (Q * Q) by
    simp [Matrix.mul_assoc], hQidem]

/-- Trace-preservation of the compressed family on the corner:
`∑ᵢ (Q Kᵢ Q)† (Q Kᵢ Q) = Q`, using unitality `∑ᵢ Kᵢ† Kᵢ = 1` and the
support-invariance identity `Kᵢ Q = Q Kᵢ Q`. -/
theorem cornerCompressionKraus_isTP
    (K : Fin d → Mat) (h_tp : IsTP K) {Q : Mat} (hQ : IsOrthogonalProjection Q)
    (hInv : ∀ i : Fin d, (1 - Q) * K i * Q = 0) :
    ∑ i : Fin d, (cornerCompressionKraus K Q i)ᴴ * cornerCompressionKraus K Q i = Q := by
  have hQidem : Q * Q = Q := hQ.2
  have hQherm : Qᴴ = Q := hQ.1.eq
  -- `Kᵢ Q = Q Kᵢ Q` from `(1 - Q) Kᵢ Q = 0`.
  have hKQ : ∀ i : Fin d, K i * Q = Q * K i * Q := by
    intro i
    have h := hInv i
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  calc
    ∑ i : Fin d, (cornerCompressionKraus K Q i)ᴴ * cornerCompressionKraus K Q i
        = ∑ i : Fin d, (Q * (K i)ᴴ * Q) * (Q * K i * Q) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [cornerCompressionKraus, Matrix.conjTranspose_mul, hQherm,
            Matrix.mul_assoc]
    _ = ∑ i : Fin d, Q * ((K i)ᴴ * K i) * Q := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hKQ' : Q * K i * Q = K i * Q := (hKQ i).symm
          calc
            (Q * (K i)ᴴ * Q) * (Q * K i * Q)
                = (Q * (K i)ᴴ * Q) * (K i * Q) := by rw [hKQ']
            _ = Q * (K i)ᴴ * (Q * K i) * Q := by simp [Matrix.mul_assoc]
            _ = Q * (K i)ᴴ * (Q * K i * Q) := by simp [Matrix.mul_assoc]
            _ = Q * (K i)ᴴ * (K i * Q) := by rw [hKQ']
            _ = Q * ((K i)ᴴ * K i) * Q := by simp [Matrix.mul_assoc]
    _ = Q * (∑ i : Fin d, (K i)ᴴ * K i) * Q := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = Q := by rw [h_tp, Matrix.mul_one, hQidem]

/-- On the corner `Q M_D Q`, the adjoint of the compressed family acts as the
ambient adjoint map sandwiched by `Q`: `adjointMap (Q Kᵢ Q) Z = Q (adjointMap K Z) Q`
for every `Z` with `Q Z Q = Z`. -/
theorem adjointMap_cornerCompressionKraus_eq
    (K : Fin d → Mat) {Q : Mat} (hQ : IsOrthogonalProjection Q)
    {Z : Mat} (hZ : Q * Z * Q = Z) :
    adjointMap (cornerCompressionKraus K Q) Z = Q * adjointMap K Z * Q := by
  have hQherm : Qᴴ = Q := hQ.1.eq
  calc
    adjointMap (cornerCompressionKraus K Q) Z
        = ∑ i : Fin d, (Q * K i * Q)ᴴ * Z * (Q * K i * Q) := by
          simp only [adjointMap, cornerCompressionKraus]
    _ = ∑ i : Fin d, Q * ((K i)ᴴ * (Q * Z * Q) * K i) * Q := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [Matrix.conjTranspose_mul, hQherm]
          simp [Matrix.mul_assoc]
    _ = ∑ i : Fin d, Q * ((K i)ᴴ * Z * K i) * Q := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hZ]
    _ = Q * (∑ i : Fin d, (K i)ᴴ * Z * K i) * Q := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = Q * adjointMap K Z * Q := by rw [adjointMap_apply]

/-- On the corner `Q M_D Q`, the compressed family's Schrödinger map acts as the
ambient map sandwiched by `Q`: `map (Q Kᵢ Q) Z = Q (map K Z) Q` for every `Z` with
`Q Z Q = Z`. -/
theorem map_cornerCompressionKraus_eq
    (K : Fin d → Mat) {Q : Mat} (hQ : IsOrthogonalProjection Q)
    {Z : Mat} (hZ : Q * Z * Q = Z) :
    map (cornerCompressionKraus K Q) Z = Q * map K Z * Q := by
  have hQherm : Qᴴ = Q := hQ.1.eq
  calc
    map (cornerCompressionKraus K Q) Z
        = ∑ i : Fin d, (Q * K i * Q) * Z * (Q * K i * Q)ᴴ := by
          simp only [map, cornerCompressionKraus]
    _ = ∑ i : Fin d, Q * (K i * (Q * Z * Q) * (K i)ᴴ) * Q := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [Matrix.conjTranspose_mul, hQherm]
          simp [Matrix.mul_assoc]
    _ = ∑ i : Fin d, Q * (K i * Z * (K i)ᴴ) * Q := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hZ]
    _ = Q * (∑ i : Fin d, K i * Z * (K i)ᴴ) * Q := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = Q * map K Z * Q := by rw [map_apply]

end Hypotheses

section CornerFixedPoints

/-- The support projection `Q := supportProj ρ` of a PSD matrix `ρ`. When `ρ` is
the (maximum-rank) fixed point of `map K`, this is Wolf's projection onto the
maximum-rank fixed point. -/
noncomputable def stationaryProj {ρ : Mat} (hρ_psd : ρ.PosSemidef) : Mat :=
  MPSTensor.supportProj (D := D) ρ hρ_psd

/-- `stationaryProj` is an orthogonal projection. -/
theorem isOrthogonalProjection_stationaryProj {ρ : Mat} (hρ_psd : ρ.PosSemidef) :
    IsOrthogonalProjection (stationaryProj hρ_psd) :=
  MPSTensor.isOrthogonalProjection_supportProj (D := D) (ρ := ρ) (hρ := hρ_psd)

/-- The lower-triangular vanishing `(1 - Q) Kᵢ Q = 0`, the support-invariance
identity used to compress the channel. -/
theorem stationaryProj_lowerZero (K : Fin d → Mat) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ) :
    ∀ i : Fin d, (1 - stationaryProj hρ_psd) * K i * stationaryProj hρ_psd = 0 := by
  have hρ_fix' : MPSTensor.transferMap (d := d) (D := D) K ρ = ρ := by
    simpa [map, MPSTensor.transferMap_apply] using hρ_fix
  have h := MPSTensor.lowerZero_of_posSemidef_fixedPoint (d := d) (D := D) K ρ hρ_psd hρ_fix'
  simpa [stationaryProj] using h.2

/-- `Q * adjointMap K Q * Q = Q`, i.e. the corner unit `Q` is fixed by the
corner-restricted map. -/
theorem cornerFixed_one
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ) :
    stationaryProj hρ_psd * adjointMap K (stationaryProj hρ_psd) *
      stationaryProj hρ_psd = stationaryProj hρ_psd := by
  set Q : Mat := stationaryProj hρ_psd with hQdef
  have hQproj : IsOrthogonalProjection Q := isOrthogonalProjection_stationaryProj hρ_psd
  have hQidem : Q * Q = Q := hQproj.2
  have hInv : ∀ i : Fin d, (1 - Q) * K i * Q = 0 :=
    stationaryProj_lowerZero K hρ_psd hρ_fix
  -- `adjointMap A Q = ∑ Aᵢ† Aᵢ = Q`, and on the corner `adjointMap A Q = Q (adjointMap K Q) Q`.
  have hAtp : ∑ i : Fin d, (cornerCompressionKraus K Q i)ᴴ * cornerCompressionKraus K Q i = Q :=
    cornerCompressionKraus_isTP K h_tp hQproj hInv
  have hQQQ : Q * Q * Q = Q := by rw [hQidem, hQidem]
  have hcorner := adjointMap_cornerCompressionKraus_eq K hQproj (Z := Q) hQQQ
  have hAQ : adjointMap (cornerCompressionKraus K Q) Q = Q := by
    have hQA : ∀ i : Fin d, Q * cornerCompressionKraus K Q i = cornerCompressionKraus K Q i := by
      intro i
      simp only [cornerCompressionKraus]
      rw [show Q * (Q * K i * Q) = (Q * Q) * K i * Q by simp [Matrix.mul_assoc], hQidem]
    calc
      adjointMap (cornerCompressionKraus K Q) Q
          = ∑ i : Fin d, (cornerCompressionKraus K Q i)ᴴ * (Q * cornerCompressionKraus K Q i) := by
            simp only [adjointMap, Matrix.mul_assoc]
      _ = ∑ i : Fin d, (cornerCompressionKraus K Q i)ᴴ * cornerCompressionKraus K Q i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hQA i]
      _ = Q := hAtp
  rw [← hcorner, hAQ]

/-- Multiplication closure of the corner-restricted fixed-point set: if `Y₁, Y₂`
lie in the corner and satisfy `Q (adjointMap K Yⱼ) Q = Yⱼ`, then so does `Y₁ Y₂`.
This is the load-bearing `*`-algebra step, proved by compressing to the support
sector and invoking Wolf Theorem 6.12 there. -/
theorem cornerFixed_mul
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ) {Y₁ Y₂ : Mat}
    (hY₁mem : stationaryProj hρ_psd * Y₁ * stationaryProj hρ_psd = Y₁)
    (hY₂mem : stationaryProj hρ_psd * Y₂ * stationaryProj hρ_psd = Y₂)
    (hY₁fix : stationaryProj hρ_psd * adjointMap K Y₁ * stationaryProj hρ_psd = Y₁)
    (hY₂fix : stationaryProj hρ_psd * adjointMap K Y₂ * stationaryProj hρ_psd = Y₂) :
    stationaryProj hρ_psd * adjointMap K (Y₁ * Y₂) * stationaryProj hρ_psd = Y₁ * Y₂ := by
  classical
  set Q : Mat := stationaryProj hρ_psd with hQdef
  have hQproj : IsOrthogonalProjection Q := isOrthogonalProjection_stationaryProj hρ_psd
  have hQidem : Q * Q = Q := hQproj.2
  have hQherm : Qᴴ = Q := hQproj.1.eq
  have hInv : ∀ i : Fin d, (1 - Q) * K i * Q = 0 :=
    stationaryProj_lowerZero K hρ_psd hρ_fix
  have hQρ : Q * ρ = ρ := MPSTensor.supportProj_mul (D := D) (ρ := ρ) hρ_psd
  have hρQ : ρ * Q = ρ := MPSTensor.mul_supportProj (D := D) (ρ := ρ) hρ_psd
  have hQρQ : Q * ρ * Q = ρ := by rw [hQρ, hρQ]
  set A : Fin d → Mat := cornerCompressionKraus K Q with hAdef
  have hAsupp : ∀ i : Fin d, Q * A i * Q = A i :=
    cornerCompressionKraus_supported K hQproj
  have hAtp : ∑ i : Fin d, (A i)ᴴ * A i = Q :=
    cornerCompressionKraus_isTP K h_tp hQproj hInv
  obtain ⟨n, C, φ, V, _hdim, hCtp, _hMpv, hIntertw, hMul, _hStar, hLetter, hVtV, hVVt, hφV⟩ :=
    MPSTensor.exists_compressedTensor_of_supported_projection_with_letter_and_isometry
      A Q hQproj hAsupp hAtp
  have hCtp' : IsTP C := hCtp
  have hCi : ∀ i : Fin d, C i = Vᴴ * A i * V := by
    intro i
    have h : V * C i * Vᴴ = A i := by simpa [hφV] using hLetter i
    calc
      C i = (Vᴴ * V) * C i * (Vᴴ * V) := by rw [hVtV]; simp
      _ = Vᴴ * (V * C i * Vᴴ) * V := by simp [Matrix.mul_assoc]
      _ = Vᴴ * A i * V := by rw [h]
  set σ : Matrix (Fin n) (Fin n) ℂ := Vᴴ * ρ * V with hσdef
  have hσpd : σ.PosDef := by
    have := Matrix.PosSemidef.compression_on_support_posDef (D := D) (ρ := ρ) hρ_psd
      (k := n) (V := Vᴴ) (by simpa [Matrix.conjTranspose_conjTranspose] using hVtV)
      (by simpa [hQdef, stationaryProj, Matrix.conjTranspose_conjTranspose] using hVVt)
    simpa [hσdef, Matrix.conjTranspose_conjTranspose] using this
  have hσfix : map C σ = σ := by
    have hmapA : map A ρ = ρ := by
      have heq : map A ρ = Q * map K ρ * Q := by
        rw [hAdef]; exact map_cornerCompressionKraus_eq K hQproj (Z := ρ) hQρQ
      rw [heq, hρ_fix, hQρQ]
    have hterm : ∀ i : Fin d,
        C i * σ * (C i)ᴴ = Vᴴ * (A i * ρ * (A i)ᴴ) * V := by
      intro i
      have hCiH : (C i)ᴴ = Vᴴ * (A i)ᴴ * V := by
        rw [hCi i]
        simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [hCiH, hCi i, hσdef]
      calc
        Vᴴ * A i * V * (Vᴴ * ρ * V) * (Vᴴ * (A i)ᴴ * V)
            = Vᴴ * (A i * (V * Vᴴ) * ρ * (V * Vᴴ) * (A i)ᴴ) * V := by
              simp [Matrix.mul_assoc]
        _ = Vᴴ * (A i * Q * ρ * Q * (A i)ᴴ) * V := by rw [hVVt]
        _ = Vᴴ * (A i * (Q * ρ * Q) * (A i)ᴴ) * V := by simp [Matrix.mul_assoc]
        _ = Vᴴ * (A i * ρ * (A i)ᴴ) * V := by rw [hQρQ]
    calc
      map C σ = ∑ i : Fin d, C i * σ * (C i)ᴴ := by rw [map_apply]
      _ = ∑ i : Fin d, Vᴴ * (A i * ρ * (A i)ᴴ) * V := by
          exact Finset.sum_congr rfl (fun i _ => hterm i)
      _ = Vᴴ * (∑ i : Fin d, A i * ρ * (A i)ᴴ) * V := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = Vᴴ * map A ρ * V := by rw [map_apply]
      _ = σ := by rw [hmapA, hσdef]
  -- Membership equivalence between the compressed and ambient fixed-point conditions.
  have hcorr : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      Q * adjointMap K (φ X).1 * Q = (φ X).1 ↔ adjointMap C X = X := by
    intro X
    have hφmem : Q * (φ X).1 * Q = (φ X).1 := (φ X).2
    have hintertw' : (φ (adjointMap C X)).1 = Q * adjointMap K (φ X).1 * Q := by
      have h1 : (φ (MPSTensor.transferMap (d := d) (D := n) (fun i => (C i)ᴴ) X)).1 =
          MPSTensor.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((φ X).1) := hIntertw X
      have h2 : MPSTensor.transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((φ X).1) =
          adjointMap A (φ X).1 := by simp [adjointMap, MPSTensor.transferMap_apply]
      have h3 : adjointMap A (φ X).1 = Q * adjointMap K (φ X).1 * Q := by
        rw [hAdef]; exact adjointMap_cornerCompressionKraus_eq K hQproj hφmem
      have h4 : MPSTensor.transferMap (d := d) (D := n) (fun i => (C i)ᴴ) X =
          adjointMap C X := by simp [adjointMap, MPSTensor.transferMap_apply]
      rw [h4] at h1
      rw [h1, h2, h3]
    constructor
    · intro hfix
      have hval : (φ (adjointMap C X)).1 = (φ X).1 := by rw [hintertw', hfix]
      exact φ.injective (Subtype.ext hval)
    · intro hfix
      rw [← hintertw', hfix]
  -- Pull `Y₁, Y₂` back to the support sector via `φ`.
  set X₁ : Matrix (Fin n) (Fin n) ℂ := φ.symm ⟨Y₁, hY₁mem⟩ with hX₁def
  set X₂ : Matrix (Fin n) (Fin n) ℂ := φ.symm ⟨Y₂, hY₂mem⟩ with hX₂def
  have hφX₁ : (φ X₁).1 = Y₁ := by rw [hX₁def, LinearEquiv.apply_symm_apply]
  have hφX₂ : (φ X₂).1 = Y₂ := by rw [hX₂def, LinearEquiv.apply_symm_apply]
  -- `X₁, X₂` are fixed by `adjointMap C`.
  have hX₁fix : adjointMap C X₁ = X₁ := (hcorr X₁).mp (by rw [hφX₁]; exact hY₁fix)
  have hX₂fix : adjointMap C X₂ = X₂ := (hcorr X₂).mp (by rw [hφX₂]; exact hY₂fix)
  -- The compressed fixed points form a `*`-algebra (Wolf Theorem 6.12), so their
  -- product is again a fixed point.
  let S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    adjointFixedPointsStarSubalgebra (K := C) hCtp' hσpd hσfix
  have hX₁memS : X₁ ∈ S :=
    (mem_adjointFixedPointsStarSubalgebra (K := C) hCtp' hσpd hσfix X₁).2 hX₁fix
  have hX₂memS : X₂ ∈ S :=
    (mem_adjointFixedPointsStarSubalgebra (K := C) hCtp' hσpd hσfix X₂).2 hX₂fix
  have hX₁₂memS : X₁ * X₂ ∈ S := S.mul_mem hX₁memS hX₂memS
  have hX₁₂fix : adjointMap C (X₁ * X₂) = X₁ * X₂ :=
    (mem_adjointFixedPointsStarSubalgebra (K := C) hCtp' hσpd hσfix (X₁ * X₂)).1 hX₁₂memS
  -- Transport back: `φ (X₁ * X₂) = Y₁ * Y₂` and it is corner-fixed.
  have hφX₁₂ : (φ (X₁ * X₂)).1 = Y₁ * Y₂ := by
    rw [hMul X₁ X₂, hφX₁, hφX₂]
  have hfinal : Q * adjointMap K (φ (X₁ * X₂)).1 * Q = (φ (X₁ * X₂)).1 :=
    (hcorr (X₁ * X₂)).mpr hX₁₂fix
  rw [hφX₁₂] at hfinal
  exact hfinal

/-- **Wolf Corollary 6.6.**

Let `T*(Y) = ∑ᵢ Kᵢ† Y Kᵢ` (`= adjointMap K`) be a trace-preserving Schwarz map,
so unitality of `T*` is `IsTP K`. Let `ρ` be a PSD fixed point of the Schrödinger
map `T = map K`, with support projection `Q := stationaryProj`. Then the
corner-restricted fixed-point set
`{Y ∈ Q M_D(ℂ) Q | Q T*(Y) Q = Y}`
is a `StarSubalgebra` of the corner algebra `Q M_D(ℂ) Q`.

The carrier consists of the corner elements `Y : hQ.Corner` (`Q Y Q = Y`) with
`Q (adjointMap K Y) Q = Y`. -/
noncomputable def cornerFixedPointsStarSubalgebra
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ) :
    letI hQ : IsIdempotentElem (stationaryProj hρ_psd) :=
      (isOrthogonalProjection_stationaryProj hρ_psd).2
    letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
      (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
    letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
      (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
    letI : StarModule ℂ hQ.Corner := MatrixCorner.cornerStarModuleComplex hQ
      (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
    StarSubalgebra ℂ hQ.Corner :=
  letI hQ : IsIdempotentElem (stationaryProj hρ_psd) :=
    (isOrthogonalProjection_stationaryProj hρ_psd).2
  letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
    (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
  letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
    (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
  letI : StarModule ℂ hQ.Corner := MatrixCorner.cornerStarModuleComplex hQ
    (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
  let Q : Mat := stationaryProj hρ_psd
  have hQproj : IsOrthogonalProjection Q := isOrthogonalProjection_stationaryProj hρ_psd
  have hQherm : Qᴴ = Q := hQproj.1.eq
  { carrier := {Y : hQ.Corner | Q * adjointMap K Y.1 * Q = Y.1}
    zero_mem' := by
      show Q * adjointMap K (0 : hQ.Corner).1 * Q = (0 : hQ.Corner).1
      show Q * adjointMap K (0 : Mat) * Q = (0 : Mat)
      simp [adjointMap]
    add_mem' := by
      intro X Y hX hY
      show Q * adjointMap K (X + Y).1 * Q = (X + Y).1
      show Q * adjointMap K (X.1 + Y.1) * Q = X.1 + Y.1
      rw [adjointMap_add, Matrix.mul_add, Matrix.add_mul, hX, hY]
    one_mem' := by
      show Q * adjointMap K (1 : hQ.Corner).1 * Q = (1 : hQ.Corner).1
      show Q * adjointMap K Q * Q = Q
      exact cornerFixed_one K h_tp hρ_psd hρ_fix
    mul_mem' := by
      intro X Y hX hY
      show Q * adjointMap K (X * Y).1 * Q = (X * Y).1
      show Q * adjointMap K (X.1 * Y.1) * Q = X.1 * Y.1
      have hXmem : Q * X.1 * Q = X.1 := by
        obtain ⟨hL, hR⟩ := (Subsemigroup.mem_corner_iff hQ).mp X.2
        rw [Matrix.mul_assoc, hR, hL]
      have hYmem : Q * Y.1 * Q = Y.1 := by
        obtain ⟨hL, hR⟩ := (Subsemigroup.mem_corner_iff hQ).mp Y.2
        rw [Matrix.mul_assoc, hR, hL]
      exact cornerFixed_mul K h_tp hρ_psd hρ_fix hXmem hYmem hX hY
    algebraMap_mem' := by
      intro c
      show Q * adjointMap K (algebraMap ℂ hQ.Corner c).1 * Q = (algebraMap ℂ hQ.Corner c).1
      show Q * adjointMap K (c • Q) * Q = c • Q
      rw [adjointMap_smul, Matrix.mul_smul, Matrix.smul_mul,
        cornerFixed_one K h_tp hρ_psd hρ_fix]
    star_mem' := by
      intro X hX
      show Q * adjointMap K (star X).1 * Q = (star X).1
      show Q * adjointMap K X.1ᴴ * Q = X.1ᴴ
      rw [adjointMap_conjTranspose]
      have h := congrArg Matrix.conjTranspose hX
      simpa [Matrix.conjTranspose_mul, hQherm, Matrix.mul_assoc] using h }

/-- Membership in the corner fixed-point `*`-algebra of Wolf Corollary 6.6: a
corner element `Y` lies in it exactly when `Q (adjointMap K Y) Q = Y`, i.e. `Y`
is fixed by the corner-restricted map. -/
@[simp] theorem mem_cornerFixedPointsStarSubalgebra
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ)
    (hQ : IsIdempotentElem (stationaryProj hρ_psd) :=
      (isOrthogonalProjection_stationaryProj hρ_psd).2)
    (Y : hQ.Corner) :
    letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
      (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
    letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
      (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
    letI : StarModule ℂ hQ.Corner := MatrixCorner.cornerStarModuleComplex hQ
      (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
    Y ∈ cornerFixedPointsStarSubalgebra K h_tp hρ_psd hρ_fix ↔
      stationaryProj hρ_psd * adjointMap K Y.1 * stationaryProj hρ_psd = Y.1 :=
  Iff.rfl

end CornerFixedPoints

end Kraus
