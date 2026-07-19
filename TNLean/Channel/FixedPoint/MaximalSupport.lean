/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.WeightedCornerFixedPoints
import TNLean.Channel.FixedPoint.MeanErgodicProjection
import TNLean.MPS.Core.CPPrimitive
import TNLean.Channel.FixedPoint.Cesaro

/-!
# A fixed point of maximal support

For a positive trace-preserving map $T$, the mean-ergodic image
$\rho_0=T_\infty(\mathbf 1)$ is a positive semidefinite fixed point whose support carries
every fixed point: $Q_0XQ_0=X$. This is the maximal-support proposition in Section 6.4
of *Quantum Channels & Operations* (Wolf 2012). The proof first decomposes every fixed
point into positive fixed points and then uses positivity of $T_\infty$ to dominate each
positive fixed point by a scalar multiple of $\rho_0$.

The preceding statement is proved for arbitrary positive trace-preserving maps. The
existing trace-preserving Kraus theorem is retained as its completely positive
specialization.

Instantiating the weighted corner fixed points at $\rho_0$ removes the corner-support
restriction: conjugation by $\sqrt{\rho_0}$ maps the weighted corner star-algebra
(`Kraus.weightedCornerFixedPointsStarSubalgebra`) onto the full fixed-point set of $T$,
which is the set $\rho_0^{-1/2}\,\{X \mid T(X) = X\}\,\rho_0^{-1/2}$ of Corollary 6.7 of
*Quantum Channels & Operations* (Wolf 2012), with the inverse square root taken on the
support of $\rho_0$.

## Main results

* `Kraus.stationaryProj_absorb_of_le_smul` -- domination by a scalar multiple transfers
  the support.
* `Kraus.stationaryProj_absorb_of_le` -- Loewner domination transfers the support: for
  positive semidefinite $P \preceq \rho$, the support projection of $\rho$ absorbs $P$.
* `IsPositiveMap.exists_maximalSupport_fixedPoint` -- $T_\infty(\mathbf 1)$ has support
  carrying every fixed point of a positive trace-preserving map.
* `Kraus.exists_maximalSupport_fixedPoint` -- a positive semidefinite fixed point whose
  support carries every fixed point.
* `Kraus.exists_maximalSupport_weightedCorner_sqrt_eq` -- at such a fixed point,
  conjugation by the square root maps the weighted corner carrier onto the full
  fixed-point set.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Domination by a scalar multiple transfers the support.** For positive semidefinite
matrices $P$ and $\rho$, if $P \preceq c\rho$, then the support projection $Q$ of $\rho$
absorbs $P$:
$Q P = P$ and $P Q = P$. From $(\mathbf 1 - Q)\rho = 0$ and
$0 \preceq (\mathbf 1 - Q) P (\mathbf 1 - Q) \preceq
(\mathbf 1 - Q)c\rho(\mathbf 1 - Q)
= 0$ one gets $(\mathbf 1 - Q)\sqrt{P}\,\bigl((\mathbf 1 - Q)\sqrt{P}\bigr)^{\dagger} = 0$,
hence $(\mathbf 1 - Q)\sqrt{P} = 0$ and $(\mathbf 1 - Q)P = 0$. -/
theorem stationaryProj_absorb_of_le_smul {ρ P : Mat} (hρ_psd : ρ.PosSemidef)
    (hP_psd : P.PosSemidef) (c : ℂ) (hle : P ≤ c • ρ) :
    stationaryProj hρ_psd * P = P ∧ P * stationaryProj hρ_psd = P := by
  set Q : Mat := stationaryProj hρ_psd
  have hQproj : IsOrthogonalProjection Q := isOrthogonalProjection_stationaryProj hρ_psd
  have hQherm : Qᴴ = Q := hQproj.1.eq
  have h1Q : (1 - Q)ᴴ = 1 - Q := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQherm]
  have hQρ : Q * ρ = ρ := MPSTensor.supportProj_mul (D := D) (ρ := ρ) hρ_psd
  -- The corner of `cρ` on the complement of the support vanishes.
  have hρ0 : (1 - Q) * (c • ρ) * (1 - Q) = 0 := by
    have h : (1 - Q) * ρ = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hQρ, sub_self]
    rw [Matrix.mul_smul, h, smul_zero, Matrix.zero_mul]
  -- Hence so does the corner of the dominated `P`.
  have hP0 : (1 - Q) * P * (1 - Q) = 0 := by
    have hupper : (1 - Q) * P * (1 - Q) ≤ 0 := by
      have hconj : (1 - Q) * P * (1 - Q) ≤ (1 - Q) * (c • ρ) * (1 - Q) := by
        rw [← sub_nonneg] at hle ⊢
        have hpsd : ((1 - Q)ᴴ * (c • ρ - P) * (1 - Q)).PosSemidef :=
          (hle.posSemidef).conjTranspose_mul_mul_same (1 - Q)
        rw [h1Q] at hpsd
        have heq : (1 - Q) * (c • ρ) * (1 - Q) - (1 - Q) * P * (1 - Q) =
            (1 - Q) * (c • ρ - P) * (1 - Q) := by
          rw [mul_sub (1 - Q) (c • ρ) P,
            sub_mul ((1 - Q) * (c • ρ)) ((1 - Q) * P) (1 - Q)]
        rw [heq]
        exact hpsd.nonneg
      calc (1 - Q) * P * (1 - Q) ≤ (1 - Q) * (c • ρ) * (1 - Q) := hconj
        _ = 0 := hρ0
    have hlower : (0 : Mat) ≤ (1 - Q) * P * (1 - Q) := by
      have : ((1 - Q)ᴴ * P * (1 - Q)).PosSemidef :=
        hP_psd.conjTranspose_mul_mul_same (1 - Q)
      rw [h1Q] at this
      exact this.nonneg
    exact le_antisymm hupper hlower
  -- Vanishing corner of a positive semidefinite matrix forces the whole row to vanish.
  have hS_herm : (CFC.sqrt P)ᴴ = CFC.sqrt P := MPSTensor.conjTranspose_cfc_sqrt (D := D) P
  have hSS : CFC.sqrt P * CFC.sqrt P = P := CFC.sqrt_mul_sqrt_self P hP_psd.nonneg
  have hM0 : ((1 - Q) * CFC.sqrt P) * ((1 - Q) * CFC.sqrt P)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, hS_herm, h1Q]
    calc (1 - Q) * CFC.sqrt P * (CFC.sqrt P * (1 - Q))
        = (1 - Q) * (CFC.sqrt P * CFC.sqrt P) * (1 - Q) := by simp [Matrix.mul_assoc]
      _ = (1 - Q) * P * (1 - Q) := by rw [hSS]
      _ = 0 := hP0
  have hMsqrt : (1 - Q) * CFC.sqrt P = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp hM0
  have hQP : Q * P = P := by
    have h : (1 - Q) * P = 0 := by
      calc (1 - Q) * P = ((1 - Q) * CFC.sqrt P) * CFC.sqrt P := by
            rw [Matrix.mul_assoc, hSS]
        _ = 0 := by rw [hMsqrt, Matrix.zero_mul]
    rw [Matrix.sub_mul, Matrix.one_mul] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨hQP, ?_⟩
  have h := congrArg Matrix.conjTranspose hQP
  rwa [Matrix.conjTranspose_mul, hQherm, hP_psd.isHermitian.eq] at h

/-- **Loewner domination transfers the support.** For positive semidefinite matrices
$P \preceq \rho$, the support projection of $\rho$ absorbs $P$. -/
theorem stationaryProj_absorb_of_le {ρ P : Mat} (hρ_psd : ρ.PosSemidef)
    (hP_psd : P.PosSemidef) (hle : P ≤ ρ) :
    stationaryProj hρ_psd * P = P ∧ P * stationaryProj hρ_psd = P := by
  simpa using stationaryProj_absorb_of_le_smul hρ_psd hP_psd 1 (by simpa using hle)

end Kraus

namespace IsPositiveMap

open Kraus

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Maximal support of fixed points.** Let $T$ be a positive trace-preserving
endomorphism of a full matrix algebra, and let $T_\infty$ be its mean-ergodic
projection. Then $\rho_0=T_\infty(\mathbf 1)$ is a positive semidefinite fixed point,
and its support projection $Q_0$ satisfies $Q_0XQ_0=X$ for every fixed point $X$ of
$T$.

This is Wolf, Proposition 6.9, “Maximal support of fixed points”; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1214--1235. The proof
uses Proposition 6.8 to decompose an arbitrary fixed point into positive fixed points.
For a positive fixed point $A$, positivity of $T_\infty$ applied to
$\operatorname{tr}(A)\mathbf 1-A$ gives
$A\preceq\operatorname{tr}(A)\rho_0$, so the support of $\rho_0$ absorbs $A$.

The restriction of $T$ to this support and the complementary zero summand required
by Wolf Theorem 6.14 are not asserted here; their remaining construction is recorded
in `docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`. -/
theorem exists_maximalSupport_fixedPoint
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    let hbounded := hT.hasBoundedOrbits_of_tracePreserving hTP
    let ρ₀ := LinearMap.meanErgodicProjection (𝕜 := ℂ)
      (E := Matrix (Fin D) (Fin D) ℂ) T hbounded 1
    ∃ hρ₀ : ρ₀.PosSemidef, T ρ₀ = ρ₀ ∧
      ∀ X : Mat, T X = X →
        stationaryProj hρ₀ * X * stationaryProj hρ₀ = X := by
  classical
  dsimp only
  let hbounded := hT.hasBoundedOrbits_of_tracePreserving hTP
  let P := LinearMap.meanErgodicProjection (𝕜 := ℂ)
    (E := Matrix (Fin D) (Fin D) ℂ) T hbounded
  let ρ₀ : Mat := P 1
  have hPpos : IsPositiveMap P := hT.meanErgodicProjection_isPositiveMap hbounded
  have hρ₀psd : ρ₀.PosSemidef := hPpos 1 Matrix.PosSemidef.one
  have hPfixed (A : Mat) (hA : T A = A) : P A = A := by
    exact (hT.meanErgodicProjection_apply_eq_self_iff_of_tracePreserving hTP A).2 hA
  have hρ₀fix : T ρ₀ = ρ₀ := by
    apply (hT.meanErgodicProjection_apply_eq_self_iff_of_tracePreserving hTP ρ₀).1
    exact hbounded.meanErgodicProjection_apply_meanErgodicProjection 1
  refine ⟨hρ₀psd, hρ₀fix, ?_⟩
  intro X hXfix
  cases isEmpty_or_nonempty (Fin D) with
  | inl hD =>
      letI := hD
      have hXzero : X = 0 := Subsingleton.elim _ _
      rw [hXzero, Matrix.mul_zero, Matrix.zero_mul]
  | inr hD =>
      letI := hD
      let H₁ : Mat := X + Xᴴ
      let H₂ : Mat := Complex.I • (X - Xᴴ)
      have hXstar : T Xᴴ = Xᴴ := by
        rw [hT.map_conjTranspose, hXfix]
      have hH₁herm : H₁.IsHermitian := by
        change (X + Xᴴ)ᴴ = X + Xᴴ
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
        exact add_comm _ _
      have hH₂herm : H₂.IsHermitian := by
        change (Complex.I • (X - Xᴴ))ᴴ = Complex.I • (X - Xᴴ)
        rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
          Matrix.conjTranspose_conjTranspose]
        rw [show star Complex.I = -Complex.I by simp]
        rw [neg_smul, ← smul_neg, neg_sub]
      have hH₁fix : T H₁ = H₁ := by
        change T (X + Xᴴ) = X + Xᴴ
        rw [T.map_add, hXfix, hXstar]
      have hH₂fix : T H₂ = H₂ := by
        change T (Complex.I • (X - Xᴴ)) = Complex.I • (X - Xᴴ)
        rw [T.map_smul, T.map_sub, hXfix, hXstar]
      obtain ⟨P₁p, P₁m, hP₁p, hP₁m, hH₁eq, hf₁p, hf₁m⟩ :=
        IsPositiveMap.posSemidef_parts_of_hermitian_fixedPoint
          T hT hTP hH₁herm hH₁fix
      obtain ⟨P₂p, P₂m, hP₂p, hP₂m, hH₂eq, hf₂p, hf₂m⟩ :=
        IsPositiveMap.posSemidef_parts_of_hermitian_fixedPoint
          T hT hTP hH₂herm hH₂fix
      have hbound (A : Mat) (hA : A.PosSemidef) (hAfix : T A = A) :
          A ≤ A.trace • ρ₀ := by
        have hshift : (A.trace • (1 : Mat) - A).PosSemidef :=
          hA.trace_smul_one_sub_self_posSemidef
        have himage := hPpos _ hshift
        change (P (A.trace • (1 : Mat) - A)).PosSemidef at himage
        rw [P.map_sub, P.map_smul, hPfixed A hAfix] at himage
        change (A.trace • ρ₀ - A).PosSemidef at himage
        exact sub_nonneg.mp himage.nonneg
      have hsupported (A : Mat) (hA : A.PosSemidef) (hAfix : T A = A) :
          stationaryProj hρ₀psd * A * stationaryProj hρ₀psd = A := by
        obtain ⟨hQA, hAQ⟩ := stationaryProj_absorb_of_le_smul
          hρ₀psd hA A.trace (hbound A hA hAfix)
        rw [Matrix.mul_assoc, hAQ, hQA]
      have hH₁support :
          stationaryProj hρ₀psd * H₁ * stationaryProj hρ₀psd = H₁ := by
        rw [hH₁eq, Matrix.mul_sub, Matrix.sub_mul,
          hsupported P₁p hP₁p hf₁p, hsupported P₁m hP₁m hf₁m]
      have hH₂support :
          stationaryProj hρ₀psd * H₂ * stationaryProj hρ₀psd = H₂ := by
        rw [hH₂eq, Matrix.mul_sub, Matrix.sub_mul,
          hsupported P₂p hP₂p hf₂p, hsupported P₂m hP₂m hf₂m]
      have hXeq : X = (2⁻¹ : ℂ) • H₁ - ((2⁻¹ : ℂ) * Complex.I) • H₂ := by
        change X = (2⁻¹ : ℂ) • (X + Xᴴ) -
          ((2⁻¹ : ℂ) * Complex.I) • (Complex.I • (X - Xᴴ))
        rw [smul_smul,
          show ((2⁻¹ : ℂ) * Complex.I) * Complex.I = -(2⁻¹ : ℂ) by
            rw [mul_assoc, Complex.I_mul_I]
            ring]
        module
      conv_lhs => rw [hXeq]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.smul_mul, hH₁support, hH₂support, ← hXeq]

end IsPositiveMap

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The transfer map of a trace-preserving Kraus family is a quantum channel; the
trace-preservation hypothesis is the normalization of the channel form of the transfer
map (`MPSTensor.transferMap_isChannel`). -/
theorem isChannel_transferMap (K : Fin d → Mat) (h_tp : IsTP K) :
    IsChannel (MPSTensor.transferMap (d := d) (D := D) K) :=
  MPSTensor.transferMap_isChannel K h_tp

/-- **A fixed point of maximal support for a Kraus map.** The mean-ergodic image
of the identity is a positive semidefinite fixed point whose support carries every fixed
point of the trace-preserving Kraus map. This is the completely positive specialization
of Wolf, Proposition 6.9, formalized for arbitrary positive trace-preserving maps by
`IsPositiveMap.exists_maximalSupport_fixedPoint`. -/
theorem exists_maximalSupport_fixedPoint (K : Fin d → Mat) (h_tp : IsTP K) :
    ∃ (ρ₀ : Mat) (hρ₀ : ρ₀.PosSemidef), map K ρ₀ = ρ₀ ∧
      ∀ X : Mat, map K X = X →
        stationaryProj hρ₀ * X * stationaryProj hρ₀ = X := by
  let E : Mat →ₗ[ℂ] Mat := MPSTensor.transferMap (d := d) (D := D) K
  have hE : IsChannel E := isChannel_transferMap K h_tp
  let hbounded := hE.cp.isPositiveMap.hasBoundedOrbits_of_tracePreserving hE.tp
  let ρ₀ : Mat := LinearMap.meanErgodicProjection (𝕜 := ℂ) (E := Mat)
    E hbounded 1
  have hgeneric : ∃ hρ₀ : ρ₀.PosSemidef, E ρ₀ = ρ₀ ∧
      ∀ X : Mat, E X = X → stationaryProj hρ₀ * X * stationaryProj hρ₀ = X := by
    simpa only [ρ₀, hbounded] using
      hE.cp.isPositiveMap.exists_maximalSupport_fixedPoint hE.tp
  obtain ⟨hρ₀, hfix, hmax⟩ := hgeneric
  refine ⟨ρ₀, hρ₀, ?_, ?_⟩
  · simpa [E, MPSTensor.transferMap_apply, map] using hfix
  · intro X hX
    apply hmax X
    simpa [E, MPSTensor.transferMap_apply, map] using hX

/-- **Conjugation by the square root at a fixed point of maximal support.** For a
trace-preserving Kraus map $T$ there is a positive semidefinite fixed point $\rho_0$ such
that every fixed point $X$ of $T$ arises as $X = \sqrt{\rho_0}\, Y \sqrt{\rho_0}$ for a
corner-supported $Y$ with $\sqrt{\rho_0}\, Y \sqrt{\rho_0}$ fixed by $T$: conjugation by
$\sqrt{\rho_0}$ maps the carrier of the weighted corner star-subalgebra
(`Kraus.weightedCornerFixedPointsStarSubalgebra`) onto the full fixed-point set, so that
set realizes, with the inverse square root taken on the support of $\rho_0$,
$$\rho_0^{-1/2}\,\{X \mid T(X) = X\}\,\rho_0^{-1/2}.$$ This is the conjugated
fixed-point set of Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012), at a
fixed point of maximal support. -/
theorem exists_maximalSupport_weightedCorner_sqrt_eq (K : Fin d → Mat) (h_tp : IsTP K) :
    ∃ (ρ₀ : Mat) (hρ₀ : ρ₀.PosSemidef), map K ρ₀ = ρ₀ ∧
      ∀ X : Mat, map K X = X →
        ∃ Y : Mat, stationaryProj hρ₀ * Y * stationaryProj hρ₀ = Y ∧
          map K (CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀) = CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀ ∧
          CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀ = X := by
  obtain ⟨ρ₀, hρ₀, hfix, hmax⟩ := exists_maximalSupport_fixedPoint K h_tp
  exact ⟨ρ₀, hρ₀, hfix, fun X hX =>
    exists_weightedCorner_sqrt_eq_of_fixedPoint K h_tp hρ₀ hfix hX (hmax X hX)⟩

end Kraus
