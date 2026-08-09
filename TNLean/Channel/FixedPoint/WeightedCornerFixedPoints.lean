/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.CornerFixedPoints
import TNLean.Channel.FixedPoint.Corollaries

/-!
# Weighted corner fixed points of a Kraus map with a singular fixed point

The following results extend Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012)
beyond the positive definite case of `TNLean.Channel.FixedPoint.Corollaries`.
Let $T$ be a
trace-preserving Kraus map, let $\rho$ be a positive semidefinite fixed point of $T$ —
possibly singular — and let $Q$ be the support projection of $\rho$. The set
$$\rho^{-1/2}\,\{X \mid T(X) = X,\ Q X Q = X\}\,\rho^{-1/2},$$
with the inverse square root taken on the support of $\rho$, is a star-subalgebra of the
corner algebra $Q M_D(\mathbb{C}) Q$. Concretely, the carrier consists of the corner
elements $Y$ with $\sqrt{\rho}\, Y \sqrt{\rho}$ fixed by $T$; conjugation by
$\sqrt{\rho}$ maps this carrier bijectively onto the fixed points of $T$ supported on the
support of $\rho$, which realizes the displayed set without naming the pseudo-inverse.

Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012) takes $\rho$ to be a
*maximum-rank* fixed-point density matrix and conjugates the full fixed-point set of $T$.
For a fixed point of maximal support the corner restriction $Q X Q = X$ is vacuous: there
is a positive semidefinite fixed point whose support projection absorbs every fixed point
(`Kraus.exists_maximalSupport_fixedPoint` in `TNLean.Channel.FixedPoint.MaximalSupport`),
and at such a fixed point the conjugation below reaches the full fixed-point set
(`Kraus.exists_maximalSupport_weightedCorner_sqrt_eq`). The statements below take an
arbitrary positive semidefinite fixed point, so for a non-maximal choice of $\rho$ they
conjugate the fixed points supported on the support of
$\rho$. The resolution of the former restriction is recorded in
`docs/paper-gaps/wolf_cor67_maximal_support_restriction.tex`.

The proofs compress to the support sector, where the compressed fixed point is positive
definite and the positive definite case applies, and transport the structure back along
the compression isometry. The square root compresses along the isometry:
$\sqrt{V^{\dagger} \rho V} = V^{\dagger} \sqrt{\rho}\, V$.

## Main declarations

* `Kraus.weightedCornerFixedPointsStarSubalgebra` -- the weighted corner fixed points form
  a star-subalgebra of the corner algebra.
* `Kraus.mem_weightedCornerFixedPointsStarSubalgebra` -- membership is exactly the
  condition that $\sqrt{\rho}\, Y \sqrt{\rho}$ is fixed by the map.
* `Kraus.exists_weightedCorner_sqrt_eq_of_fixedPoint` -- every fixed point supported on
  the support of $\rho$ is $\sqrt{\rho}\, Y \sqrt{\rho}$ for a corner element $Y$ of the
  carrier: conjugation by $\sqrt{\rho}$ is onto the corner-supported fixed points.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## The square root of a positive semidefinite matrix and its support -/

/-- The support projection absorbs the square root from the left:
$Q \sqrt{\rho} = \sqrt{\rho}$. -/
theorem stationaryProj_mul_cfc_sqrt {ρ : Mat} (hρ_psd : ρ.PosSemidef) :
    stationaryProj hρ_psd * CFC.sqrt ρ = CFC.sqrt ρ := by
  set Q : Mat := stationaryProj hρ_psd with hQdef
  set S : Mat := CFC.sqrt ρ with hSdef
  have hQproj : IsOrthogonalProjection Q := isOrthogonalProjection_stationaryProj hρ_psd
  have hQherm : Qᴴ = Q := hQproj.1.eq
  have hS_herm : Sᴴ = S := by
    simpa [S] using Matrix.conjTranspose_cfc_sqrt ρ
  have hSS : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ hρ_psd.nonneg
  have hQρ : Q * ρ = ρ := MPSTensor.supportProj_mul (D := D) (ρ := ρ) hρ_psd
  -- `(1 - Q) S` has vanishing square, hence vanishes.
  have h0 : ((1 - Q) * S) * ((1 - Q) * S)ᴴ = 0 := by
    have h1 : (1 - Q)ᴴ = 1 - Q := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQherm]
    have h2 : ((1 - Q) * S) * ((1 - Q) * S)ᴴ = (1 - Q) * ρ * (1 - Q) := by
      rw [Matrix.conjTranspose_mul, hS_herm, h1, ← hSS]
      simp [Matrix.mul_assoc]
    have h3 : (1 - Q) * ρ = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, hQρ, sub_self]
    rw [h2, h3, Matrix.zero_mul]
  have h4 : (1 - Q) * S = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp h0
  rw [Matrix.sub_mul, Matrix.one_mul] at h4
  exact (sub_eq_zero.mp h4).symm

/-- The support projection absorbs the square root from the right:
$\sqrt{\rho}\, Q = \sqrt{\rho}$. -/
theorem cfc_sqrt_mul_stationaryProj {ρ : Mat} (hρ_psd : ρ.PosSemidef) :
    CFC.sqrt ρ * stationaryProj hρ_psd = CFC.sqrt ρ := by
  have hQherm : (stationaryProj hρ_psd)ᴴ = stationaryProj hρ_psd :=
    (isOrthogonalProjection_stationaryProj hρ_psd).1.eq
  have hS_herm : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    Matrix.conjTranspose_cfc_sqrt ρ
  have h := congrArg Matrix.conjTranspose (stationaryProj_mul_cfc_sqrt hρ_psd)
  rwa [Matrix.conjTranspose_mul, hQherm, hS_herm] at h

/-- Conjugation by $\sqrt{\rho}$ lands in the corner: the matrix
$\sqrt{\rho}\, Y \sqrt{\rho}$ is supported on the support of $\rho$. -/
theorem sqrt_conj_supported {ρ : Mat} (hρ_psd : ρ.PosSemidef) (Y : Mat) :
    stationaryProj hρ_psd * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * stationaryProj hρ_psd =
      CFC.sqrt ρ * Y * CFC.sqrt ρ := by
  calc stationaryProj hρ_psd * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * stationaryProj hρ_psd
      = (stationaryProj hρ_psd * CFC.sqrt ρ) * Y *
          (CFC.sqrt ρ * stationaryProj hρ_psd) := by simp [Matrix.mul_assoc]
    _ = CFC.sqrt ρ * Y * CFC.sqrt ρ := by
        rw [stationaryProj_mul_cfc_sqrt hρ_psd, cfc_sqrt_mul_stationaryProj hρ_psd]

/-- The square root compresses along an isometry onto the support:
$\sqrt{V^{\dagger} \rho V} = V^{\dagger} \sqrt{\rho}\, V$ for $V$ with
$V^{\dagger} V = \mathbf{1}$ and $V V^{\dagger} = Q$ the support projection of $\rho$. -/
theorem cfc_sqrt_compression {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    {r : ℕ} {V : Matrix (Fin D) (Fin r) ℂ}
    (hVVt : V * Vᴴ = stationaryProj hρ_psd) :
    CFC.sqrt (Vᴴ * ρ * V) = Vᴴ * CFC.sqrt ρ * V := by
  have hb : (0 : Matrix (Fin r) (Fin r) ℂ) ≤ Vᴴ * CFC.sqrt ρ * V :=
    (((CFC.sqrt_nonneg ρ).posSemidef).conjTranspose_mul_mul_same V).nonneg
  refine CFC.sqrt_unique ?_ hb
  calc (Vᴴ * CFC.sqrt ρ * V) * (Vᴴ * CFC.sqrt ρ * V)
      = Vᴴ * (CFC.sqrt ρ * (V * Vᴴ) * CFC.sqrt ρ) * V := by simp [Matrix.mul_assoc]
    _ = Vᴴ * (CFC.sqrt ρ * stationaryProj hρ_psd * CFC.sqrt ρ) * V := by rw [hVVt]
    _ = Vᴴ * (CFC.sqrt ρ * CFC.sqrt ρ) * V := by
        rw [cfc_sqrt_mul_stationaryProj hρ_psd]
    _ = Vᴴ * ρ * V := by rw [CFC.sqrt_mul_sqrt_self ρ hρ_psd.nonneg]

/-! ## Compression of the weighted fixed-point condition to the support sector -/

/-- Compression onto the support sector for the weighted corner statements: a
trace-preserving compressed family with a positive definite fixed point, the compression
identity for the square root, the transport identity for conjugation by the square root,
and the correspondence between the ambient and compressed fixed-point equations for
corner-supported matrices. -/
private theorem exists_weighted_compression
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ) :
    ∃ (r : ℕ) (C : Fin d → Matrix (Fin r) (Fin r) ℂ) (V : Matrix (Fin D) (Fin r) ℂ)
      (σ : Matrix (Fin r) (Fin r) ℂ),
      IsTP C ∧ σ.PosDef ∧ map C σ = σ ∧ Vᴴ * V = 1 ∧
        V * Vᴴ = stationaryProj hρ_psd ∧
        CFC.sqrt σ = Vᴴ * CFC.sqrt ρ * V ∧
        (∀ Y : Mat, stationaryProj hρ_psd * Y * stationaryProj hρ_psd = Y →
          CFC.sqrt σ * (Vᴴ * Y * V) * CFC.sqrt σ =
            Vᴴ * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * V) ∧
        ∀ W : Mat, stationaryProj hρ_psd * W * stationaryProj hρ_psd = W →
          (map K W = W ↔ map C (Vᴴ * W * V) = Vᴴ * W * V) := by
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
  obtain ⟨r, C, φ, V, -, hCtp, -, -, -, -, hLetter, hVtV, hVVt, hφV⟩ :=
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
  set σ : Matrix (Fin r) (Fin r) ℂ := Vᴴ * ρ * V with hσdef
  have hσpd : σ.PosDef := by
    have := Matrix.PosSemidef.compression_on_support_posDef (D := D) (ρ := ρ) hρ_psd
      (k := r) (V := Vᴴ) (by simpa [Matrix.conjTranspose_conjTranspose] using hVtV)
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
      _ = ∑ i : Fin d, Vᴴ * (A i * ρ * (A i)ᴴ) * V :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = Vᴴ * (∑ i : Fin d, A i * ρ * (A i)ᴴ) * V := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = Vᴴ * map A ρ * V := by rw [map_apply]
      _ = σ := by rw [hmapA, hσdef]
  -- The square root compresses along the isometry.
  have hs : CFC.sqrt σ = Vᴴ * CFC.sqrt ρ * V := by
    rw [hσdef]
    exact cfc_sqrt_compression hρ_psd hVVt
  -- The transport identity for conjugation by the square root.
  have htrans : ∀ Y : Mat, Q * Y * Q = Y →
      CFC.sqrt σ * (Vᴴ * Y * V) * CFC.sqrt σ =
        Vᴴ * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * V := by
    intro Y hY
    rw [hs]
    calc (Vᴴ * CFC.sqrt ρ * V) * (Vᴴ * Y * V) * (Vᴴ * CFC.sqrt ρ * V)
        = Vᴴ * (CFC.sqrt ρ * ((V * Vᴴ) * Y * (V * Vᴴ)) * CFC.sqrt ρ) * V := by
          simp [Matrix.mul_assoc]
      _ = Vᴴ * (CFC.sqrt ρ * (Q * Y * Q) * CFC.sqrt ρ) * V := by rw [hVVt]
      _ = Vᴴ * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * V := by rw [hY]
  -- The corner-supported ambient fixed-point equation corresponds to the compressed one.
  have hQV : Q * V = V := by
    calc Q * V = (V * Vᴴ) * V := by rw [hVVt]
      _ = V * (Vᴴ * V) := by rw [Matrix.mul_assoc]
      _ = V := by rw [hVtV, Matrix.mul_one]
  have hVQ : Vᴴ * Q = Vᴴ := by
    calc Vᴴ * Q = Vᴴ * (V * Vᴴ) := by rw [hVVt]
      _ = (Vᴴ * V) * Vᴴ := by rw [← Matrix.mul_assoc]
      _ = Vᴴ := by rw [hVtV, Matrix.one_mul]
  have hKQ : ∀ i : Fin d, K i * Q = Q * K i * Q := by
    intro i
    have h := hInv i
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hQKH : ∀ i : Fin d, Q * (K i)ᴴ = Q * (K i)ᴴ * Q := by
    intro i
    have h := congrArg Matrix.conjTranspose (hKQ i)
    simpa [Matrix.conjTranspose_mul, hQherm, Matrix.mul_assoc] using h
  have hmapK_corner : ∀ W : Mat, Q * W * Q = W → Q * map K W * Q = map K W := by
    intro W hW
    have hterm : ∀ i : Fin d,
        K i * W * (K i)ᴴ = Q * (K i * W * (K i)ᴴ) * Q := by
      intro i
      conv_lhs => rw [← hW]
      calc K i * (Q * W * Q) * (K i)ᴴ
          = (K i * Q) * W * (Q * (K i)ᴴ) := by simp [Matrix.mul_assoc]
        _ = (Q * K i * Q) * W * (Q * (K i)ᴴ * Q) := by
            conv_lhs => rw [hKQ i, hQKH i]
        _ = Q * (K i * (Q * W * Q) * (K i)ᴴ) * Q := by simp [Matrix.mul_assoc]
        _ = Q * (K i * W * (K i)ᴴ) * Q := by rw [hW]
    calc Q * map K W * Q
        = Q * (∑ i : Fin d, K i * W * (K i)ᴴ) * Q := by rw [map_apply]
      _ = ∑ i : Fin d, Q * (K i * W * (K i)ᴴ) * Q := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = ∑ i : Fin d, K i * W * (K i)ᴴ :=
          Finset.sum_congr rfl fun i _ => (hterm i).symm
      _ = map K W := by rw [map_apply]
  have hmapC : ∀ Z : Matrix (Fin r) (Fin r) ℂ,
      map C Z = Vᴴ * map A (V * Z * Vᴴ) * V := by
    intro Z
    calc map C Z = ∑ i : Fin d, C i * Z * (C i)ᴴ := by rw [map_apply]
      _ = ∑ i : Fin d, Vᴴ * (A i * (V * Z * Vᴴ) * (A i)ᴴ) * V := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hCiH : (C i)ᴴ = Vᴴ * (A i)ᴴ * V := by
            rw [hCi i]
            simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
              Matrix.mul_assoc]
          rw [hCiH, hCi i]
          simp [Matrix.mul_assoc]
      _ = Vᴴ * (∑ i : Fin d, A i * (V * Z * Vᴴ) * (A i)ᴴ) * V := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = Vᴴ * map A (V * Z * Vᴴ) * V := by rw [map_apply]
  have hcorrS : ∀ W : Mat, Q * W * Q = W →
      (map K W = W ↔ map C (Vᴴ * W * V) = Vᴴ * W * V) := by
    intro W hW
    have hVWV : V * (Vᴴ * W * V) * Vᴴ = W := by
      calc V * (Vᴴ * W * V) * Vᴴ = (V * Vᴴ) * W * (V * Vᴴ) := by simp [Matrix.mul_assoc]
        _ = Q * W * Q := by rw [hVVt]
        _ = W := hW
    have hmapCW : map C (Vᴴ * W * V) = Vᴴ * map K W * V := by
      rw [hmapC, hVWV, hAdef, map_cornerCompressionKraus_eq K hQproj hW]
      calc Vᴴ * (Q * map K W * Q) * V
          = (Vᴴ * Q) * map K W * (Q * V) := by simp [Matrix.mul_assoc]
        _ = Vᴴ * map K W * V := by rw [hVQ, hQV]
    constructor
    · intro h
      rw [hmapCW, h]
    · intro h
      have h2 : Q * map K W * Q = W := by
        calc Q * map K W * Q
            = (V * Vᴴ) * map K W * (V * Vᴴ) := by rw [hVVt]
          _ = V * (Vᴴ * map K W * V) * Vᴴ := by simp [Matrix.mul_assoc]
          _ = V * (Vᴴ * W * V) * Vᴴ := by rw [← hmapCW, h]
          _ = W := hVWV
      rw [← hmapK_corner W hW]
      exact h2
  exact ⟨r, C, V, σ, hCtp', hσpd, hσfix, hVtV, hVVt, hs, htrans, hcorrS⟩

/-! ## The weighted corner fixed-point star-algebra -/

/-- Multiplication closure of the weighted corner fixed points: if $Y_1$ and $Y_2$ are
supported on the support of $\rho$ and $\sqrt{\rho}\, Y_j \sqrt{\rho}$ is fixed by the
map, then the same holds for $Y_1 Y_2$. Proved by compressing to the support sector, where
the fixed point is positive definite and the weighted fixed points form a star-subalgebra
in the sense of the positive definite case of Corollary 6.7 of
*Quantum Channels & Operations* (Wolf 2012). -/
theorem weightedCornerFixed_mul
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ) {Y₁ Y₂ : Mat}
    (hY₁mem : stationaryProj hρ_psd * Y₁ * stationaryProj hρ_psd = Y₁)
    (hY₂mem : stationaryProj hρ_psd * Y₂ * stationaryProj hρ_psd = Y₂)
    (hY₁ : map K (CFC.sqrt ρ * Y₁ * CFC.sqrt ρ) = CFC.sqrt ρ * Y₁ * CFC.sqrt ρ)
    (hY₂ : map K (CFC.sqrt ρ * Y₂ * CFC.sqrt ρ) = CFC.sqrt ρ * Y₂ * CFC.sqrt ρ) :
    map K (CFC.sqrt ρ * (Y₁ * Y₂) * CFC.sqrt ρ) =
      CFC.sqrt ρ * (Y₁ * Y₂) * CFC.sqrt ρ := by
  classical
  obtain ⟨r, C, V, σ, hCtp, hσpd, hσfix, hVtV, hVVt, hs, htrans, hcorrS⟩ :=
    exists_weighted_compression K h_tp hρ_psd hρ_fix
  set Q : Mat := stationaryProj hρ_psd with hQdef
  have hQidem : Q * Q = Q := (isOrthogonalProjection_stationaryProj hρ_psd).2
  -- One-sided corner absorptions for the two factors.
  have hQY₁ : Q * Y₁ = Y₁ := by
    conv_lhs => rw [← hY₁mem]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQidem]
    exact hY₁mem
  have hY₂Q : Y₂ * Q = Y₂ := by
    conv_lhs => rw [← hY₂mem]
    rw [Matrix.mul_assoc, hQidem]
    exact hY₂mem
  have hY₁Q : Y₁ * Q = Y₁ := by
    conv_lhs => rw [← hY₁mem]
    rw [Matrix.mul_assoc, hQidem]
    exact hY₁mem
  have hprodmem : Q * (Y₁ * Y₂) * Q = Y₁ * Y₂ := by
    calc Q * (Y₁ * Y₂) * Q = (Q * Y₁) * (Y₂ * Q) := by simp [Matrix.mul_assoc]
      _ = Y₁ * Y₂ := by rw [hQY₁, hY₂Q]
  -- Sector membership of the compressed factors in the weighted algebra.
  have hmem : ∀ Y : Mat, Q * Y * Q = Y →
      map K (CFC.sqrt ρ * Y * CFC.sqrt ρ) = CFC.sqrt ρ * Y * CFC.sqrt ρ →
      Vᴴ * Y * V ∈ weightedFixedPointsStarSubalgebra (K := C) hCtp hσpd hσfix := by
    intro Y hYmem hYfix
    rw [mem_weightedFixedPointsStarSubalgebra_iff, htrans Y hYmem]
    exact (hcorrS _ (sqrt_conj_supported hρ_psd Y)).mp hYfix
  have hZmul :=
    (weightedFixedPointsStarSubalgebra (K := C) hCtp hσpd hσfix).mul_mem
      (hmem Y₁ hY₁mem hY₁) (hmem Y₂ hY₂mem hY₂)
  have hZZ : (Vᴴ * Y₁ * V) * (Vᴴ * Y₂ * V) = Vᴴ * (Y₁ * Y₂) * V := by
    calc (Vᴴ * Y₁ * V) * (Vᴴ * Y₂ * V)
        = Vᴴ * (Y₁ * (V * Vᴴ) * Y₂) * V := by simp [Matrix.mul_assoc]
      _ = Vᴴ * (Y₁ * Q * Y₂) * V := by rw [hVVt]
      _ = Vᴴ * (Y₁ * Y₂) * V := by rw [hY₁Q]
  rw [hZZ] at hZmul
  have hfix :=
    (mem_weightedFixedPointsStarSubalgebra_iff (K := C) hCtp hσpd hσfix _).mp hZmul
  rw [htrans (Y₁ * Y₂) hprodmem] at hfix
  exact (hcorrS _ (sqrt_conj_supported hρ_psd (Y₁ * Y₂))).mpr hfix

/-- **The weighted corner fixed points form a star-algebra** (Corollary 6.7 of
*Quantum Channels & Operations* (Wolf 2012), restricted to corner-supported fixed
points). Let $T(X) = \sum_i K_i X K_i^\dagger$ be trace-preserving, let $\rho \succeq 0$
satisfy $T(\rho) = \rho$, and let $Q$ be the support projection of $\rho$. The corner
elements $Y$ (with $Q Y Q = Y$) such that $\sqrt{\rho}\, Y \sqrt{\rho}$ is fixed by $T$
form a star-subalgebra of the corner algebra $Q M_D(\mathbb{C}) Q$. Under conjugation by
$\sqrt{\rho}$ this carrier corresponds exactly to the fixed points of $T$ supported on
the support of $\rho$ (`Kraus.exists_weightedCorner_sqrt_eq_of_fixedPoint`), so it
realizes the set $\rho^{-1/2}\{X \mid T(X) = X,\ Q X Q = X\}\rho^{-1/2}$ of the
corollary, with the inverse square root taken on the support of $\rho$.

The corollary in the reference takes a maximum-rank fixed point, for which every fixed
point of $T$ is supported on the support of $\rho$ and the corner restriction disappears:
a positive semidefinite fixed point whose support projection absorbs every fixed point
exists (`Kraus.exists_maximalSupport_fixedPoint`), and at such a fixed point the
conjugation reaches the full fixed-point set
(`Kraus.exists_maximalSupport_weightedCorner_sqrt_eq`), both in
`TNLean.Channel.FixedPoint.MaximalSupport`. -/
noncomputable def weightedCornerFixedPointsStarSubalgebra
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
  have hS_herm : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    Matrix.conjTranspose_cfc_sqrt ρ
  have hSρS : CFC.sqrt ρ * Q * CFC.sqrt ρ = ρ := by
    rw [show CFC.sqrt ρ * Q * CFC.sqrt ρ = (CFC.sqrt ρ * Q) * CFC.sqrt ρ from rfl,
      cfc_sqrt_mul_stationaryProj hρ_psd, CFC.sqrt_mul_sqrt_self ρ hρ_psd.nonneg]
  { carrier := {Y : hQ.Corner |
      map K (CFC.sqrt ρ * Y.1 * CFC.sqrt ρ) = CFC.sqrt ρ * Y.1 * CFC.sqrt ρ}
    zero_mem' := by
      change map K (CFC.sqrt ρ * (0 : Mat) * CFC.sqrt ρ) =
        CFC.sqrt ρ * (0 : Mat) * CFC.sqrt ρ
      simp [map]
    add_mem' := by
      intro X Y hX hY
      change map K (CFC.sqrt ρ * (X.1 + Y.1) * CFC.sqrt ρ) =
        CFC.sqrt ρ * (X.1 + Y.1) * CFC.sqrt ρ
      rw [Matrix.mul_add, Matrix.add_mul, map_add, hX, hY]
    one_mem' := by
      change map K (CFC.sqrt ρ * Q * CFC.sqrt ρ) = CFC.sqrt ρ * Q * CFC.sqrt ρ
      rw [hSρS]
      exact hρ_fix
    mul_mem' := by
      intro X Y hX hY
      change map K (CFC.sqrt ρ * (X.1 * Y.1) * CFC.sqrt ρ) =
        CFC.sqrt ρ * (X.1 * Y.1) * CFC.sqrt ρ
      have hXmem : Q * X.1 * Q = X.1 := by
        obtain ⟨hL, hR⟩ := (Subsemigroup.mem_corner_iff hQ).mp X.2
        rw [Matrix.mul_assoc, hR, hL]
      have hYmem : Q * Y.1 * Q = Y.1 := by
        obtain ⟨hL, hR⟩ := (Subsemigroup.mem_corner_iff hQ).mp Y.2
        rw [Matrix.mul_assoc, hR, hL]
      exact weightedCornerFixed_mul K h_tp hρ_psd hρ_fix hXmem hYmem hX hY
    algebraMap_mem' := by
      intro c
      change map K (CFC.sqrt ρ * (c • Q) * CFC.sqrt ρ) =
        CFC.sqrt ρ * (c • Q) * CFC.sqrt ρ
      have hsmul : CFC.sqrt ρ * (c • Q) * CFC.sqrt ρ = c • ρ := by
        rw [Matrix.mul_smul, Matrix.smul_mul, hSρS]
      rw [hsmul, map_smul, hρ_fix]
    star_mem' := by
      intro X hX
      change map K (CFC.sqrt ρ * X.1ᴴ * CFC.sqrt ρ) = CFC.sqrt ρ * X.1ᴴ * CFC.sqrt ρ
      have hconj : CFC.sqrt ρ * X.1ᴴ * CFC.sqrt ρ = (CFC.sqrt ρ * X.1 * CFC.sqrt ρ)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS_herm, Matrix.mul_assoc]
      rw [hconj]
      exact conjTranspose_mem_fixedPoints (K := K) hX }

/-- Membership in the weighted corner fixed-point star-algebra: a corner element $Y$ lies
in it exactly when $\sqrt{\rho}\, Y \sqrt{\rho}$ is fixed by the map. -/
@[simp] theorem mem_weightedCornerFixedPointsStarSubalgebra
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
    Y ∈ weightedCornerFixedPointsStarSubalgebra K h_tp hρ_psd hρ_fix ↔
      map K (CFC.sqrt ρ * Y.1 * CFC.sqrt ρ) = CFC.sqrt ρ * Y.1 * CFC.sqrt ρ :=
  Iff.rfl

/-- **Conjugation by the square root is onto the corner-supported fixed points.** Every
fixed point $X$ of the map that is supported on the support of $\rho$ arises as
$X = \sqrt{\rho}\, Y \sqrt{\rho}$ for a corner-supported $Y$ whose class lies in the
weighted corner fixed-point star-algebra. Together with the membership description of
the star-algebra (`Kraus.mem_weightedCornerFixedPointsStarSubalgebra`) this identifies
the carrier with the set $\rho^{-1/2}\{X \mid T(X) = X,\ Q X Q = X\}\rho^{-1/2}$ of
Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012), with the inverse square
root taken on the support of $\rho$.

The source's corollary takes a maximum-rank fixed point, for which the support condition
on $X$ is automatic by the maximal-support property
(`Kraus.exists_maximalSupport_fixedPoint` in `TNLean.Channel.FixedPoint.MaximalSupport`);
at such a fixed point the conjugation reaches the full fixed-point set without the
support hypothesis (`Kraus.exists_maximalSupport_weightedCorner_sqrt_eq`). -/
theorem exists_weightedCorner_sqrt_eq_of_fixedPoint
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ) {X : Mat} (hX_fix : map K X = X)
    (hX_supp : stationaryProj hρ_psd * X * stationaryProj hρ_psd = X) :
    ∃ Y : Mat, stationaryProj hρ_psd * Y * stationaryProj hρ_psd = Y ∧
      map K (CFC.sqrt ρ * Y * CFC.sqrt ρ) = CFC.sqrt ρ * Y * CFC.sqrt ρ ∧
      CFC.sqrt ρ * Y * CFC.sqrt ρ = X := by
  classical
  obtain ⟨r, C, V, σ, hCtp, hσpd, hσfix, hVtV, hVVt, hs, htrans, hcorrS⟩ :=
    exists_weighted_compression K h_tp hρ_psd hρ_fix
  set Q : Mat := stationaryProj hρ_psd with hQdef
  set s : Matrix (Fin r) (Fin r) ℂ := CFC.sqrt σ with hsdef
  have hs_det : IsUnit s.det := by
    simpa [hsdef] using hσpd.isUnit_det_cfc_sqrt
  have hs_inv_mul : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul s hs_det
  have hs_mul_inv : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hs_det
  -- The candidate corner element, built on the support sector.
  set Z : Matrix (Fin r) (Fin r) ℂ := s⁻¹ * (Vᴴ * X * V) * s⁻¹ with hZdef
  set Y : Mat := V * Z * Vᴴ with hYdef
  have hYmem : Q * Y * Q = Y := by
    calc Q * (V * Z * Vᴴ) * Q = (Q * V) * Z * (Vᴴ * Q) := by simp [Matrix.mul_assoc]
      _ = ((V * Vᴴ) * V) * Z * (Vᴴ * (V * Vᴴ)) := by rw [hVVt]
      _ = (V * (Vᴴ * V)) * Z * ((Vᴴ * V) * Vᴴ) := by simp [Matrix.mul_assoc]
      _ = V * Z * Vᴴ := by rw [hVtV]; simp
  have hVYV : Vᴴ * Y * V = Z := by
    calc Vᴴ * (V * Z * Vᴴ) * V = (Vᴴ * V) * Z * (Vᴴ * V) := by simp [Matrix.mul_assoc]
      _ = Z := by rw [hVtV]; simp
  have hsZs : s * Z * s = Vᴴ * X * V := by
    calc s * (s⁻¹ * (Vᴴ * X * V) * s⁻¹) * s
        = (s * s⁻¹) * (Vᴴ * X * V) * (s⁻¹ * s) := by simp [Matrix.mul_assoc]
      _ = Vᴴ * X * V := by rw [hs_mul_inv, hs_inv_mul]; simp
  -- The conjugate of `Y` by the square root recovers `X`.
  have hsqrtY : CFC.sqrt ρ * Y * CFC.sqrt ρ = X := by
    have h1 : Vᴴ * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * V = Vᴴ * X * V := by
      rw [← htrans Y hYmem, hVYV]
      exact hsZs
    calc CFC.sqrt ρ * Y * CFC.sqrt ρ
        = Q * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * Q := (sqrt_conj_supported hρ_psd Y).symm
      _ = (V * Vᴴ) * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * (V * Vᴴ) := by rw [hVVt]
      _ = V * (Vᴴ * (CFC.sqrt ρ * Y * CFC.sqrt ρ) * V) * Vᴴ := by
          simp [Matrix.mul_assoc]
      _ = V * (Vᴴ * X * V) * Vᴴ := by rw [h1]
      _ = (V * Vᴴ) * X * (V * Vᴴ) := by simp [Matrix.mul_assoc]
      _ = Q * X * Q := by rw [hVVt]
      _ = X := hX_supp
  exact ⟨Y, hYmem, by rw [hsqrtY]; exact hX_fix, hsqrtY⟩

end Kraus
