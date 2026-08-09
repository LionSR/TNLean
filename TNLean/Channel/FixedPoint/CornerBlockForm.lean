/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.CornerFixedPoints
import TNLean.Channel.FixedPoint.BlockForm

/-!
# Block form of the corner-restricted fixed points of a Kraus map

This file combines the corner-restricted fixed-point star-algebra of Corollary 6.6 of
*Quantum Channels & Operations* (Wolf 2012) with the block representation of Equation (1.39)
of the same reference. For a trace-preserving Kraus map whose Schrödinger picture has a
positive semidefinite fixed point $\rho$ with support projection $Q$, the corner-restricted
fixed-point set carries the block structure
$$\{Y \in Q M_D(\mathbb{C}) Q \mid Q T^{*}(Y) Q = Y\}
  \;=\; W \Bigl(\bigoplus_{k} \mathbf{1}_{m_k} \otimes M_{d_k}(\mathbb{C})\Bigr)
  W^{\dagger},$$
where $W$ is an isometry onto the support sector ($W^{\dagger} W = \mathbf{1}$,
$W W^{\dagger} = Q$) and $\sum_k d_k m_k = r$ for the support-sector dimension
$r \le D$. This is the block form of the
corner-restricted fixed-point star-algebra of Corollary 6.6 of *Quantum Channels &
Operations* (Wolf 2012), the support-sector ingredient of the zero-block representation
invoked by Theorem 6.14 of the same reference. A corner-restricted fixed point extended
by zero on the complement of the support sector need not be a fixed point of the ambient
Heisenberg-picture map (the identity matrix is always an ambient fixed point of the
adjoint of a trace-preserving map, and it is not supported on the sector), so the
identification of the ambient fixed-point space with a zero-block form is not asserted
here. The Kronecker factors are written in the order
identity-times-matrix, as in the block form of the fixed-point algebra of a map with a
positive definite fixed point.

## Main result

* `Kraus.cornerFixedPoints_blockDiagonal_iff` -- a corner element is a corner-restricted
  fixed point exactly when it is carried by the support isometry from a block-diagonal
  matrix with blocks $\mathbf{1}_{m_k} \otimes B_k$.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Block form of the corner-restricted fixed points.** Let $T$ be a trace-preserving
Kraus map on $M_D(\mathbb{C})$, let $\rho$ be a positive semidefinite fixed point of $T$,
and let $Q$ be the support projection of $\rho$. Then there are a sector dimension
$r \le D$, a number $n$ of blocks, positive dimensions $d_k$ and multiplicities $m_k$ with
$\sum_k d_k m_k = r$, and an isometry $W$ onto the support sector, with
$W^{\dagger} W = \mathbf{1}_r$ and $W W^{\dagger} = Q$, such that a matrix $Y$ satisfies
$Q Y Q = Y$ and $Q T^{*}(Y) Q = Y$ exactly when
$$Y \;=\; W \Bigl(\bigoplus_{k} \mathbf{1}_{m_k} \otimes B_k\Bigr) W^{\dagger}$$
for some matrices $B_k \in M_{d_k}(\mathbb{C})$: the corner-restricted fixed-point
star-algebra of Corollary 6.6 of *Quantum Channels & Operations* (Wolf 2012) is carried by
the isometry onto the block algebra, up to reordering the two Kronecker factors of each
block. The right-hand side is the support-sector block representation of
Equation (1.39) of *Quantum Channels & Operations* (Wolf 2012) in the
$\sum_k d_k m_k \le D$ form, without a full-rank hypothesis on the fixed point. The
equivalence characterizes the corner-restricted set only: a corner-restricted fixed
point extended by zero on the complement need not satisfy the ambient fixed-point
equation, so this does not by itself identify the ambient fixed-point space of the
adjoint map with a zero-block form. As in the corner star-algebra of Corollary 6.6, the
map is a Kraus map,
the completely positive case of the Schwarz hypothesis of the reference. The
density-weighted form of Theorem 6.14 for the Schrödinger-picture fixed points is not
asserted here.

The compressed family on the support sector is trace-preserving with a positive definite
fixed point, so the block form of the fixed-point algebra applies there; the compression
isometry transports the equivalence to the corner. -/
theorem cornerFixedPoints_blockDiagonal_iff
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ) :
    ∃ (r n : ℕ) (dims mult : Fin n → ℕ)
      (e : ((k : Fin n) × (Fin (mult k) × Fin (dims k))) ≃ Fin r)
      (W : Matrix (Fin D) (Fin r) ℂ),
      r ≤ D ∧ Wᴴ * W = 1 ∧ W * Wᴴ = stationaryProj hρ_psd ∧
        (∀ k, 0 < dims k) ∧ (∀ k, 0 < mult k) ∧
        ∀ Y : Mat,
          (stationaryProj hρ_psd * Y * stationaryProj hρ_psd = Y ∧
            stationaryProj hρ_psd * adjointMap K Y * stationaryProj hρ_psd = Y) ↔
          ∃ B : ∀ k, Matrix (Fin (dims k)) (Fin (dims k)) ℂ,
            Y = W * Matrix.reindex e e
              (Matrix.blockDiagonal' fun k =>
                (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) * Wᴴ := by
  classical
  set Q : Mat := stationaryProj hρ_psd with hQdef
  have hQproj : IsOrthogonalProjection Q := isOrthogonalProjection_stationaryProj hρ_psd
  have hInv : ∀ i : Fin d, (1 - Q) * K i * Q = 0 :=
    stationaryProj_lowerZero K hρ_psd hρ_fix
  have hQρ : Q * ρ = ρ := stationaryProj_mul hρ_psd
  have hρQ : ρ * Q = ρ := mul_stationaryProj hρ_psd
  have hQρQ : Q * ρ * Q = ρ := by rw [hQρ, hρQ]
  set A : Fin d → Mat := cornerCompressionKraus K Q with hAdef
  have hAsupp : ∀ i : Fin d, Q * A i * Q = A i :=
    cornerCompressionKraus_supported K hQproj
  have hAtp : ∑ i : Fin d, (A i)ᴴ * A i = Q :=
    cornerCompressionKraus_isTP K h_tp hQproj hInv
  -- Compress the corner family to the support sector along the isometry `V`.
  obtain ⟨r, C, φ, V, -, hCtp, hIntertw, -, -, -, hCi, hVtV, hVVt, hφV⟩ :=
    exists_corner_compression_of_supported_projection
      A Q hQproj hAsupp hAtp
  have hCtp' : IsTP C := hCtp
  -- The compressed Schrödinger map has the positive definite fixed point `σ`.
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
  -- The corner fixed-point condition corresponds to the compressed one along `φ`.
  have hcorr : ∀ X : Matrix (Fin r) (Fin r) ℂ,
      Q * adjointMap K (φ X).1 * Q = (φ X).1 ↔ adjointMap C X = X := by
    intro X
    have hφmem : Q * (φ X).1 * Q = (φ X).1 := (φ X).2
    have hintertw' : (φ (adjointMap C X)).1 = Q * adjointMap K (φ X).1 * Q := by
      rw [hIntertw X]
      rw [hAdef]
      exact adjointMap_cornerCompressionKraus_eq K hQproj hφmem
    constructor
    · intro hfix
      have hval : (φ (adjointMap C X)).1 = (φ X).1 := by rw [hintertw', hfix]
      exact φ.injective (Subtype.ext hval)
    · intro hfix
      rw [← hintertw', hfix]
  -- The block form of the compressed fixed-point algebra.
  obtain ⟨n, dims, mult, e, U, hUmem, hdims, hmult, hUiff⟩ :=
    adjointFixedPoints_blockDiagonal_iff (D := r) C hCtp' hσpd hσfix
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hUmem
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hUmem
  -- The support isometry composed with the block unitary.
  set W : Matrix (Fin D) (Fin r) ℂ := V * U with hWdef
  have hWH : Wᴴ = star U * Vᴴ := by
    rw [hWdef, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
  have hWtW : Wᴴ * W = 1 := by
    rw [hWH, hWdef]
    calc star U * Vᴴ * (V * U) = star U * (Vᴴ * V) * U := by simp [Matrix.mul_assoc]
      _ = star U * U := by rw [hVtV]; simp
      _ = 1 := hU1
  have hWWt : W * Wᴴ = Q := by
    rw [hWH, hWdef]
    calc V * U * (star U * Vᴴ) = V * (U * star U) * Vᴴ := by simp [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hU2]; simp
      _ = Q := hVVt
  -- The sector dimension is bounded by the ambient dimension.
  have hrD : r ≤ D := by
    have hinj : Function.Injective (Matrix.mulVecLin V) := by
      intro x y hxy
      have hxy' : V.mulVec x = V.mulVec y := hxy
      have h1 : (Vᴴ * V).mulVec x = (Vᴴ * V).mulVec y := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact congrArg _ hxy'
      simpa [hVtV] using h1
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  refine ⟨r, n, dims, mult, e, W, hrD, hWtW, hWWt, hdims, hmult, fun Y => ?_⟩
  constructor
  · rintro ⟨hYmem, hYfix⟩
    -- Pull `Y` back to the sector, apply the block form there, and push forward.
    set X : Matrix (Fin r) (Fin r) ℂ := φ.symm ⟨Y, hYmem⟩ with hXdef
    have hφX : (φ X).1 = Y := by rw [hXdef, LinearEquiv.apply_symm_apply]
    have hXfix : adjointMap C X = X := (hcorr X).mp (by rw [hφX]; exact hYfix)
    obtain ⟨B, hB⟩ := (hUiff X).mp hXfix
    refine ⟨B, ?_⟩
    have hXeq : X = U * Matrix.reindex e e
        (Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) * star U := by
      calc X = (U * star U) * X * (U * star U) := by rw [hU2]; simp
        _ = U * (star U * X * U) * star U := by simp [Matrix.mul_assoc]
        _ = _ := by rw [hB]
    calc Y = V * X * Vᴴ := by rw [← hφX, hφV]
      _ = W * Matrix.reindex e e
            (Matrix.blockDiagonal' fun k =>
              (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) * Wᴴ := by
          rw [hXeq, hWdef, hWH]
          simp [Matrix.mul_assoc]
  · rintro ⟨B, hYeq⟩
    -- The block-diagonal matrix on the sector is a compressed fixed point.
    set X : Matrix (Fin r) (Fin r) ℂ := U * Matrix.reindex e e
        (Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) * star U with hXdef
    have hXBd : star U * X * U = Matrix.reindex e e
        (Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) := by
      calc star U * (U * Matrix.reindex e e
            (Matrix.blockDiagonal' fun k =>
              (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) * star U) * U
          = (star U * U) * Matrix.reindex e e
              (Matrix.blockDiagonal' fun k =>
                (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) * (star U * U) := by
            simp [Matrix.mul_assoc]
        _ = _ := by rw [hU1]; simp
    have hXfix : adjointMap C X = X := (hUiff X).mpr ⟨B, hXBd⟩
    have hYX : Y = V * X * Vᴴ := by
      rw [hYeq, hXdef, hWdef, hWH]
      simp [Matrix.mul_assoc]
    have hYmem : Q * Y * Q = Y := by
      rw [hYX, ← hφV X]
      exact (φ X).2
    refine ⟨hYmem, ?_⟩
    have hfix := (hcorr X).mpr hXfix
    rwa [hφV X, ← hYX] at hfix

end Kraus
