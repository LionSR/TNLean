/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

/-!
# Compression to cyclic sectors

This file contains the compression theorem for tensors supported on an
orthogonal projection, together with the resulting intertwining,
multiplicative, and star-preserving identities.

## Main declarations

* `exists_compressedTensor_of_supported_projection_with_letter`
* `exists_compressedTensor_of_supported_projection`

## References

* [Cirac–Pérez-García–Schuch–Verstraete, arXiv:1606.00608, Appendix A]
* [Wolf, *Quantum Channels & Operations*, Chapter 6]
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset Complex KadisonSchwarz

namespace MPSTensor

variable {d D : ℕ}

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
      simp only [evalWord, hUU, Matrix.mul_one]
  | cons i w ih =>
      have hUU : (↑U : MatrixAlg D) * (↑U : MatrixAlg D)ᴴ = 1 := by
        simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem U.prop
      simp only [evalWord]
      rw [ih]
      calc (↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D) *
            ((↑U : MatrixAlg D)ᴴ * evalWord A w * (↑U : MatrixAlg D))
          = (↑U : MatrixAlg D)ᴴ * A i * ((↑U : MatrixAlg D) * (↑U : MatrixAlg D)ᴴ) *
              evalWord A w * (↑U : MatrixAlg D) := by noncomm_ring
        _ = (↑U : MatrixAlg D)ᴴ * (A i * evalWord A w) * (↑U : MatrixAlg D) := by
              simp only [Matrix.mul_assoc, hUU, Matrix.one_mul]

/-- Compress a tensor supported on an orthogonal projection to the corresponding sector bond
space.  The compressed tensor has the same sector MPVs and inherits the left-canonical equation.
Moreover, the compression equivalence sends each compressed letter back to the
ambient supported letter.

The theorem also records the compression isomorphism from the compressed matrix
algebra onto the corner subspace.  This isomorphism intertwines the compressed
adjoint transfer map with the ambient adjoint transfer map restricted to the
corner.  The strengthened form returns a rectangular support isometry
V : ℂ^n → ℂ^D with Vᴴ V = 1, V Vᴴ = P, and φ(X) = V X Vᴴ. -/
theorem exists_compressedTensor_of_supported_projection_with_letter_and_isometry
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n)
      (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P)
      (V : Matrix (Fin D) (Fin n) ℂ),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv C σ = Matrix.trace (P * evalWord A (List.ofFn σ))) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φ (transferMap (d := d) (D := n) (fun i => (C i)ᴴ) X)).1 =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((φ X).1)) ∧
      (∀ X Y : Matrix (Fin n) (Fin n) ℂ,
        (φ (X * Y)).1 = (φ X).1 * (φ Y).1) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, (φ Xᴴ).1 = ((φ X).1)ᴴ) ∧
      (∀ i : Fin d, (φ (C i)).1 = A i) ∧
      Vᴴ * V = 1 ∧
      V * Vᴴ = P ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, (φ X).1 = V * X * Vᴴ) := by
  classical
  -- Spectral splitting of `P` via the shared bundle.
  obtain ⟨Umat, S, T, n, -, eST, eS, hUU, hU'U, hPdiag_std_lin, hP_decomp,
    hPdiag_back, htrace, trace_conj⟩ :=
    ProjectionSpectralSplit.ofOrthogonalProjection P hP
  let Pdiag : MatrixAlg D := Umatᴴ * P * Umat
  -- The diagonalizing matrix as a unitary-group element.
  have hUmem : Umat ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    ⟨by simpa [Matrix.star_eq_conjTranspose] using hU'U,
      by simpa [Matrix.star_eq_conjTranspose] using hUU⟩
  let U : Matrix.unitaryGroup (Fin D) ℂ := ⟨Umat, hUmem⟩
  -- Conjugated tensor
  let B : MPSTensor d D := fun i => Umatᴴ * A i * Umat
  -- Algebra isomorphism for reindexing (renamed to avoid clashing with the
  -- returned `φ` below).
  let rAlg : MatrixAlg D ≃ₐ[ℂ] Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.reindexAlgEquiv ℂ ℂ eST
  let P0 : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
    Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ)
  -- Pdiag in S⊕T basis
  have hPdiag_std : rAlg Pdiag = P0 := hPdiag_std_lin
  -- B_i is Pdiag-supported
  have hBsupp : ∀ i : Fin d, Pdiag * B i * Pdiag = B i := by
    intro i
    have hkey : Pdiag * B i * Pdiag = Umatᴴ * (P * A i * P) * Umat := by
      change Umatᴴ * P * Umat * (Umatᴴ * A i * Umat) * (Umatᴴ * P * Umat) =
          Umatᴴ * (P * A i * P) * Umat
      calc
        Umatᴴ * P * Umat * (Umatᴴ * A i * Umat) * (Umatᴴ * P * Umat)
            = Umatᴴ * (P * (Umat * Umatᴴ) * A i * (Umat * Umatᴴ) * P) * Umat := by
                simp only [Matrix.mul_assoc]
        _ = Umatᴴ * (P * A i * P) * Umat := by rw [hUU, Matrix.mul_one, Matrix.mul_one]
    rw [hkey, hSupp i]
  -- Block structure
  let X : Fin d → Matrix (S ⊕ T) (S ⊕ T) ℂ := fun i => rAlg (B i)
  let B11 : Fin d → Matrix S S ℂ := fun i => (X i).toBlocks₁₁
  have hX_block : ∀ i : Fin d,
      X i = Matrix.fromBlocks (B11 i) 0 0 (0 : Matrix T T ℂ) := by
    intro i
    have hsupp_block : P0 * X i * P0 = X i := by
      have := congrArg rAlg (hBsupp i)
      simp only [map_mul, hPdiag_std] at this
      exact this
    rw [(Matrix.fromBlocks_toBlocks (X i)).symm]
    rw [(Matrix.fromBlocks_toBlocks (X i)).symm] at hsupp_block
    simp only [P0, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero] at hsupp_block
    -- `hsupp_block` forces all blocks outside the `S`-sector to vanish.
    have extract (x y : S ⊕ T) := congrFun (congrFun hsupp_block x) y
    have h12 : (X i).toBlocks₁₂ = 0 := by
      ext s t
      have h := extract (Sum.inl s) (Sum.inr t)
      simp only [Matrix.fromBlocks_apply₁₂] at h
      exact h.symm
    have h21 : (X i).toBlocks₂₁ = 0 := by
      ext t s
      have h := extract (Sum.inr t) (Sum.inl s)
      simp only [Matrix.fromBlocks_apply₂₁] at h
      exact h.symm
    have h22 : (X i).toBlocks₂₂ = 0 := by
      ext t t'
      have h := extract (Sum.inr t) (Sum.inr t')
      simp only [Matrix.fromBlocks_apply₂₂] at h
      exact h.symm
    rw [h12, h21, h22]
  -- Compressed tensor
  let C : MPSTensor d n := fun i => Matrix.reindex eS eS (B11 i)
  let expand : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] MatrixAlg D :=
    cornerCompressionExpand Umat eST eS
  have hP0_def : P0 = Matrix.fromBlocks (1 : Matrix S S ℂ) 0 0 (0 : Matrix T T ℂ) := rfl
  have hexpand_def : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      expand M = Umat *
        Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm
          (Matrix.fromBlocks (Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm M)
            (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ)) * Umatᴴ := by
    intro M
    exact cornerCompressionExpand_apply Umat eST eS M
  have hPdiag_UPU : Pdiag = Umatᴴ * P * Umat := rfl
  let cornerEmbed : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P :=
    cornerCompressionLinearEquiv (P := P) (Pdiag := Pdiag) Umat eST eS P0 hP0_def
      hP_decomp hPdiag_UPU hPdiag_std_lin hPdiag_back hU'U hUU
  let V : Matrix (Fin D) (Fin n) ℂ := cornerCompressionIsometry Umat eST eS
  have hV_iso : Vᴴ * V = 1 := by
    exact cornerCompressionIsometry_conjTranspose_mul Umat eST eS hU'U
  have hExpand_one : cornerCompressionExpand Umat eST eS 1 = P :=
    cornerCompressionExpand_one (P := P) (Pdiag := Pdiag) Umat eST eS P0 hP0_def
      hP_decomp hPdiag_back
  have hV_range : V * Vᴴ = P := by
    have h := cornerCompressionExpand_eq_isometry Umat eST eS
      (1 : Matrix (Fin n) (Fin n) ℂ)
    rw [hExpand_one] at h
    simpa [V] using h.symm
  have hEmbed_eq_V :
      ∀ X : Matrix (Fin n) (Fin n) ℂ, (cornerEmbed X).1 = V * X * Vᴴ := by
    intro X
    change expand X = V * X * Vᴴ
    simpa [V] using cornerCompressionExpand_eq_isometry Umat eST eS X
  -- `A i = Umat * B i * Umatᴴ`.
  have hA_i : ∀ i, A i = Umat * B i * Umatᴴ := by
    intro i
    change A i = Umat * (Umatᴴ * A i * Umat) * Umatᴴ
    calc
      A i = (Umat * Umatᴴ) * A i * (Umat * Umatᴴ) := by rw [hUU]; simp
      _ = Umat * (Umatᴴ * A i * Umat) * Umatᴴ := by simp [Matrix.mul_assoc]
  -- `reindex eS.symm eS.symm (C i) = B11 i`.
  have hExM_C : ∀ i, Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm (C i) = B11 i :=
    fun i => (Matrix.reindexLinearEquiv ℂ ℂ eS eS).symm_apply_apply (B11 i)
  -- `reindex eST.symm eST.symm (X i) = B i`.
  have hExST_X : ∀ i, Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm (X i) = B i :=
    fun i => (Matrix.reindexLinearEquiv ℂ ℂ eST eST).symm_apply_apply (B i)
  refine ⟨n, C, cornerEmbed, V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hV_iso, hV_range,
    hEmbed_eq_V⟩
  -- (1) Trace identity: n = tr P
  · exact htrace
  -- (2) TP condition: ∑ C_i† C_i = 1
  · show ∑ i : Fin d, (C i)ᴴ * C i = 1
    -- First: ∑ B_i† B_i = Pdiag
    have hTPB : ∑ i : Fin d, (B i)ᴴ * B i = Pdiag := by
      have hterm : ∀ i, (B i)ᴴ * B i = Umatᴴ * ((A i)ᴴ * A i) * Umat := by
        intro i
        change
          (Umatᴴ * A i * Umat)ᴴ * (Umatᴴ * A i * Umat) = Umatᴴ * ((A i)ᴴ * A i) * Umat
        -- (U† A U)† = U† A† U†† = U† A† U (note U†† = U)
        have hconj : (Umatᴴ * A i * Umat)ᴴ = Umatᴴ * (A i)ᴴ * Umat := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
          rw [Matrix.mul_assoc]
        rw [hconj]
        -- U† A† U * U† A U = U† A† (UU†) A U = U† (A† A) U
        calc
          Umatᴴ * (A i)ᴴ * Umat * (Umatᴴ * A i * Umat)
              = Umatᴴ * ((A i)ᴴ * (Umat * Umatᴴ) * A i) * Umat := by
                  simp only [Matrix.mul_assoc]
          _ = Umatᴴ * ((A i)ᴴ * A i) * Umat := by rw [hUU, Matrix.mul_one]
      simp_rw [hterm]
      -- ∑ i, U† ((A i)† A i) U = U† (∑ (A i)† A i) U = U† P U = Pdiag
      trans Umatᴴ * (∑ i : Fin d, (A i)ᴴ * A i) * Umat
      · rw [Finset.mul_sum, Finset.sum_mul]
      · rw [hTP]
    -- Transport to S⊕T: ∑ B11_i† B11_i = 1_S
    have hTPblock : ∑ i : Fin d, (B11 i)ᴴ * B11 i = (1 : Matrix S S ℂ) := by
      -- φ(∑ B_i† B_i) = ∑ φ(B_i† * B_i) = ∑ (X_i)† (X_i) = P0
      -- But we also need φ(B_i†) = (X_i)†
      have hφ_ct : ∀ i, rAlg ((B i)ᴴ) = (X i)ᴴ := by
        intro i; ext a b
        simp [rAlg, X, Matrix.reindex_apply, Matrix.conjTranspose_apply,
          Matrix.submatrix_apply, Matrix.reindexAlgEquiv]
      -- h : ∑ (X_i)† * X_i = P0
      have h : ∑ i : Fin d, (X i)ᴴ * X i = P0 := by
        have h0 := congrArg rAlg hTPB
        rw [map_sum] at h0
        simp only [map_mul] at h0
        -- h0 : ∑ rAlg (B i)ᴴ * rAlg (B i) = rAlg Pdiag
        -- rAlg (B i)ᴴ is actually rAlg((B i)ᴴ) after map_mul, which equals (X i)ᴴ by hφ_ct
        simp only [show ∀ i, rAlg (B i) = X i from fun i => rfl] at h0
        -- Now use the fact that rAlg preserves star/conjTranspose
        rw [hPdiag_std] at h0
        simpa [hφ_ct] using h0
      -- Substitute block form X_i = fromBlocks(B11_i, 0, 0, 0)
      have hblock : ∀ i, (X i)ᴴ * X i =
          Matrix.fromBlocks ((B11 i)ᴴ * B11 i) 0 0 (0 : Matrix T T ℂ) := by
        intro i; rw [hX_block i]
        simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      simp_rw [hblock] at h
      -- Extract (S,S) block from h
      ext s s'
      have h1 := congrFun (congrFun h (Sum.inl s)) (Sum.inl s')
      -- LHS of h1: (∑ fromBlocks(...))(inl s)(inl s') = ∑ (fromBlocks(...))(inl s)(inl s')
      -- = ∑ (B11 i)† * B11 i s s'
      -- RHS of h1: P0 (inl s) (inl s') = 1 s s'
      -- h1 : (∑ x, fromBlocks((B11 x)† * B11 x, 0, 0, 0))(inl s)(inl s') = 1 s s'
      -- goal : (∑ i, (B11 i)† * B11 i) s s' = 1 s s'
      have hsum : ∑ i : Fin d, (B11 i)ᴴ * B11 i = (1 : Matrix S S ℂ) := by
        ext s1 s2
        have h2 := congrFun (congrFun h (Sum.inl s1)) (Sum.inl s2)
        simp only [P0, Matrix.fromBlocks_apply₁₁, Matrix.sum_apply,
          Matrix.fromBlocks_apply₁₁] at h2
        rwa [Matrix.sum_apply]
      exact congrFun (congrFun hsum s) s'
    -- Transport to Fin n
    have hterm : ∀ i, (C i)ᴴ * C i = Matrix.reindex eS eS ((B11 i)ᴴ * B11 i) := by
      intro i
      change
        (Matrix.reindex eS eS (B11 i))ᴴ * Matrix.reindex eS eS (B11 i) =
          Matrix.reindex eS eS ((B11 i)ᴴ * B11 i)
      rw [show (Matrix.reindex eS eS (B11 i))ᴴ = Matrix.reindex eS eS ((B11 i)ᴴ) from by
        ext a b
        simp only [Matrix.reindex_apply, Matrix.conjTranspose_apply,
          Matrix.submatrix_apply]]
      simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    simp_rw [hterm]
    -- ∑ reindex eS eS (f i) = reindex eS eS (∑ f i)
    ext a b
    simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.one_apply]
    rw [show (∑ i : Fin d, ((B11 i)ᴴ * B11 i) (eS.symm a) (eS.symm b)) =
        (∑ i : Fin d, (B11 i)ᴴ * B11 i) (eS.symm a) (eS.symm b) from
      (Matrix.sum_apply (eS.symm a) (eS.symm b) _ _).symm]
    rw [hTPblock, Matrix.one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  -- (3) MPV identity
  · intro N σ
    set w := List.ofFn σ
    -- mpv C σ = tr(evalWord B11 w) (by reindexing)
    have hmpv_C : mpv C σ = Matrix.trace (_root_.evalWord B11 w) := by
      simp only [mpv, coeff]
      have : MPSTensor.evalWord C w = Matrix.reindex eS eS (_root_.evalWord B11 w) := by
        simpa [C] using MPSTensor.evalWord_reindex (e := eS) (A := B11) w
      rw [this]; exact Matrix.trace_reindex eS _
    -- tr(evalWord B11 w) = tr(Pdiag * evalWord B w)
    -- Proved entrywise using the block structure
    have htr_key : Matrix.trace (_root_.evalWord B11 w) =
        Matrix.trace (Pdiag * evalWord B w) := by
      -- Both sides = ∑_{s:S} (evalWord B11 w) s s
      -- Reindex RHS to S⊕T
      have htrace_reindex :
          Matrix.trace (Pdiag * evalWord B w) =
            Matrix.trace (rAlg (Pdiag * evalWord B w)) := by
        change Matrix.trace (Pdiag * evalWord B w) =
          Matrix.trace (Matrix.reindex eST eST (Pdiag * evalWord B w))
        rw [Matrix.trace_reindex]
      rw [htrace_reindex]
      rw [map_mul, hPdiag_std]
      -- rAlg(evalWord B w) = evalWord X w
      have hφ_eval : rAlg (evalWord B w) = _root_.evalWord X w := by
        change Matrix.reindex eST eST (evalWord B w) = _root_.evalWord X w
        have h := evalWord_reindex_fin (e := eST) (A := B) w
        rw [show (fun i => Matrix.reindex eST eST (B i)) = X from by
          ext i; simp [rAlg, X]] at h
        exact h.symm
      rw [hφ_eval]
      -- Now: tr(P0 * evalWord X w) = tr(evalWord B11 w)
      -- Entrywise argument
      change Matrix.trace (_root_.evalWord B11 w) =
        Matrix.trace (P0 * _root_.evalWord X w)
      symm
      -- tr(P0 * M) = ∑_{s:S} M (inl s) (inl s) for any M
      rw [show Matrix.trace (P0 * _root_.evalWord X w) =
          ∑ x : S ⊕ T, (P0 * _root_.evalWord X w) x x from rfl,
        Fintype.sum_sum_type]
      -- T part is zero since P0 has zero T-rows
      have hT_zero : ∑ t : T, (P0 * _root_.evalWord X w) (Sum.inr t) (Sum.inr t) = 0 := by
        apply Finset.sum_eq_zero; intro t _
        change (P0 * _root_.evalWord X w) (Sum.inr t) (Sum.inr t) = 0
        simp only [Matrix.mul_apply]
        apply Finset.sum_eq_zero; intro y _
        cases y with
        | inl s => simp [P0, Matrix.fromBlocks_apply₂₁]
        | inr t' => simp [P0, Matrix.fromBlocks_apply₂₂]
      rw [hT_zero, add_zero]
      -- S part: (P0 * M)(inl s)(inl s) = M(inl s)(inl s) since P0 is identity on S
      have hS_eq : ∀ s : S, (P0 * _root_.evalWord X w) (Sum.inl s) (Sum.inl s) =
          _root_.evalWord X w (Sum.inl s) (Sum.inl s) := by
        intro s; simp only [Matrix.mul_apply]
        rw [Fintype.sum_sum_type]
        have hT : ∑ t : T, P0 (Sum.inl s) (Sum.inr t) *
            _root_.evalWord X w (Sum.inr t) (Sum.inl s) = 0 := by
          apply Finset.sum_eq_zero; intro t _
          simp [P0, Matrix.fromBlocks_apply₁₂]
        rw [hT, add_zero]
        rw [Finset.sum_eq_single s]
        · simp [P0, Matrix.fromBlocks_apply₁₁]
        · intro s' _ hs'
          have hsne : s ≠ s' := hs' ∘ Eq.symm
          have hzero : P0 (Sum.inl s) (Sum.inl s') = 0 := by
            simp [P0, Matrix.fromBlocks_apply₁₁, hsne]
          simp [hzero]
        · intro h; exact absurd (Finset.mem_univ s) h
      simp_rw [hS_eq]
      -- Now: ∑_{s:S} evalWord X w (inl s) (inl s) = ∑_{s:S} evalWord B11 w s s
      -- This follows because (evalWord X w).toBlocks₁₁ = evalWord B11 w
      -- (by induction, since each X_i = fromBlocks(B11_i, 0, 0, 0))
      congr 1; ext s
      -- evalWord X w (inl s) (inl s) = evalWord B11 w s s
      suffices ∀ ww : List (Fin d), ∀ s1 s2 : S,
          _root_.evalWord X ww (Sum.inl s1) (Sum.inl s2) =
          _root_.evalWord B11 ww s1 s2 from this w s s
      intro ww; induction ww with
      | nil =>
          intro s1 s2; simp [_root_.evalWord, Matrix.one_apply, Sum.inl.injEq]
      | cons j ww ih =>
          intro s1 s2
          simp only [_root_.evalWord, Matrix.mul_apply, Fintype.sum_sum_type]
          -- T contribution is zero
          have : ∑ t : T, X j (Sum.inl s1) (Sum.inr t) *
              _root_.evalWord X ww (Sum.inr t) (Sum.inl s2) = 0 := by
            apply Finset.sum_eq_zero; intro t _
            rw [show X j (Sum.inl s1) (Sum.inr t) = 0 from by
              rw [hX_block j]; simp [Matrix.fromBlocks_apply₁₂]]
            simp
          rw [this, add_zero]
          congr 1; ext s'
          rw [show X j (Sum.inl s1) (Sum.inl s') = B11 j s1 s' from by
            rw [hX_block j]; simp [Matrix.fromBlocks_apply₁₁]]
          rw [ih s' s2]
    -- tr(Pdiag * evalWord B w) = tr(P * evalWord A w) by unitary conjugation
    have htr_conj : Matrix.trace (Pdiag * evalWord B w) =
        Matrix.trace (P * evalWord A (List.ofFn σ)) := by
      have hEvalB := evalWord_conj_unitary A U (List.ofFn σ)
      rw [show (fun i => (↑U : MatrixAlg D)ᴴ * A i * (↑U : MatrixAlg D)) = B
        from rfl] at hEvalB
      rw [hEvalB]
      change
        Matrix.trace (Umatᴴ * P * Umat * (Umatᴴ * evalWord A (List.ofFn σ) * Umat)) =
          Matrix.trace (P * evalWord A (List.ofFn σ))
      set M := evalWord A (List.ofFn σ)
      -- U†PU * U†MU = U†P(UU†)MU = U†(PM)U, tr = tr(PM) by trace_conj
      have hprod : Umatᴴ * P * Umat * (Umatᴴ * M * Umat) = Umatᴴ * (P * M) * Umat := by
        calc
          Umatᴴ * P * Umat * (Umatᴴ * M * Umat)
              = Umatᴴ * (P * (Umat * Umatᴴ) * M) * Umat := by
                  simp only [Matrix.mul_assoc]
          _ = Umatᴴ * (P * M) * Umat := by rw [hUU, Matrix.mul_one]
      rw [hprod, trace_conj]
    calc mpv C σ
        = Matrix.trace (_root_.evalWord B11 w) := hmpv_C
      _ = Matrix.trace (Pdiag * evalWord B w) := htr_key
      _ = Matrix.trace (P * evalWord A (List.ofFn σ)) := htr_conj
  -- (4) Intertwining identity:
  --     (φ (transferMap (C†) Z)).1 = transferMap (A†) ((φ Z).1)
  · intro Z
    change expand (transferMap (d := d) (D := n) (fun j => (C j)ᴴ) Z) =
      transferMap (d := d) (D := D) (fun j => (A j)ᴴ) (expand Z)
    simp only [transferMap_apply, Matrix.conjTranspose_conjTranspose]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- Per-letter: expand ((C i)ᴴ * Z * C i) = (A i)ᴴ * expand Z * A i.
    -- Abbreviations for readability.
    set M' : Matrix S S ℂ := Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm Z
    set F : Matrix (S ⊕ T) (S ⊕ T) ℂ :=
      Matrix.fromBlocks M'
        (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) with hF_def
    set G : MatrixAlg D := Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm F
    -- `expand Z = Umat * G * Umatᴴ`.
    have hexpand_Z : expand Z = Umat * G * Umatᴴ := hexpand_def Z
    -- `(A i)ᴴ = Umat * (B i)ᴴ * Umatᴴ`.
    have hA_i_ct : (A i)ᴴ = Umat * (B i)ᴴ * Umatᴴ := by
      rw [hA_i i, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    -- Reduction: reindex eS.symm eS.symm ((C i)ᴴ * Z * C i) = (B11 i)ᴴ * M' * B11 i.
    have hExM_letter :
        Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm ((C i)ᴴ * Z * C i) =
          (B11 i)ᴴ * M' * B11 i := by
      rw [← Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
            eS.symm eS.symm eS.symm ((C i)ᴴ * Z) (C i),
          ← Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
            eS.symm eS.symm eS.symm ((C i)ᴴ) Z]
      have hCt_reindex :
          Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm ((C i)ᴴ) = (B11 i)ᴴ := by
        change Matrix.reindex eS.symm eS.symm ((C i)ᴴ) = (B11 i)ᴴ
        simpa [Matrix.conjTranspose_reindex] using congrArg (fun M => Mᴴ) (hExM_C i)
      rw [hCt_reindex, hExM_C i]
    -- Block identity: fromBlocks ((B11 i)ᴴ * M' * B11 i) 0 0 0 = (X i)ᴴ * F * X i.
    have hF_letter :
        Matrix.fromBlocks ((B11 i)ᴴ * M' * B11 i) (0 : Matrix S T ℂ)
            (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) =
          (X i)ᴴ * F * X i := by
      rw [hX_block i, hF_def]
      rw [show (Matrix.fromBlocks (B11 i) (0 : Matrix S T ℂ)
              (0 : Matrix T S ℂ) (0 : Matrix T T ℂ))ᴴ =
            Matrix.fromBlocks (B11 i)ᴴ (0 : Matrix S T ℂ)
              (0 : Matrix T S ℂ) (0 : Matrix T T ℂ) from by
          simp [Matrix.fromBlocks_conjTranspose]]
      simp [Matrix.fromBlocks_multiply]
    -- Compute LHS = Umat * ((B i)ᴴ * G * B i) * Umatᴴ.
    have hLHS :
        expand ((C i)ᴴ * Z * C i) = Umat * ((B i)ᴴ * G * B i) * Umatᴴ := by
      rw [hexpand_def ((C i)ᴴ * Z * C i)]
      congr 1
      congr 1
      rw [hExM_letter, hF_letter]
      rw [← Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
            eST.symm eST.symm eST.symm ((X i)ᴴ * F) (X i),
          ← Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
            eST.symm eST.symm eST.symm ((X i)ᴴ) F]
      have hXct_reindex :
          Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm ((X i)ᴴ) = (B i)ᴴ := by
        change Matrix.reindex eST.symm eST.symm ((X i)ᴴ) = (B i)ᴴ
        simpa [Matrix.conjTranspose_reindex] using congrArg (fun M => Mᴴ) (hExST_X i)
      rw [hXct_reindex, hExST_X i]
    -- Compute RHS = Umat * ((B i)ᴴ * G * B i) * Umatᴴ.
    have hRHS :
        (A i)ᴴ * expand Z * A i = Umat * ((B i)ᴴ * G * B i) * Umatᴴ := by
      rw [hexpand_Z, hA_i_ct, hA_i i]
      calc
        (Umat * (B i)ᴴ * Umatᴴ) * (Umat * G * Umatᴴ) * (Umat * B i * Umatᴴ)
            = Umat * (B i)ᴴ * (Umatᴴ * Umat) * G * (Umatᴴ * Umat) * B i * Umatᴴ := by
              noncomm_ring
        _ = Umat * ((B i)ᴴ * G * B i) * Umatᴴ := by
              rw [hU'U]; noncomm_ring
    rw [hLHS, hRHS]
  -- (5) Multiplicativity: (φ (X * Y)).1 = (φ X).1 * (φ Y).1.
  · intro X Y
    change expand (X * Y) = expand X * expand Y
    exact cornerCompressionExpand_mul Umat eST eS hU'U X Y
  -- (6) Star-preservation: (φ Xᴴ).1 = ((φ X).1)ᴴ.
  · intro X
    change expand Xᴴ = (expand X)ᴴ
    exact (cornerCompressionExpand_conjTranspose Umat eST eS X).symm
  -- (7) Letter expansion: φ(C_i) is the original supported ambient letter.
  · intro i
    change expand (C i) = A i
    have hBlockBack :
        Matrix.reindexLinearEquiv ℂ ℂ eST.symm eST.symm
            (Matrix.fromBlocks
              (Matrix.reindexLinearEquiv ℂ ℂ eS.symm eS.symm (C i))
              (0 : Matrix S T ℂ) (0 : Matrix T S ℂ) (0 : Matrix T T ℂ)) =
          B i := by
      rw [hExM_C i, ← hX_block i]
      exact hExST_X i
    calc
      expand (C i) = Umat * B i * Umatᴴ := by
        rw [hexpand_def, hBlockBack]
      _ = A i := (hA_i i).symm

/-- Compress a tensor supported on an orthogonal projection to the corresponding sector bond
space.  The compressed tensor has the same sector MPVs and inherits the left-canonical equation.
Moreover, the compression equivalence sends each compressed letter back to the
ambient supported letter.

This is the projection of
`exists_compressedTensor_of_supported_projection_with_letter_and_isometry` that
forgets the support isometry. -/
theorem exists_compressedTensor_of_supported_projection_with_letter
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n)
      (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv C σ = Matrix.trace (P * evalWord A (List.ofFn σ))) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φ (transferMap (d := d) (D := n) (fun i => (C i)ᴴ) X)).1 =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((φ X).1)) ∧
      (∀ X Y : Matrix (Fin n) (Fin n) ℂ,
        (φ (X * Y)).1 = (φ X).1 * (φ Y).1) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, (φ Xᴴ).1 = ((φ X).1)ᴴ) ∧
      (∀ i : Fin d, (φ (C i)).1 = A i) := by
  obtain ⟨n, C, φ, _V, hdim, hCtp, hCmpv, hIntertwine, hMul, hStar, hLetter,
    _hV_iso, _hV_range, _hEmbed_eq_V⟩ :=
    exists_compressedTensor_of_supported_projection_with_letter_and_isometry A P hP hSupp hTP
  exact ⟨n, C, φ, hdim, hCtp, hCmpv, hIntertwine, hMul, hStar, hLetter⟩

/-- Compress a tensor supported on an orthogonal projection to the corresponding sector bond
space.  The compressed tensor has the same sector MPVs and inherits the left-canonical equation.

This is the projection of
`exists_compressedTensor_of_supported_projection_with_letter` that forgets the
letter-expansion identity. -/
theorem exists_compressedTensor_of_supported_projection
    (A : MPSTensor d D) (P : MatrixAlg D)
    (hP : IsOrthogonalProjection P)
    (hSupp : ∀ i : Fin d, P * A i * P = A i)
    (hTP : ∑ i : Fin d, (A i)ᴴ * A i = P) :
    ∃ (n : ℕ) (C : MPSTensor d n)
      (φ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P),
      ((n : ℂ) = Matrix.trace P) ∧
      (∑ i : Fin d, (C i)ᴴ * C i = 1) ∧
      (∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv C σ = Matrix.trace (P * evalWord A (List.ofFn σ))) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φ (transferMap (d := d) (D := n) (fun i => (C i)ᴴ) X)).1 =
          transferMap (d := d) (D := D) (fun i => (A i)ᴴ) ((φ X).1)) ∧
      (∀ X Y : Matrix (Fin n) (Fin n) ℂ,
        (φ (X * Y)).1 = (φ X).1 * (φ Y).1) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, (φ Xᴴ).1 = ((φ X).1)ᴴ) := by
  obtain ⟨n, C, φ, hdim, hCtp, hCmpv, hIntertwine, hMul, hStar, _hLetter⟩ :=
    exists_compressedTensor_of_supported_projection_with_letter A P hP hSupp hTP
  exact ⟨n, C, φ, hdim, hCtp, hCmpv, hIntertwine, hMul, hStar⟩

end Compression

end MPSTensor
