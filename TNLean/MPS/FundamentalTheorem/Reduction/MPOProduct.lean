/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.SingleBlock
import TNLean.MPS.FundamentalTheorem.Reduction.WeightedMultiBlock
import TNLean.MPS.MPDO.ActionTensor
import TNLean.MPS.MPU.GroupRepresentation

/-!
# Compression of matrix product operator products, fusion tensors and action tensors

The asymmetric compression theorem applies verbatim to matrix product operators once a pair of
physical indices is read as one letter.  This file records three consequences.

* The stacked product `B^{ij} = ∑_m M_α^{im} ⊗ M_β^{mj}` of two MPO tensors, whose periodic
  operators decompose as `O_N(B) = ∑_{γ,μ} λ_{γμ}^N O_N(M_γ)` with normal `M_γ` and nonzero
  weights, compresses onto every weighted block
  (`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.7, Theorem 7.12,
  `cor:p5-mpo-product`).
* An MPO group representation `U_g U_h = U_{gh}` by injective tensors has fusion tensors that
  decompose the product of two tensors at every length, with a nilpotent off-diagonal
  remainder (Garre-Rubio--Lootens--Molnár, arXiv:2203.12563, equation `fusiontensorG2`; the
  original statement is Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Proposition 20).
* A matrix product state whose periodic vector is carried by an MPO to the periodic vector of
  a normal tensor has action tensors that decompose the action at every length
  (arXiv:2203.12563, equation `mpoMPSsten`).

The weights of a group representation are all one; the weighted form is what covers the
non-invertible case in which the acted state decomposes over several blocks.

## Main results

* `MPOTensor.mpv_toMPSTensor`: the periodic vector of the doubled-index view is the matrix
  entry of the periodic operator.
* `MPOTensor.left_mul_evalWord_mul_right_smul`: the compression identity
  `W B^{i₁j₁} ⋯ B^{i_Nj_N} V = λ^N M^{i₁j₁} ⋯ M^{i_Nj_N}`, the note's
  `eq:p5-mpo-product-compression`.
* `MPOTensor.exists_multiBlockCompression_mulTensor_of_mpo_eq_sum`: Theorem 7.12 itself.
* `MPOTensor.GroupFamily.IsRepresentation.exists_fusionTensors`: the fusion tensors of an MPO
  group representation, with the sharpened nilpotency length.
* `MPOTensor.exists_isReduction_actTensor_of_isNormal`: the action tensors of a single target
  block.
* `MPOTensor.exists_multiBlockCompression_actTensor_of_isNormal`: the action tensors of a
  weighted family of target blocks.
-/

open scoped Matrix

namespace MPOTensor

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

/-! ### Periodic vectors of the doubled-index view -/

/-- The periodic vector of the doubled-index MPS view of an MPO tensor, at an arbitrary
configuration of the pair alphabet, is the matrix entry of the periodic operator at the ket and
bra configurations encoded by that letter.

Source: arXiv:1606.00608, Section 4.1 (the operator family `O_N` and its matrix entries). -/
theorem mpv_toMPSTensor {D : ℕ} (M : MPOTensor d D) {N : ℕ} (ρ : Fin N → Fin (d * d)) :
    MPSTensor.mpv M.toMPSTensor ρ =
      mpo M N (fun k => (ρ k).divNat) (fun k => (ρ k).modNat) := by
  simp only [MPSTensor.mpv, MPSTensor.coeff, mpo_apply, mpoMatrixEntry]
  rw [evalWord_toMPSTensor_ofFn]

/-! ### Compression of a product of matrix product operators -/

/-- **The compression identity for matrix product operators** (P5 note, Theorem 7.12,
`eq:p5-mpo-product-compression`). Compressing a length-`N` pair word of an MPO tensor `B` onto
the slot `s` of a multi-block compression whose blocks are the weighted doubled-index views
`λ s • (C s)` returns the corresponding pair word of `C s` scaled by `λ s ^ N`. -/
theorem left_mul_evalWord_mul_right_smul {DB : ℕ} {Dγ : ι → ℕ} {B : MPOTensor d DB}
    {S : Finset ι} {lam : ι → ℂ} {C : ∀ s, MPOTensor d (Dγ s)}
    (P : MPSTensor.MultiBlockCompression B.toMPSTensor S
      fun s => lam s • (C s).toMPSTensor)
    (s : {s // s ∈ S}) {N : ℕ} (σ τ : Fin N → Fin d) :
    P.left s * evalWord B (List.ofFn σ) (List.ofFn τ) * P.right s =
      lam s.1 ^ N • evalWord (C s.1) (List.ofFn σ) (List.ofFn τ) := by
  have h := P.left_mul_evalWord_mul_right_smul s
    (List.ofFn fun k => finProdFinEquiv (σ k, τ k))
  rw [List.length_ofFn] at h
  simpa only [evalWord_toMPSTensor_pairConfig] using h

/-- **Compression of an MPO product** (P5 note, Theorem 7.12, `cor:p5-mpo-product`). Let the
periodic operators of the stacked product `B^{ij} = ∑_m M_α^{im} ⊗ M_β^{mj}` decompose as
`O_N(B) = ∑_{s ∈ S} λ_s^N O_N(M_s)` at every positive length, with normal MPO tensors `M_s` of
positive bond dimension and nonzero weights `λ_s`.  Then the stacked product admits a
multi-block compression onto the weighted blocks on the pair alphabet.

Reading the conclusions: `MPSTensor.MultiBlockCompression.left_mul_right_self` gives
`W_s V_s = 1`, `MPOTensor.left_mul_evalWord_mul_right_smul` gives
`W_s B^{i₁j₁} ⋯ B^{i_Nj_N} V_s = λ_s^N M_s^{i₁j₁} ⋯ M_s^{i_Nj_N}`,
`MPSTensor.MultiBlockCompression.left_mul_right_of_ne` gives the mutual biorthogonality of
distinct slots, and `MPSTensor.MultiBlockCompression.evalWord_remainder_eq_zero` gives the
nilpotency of the remainder. -/
theorem exists_multiBlockCompression_mulTensor_of_mpo_eq_sum {Dα Dβ : ℕ} {Dγ : ι → ℕ}
    (Mα : MPOTensor d Dα) (Mβ : MPOTensor d Dβ) (S : Finset ι) (lam : ι → ℂ)
    (Mγ : ∀ s, MPOTensor d (Dγ s)) (hlam : ∀ s ∈ S, lam s ≠ 0)
    (hMγ : ∀ s ∈ S, Kraus.IsNormal (Mγ s).toMPSTensor) (hD : ∀ s ∈ S, 0 < Dγ s)
    (hmpo : ∀ N : ℕ, 0 < N →
      mpo (mulTensor Mα Mβ) N = ∑ s ∈ S, lam s ^ N • mpo (Mγ s) N) :
    Nonempty (MPSTensor.MultiBlockCompression (mulTensor Mα Mβ).toMPSTensor S
      fun s => lam s • (Mγ s).toMPSTensor) := by
  refine MPSTensor.exists_weightedMultiBlockCompression_of_isNormal S lam
    (fun s => (Mγ s).toMPSTensor) hlam hMγ hD _ ?_
  intro N hN ρ
  have h : mpo (mulTensor Mα Mβ) N (fun k => (ρ k).divNat) (fun k => (ρ k).modNat) =
      (∑ s ∈ S, lam s ^ N • mpo (Mγ s) N) (fun k => (ρ k).divNat)
        (fun k => (ρ k).modNat) := by
    rw [hmpo N hN]
  rw [mpv_toMPSTensor, h, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun s _ => by
    rw [Matrix.smul_apply, smul_eq_mul, mpv_toMPSTensor]

/-! ### Fusion tensors of a matrix product operator group representation -/

/-- A rectangular reduction between the doubled-index views of two MPO tensors intertwines
every pair word.

Source: arXiv:2203.12563, equation `fusiontensorG2`, lines 1002--1026. -/
theorem isReduction_evalWord {DB DA : ℕ} {B : MPOTensor d DB} {A : MPOTensor d DA}
    {V : Matrix (Fin DA) (Fin DB) ℂ} {W : Matrix (Fin DB) (Fin DA) ℂ}
    (h : MPSTensor.IsReduction B.toMPSTensor A.toMPSTensor V W) {N : ℕ}
    (σ τ : Fin N → Fin d) :
    V * evalWord B (List.ofFn σ) (List.ofFn τ) * W =
      evalWord A (List.ofFn σ) (List.ofFn τ) := by
  simpa only [evalWord_toMPSTensor_pairConfig] using
    h.evalWord (List.ofFn fun k => finProdFinEquiv (σ k, τ k))

namespace GroupFamily

universe u

variable {G : Type u} [Group G]

/-- **Fusion tensors of an MPO group representation** (Garre-Rubio--Lootens--Molnár,
arXiv:2203.12563, equation `fusiontensorG2`, lines 1002--1026). For an exact positive-length
representation by injective tensors, the stacked product of the tensors of `g` and `h` reduces
onto the tensor of `g * h`: there are maps `V` and `W` that intertwine the pair word of the
product with the pair word of the tensor of `g * h` at every length, and the remainder after
the matched sector is removed is nilpotent.

The empty pair word gives `V W = 1`, the biorthogonality relations of the fusion tensors that
the paper obtains at `n = 0`.  The nilpotency length is the sharpened bound of the single-block
compression theorem, and is the paper's `ℓ`, "of the order of the bond dimension".

The result is the single-block asymmetric compression theorem of
Molnár--Ge--Schuch--Cirac, arXiv:1706.07329v2, Proposition 20, applied on the pair alphabet;
the paper cites exactly that reference at line 1002.  The weights are absent here because the
representation law `U_g U_h = U_{gh}` is an exact operator identity.  Example D of
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex` is the anomalous
instance just outside this hypothesis: the CZX-type matrix product operator squares to
`(-1)^L` times the identity rather than to the identity, so it is covered by the weighted
theorem `MPOTensor.exists_multiBlockCompression_mulTensor_of_mpo_eq_sum` with weight `-1`
instead. -/
theorem IsRepresentation.exists_fusionTensors (F : GroupFamily G d)
    (hF : F.IsRepresentation) (g h : G) :
    ∃ (V : Matrix (Fin (F.bondDim (g * h))) (Fin (F.bondDim g * F.bondDim h)) ℂ)
      (W : Matrix (Fin (F.bondDim g * F.bondDim h)) (Fin (F.bondDim (g * h))) ℂ),
      MPSTensor.IsReduction (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
          (F.tensor (g * h)).toMPSTensor V W ∧
        ∀ w : List (Fin (d * d)),
          F.bondDim g * F.bondDim h - F.bondDim (g * h) + 1 ≤ w.length →
            Kraus.evalWord (fun i => (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor i -
              W * (F.tensor (g * h)).toMPSTensor i * V) w = 0 :=
  MPSTensor.exists_isReduction_and_nilpotent_of_isNormal
    (F.tensor (g * h)).toMPSTensor (hF.isInjective (g * h)).isNormal
    (F.bondDim_pos (g * h)) (mulTensor (F.tensor g) (F.tensor h)).toMPSTensor
    (hF.sameMPV₂Pos_mulTensor F g h).symm

end GroupFamily

/-! ### Action tensors -/

/-- **Action tensors of an MPO acting on a single block** (Garre-Rubio--Lootens--Molnár,
arXiv:2203.12563, equation `mpoMPSsten`, lines 1070--1090). If the periodic operator of `T`
carries the periodic vector of `Ax` to the periodic vector of a normal tensor `Ay` of positive
bond dimension at every positive length, then the action tensor `T · Ax` reduces onto `Ay`:
there are maps `V` and `W` that decompose the action at every length, with a nilpotent
remainder.

This is the single-block asymmetric compression theorem of Molnár--Ge--Schuch--Cirac,
arXiv:1706.07329v2, Proposition 20, applied to the action tensor, which is the reference the
paper cites at line 1078. -/
theorem exists_isReduction_actTensor_of_isNormal {D Dx Dy : ℕ} (T : MPOTensor d D)
    (Ax : MPSTensor d Dx) (Ay : MPSTensor d Dy) (hAy : Kraus.IsNormal Ay) (hDy : 0 < Dy)
    (hact : ∀ N : ℕ, 0 < N →
      mpo T N *ᵥ (fun τ : Fin N → Fin d => MPSTensor.mpv Ax τ) =
        fun σ : Fin N → Fin d => MPSTensor.mpv Ay σ) :
    ∃ (V : Matrix (Fin Dy) (Fin (D * Dx)) ℂ) (W : Matrix (Fin (D * Dx)) (Fin Dy) ℂ),
      MPSTensor.IsReduction (actTensor T Ax) Ay V W ∧
        ∀ w : List (Fin d), D * Dx - Dy + 1 ≤ w.length →
          Kraus.evalWord (fun i => actTensor T Ax i - W * Ay i * V) w = 0 := by
  refine MPSTensor.exists_isReduction_and_nilpotent_of_isNormal Ay hAy hDy (actTensor T Ax)
    fun N hN σ => ?_
  have h := (mpo_mulVec_mpv T Ax N).symm.trans (hact N hN)
  exact congrFun h σ

/-- **Action tensors of an MPO acting on a weighted family of blocks** (P5 note, Theorem 7.8,
`cor:p5-weighted-compression`, applied to the action tensor; Garre-Rubio--Lootens--Molnár,
arXiv:2203.12563, equation `mpoMPSsten`, lines 1070--1090). If the periodic operator of `T`
carries the periodic vector of `Ax` to the weighted sum `∑_{s ∈ S} μ_s^N V_N(A_s)` of the
periodic vectors of normal tensors of positive bond dimension, with nonzero weights, then the
action tensor `T · Ax` admits a multi-block compression onto the weighted blocks.

This is the form needed when the acting operator is not invertible, so that the image of a
block is a superposition of several blocks rather than a single one. -/
theorem exists_multiBlockCompression_actTensor_of_isNormal {D Dx : ℕ} {Dy : ι → ℕ}
    (T : MPOTensor d D) (Ax : MPSTensor d Dx) (S : Finset ι) (μ : ι → ℂ)
    (Ay : ∀ s, MPSTensor d (Dy s)) (hμ : ∀ s ∈ S, μ s ≠ 0)
    (hAy : ∀ s ∈ S, Kraus.IsNormal (Ay s)) (hD : ∀ s ∈ S, 0 < Dy s)
    (hact : ∀ N : ℕ, 0 < N →
      mpo T N *ᵥ (fun τ : Fin N → Fin d => MPSTensor.mpv Ax τ) =
        fun σ : Fin N → Fin d => ∑ s ∈ S, μ s ^ N * MPSTensor.mpv (Ay s) σ) :
    Nonempty (MPSTensor.MultiBlockCompression (actTensor T Ax) S fun s => μ s • Ay s) :=
  MPSTensor.exists_weightedMultiBlockCompression_of_isNormal S μ Ay hμ hAy hD
    (actTensor T Ax) fun N hN σ =>
      congrFun ((mpo_mulVec_mpv T Ax N).symm.trans (hact N hN)) σ

end MPOTensor
