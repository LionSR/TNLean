/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import TNLean.Algebra.OperatorNormFrobenius
import TNLean.Analysis.SpectralRadiusPowerDecay
import TNLean.Channel.Primitive
import TNLean.MPS.Core.TransferChannel
import TNLean.MPS.Overlap.Basic

/-!
# Half-chain Schmidt reduction for a translation-invariant MPS ring

On a ring of `2 L` sites the translation-invariant MPS coefficient at a split
configuration `(σ, τ)` is `tr(A_σ A_τ) = ∑_{α,β} ⟨α|A_σ|β⟩ ⟨β|A_τ|α⟩`, so the
state is the image of a boundary pairing under the two half-chain families
`|Ψ_{α,β}⟩ = ∑_σ ⟨α|A_σ|β⟩ |σ⟩`.  This file formalizes the
Schmidt-decomposition calculation behind the half-chain interpretation of the
dual fixed point: the unnormalized half-chain reduced density matrix factors
exactly through the half-chain overlap Gram matrix, its characteristic
polynomial agrees (away from zero) with that of a `D² × D²` comparison matrix
built from the `L`-fold transfer map, and the Gram entries converge
geometrically to the entries of the rank-one fixed-point projection, with rate
controlled by the subleading spectrum of the transfer map.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 6 ("Interpretation of
`Λ`", `MPSarchive.tex` lines 987--993) and the Schmidt-decomposition
calculation at lines 970--985.  The gauge convention here places the
trace-preserving direction on the transfer map itself, so the source's
positive diagonal dual fixed point `Λ` appears as the fixed point of
`transferMap A`; the source's unit fixed point corresponds to the dual
(trace-adjoint) direction.

## Main results

- `MPSTensor.halfChainKernel_eq_mul`: the ring coefficient kernel factors
  through the half-chain families (lines 970--976).
- `MPSTensor.halfChainGram_apply_eq_transferMap_pow`: the half-chain overlap
  Gram entries are matrix elements of the `L`-fold transfer map on matrix
  units (the display `⟨Ψ_{α,β}|Ψ_{α',β'}⟩ = ⟨α'|E^{N/2}(|β'⟩⟨β|)|α⟩`,
  lines 977--979).
- `MPSTensor.halfChainReducedMatrix_eq_mul_swap_gram`: the unnormalized
  half-chain reduced density matrix equals `Ψ W Ψᴴ` with `W` the
  index-swapped Gram matrix of the complementary half (lines 979--985).
- `MPSTensor.charpoly_halfChainReducedMatrix`: away from zero, the spectrum
  of the half-chain reduced density matrix is that of the `D² × D²`
  comparison matrix `W · G`.
- `MPSTensor.exists_geometric_bound_halfChainGram_sub_fixedPointProj`: the
  transfer-error term, geometric in `L` under a complementary spectral-radius
  gap (the correction "of the order `|ν₂|^{N/2}`", lines 979--981).
- `MPSTensor.fixedPointProj_single_entry_diagonal`: for diagonal `Λ` the
  limiting Gram matrix is the diagonal matrix of eigenvalues of `Λ`
  (the display `λ_α δ_{α,α'} δ_{β,β'}`, line 979).
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open Matrix Polynomial

namespace MPSTensor

variable {d D : ℕ}

/-- The half-chain family of PGVWC07: the matrix whose column at boundary pair
`(α, β)` is the half-chain vector `|Ψ_{α,β}⟩ = ∑_σ ⟨α|A_σ|β⟩ |σ⟩`.
Source: arXiv:quant-ph/0608197, lines 970--976. -/
noncomputable def halfChainMatrix (A : MPSTensor d D) (L : ℕ) :
    Matrix (Cfg d L) (Fin D × Fin D) ℂ :=
  Matrix.of fun σ p => evalWord A (List.ofFn σ) p.1 p.2

@[simp]
theorem halfChainMatrix_apply (A : MPSTensor d D) (L : ℕ) (σ : Cfg d L)
    (p : Fin D × Fin D) :
    halfChainMatrix A L σ p = evalWord A (List.ofFn σ) p.1 p.2 := rfl

/-- The complementary half-chain family with swapped boundary indices: the row
at `(α, β)` is the vector `|Ψ_{β,α}⟩` appearing on the second half of the ring
in `|ψ⟩ = ∑_{α,β} |Ψ_{α,β}⟩ |Ψ_{β,α}⟩`.
Source: arXiv:quant-ph/0608197, lines 970--976. -/
noncomputable def halfChainSwapMatrix (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin D × Fin D) (Cfg d L) ℂ :=
  Matrix.of fun p τ => evalWord A (List.ofFn τ) p.2 p.1

@[simp]
theorem halfChainSwapMatrix_apply (A : MPSTensor d D) (L : ℕ)
    (p : Fin D × Fin D) (τ : Cfg d L) :
    halfChainSwapMatrix A L p τ = evalWord A (List.ofFn τ) p.2 p.1 := rfl

/-- The coefficient kernel of the ring of `2 L` sites, read as a matrix over
the two half-chain configuration spaces: the entry at `(σ, τ)` is the MPS
coefficient `tr(A_σ A_τ)` of the joined configuration.
Source: arXiv:quant-ph/0608197, lines 970--976. -/
noncomputable def halfChainKernel (A : MPSTensor d D) (L : ℕ) :
    Matrix (Cfg d L) (Cfg d L) ℂ :=
  Matrix.of fun σ τ => mpv A (Fin.append σ τ)

@[simp]
theorem halfChainKernel_apply (A : MPSTensor d D) (L : ℕ) (σ τ : Cfg d L) :
    halfChainKernel A L σ τ = mpv A (Fin.append σ τ) := rfl

/-- Splitting the ring trace at the two boundaries: the coefficient kernel is
the product of the half-chain family with its index-swapped complement.  This
is the resolution of the identity producing
`|ψ⟩ = ∑_{α,β} |Ψ_{α,β}⟩ |Ψ_{β,α}⟩`.
Source: arXiv:quant-ph/0608197, lines 970--976. -/
theorem halfChainKernel_eq_mul (A : MPSTensor d D) (L : ℕ) :
    halfChainKernel A L = halfChainMatrix A L * halfChainSwapMatrix A L := by
  ext σ τ
  rw [halfChainKernel_apply, mpv_eq, coeff_eq, List.ofFn_fin_append, evalWord_append,
    Matrix.mul_apply]
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]

/-- The unnormalized half-chain reduced density matrix of the ring state on
`2 L` sites: the second half of the ring is traced out from the rank-one state
built from the coefficient kernel.
Source: arXiv:quant-ph/0608197, lines 979--985. -/
noncomputable def halfChainReducedMatrix (A : MPSTensor d D) (L : ℕ) :
    Matrix (Cfg d L) (Cfg d L) ℂ :=
  halfChainKernel A L * (halfChainKernel A L)ᴴ

/-- Entrywise, the half-chain reduced density matrix is the partial trace of
the ring state over the complementary half-chain configurations. -/
theorem halfChainReducedMatrix_apply (A : MPSTensor d D) (L : ℕ) (σ σ' : Cfg d L) :
    halfChainReducedMatrix A L σ σ' =
      ∑ τ : Cfg d L, mpv A (Fin.append σ τ) * star (mpv A (Fin.append σ' τ)) := by
  simp [halfChainReducedMatrix, Matrix.mul_apply]

/-- The half-chain reduced density matrix is positive semidefinite. -/
theorem posSemidef_halfChainReducedMatrix (A : MPSTensor d D) (L : ℕ) :
    (halfChainReducedMatrix A L).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- The half-chain overlap Gram matrix
`G_{(α,β),(α',β')} = ⟨Ψ_{α,β}|Ψ_{α',β'}⟩`.
Source: arXiv:quant-ph/0608197, lines 977--979. -/
noncomputable def halfChainGram (A : MPSTensor d D) (L : ℕ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  (halfChainMatrix A L)ᴴ * halfChainMatrix A L

/-- The half-chain overlap is a matrix element of the iterated transfer map on
a matrix unit: `⟨Ψ_{α,β}|Ψ_{α',β'}⟩ = (E^L(|β'⟩⟨β|))_{α',α}`.
Source: arXiv:quant-ph/0608197, the display at lines 977--979. -/
theorem halfChainGram_apply_eq_transferMap_pow (A : MPSTensor d D) (L : ℕ)
    (p q : Fin D × Fin D) :
    halfChainGram A L p q =
      (((transferMap (d := d) (D := D) A) ^ L) (Matrix.single q.2 p.2 1)) q.1 p.1 := by
  classical
  have hmul (W : Matrix (Fin D) (Fin D) ℂ) (a b c e : Fin D) :
      ((W * Matrix.single c a 1 * Wᴴ : Matrix (Fin D) (Fin D) ℂ) e b) =
        W e c * star (W b a) := by
    rw [Matrix.mul_apply]
    calc
      ∑ j, ((W * Matrix.single c a 1 : Matrix (Fin D) (Fin D) ℂ) e j) * Wᴴ j b =
          ((W * Matrix.single c a 1 : Matrix (Fin D) (Fin D) ℂ) e a) * Wᴴ a b := by
        apply Finset.sum_eq_single a
        · intro j _ hja
          rw [Matrix.mul_apply]
          simp [hja.symm]
        · simp
      _ = W e c * star (W b a) := by
        rw [Matrix.mul_apply]
        simp [Matrix.single_apply]
  rw [halfChainGram, Matrix.mul_apply, transferMap_pow_apply' A L, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hmul (evalWord A (List.ofFn σ)) p.2 p.1 q.2 q.1]
  simp [mul_comm]

/-- The Gram matrix of the complementary half-chain family is the transpose of
the boundary-swapped Gram matrix of the first half. -/
theorem halfChainSwapMatrix_mul_conjTranspose (A : MPSTensor d D) (L : ℕ) :
    halfChainSwapMatrix A L * (halfChainSwapMatrix A L)ᴴ =
      ((halfChainGram A L).submatrix Prod.swap Prod.swap)ᵀ := by
  ext p q
  simp only [Matrix.mul_apply, halfChainSwapMatrix_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Matrix.submatrix_apply, Prod.fst_swap, Prod.snd_swap,
    halfChainGram, halfChainMatrix_apply]
  exact Finset.sum_congr rfl fun τ _ => mul_comm _ _

/-- The Schmidt-decomposition calculation of PGVWC07: the unnormalized
half-chain reduced density matrix factors exactly as `Ψ (S Gᵀ S) Ψᴴ`, where
`Ψ` is the half-chain family, `G` the half-chain Gram matrix, and `S` the swap
of the two boundary indices.
Source: arXiv:quant-ph/0608197, lines 979--985. -/
theorem halfChainReducedMatrix_eq_mul_swap_gram (A : MPSTensor d D) (L : ℕ) :
    halfChainReducedMatrix A L =
      halfChainMatrix A L *
        (((halfChainGram A L).submatrix Prod.swap Prod.swap)ᵀ *
          (halfChainMatrix A L)ᴴ) := by
  rw [halfChainReducedMatrix, halfChainKernel_eq_mul, ← halfChainSwapMatrix_mul_conjTranspose,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Away from zero, the spectrum of the half-chain reduced density matrix is
computed by the `D² × D²` comparison matrix `(S Gᵀ S) · G` built from the
half-chain Gram matrix: the two characteristic polynomials agree after
matching the trivial kernel factors.  This reduces the half-chain spectral
comparison of PGVWC07, Theorem 6, to the boundary comparison matrix.
Source: arXiv:quant-ph/0608197, lines 979--993. -/
theorem charpoly_halfChainReducedMatrix (A : MPSTensor d D) (L : ℕ) :
    X ^ (D * D) * (halfChainReducedMatrix A L).charpoly =
      X ^ d ^ L *
        (((halfChainGram A L).submatrix Prod.swap Prod.swap)ᵀ *
          halfChainGram A L).charpoly := by
  have h := Matrix.charpoly_mul_comm' (halfChainMatrix A L)
    (((halfChainGram A L).submatrix Prod.swap Prod.swap)ᵀ * (halfChainMatrix A L)ᴴ)
  rw [← halfChainReducedMatrix_eq_mul_swap_gram, Matrix.mul_assoc,
    show (halfChainMatrix A L)ᴴ * halfChainMatrix A L = halfChainGram A L from rfl] at h
  simpa [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun] using h

section Convergence

/-- Transfer-error control for the half-chain overlaps: if the transfer map is
trace preserving with fixed point `Λ` and the complementary part of the
transfer map has spectral radius below one, then every half-chain Gram entry
converges geometrically to the corresponding entry of the rank-one fixed-point
projection, uniformly in the boundary indices.  This is the correction term
"of the order `|ν₂|^{N/2}`" controlled by the subleading spectrum.
Source: arXiv:quant-ph/0608197, lines 977--981. -/
theorem exists_geometric_bound_halfChainGram_sub_fixedPointProj
    (A : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (htr : Matrix.trace Λ ≠ 0)
    (hTP : IsTracePreservingMap (transferMap A))
    (hΛ : transferMap A Λ = Λ)
    (hgap : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (transferMap A - fixedPointProj Λ htr)) < 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ L, 1 ≤ L → ∀ p q : Fin D × Fin D,
      ‖halfChainGram A L p q -
        fixedPointProj Λ htr (Matrix.single q.2 p.2 1) q.1 p.1‖ ≤ C * r ^ L := by
  set N := transferMap (d := d) (D := D) A - fixedPointProj Λ htr with hN
  set T := (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) N with hT
  obtain ⟨C, r, hC, hr0, hr1, hbound⟩ :=
    geometric_bound_of_spectralRadius_lt_one T (by simpa [hT, hN] using hgap)
  refine ⟨C, r, hC, hr0, hr1, fun L hL p q => ?_⟩
  have hpow : (transferMap (d := d) (D := D) A) ^ L = fixedPointProj Λ htr + N ^ L :=
    pow_eq_fixedPointProj_add_compl_pow (E := transferMap A) (ρ := Λ) htr hTP hΛ hL
  have hentry : halfChainGram A L p q -
      fixedPointProj Λ htr (Matrix.single q.2 p.2 1) q.1 p.1 =
      ((N ^ L) (Matrix.single q.2 p.2 1)) q.1 p.1 := by
    rw [halfChainGram_apply_eq_transferMap_pow, hpow]
    simp [Matrix.add_apply]
  rw [hentry]
  have hentry_le : ‖((N ^ L) (Matrix.single q.2 p.2 1)) q.1 p.1‖ ≤
      ‖(N ^ L) (Matrix.single q.2 p.2 1)‖ := by
    have hsum := Matrix.sum_column_norm_sq_le_norm_sq ((N ^ L) (Matrix.single q.2 p.2 1)) p.1
    have hterm : ‖((N ^ L) (Matrix.single q.2 p.2 1)) q.1 p.1‖ ^ 2 ≤
        ∑ k, ‖((N ^ L) (Matrix.single q.2 p.2 1)) k p.1‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun k => ‖((N ^ L) (Matrix.single q.2 p.2 1)) k p.1‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ q.1)
    nlinarith [norm_nonneg (((N ^ L) (Matrix.single q.2 p.2 1)) q.1 p.1),
      norm_nonneg ((N ^ L) (Matrix.single q.2 p.2 1))]
  have hop : ‖(N ^ L) (Matrix.single q.2 p.2 1)‖ ≤ ‖T ^ L‖ := by
    have happly : (N ^ L) (Matrix.single q.2 p.2 1) = (T ^ L) (Matrix.single q.2 p.2 1) := by
      rw [hT, ← map_pow]
      rfl
    calc ‖(N ^ L) (Matrix.single q.2 p.2 1)‖
        = ‖(T ^ L) (Matrix.single q.2 p.2 1)‖ := by rw [happly]
      _ ≤ ‖T ^ L‖ * ‖(Matrix.single q.2 p.2 1 : Matrix (Fin D) (Fin D) ℂ)‖ :=
          (T ^ L).le_opNorm _
      _ = ‖T ^ L‖ := by rw [Matrix.l2_opNorm_single_one, mul_one]
  calc ‖((N ^ L) (Matrix.single q.2 p.2 1)) q.1 p.1‖
      ≤ ‖(N ^ L) (Matrix.single q.2 p.2 1)‖ := hentry_le
    _ ≤ ‖T ^ L‖ := hop
    _ ≤ C * r ^ L := hbound L

/-- For a positive diagonal fixed point `Λ = diag(λ_1, …, λ_D)` the limiting
Gram entries reproduce the source's display `λ_α δ_{α,α'} δ_{β,β'}` up to the
trace normalization: the limiting Gram matrix is diagonal in the boundary
pairs with entry `λ_α / tr Λ` at `(α, β)`.
Source: arXiv:quant-ph/0608197, line 979. -/
theorem fixedPointProj_single_entry_diagonal
    (lam : Fin D → ℂ) (htr : Matrix.trace (Matrix.diagonal lam) ≠ 0)
    (p q : Fin D × Fin D) :
    fixedPointProj (Matrix.diagonal lam) htr (Matrix.single q.2 p.2 1) q.1 p.1 =
      Matrix.diagonal
        (fun x : Fin D × Fin D => lam x.1 / Matrix.trace (Matrix.diagonal lam)) p q := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨a', b'⟩
  have happ : fixedPointProj (Matrix.diagonal lam) htr
      (Matrix.single b' b 1 : Matrix (Fin D) (Fin D) ℂ) =
      (Matrix.trace (Matrix.single b' b 1 : Matrix (Fin D) (Fin D) ℂ) /
        Matrix.trace (Matrix.diagonal lam)) • Matrix.diagonal lam := rfl
  rw [happ, Matrix.smul_apply, smul_eq_mul]
  by_cases hb : b' = b
  · subst hb
    rw [Matrix.trace_single_eq_same]
    by_cases ha : a' = a
    · subst ha
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, div_mul_eq_mul_div, one_mul]
    · rw [Matrix.diagonal_apply_ne lam ha, mul_zero,
        Matrix.diagonal_apply_ne _ (fun h => ha ((Prod.ext_iff.mp h).1).symm)]
  · rw [Matrix.trace_single_eq_of_ne b' b (1 : ℂ) hb, zero_div, zero_mul,
      Matrix.diagonal_apply_ne _ (fun h => hb ((Prod.ext_iff.mp h).2).symm)]

/-- Entrywise perturbation bound for a matrix product: if both factors are
entrywise within `ε` of limiting matrices whose entries are bounded by `B`,
then the product is entrywise within `card n * (ε * (B + ε) + B * ε)` of the
limiting product. -/
private theorem entrywise_mul_bound {n : Type*} [Fintype n]
    (X X₀ Y Y₀ : Matrix n n ℂ) {ε B : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hX : ∀ p q, ‖X p q - X₀ p q‖ ≤ ε) (hY : ∀ p q, ‖Y p q - Y₀ p q‖ ≤ ε)
    (hX₀ : ∀ p q, ‖X₀ p q‖ ≤ B) (hY₀ : ∀ p q, ‖Y₀ p q‖ ≤ B) (p q : n) :
    ‖(X * Y) p q - (X₀ * Y₀) p q‖ ≤ (Fintype.card n : ℝ) * (ε * (B + ε) + B * ε) := by
  have hterm : ∀ k, ‖X p k * Y k q - X₀ p k * Y₀ k q‖ ≤ ε * (B + ε) + B * ε := by
    intro k
    have hY' : ‖Y k q‖ ≤ B + ε :=
      calc ‖Y k q‖ = ‖Y₀ k q + (Y k q - Y₀ k q)‖ := by rw [add_sub_cancel]
        _ ≤ ‖Y₀ k q‖ + ‖Y k q - Y₀ k q‖ := norm_add_le _ _
        _ ≤ B + ε := add_le_add (hY₀ k q) (hY k q)
    have hsplit : X p k * Y k q - X₀ p k * Y₀ k q =
        (X p k - X₀ p k) * Y k q + X₀ p k * (Y k q - Y₀ k q) := by ring
    rw [hsplit]
    calc ‖(X p k - X₀ p k) * Y k q + X₀ p k * (Y k q - Y₀ k q)‖
        ≤ ‖(X p k - X₀ p k) * Y k q‖ + ‖X₀ p k * (Y k q - Y₀ k q)‖ := norm_add_le _ _
      _ ≤ ε * (B + ε) + B * ε := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul (hX p k) hY' (norm_nonneg _) hε)
            (mul_le_mul (hX₀ p k) (hY k q) (norm_nonneg _) hB)
  calc ‖(X * Y) p q - (X₀ * Y₀) p q‖
      = ‖∑ k, (X p k * Y k q - X₀ p k * Y₀ k q)‖ := by
        rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_sub_distrib]
    _ ≤ ∑ k, ‖X p k * Y k q - X₀ p k * Y₀ k q‖ := norm_sum_le _ _
    _ ≤ Finset.univ.card • (ε * (B + ε) + B * ε) :=
        Finset.sum_le_card_nsmul Finset.univ
          (fun k => ‖X p k * Y k q - X₀ p k * Y₀ k q‖) (ε * (B + ε) + B * ε)
          (fun k _ => hterm k)
    _ = (Fintype.card n : ℝ) * (ε * (B + ε) + B * ε) := by
        rw [Finset.card_univ, nsmul_eq_mul]

/-- The boundary comparison matrix of the half-chain Schmidt calculation
converges entrywise, geometrically in the half-chain length, to the diagonal
matrix with entries `λ_α λ_β / (tr Λ)²`: the trace normalization of
`Λ ⊗ Λ` for the positive diagonal fixed point `Λ = diag(λ_1, …, λ_D)`.
Together with `charpoly_halfChainReducedMatrix` this expresses the half-chain
interpretation of `Λ` at the level of the boundary comparison matrix: the
nonzero spectrum of the half-chain reduced density matrix is that of a matrix
converging geometrically to `Λ ⊗ Λ` up to the trace normalization.
Source: arXiv:quant-ph/0608197, Theorem 6 ("Interpretation of `Λ`",
`MPSarchive.tex` lines 987--993). -/
theorem exists_geometric_bound_halfChainComparison_sub_diagonal
    (A : MPSTensor d D) (lam : Fin D → ℂ)
    (htr : Matrix.trace (Matrix.diagonal lam) ≠ 0)
    (hTP : IsTracePreservingMap (transferMap A))
    (hΛ : transferMap A (Matrix.diagonal lam) = Matrix.diagonal lam)
    (hgap : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (transferMap A - fixedPointProj (Matrix.diagonal lam) htr)) < 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ L, 1 ≤ L → ∀ p q : Fin D × Fin D,
      ‖(((halfChainGram A L).submatrix Prod.swap Prod.swap)ᵀ * halfChainGram A L) p q -
        Matrix.diagonal (fun x : Fin D × Fin D =>
          lam x.1 * lam x.2 / Matrix.trace (Matrix.diagonal lam) ^ 2) p q‖ ≤ C * r ^ L := by
  classical
  obtain ⟨C, r, hC, hr0, hr1, hbound⟩ :=
    exists_geometric_bound_halfChainGram_sub_fixedPointProj A (Matrix.diagonal lam) htr hTP hΛ hgap
  set t : ℂ := Matrix.trace (Matrix.diagonal lam) with ht_def
  set B : ℝ := (∑ a, ‖lam a‖) / ‖t‖ with hB_def
  have hB : 0 ≤ B := div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (norm_nonneg _)
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr htr
  have hentryB : ∀ i : Fin D, ‖lam i / t‖ ≤ B := by
    intro i
    rw [norm_div, hB_def]
    have hsum : ‖lam i‖ ≤ ∑ a, ‖lam a‖ :=
      Finset.single_le_sum (f := fun a => ‖lam a‖) (fun a _ => norm_nonneg _)
        (Finset.mem_univ i)
    gcongr
  set Ginf : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    Matrix.diagonal (fun x : Fin D × Fin D => lam x.1 / t) with hGinf_def
  set Winf : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    Matrix.diagonal (fun x : Fin D × Fin D => lam x.2 / t) with hWinf_def
  have hGinfB : ∀ p q : Fin D × Fin D, ‖Ginf p q‖ ≤ B := by
    intro p q
    by_cases h : p = q
    · subst h
      rw [hGinf_def, Matrix.diagonal_apply_eq]
      exact hentryB p.1
    · rw [hGinf_def, Matrix.diagonal_apply_ne _ h]
      simpa using hB
  have hWinfB : ∀ p q : Fin D × Fin D, ‖Winf p q‖ ≤ B := by
    intro p q
    by_cases h : p = q
    · subst h
      rw [hWinf_def, Matrix.diagonal_apply_eq]
      exact hentryB p.2
    · rw [hWinf_def, Matrix.diagonal_apply_ne _ h]
      simpa using hB
  have hGL : ∀ L, 1 ≤ L → ∀ p q : Fin D × Fin D,
      ‖halfChainGram A L p q - Ginf p q‖ ≤ C * r ^ L := by
    intro L hL p q
    have h := hbound L hL p q
    rwa [fixedPointProj_single_entry_diagonal lam htr p q] at h
  have hWL : ∀ L, 1 ≤ L → ∀ p q : Fin D × Fin D,
      ‖((halfChainGram A L).submatrix Prod.swap Prod.swap)ᵀ p q - Winf p q‖ ≤ C * r ^ L := by
    intro L hL p q
    have h := hGL L hL q.swap p.swap
    have hentry : ((halfChainGram A L).submatrix Prod.swap Prod.swap)ᵀ p q =
        halfChainGram A L q.swap p.swap := rfl
    have hlim : Winf p q = Ginf q.swap p.swap := by
      by_cases hpq : p = q
      · subst hpq
        rw [hWinf_def, hGinf_def, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
          Prod.fst_swap]
      · rw [hWinf_def, hGinf_def, Matrix.diagonal_apply_ne _ hpq,
          Matrix.diagonal_apply_ne _ (fun hc => hpq (Prod.swap_injective hc).symm)]
    rw [hentry, hlim]
    exact h
  have hprod : Winf * Ginf =
      Matrix.diagonal (fun x : Fin D × Fin D => lam x.1 * lam x.2 / t ^ 2) := by
    rw [hWinf_def, hGinf_def, Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    ring
  have hDD : (0 : ℝ) ≤ (D * D : ℝ) := by positivity
  have hK : (0 : ℝ) < (D * D : ℝ) * (C * (B + C) + B * C) + 1 := by
    have h2 : (0 : ℝ) ≤ C * (B + C) + B * C := by
      nlinarith [mul_nonneg hB hC.le, mul_nonneg hC.le hC.le]
    nlinarith [mul_nonneg hDD h2]
  refine ⟨(D * D : ℝ) * (C * (B + C) + B * C) + 1, r, hK, hr0, hr1, ?_⟩
  intro L hL p q
  have hrL0 : 0 < r ^ L := pow_pos hr0 L
  have hrL1 : r ^ L ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hmul := entrywise_mul_bound
    (((halfChainGram A L).submatrix Prod.swap Prod.swap)ᵀ) Winf (halfChainGram A L) Ginf
    (mul_nonneg hC.le (pow_nonneg hr0.le L)) hB (hWL L hL) (hGL L hL) hWinfB hGinfB p q
  rw [hprod] at hmul
  have hcard : (Fintype.card (Fin D × Fin D) : ℝ) = (D * D : ℝ) := by
    simp [Fintype.card_prod]
  rw [hcard] at hmul
  refine hmul.trans ?_
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hDD (mul_nonneg hC.le hC.le)) hrL0.le)
    (sub_nonneg.mpr hrL1), hrL0.le]

end Convergence

end MPSTensor
