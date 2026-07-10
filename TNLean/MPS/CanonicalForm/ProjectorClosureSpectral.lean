/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.ProjectorClosureDecomposition
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.SharedInfra.Scaling
import TNLean.MPS.Irreducible.FormII
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.Channel.Irreducible.SpectralRadius

/-!
# Spectral steps of the canonical-form sufficient condition

This file completes the spectral part of the sufficient condition for canonical
form of Cirac, Pérez-García, Schuch, and Verstraete, arXiv:1606.00608,
lines 253--255: a tensor with no nontrivial `p`-periodic vectors whose
invariant projections are all two-sided invariant generates the same matrix
product vectors as a direct sum `⊕ₖ μₖ Aₖ` of normal tensors with nonzero
weights (eq:II_CF1, lines 237--242).

The two steps beyond the direct-sum decomposition of
`MPSTensor.exists_irreducible_blockDecomp_with_isometry_of_hasInvariantProjectorClosure`
are those of arXiv:1606.00608, lines 220--230:

* every nonzero irreducible corner is rescaled so that its transfer map has
  spectral radius one, the removed scale becoming the weight `μₖ`
  (lines 224--225); and
* the absence of nontrivial `p`-periodic vectors — peripheral transfer
  eigenvalues `exp(2πiq/p) ≠ 1` of the rescaled corners (line 226) — makes
  every rescaled corner a normal tensor.

Corners carrying the zero tensor cannot be rescaled to spectral radius one;
they are the zero blocks of eq:II_Aiplusk1 (line 219, `∑ₖ Dₖ ≤ D`).  They
contribute their bond dimension only to the length-zero coefficient, so the
main conclusion states matrix-product-vector equality at every positive length
together with the dimension bound `∑ₖ Dₖ ≤ D`.  When no corner carries the
zero tensor the equality holds at every length, including zero; this variant
is stated separately with the explicit no-zero-corner hypothesis.  The
length-zero convention is recorded in
`docs/paper-gaps/cpsv16_projector_closure_canonical_form.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **Absence of nontrivial `p`-periodic vectors** (arXiv:1606.00608,
lines 220--230).

The source attaches to each block `A_k` of the invariant-subspace
decomposition (eq:II_Aiplusk1, lines 214--219) the completely positive map
`E_k(X) = ∑ᵢ A_kⁱ X (A_kⁱ)†` and rescales it to spectral radius one
(lines 220--225); a `p`-periodic vector is an eigenvector of a rescaled `E_k`
with peripheral eigenvalue `exp(2πiq/p) ≠ 1` (line 226).  Under the projector
hypothesis of the proposition at lines 253--255 every projection in that
decomposition commutes with the tensor matrices, so the blocks of any run of
the source procedure are precisely the restrictions of `A` to minimal
invariant subspaces: isometries `V` with `A i * V = V * B i` whose corner
tensor `B` is irreducible.

Accordingly, `A` has no nontrivial `p`-periodic vectors if for every such
corner `B` and every positive eigenvalue `r` of `transferMap B` with
positive-definite eigenvector — by Wolf Theorem 6.3(4)
(`spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp`) this `r` is the
spectral radius of `transferMap B` — every eigenvalue of `transferMap B` of
modulus `r` equals `r`.  After rescaling by `r^{-1/2}` this says the corner
transfer map has no peripheral eigenvalue besides `1`, which is the source's
condition. -/
def HasNoPeriodicVectors (A : MPSTensor d D) : Prop :=
  ∀ ⦃n : ℕ⦄ (V : Matrix (Fin D) (Fin n) ℂ) (B : MPSTensor d n)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (r : ℝ),
    Vᴴ * V = 1 → (∀ i : Fin d, A i * V = V * B i) → IsIrreducibleTensor B →
    ρ.PosDef → 0 < r → transferMap (d := d) (D := n) B ρ = (r : ℂ) • ρ →
    ∀ μ : ℂ, Module.End.HasEigenvalue (transferMap (d := d) (D := n) B) μ →
      ‖μ‖ = r → μ = (r : ℂ)

/-- The transfer map of an intertwined corner: if `A i * V = V * B i` for
every letter, then conjugation by `V` intertwines the transfer maps,
`E_A(V X V†) = V E_B(X) V†`.

This is the normalization-free relation between the transfer map of a tensor
and the transfer maps of the corners of its invariant-subspace decomposition
(arXiv:1606.00608, eq:II_Aiplusk1, lines 214--219 and eq. Ek, lines 220--223). -/
theorem transferMap_conj_of_intertwine {n : ℕ} (A : MPSTensor d D) (B : MPSTensor d n)
    (V : Matrix (Fin D) (Fin n) ℂ) (hint : ∀ i : Fin d, A i * V = V * B i)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    transferMap (d := d) (D := D) A (V * X * Vᴴ)
      = V * transferMap (d := d) (D := n) B X * Vᴴ := by
  rw [transferMap_apply, transferMap_apply, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hstar : Vᴴ * (A i)ᴴ = (B i)ᴴ * Vᴴ := by
    calc Vᴴ * (A i)ᴴ
        = (A i * V)ᴴ := (Matrix.conjTranspose_mul _ _).symm
      _ = (V * B i)ᴴ := by rw [hint i]
      _ = (B i)ᴴ * Vᴴ := Matrix.conjTranspose_mul _ _
  calc A i * (V * X * Vᴴ) * (A i)ᴴ
      = (A i * V) * (X * (Vᴴ * (A i)ᴴ)) := by simp only [Matrix.mul_assoc]
    _ = (V * B i) * (X * ((B i)ᴴ * Vᴴ)) := by rw [hint i, hstar]
    _ = V * (B i * X * (B i)ᴴ) * Vᴴ := by simp only [Matrix.mul_assoc]

/-- Eigenvalues of a corner transfer map are eigenvalues of the ambient
transfer map: if `V` is an isometry with `A i * V = V * B i` for every letter,
then every eigenvalue of `E_B` is an eigenvalue of `E_A`.

In particular the `p`-periodic vectors of arXiv:1606.00608, line 226 — the
peripheral eigenvectors of the block transfer maps — give eigenvectors of the
transfer map of the undecomposed tensor. -/
theorem hasEigenvalue_transferMap_of_intertwine {n : ℕ} (A : MPSTensor d D)
    (B : MPSTensor d n) (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (hint : ∀ i : Fin d, A i * V = V * B i) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (transferMap (d := d) (D := n) B) μ) :
    Module.End.HasEigenvalue (transferMap (d := d) (D := D) A) μ := by
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have hX_eq : transferMap (d := d) (D := n) B X = μ • X :=
    Module.End.mem_eigenspace_iff.mp (Module.End.hasEigenvector_iff.mp hX).1
  have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX).2
  refine hasEigenvalue_of_eigenvector_eq _ μ (V * X * Vᴴ) ?_ ?_
  · rw [transferMap_conj_of_intertwine A B V hint X, hX_eq,
      Matrix.mul_smul, Matrix.smul_mul]
  · intro h0
    apply hX_ne
    have h1 : Vᴴ * (V * X * Vᴴ) * V = X := by
      calc Vᴴ * (V * X * Vᴴ) * V
          = (Vᴴ * V) * X * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hV, Matrix.one_mul, Matrix.mul_one]
    rw [← h1, h0, Matrix.mul_zero, Matrix.zero_mul]

/-- Perron--Frobenius eigenvalue of a nonzero irreducible tensor: the transfer
map of a nonzero irreducible tensor has a positive eigenvalue with a
positive-definite eigenvector (Wolf Theorem 6.3(2), specialized to transfer
maps).  This is the eigenvalue used for the spectral-radius normalization of
arXiv:1606.00608, lines 224--225. -/
theorem exists_posDef_transferMap_eigenvector_of_irreducible {n : ℕ} [NeZero n]
    (B : MPSTensor d n) (hIrr : IsIrreducibleTensor B) (hB : ∃ i, B i ≠ 0) :
    ∃ (ρ : Matrix (Fin n) (Fin n) ℂ) (r : ℝ),
      ρ.PosDef ∧ 0 < r ∧ transferMap (d := d) (D := n) B ρ = (r : ℂ) • ρ := by
  have hne : transferMap (d := d) (D := n) B ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hB
    have h1 : transferMap (d := d) (D := n) B 1 = 0 := by rw [h0]; simp
    rw [transferMap_apply] at h1
    simp only [Matrix.mul_one] at h1
    exact hi (Matrix.eq_zero_of_sum_mul_conjTranspose_eq_zero (fun j => B j) h1 i)
  obtain ⟨ρ, r, hρ, hr, hEig⟩ :=
    exists_posDef_eigenvector_of_irreducible_cp (transferMap (d := d) (D := n) B)
      (transferMap_isCPMap B)
      (isIrreducibleCP_transferMap_of_isIrreducibleTensor B hIrr) hne
  exact ⟨ρ, r, hρ, hr, hEig⟩

/-- **Spectral normalization of an irreducible block** (arXiv:1606.00608,
lines 224--226): rescaling a nonzero irreducible tensor by the inverse square
root of the Perron--Frobenius eigenvalue of its transfer map yields a normal
tensor, provided the transfer map has no eigenvalue of modulus equal to, but
different from, that eigenvalue.

Rescaling the tensor by `r^{-1/2}` rescales the transfer map by `r⁻¹`, so the
positive-definite eigenvector becomes a fixed point and the peripheral
eigenvalues become the eigenvalues of modulus one; the uniqueness hypothesis
forces the peripheral eigenvalue set to be `{1}`, which together with
irreducibility is the normal-tensor condition of arXiv:1606.00608,
lines 233--235. -/
theorem isNormalTensor_invSqrt_smul_of_unique_peripheral {n : ℕ} [NeZero n]
    (B : MPSTensor d n) (hIrr : IsIrreducibleTensor B)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (hρ : ρ.PosDef) (hr : 0 < r)
    (hEig : transferMap (d := d) (D := n) B ρ = (r : ℂ) • ρ)
    (huniq : ∀ μ : ℂ, Module.End.HasEigenvalue (transferMap (d := d) (D := n) B) μ →
      ‖μ‖ = r → μ = (r : ℂ)) :
    IsNormalTensor (fun i => (((Real.sqrt r : ℝ) : ℂ))⁻¹ • B i) := by
  have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsqrt_ne : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  have hc_ne : (((Real.sqrt r : ℝ) : ℂ))⁻¹ ≠ 0 := inv_ne_zero hsqrt_ne
  have hcc : (((Real.sqrt r : ℝ) : ℂ))⁻¹ *
      starRingEnd ℂ (((Real.sqrt r : ℝ) : ℂ))⁻¹ = (r : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hr.le]
  have hmap : transferMap (d := d) (D := n) (fun i => (((Real.sqrt r : ℝ) : ℂ))⁻¹ • B i)
      = (r : ℂ)⁻¹ • transferMap (d := d) (D := n) B := by
    apply LinearMap.ext
    intro X
    rw [transferMap_smul, LinearMap.smul_apply, hcc]
  have hρ_ne : ρ ≠ 0 := (Matrix.PosDef.isUnit hρ).ne_zero
  have hfix : transferMap (d := d) (D := n)
      (fun i => (((Real.sqrt r : ℝ) : ℂ))⁻¹ • B i) ρ = ρ := by
    rw [hmap, LinearMap.smul_apply, hEig, smul_smul, inv_mul_cancel₀ hr_ne, one_smul]
  have hIrrScaled : IsIrreducibleTensor
      (fun i => (((Real.sqrt r : ℝ) : ℂ))⁻¹ • B i) :=
    isIrreducibleTensor_smul hc_ne B hIrr
  refine ⟨hIrrScaled, ?_, ?_⟩
  · simpa using
      (spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp
        (transferMap (d := d) (D := n)
          (fun i => (((Real.sqrt r : ℝ) : ℂ))⁻¹ • B i))
        (transferMap_isCPMap _) (isIrreducibleCP_transferMap_of_isIrreducibleTensor _ hIrrScaled)
        ρ 1 hρ (by norm_num) (by simpa using hfix))
  · refine isPrimitive_of_unique_norm_one _ ρ hfix hρ_ne ?_
    intro μ hμ hμnorm
    obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
    have hX_eq : transferMap (d := d) (D := n)
        (fun i => (((Real.sqrt r : ℝ) : ℂ))⁻¹ • B i) X = μ • X :=
      Module.End.mem_eigenspace_iff.mp (Module.End.hasEigenvector_iff.mp hX).1
    have hX_ne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX).2
    have hBX : transferMap (d := d) (D := n) B X = ((r : ℂ) * μ) • X := by
      have h1 : (r : ℂ)⁻¹ • transferMap (d := d) (D := n) B X = μ • X := by
        rw [← LinearMap.smul_apply, ← hmap]
        exact hX_eq
      calc transferMap (d := d) (D := n) B X
          = (r : ℂ) • ((r : ℂ)⁻¹ • transferMap (d := d) (D := n) B X) := by
            rw [smul_smul, mul_inv_cancel₀ hr_ne, one_smul]
        _ = (r : ℂ) • (μ • X) := by rw [h1]
        _ = ((r : ℂ) * μ) • X := by rw [smul_smul]
    have hBμ : Module.End.HasEigenvalue
        (transferMap (d := d) (D := n) B) ((r : ℂ) * μ) :=
      hasEigenvalue_of_eigenvector_eq _ _ X hBX hX_ne
    have hnorm : ‖(r : ℂ) * μ‖ = r := by
      rw [norm_mul, hμnorm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_left_cancel₀ hr_ne ((huniq _ hBμ hnorm).trans (mul_one (r : ℂ)).symm)

/-- At positive length, a tensor whose letter matrices all vanish has vanishing
matrix product vector coefficients.  These are the zero blocks of
arXiv:1606.00608, eq:II_Aiplusk1, line 219. -/
private lemma mpv_eq_zero_of_letter_zero {n : ℕ} (B : MPSTensor d n)
    (hB : ∀ i, B i = 0) {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin d) :
    mpv B σ = 0 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simp only [mpv, coeff, List.ofFn_succ, evalWord_cons, hB, Matrix.zero_mul,
    Matrix.trace_zero]

/-- **Sufficient condition for canonical form** (arXiv:1606.00608,
lines 253--255).

If `A` satisfies the invariant-projector closure condition and has no
nontrivial `p`-periodic vectors, then there are nonzero weights `μ k` and
normal tensors `blocks k` of positive bond dimensions summing to at most `D`
such that `A` and the direct sum `⊕ₖ μₖ blocksₖ` have equal matrix product
vector coefficients at every positive length.  This is the canonical form
`A^i = ⊕ₖ μₖ A_kⁱ` of eq:II_CF1 (lines 237--242) at the level of the generated
matrix product vectors, with the source convention `∑ₖ Dₖ ≤ D` that allows
zero blocks (eq:II_Aiplusk1, line 219).

Corners of `A` carrying the zero tensor cannot be rescaled to spectral radius
one and are omitted from the direct sum; each contributes its bond dimension
only to the length-zero coefficient.  The variant
`MPSTensor.exists_normalTensor_blockDecomp_sameMPV₂_of_hasInvariantProjectorClosure`
states equality at every length under the explicit additional hypothesis that
no irreducible corner of `A` carries the zero tensor.  The length-zero
convention is recorded in
`docs/paper-gaps/cpsv16_projector_closure_canonical_form.tex`. -/
theorem exists_normalTensor_blockDecomp_sameMPV₂Pos_of_hasInvariantProjectorClosure
    (A : MPSTensor d D) (hClosure : HasInvariantProjectorClosure A)
    (hPer : HasNoPeriodicVectors A) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      SameMPV₂Pos A (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      (∀ k, IsNormalTensor (blocks k)) ∧
      (∀ k, μ k ≠ 0) ∧
      (∀ k, 0 < dim k) ∧
      (∑ k, dim k) ≤ D := by
  classical
  obtain ⟨r₀, dim₀, blocks₀, V, hpos, hiso, hsum, -, hint, -, -, hirr, hSame⟩ :=
    exists_irreducible_blockDecomp_with_isometry_of_hasInvariantProjectorClosure A hClosure
  -- Perron--Frobenius eigenvalue and eigenvector of every nonzero corner.
  have hPF : ∀ k : Fin r₀, (∃ i, blocks₀ k i ≠ 0) →
      ∃ (ρ : Matrix (Fin (dim₀ k)) (Fin (dim₀ k)) ℂ) (t : ℝ),
        ρ.PosDef ∧ 0 < t ∧
        transferMap (d := d) (D := dim₀ k) (blocks₀ k) ρ = (t : ℂ) • ρ := by
    intro k hk
    haveI : NeZero (dim₀ k) := ⟨(hpos k).ne'⟩
    exact exists_posDef_transferMap_eigenvector_of_irreducible (blocks₀ k) (hirr k) hk
  choose ρf tf hρf htf hEigf using hPF
  -- The kept indices: corners with a nonzero letter matrix.
  let κ := {k : Fin r₀ // ∃ i, blocks₀ k i ≠ 0}
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hsqrt_ne : ∀ x : κ, ((Real.sqrt (tf x.1 x.2) : ℝ) : ℂ) ≠ 0 := fun x =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (htf x.1 x.2)).ne'
  refine ⟨Fintype.card κ, fun j => dim₀ (e j).1,
    fun j => ((Real.sqrt (tf (e j).1 (e j).2) : ℝ) : ℂ),
    fun j => fun i => (((Real.sqrt (tf (e j).1 (e j).2) : ℝ) : ℂ))⁻¹ • blocks₀ (e j).1 i,
    ?_, ?_, fun j => hsqrt_ne (e j), fun j => hpos (e j).1, ?_⟩
  · -- Positive-length matrix product vector equality.
    intro N hN σ
    have hA : mpv A σ = ∑ k : Fin r₀, mpv (blocks₀ k) σ :=
      mpv_eq_sum_of_sameMPV₂_toTensorFromBlocks_one A blocks₀ hSame σ
    have hkeep : ∑ k ∈ Finset.univ.filter (fun k => ∃ i, blocks₀ k i ≠ 0),
        mpv (blocks₀ k) σ = ∑ k : Fin r₀, mpv (blocks₀ k) σ := by
      refine Finset.sum_filter_of_ne ?_
      intro k _ hne
      by_contra hnot
      push Not at hnot
      exact hne (mpv_eq_zero_of_letter_zero (blocks₀ k) hnot hN σ)
    have hsubtype : ∑ k ∈ Finset.univ.filter (fun k => ∃ i, blocks₀ k i ≠ 0),
        mpv (blocks₀ k) σ = ∑ x : κ, mpv (blocks₀ x.1) σ :=
      Finset.sum_subtype _ (by simp) _
    have hequiv : ∑ x : κ, mpv (blocks₀ x.1) σ
        = ∑ j : Fin (Fintype.card κ), mpv (blocks₀ (e j).1) σ :=
      (Equiv.sum_comp e (fun x : κ => mpv (blocks₀ x.1) σ)).symm
    rw [hA, ← hkeep, hsubtype, hequiv, mpv_toTensorFromBlocks_eq_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mpv_smul, smul_eq_mul, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (hsqrt_ne (e j)), one_pow, one_mul]
  · -- Every kept, rescaled corner is a normal tensor.
    intro j
    haveI : NeZero (dim₀ (e j).1) := ⟨(hpos (e j).1).ne'⟩
    refine isNormalTensor_invSqrt_smul_of_unique_peripheral (blocks₀ (e j).1)
      (hirr (e j).1) (ρf (e j).1 (e j).2) (tf (e j).1 (e j).2) (hρf (e j).1 (e j).2)
      (htf (e j).1 (e j).2) (hEigf (e j).1 (e j).2) ?_
    intro μ hμ hnorm
    exact hPer (V (e j).1) (blocks₀ (e j).1) (ρf (e j).1 (e j).2) (tf (e j).1 (e j).2)
      (hiso (e j).1) (hint (e j).1) (hirr (e j).1) (hρf (e j).1 (e j).2)
      (htf (e j).1 (e j).2) (hEigf (e j).1 (e j).2) μ hμ hnorm
  · -- The block dimensions sum to at most `D`.
    have hDim : ∑ k : Fin r₀, dim₀ k = D := by
      have hc : (∑ k : Fin r₀, (dim₀ k : ℂ)) = (D : ℂ) := by
        calc ∑ k : Fin r₀, (dim₀ k : ℂ)
            = ∑ k : Fin r₀, Matrix.trace ((V k)ᴴ * V k) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hiso k, Matrix.trace_one, Fintype.card_fin]
          _ = ∑ k : Fin r₀, Matrix.trace (V k * (V k)ᴴ) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              exact Matrix.trace_mul_comm _ _
          _ = Matrix.trace (∑ k : Fin r₀, V k * (V k)ᴴ) := (Matrix.trace_sum _ _).symm
          _ = (D : ℂ) := by rw [hsum, Matrix.trace_one, Fintype.card_fin]
      exact_mod_cast hc
    calc ∑ j : Fin (Fintype.card κ), dim₀ (e j).1
        = ∑ x : κ, dim₀ x.1 := Equiv.sum_comp e (fun x : κ => dim₀ x.1)
      _ = ∑ k ∈ Finset.univ.filter (fun k => ∃ i, blocks₀ k i ≠ 0), dim₀ k :=
          (Finset.sum_subtype _ (by simp) _).symm
      _ ≤ ∑ k : Fin r₀, dim₀ k :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = D := hDim

/-- All-lengths variant of the sufficient condition for canonical form
(arXiv:1606.00608, lines 253--255).

**Scope restriction (no zero corners):** in addition to the source hypotheses,
every irreducible corner of `A` of positive dimension is assumed to carry a
nonzero letter matrix.  Without this hypothesis a corner may be the zero
tensor, which cannot be rescaled to spectral radius one; the source drops
such zero blocks (eq:II_Aiplusk1, line 219, `∑ₖ Dₖ ≤ D`), which changes the
length-zero coefficient.  The premise `0 < n` excludes only the
zero-dimensional corner, whose letter matrices all vanish for lack of
entries; without it no tensor could satisfy the hypothesis.  The
unrestricted positive-length statement is
`MPSTensor.exists_normalTensor_blockDecomp_sameMPV₂Pos_of_hasInvariantProjectorClosure`.
The restriction is recorded in
`docs/paper-gaps/cpsv16_projector_closure_canonical_form.tex`. -/
theorem exists_normalTensor_blockDecomp_sameMPV₂_of_hasInvariantProjectorClosure
    (A : MPSTensor d D) (hClosure : HasInvariantProjectorClosure A)
    (hPer : HasNoPeriodicVectors A)
    (hcorner : ∀ ⦃n : ℕ⦄ (V : Matrix (Fin D) (Fin n) ℂ) (B : MPSTensor d n),
      0 < n → Vᴴ * V = 1 → (∀ i : Fin d, A i * V = V * B i) → IsIrreducibleTensor B →
      ∃ i, B i ≠ 0) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor d (dim k)),
      SameMPV₂ A (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      (∀ k, IsNormalTensor (blocks k)) ∧
      (∀ k, μ k ≠ 0) := by
  classical
  obtain ⟨r₀, dim₀, blocks₀, V, hpos, hiso, hsum, -, hint, -, -, hirr, hSame⟩ :=
    exists_irreducible_blockDecomp_with_isometry_of_hasInvariantProjectorClosure A hClosure
  have hPF : ∀ k : Fin r₀,
      ∃ (ρ : Matrix (Fin (dim₀ k)) (Fin (dim₀ k)) ℂ) (t : ℝ),
        ρ.PosDef ∧ 0 < t ∧
        transferMap (d := d) (D := dim₀ k) (blocks₀ k) ρ = (t : ℂ) • ρ := by
    intro k
    haveI : NeZero (dim₀ k) := ⟨(hpos k).ne'⟩
    exact exists_posDef_transferMap_eigenvector_of_irreducible (blocks₀ k) (hirr k)
      (hcorner (V k) (blocks₀ k) (hpos k) (hiso k) (hint k) (hirr k))
  choose ρf tf hρf htf hEigf using hPF
  have hsqrt_ne : ∀ k : Fin r₀, ((Real.sqrt (tf k) : ℝ) : ℂ) ≠ 0 := fun k =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (htf k)).ne'
  refine ⟨r₀, dim₀, fun k => ((Real.sqrt (tf k) : ℝ) : ℂ),
    fun k => fun i => (((Real.sqrt (tf k) : ℝ) : ℂ))⁻¹ • blocks₀ k i,
    ?_, ?_, fun k => hsqrt_ne k⟩
  · -- Matrix product vector equality at every length.
    intro N σ
    rw [hSame N σ, mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mpv_smul, one_pow, one_smul, smul_eq_mul, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (hsqrt_ne k), one_pow, one_mul]
  · -- Every rescaled corner is a normal tensor.
    intro k
    haveI : NeZero (dim₀ k) := ⟨(hpos k).ne'⟩
    refine isNormalTensor_invSqrt_smul_of_unique_peripheral (blocks₀ k) (hirr k)
      (ρf k) (tf k) (hρf k) (htf k) (hEigf k) ?_
    intro μ hμ hnorm
    exact hPer (V k) (blocks₀ k) (ρf k) (tf k) (hiso k) (hint k) (hirr k)
      (hρf k) (htf k) (hEigf k) μ hμ hnorm

end MPSTensor
