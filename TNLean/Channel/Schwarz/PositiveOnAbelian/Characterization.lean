/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Schwarz.PositiveOnAbelian.Basic

/-!
# Positivity on commuting block families

This file proves the main positive-on-abelian amplification theorem used later
in the Schwarz development: if a linear map on $M_D(\mathbb{C})$ is positive,
then every finite block family with pairwise commuting images has nonnegative
block quadratic form.

## Main statements

* `quadraticForm_nonneg_of_isPositiveMap_of_commuting_images` — Wolf
  Proposition 1.6 in block-quadratic-form form.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.6]
  [Wolf2012QChannels]

## Tags

positive map, commuting family, block positivity, Schwarz inequality
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators TNMatrixCFC
open Matrix Finset Complex Module.End

namespace PositiveOnAbelian

variable {D : ℕ}

/-- Multiplicativity of `Matrix.toEuclideanLin`: lifting matrix multiplication to the
Euclidean linear map level. -/
private lemma toEuclideanLin_mul (A B : Matrix (Fin D) (Fin D) ℂ) :
    (Matrix.toEuclideanLin A : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D)) *
      Matrix.toEuclideanLin B = Matrix.toEuclideanLin (A * B) := by
  simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
    (Matrix.toLin_mul (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin D) ℂ).toBasis A B).symm

/-- Wolf Proposition 1.6 in the block-quadratic-form form used later in the
construction: positivity upgrades to positivity of every finite amplification once
all block images commute pairwise.

**Proof outline**: simultaneously diagonalize the commuting Hermitian images of
the block entries, reduce to the scalar case, and then apply
`diagonal_family_schwarz_le`. -/
-- Block Hermiticity: a BlockPositive block matrix satisfies (a j i)ᴴ = a i j.
-- Proof: 0 ≤ Q(ψ) means Q(ψ) nonneg real, so Q = conj Q. Conjugating and
-- relabeling yields the Hermiticity of the big nD×nD block matrix.
private lemma blockHermitian_of_blockPositive {n D : ℕ}
    {a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)}
    (ha : BlockPositive a) :
    ∀ i j, (a j i)ᴴ = a i j := by
  classical
  let A : Matrix (Fin n × Fin D) (Fin n × Fin D) ℂ :=
    fun p q => a p.1 q.1 p.2 q.2
  have hAsym : A.toEuclideanLin.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_inner_map_self_real]
    intro x
    let ψ : Fin n → Fin D → ℂ := fun i r => x.ofLp (i, r)
    set q : ℂ := star x.ofLp ⬝ᵥ A.mulVec x.ofLp
    have hq' : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        star (ψ i) ⬝ᵥ (a i j).mulVec (ψ j) := ha ψ
    have hq'' : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin D,
        (starRingEnd ℂ) (x.ofLp (i, r)) * ∑ s : Fin D, a i j r s * x.ofLp (j, s) := by
      simpa only [dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec] using hq'
    have hinnerSum (i : Fin n) (r : Fin D) :
        (∑ x_2 : Fin n × Fin D, a i x_2.1 r x_2.2 * x.ofLp x_2) =
          ∑ j : Fin n, ∑ s : Fin D, a i j r s * x.ofLp (j, s) := by
      rw [Fintype.sum_prod_type]
    have hq : 0 ≤ q := by
      dsimp [q, A]
      simp only [dotProduct, Matrix.mulVec]
      rw [Fintype.sum_prod_type]
      convert hq'' using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [hinnerSum i r, Finset.mul_sum]
      rfl
    have hqreal : star q = q := by
      have hqim : q.im = 0 := (Complex.nonneg_iff.mp hq).2.symm
      apply Complex.ext
      · simp only [RCLike.star_def, conj_re]
      · simp only [RCLike.star_def, conj_im, hqim, neg_zero]
    have hinner : inner ℂ (A.toEuclideanLin x) x = star q := by
      calc
        inner ℂ (A.toEuclideanLin x) x = x.ofLp ⬝ᵥ star (A.toEuclideanLin x).ofLp := by
          simp only [EuclideanSpace.inner_eq_star_dotProduct]
        _ = x.ofLp ⬝ᵥ star (A.mulVec x.ofLp) := by
          simp only [Matrix.ofLp_toLpLin (p := 2) (q := 2), Matrix.toLin'_apply]
        _ = star (A.mulVec x.ofLp ⬝ᵥ star x.ofLp) := by rw [Matrix.dotProduct_star]
        _ = star (star x.ofLp ⬝ᵥ A.mulVec x.ofLp) := by rw [dotProduct_comm]
        _ = star q := by rfl
    calc
      star (inner ℂ (A.toEuclideanLin x) x) = star (star q) := by rw [hinner]
      _ = q := by simp only [RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply]
      _ = star q := hqreal.symm
      _ = inner ℂ (A.toEuclideanLin x) x := by rw [hinner]
  have hAherm : A.IsHermitian := (Matrix.isHermitian_iff_isSymmetric (A := A)).2 hAsym
  intro i j
  ext r s
  simpa only [conjTranspose_apply, RCLike.star_def] using congrArg
    (fun N : Matrix (Fin n × Fin D) (Fin n × Fin D) ℂ => N (i, r) (j, s)) hAherm.eq

-- Weighted sum ∑ conj(w i) w j • a i j is PSD for block-positive a.
-- Proof: BlockPositive applied to ψ i = w i • v gives PSD of weighted sum.
private lemma weighted_block_sum_posSemidef {n D : ℕ}
    {a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)}
    (ha : BlockPositive a) (w : Fin n → ℂ) :
    (∑ i, ∑ j, (starRingEnd ℂ (w i) * w j) • a i j).PosSemidef := by
  classical
  let B : Matrix (Fin D) (Fin D) ℂ := ∑ i, ∑ j, (starRingEnd ℂ (w i) * w j) • a i j
  have hBH : ∀ i j, (a j i)ᴴ = a i j := blockHermitian_of_blockPositive ha
  have hBherm : B.IsHermitian := by
    change Bᴴ = B
    calc
      Bᴴ = ∑ i, ∑ j, star (starRingEnd ℂ (w i) * w j) • (a i j)ᴴ := by
        simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_mul',
          RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply, B]
      _ = ∑ i, ∑ j, star (starRingEnd ℂ (w i) * w j) • a j i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simpa only [star_mul', RCLike.star_def, RingHomCompTriple.comp_apply,
          RingHom.id_apply] using congrArg
          (fun N : Matrix (Fin D) (Fin D) ℂ => star (starRingEnd ℂ (w i) * w j) • N) (hBH j i)
      _ = ∑ i, ∑ j, (starRingEnd ℂ (w i) * w j) • a i j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        simp only [mul_comm, star_mul', RCLike.star_def, RingHomCompTriple.comp_apply,
          RingHom.id_apply]
      _ = B := by rfl
  have hBnonneg : ∀ v : Fin D → ℂ, 0 ≤ star v ⬝ᵥ B.mulVec v := by
    intro v
    let ψ : Fin n → Fin D → ℂ := fun i => w i • v
    have hψ : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (a i j).mulVec (ψ j) := ha ψ
    have hψ' : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ (w i) * w j) * (star v ⬝ᵥ (a i j).mulVec v) := by
      simpa only [ψ, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc, star_smul, RCLike.star_def] using hψ
    convert hψ' using 1
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, mul_assoc, B]
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hBherm hBnonneg

-- Commuting images whose scalar matrices are all PSD give a nonneg block form.
-- This is the simultaneous-diagonalisation core: for pairwise-commuting images,
-- the block quadratic form is nonneg whenever every scalar matrix is PSD.
-- Proved via the joint-eigenspace decomposition
-- (LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute).
set_option maxHeartbeats 1600000 in
-- Elaborating the joint-eigenspace decomposition and the finite-index reduction
-- requires more heartbeats than the default.
private lemma blockForm_nonneg_of_scalarPSD_of_commuting {n D : ℕ}
    (M : Fin n → Fin n → Matrix (Fin D) (Fin D) ℂ)
    (hMadj : ∀ i j, (M j i)ᴴ = M i j)
    (hcomm : ∀ i j k l, Commute (M i j) (M k l))
    (hscalar : ∀ (w : Fin n → ℂ) (e : Fin D → ℂ),
      0 ≤ ∑ i, ∑ j, starRingEnd ℂ (w i) * w j *
        (star e ⬝ᵥ (M i j).mulVec e))
    (ψ : Fin n → Fin D → ℂ) :
    0 ≤ ∑ i, ∑ j, star (ψ i) ⬝ᵥ (M i j).mulVec (ψ j) := by
  classical
  let H : Fin n → Fin n → Matrix (Fin D) (Fin D) ℂ :=
    fun i j => (1 / 2 : ℂ) • (M i j + (M i j)ᴴ)
  let K : Fin n → Fin n → Matrix (Fin D) (Fin D) ℂ :=
    fun i j => (Complex.I / 2 : ℂ) • ((M i j)ᴴ - M i j)
  let ι := ((Fin n × Fin n) ⊕ (Fin n × Fin n))
  let T : ι → EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D)
    | Sum.inl ij => Matrix.toEuclideanLin (H ij.1 ij.2)
    | Sum.inr ij => Matrix.toEuclideanLin (K ij.1 ij.2)
  have hH : ∀ i j, (H i j).IsHermitian := by
    intro i j
    ext r s
    simp only [one_div, smul_add, conjTranspose_apply, add_apply, smul_apply, smul_eq_mul,
      RCLike.star_def, star_add, star_mul', star_inv₀, star_ofNat,
      RingHomCompTriple.comp_apply, RingHom.id_apply, add_comm, H]
  have hK : ∀ i j, (K i j).IsHermitian := by
    intro i j
    ext r s
    simp only [sub_eq_add_neg, smul_add, smul_neg, conjTranspose_apply, add_apply, smul_apply,
      RCLike.star_def, smul_eq_mul, neg_apply, star_add, star_mul', star_div₀, conj_I,
      star_ofNat, RingHomCompTriple.comp_apply, RingHom.id_apply, star_neg, K]
    ring
  have hTsymm : ∀ idx, (T idx).IsSymmetric := by
    intro idx
    cases idx with
    | inl ij =>
        rcases ij with ⟨i, j⟩
        simpa only [T] using (Matrix.isHermitian_iff_isSymmetric (A := H i j)).mp (hH i j)
    | inr ij =>
        rcases ij with ⟨i, j⟩
        simpa only [T] using (Matrix.isHermitian_iff_isSymmetric (A := K i j)).mp (hK i j)
  have hEuclMul := toEuclideanLin_mul (D := D)
  have htoEuclComm {A B : Matrix (Fin D) (Fin D) ℂ} (hAB : Commute A B) :
      Commute (Matrix.toEuclideanLin A : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D))
        (Matrix.toEuclideanLin B) :=
    hEuclMul A B |>.trans (congrArg Matrix.toEuclideanLin hAB.eq) |>.trans (hEuclMul B A).symm
  have hcommAdjLeft : ∀ i j k l, Commute (M i j)ᴴ (M k l) := by
    intro i j k l
    simpa only [hMadj j i] using hcomm j i k l
  have hcommAdjRight : ∀ i j k l, Commute (M i j) (M k l)ᴴ := by
    intro i j k l
    simpa only [hMadj l k] using hcomm i j l k
  have hcommAdjAdj : ∀ i j k l, Commute (M i j)ᴴ (M k l)ᴴ := by
    intro i j k l
    simpa only [hMadj j i, hMadj l k] using hcomm j i l k
  have hHH : ∀ i j k l, Commute (H i j) (H k l) := by
    intro i j k l
    have h1 : Commute (M i j + (M i j)ᴴ) (M k l) :=
      (hcomm i j k l).add_left (hcommAdjLeft i j k l)
    have h2 : Commute (M i j + (M i j)ᴴ) (M k l)ᴴ :=
      (hcommAdjRight i j k l).add_left (hcommAdjAdj i j k l)
    have hsum : Commute (M i j + (M i j)ᴴ) (M k l + (M k l)ᴴ) := h1.add_right h2
    simpa only [H, one_div, smul_add, Matrix.smul_mul, Matrix.mul_smul, mul_comm,
      mul_left_comm, mul_assoc] using
      (hsum.smul_left (1 / 2 : ℂ)).smul_right (1 / 2 : ℂ)
  have hHK : ∀ i j k l, Commute (H i j) (K k l) := by
    intro i j k l
    have h1 : Commute (M i j + (M i j)ᴴ) (M k l) :=
      (hcomm i j k l).add_left (hcommAdjLeft i j k l)
    have h2 : Commute (M i j + (M i j)ᴴ) (M k l)ᴴ :=
      (hcommAdjRight i j k l).add_left (hcommAdjAdj i j k l)
    have hsub : Commute (M i j + (M i j)ᴴ) ((M k l)ᴴ - M k l) := h2.sub_right h1
    simpa only [H, K, one_div, smul_add, Matrix.smul_mul, Matrix.mul_smul, mul_comm,
      mul_left_comm, mul_assoc, ne_eq, div_eq_zero_iff, Complex.I_ne_zero,
      OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Commute.smul_right_iff₀] using
      (hsub.smul_left (1 / 2 : ℂ)).smul_right (Complex.I / 2 : ℂ)
  have hKK : ∀ i j k l, Commute (K i j) (K k l) := by
    intro i j k l
    have h1 : Commute ((M i j)ᴴ - M i j) (M k l) :=
      (hcommAdjLeft i j k l).sub_left (hcomm i j k l)
    have h2 : Commute ((M i j)ᴴ - M i j) (M k l)ᴴ :=
      (hcommAdjAdj i j k l).sub_left (hcommAdjRight i j k l)
    have hsub : Commute ((M i j)ᴴ - M i j) ((M k l)ᴴ - M k l) := h2.sub_right h1
    simpa only [K, Matrix.smul_mul, Matrix.mul_smul, mul_comm, mul_left_comm, mul_assoc, ne_eq,
      div_eq_zero_iff, Complex.I_ne_zero, OfNat.ofNat_ne_zero, or_self, not_false_eq_true,
      Commute.smul_right_iff₀, Commute.smul_left_iff₀] using
      (hsub.smul_left (Complex.I / 2 : ℂ)).smul_right (Complex.I / 2 : ℂ)
  have hTcomm : Pairwise (fun x y => Commute (T x) (T y)) := by
    intro x y _
    cases x with
    | inl x =>
        rcases x with ⟨i, j⟩
        cases y with
        | inl y =>
            rcases y with ⟨k, l⟩
            simpa only [T] using htoEuclComm (hHH i j k l)
        | inr y =>
            rcases y with ⟨k, l⟩
            simpa only [T] using htoEuclComm (hHK i j k l)
    | inr x =>
        rcases x with ⟨i, j⟩
        cases y with
        | inl y =>
            rcases y with ⟨k, l⟩
            simpa only [T] using (htoEuclComm (hHK k l i j)).symm
        | inr y =>
            rcases y with ⟨k, l⟩
            simpa only [T] using htoEuclComm (hKK i j k l)
  let V : (ι → ℂ) → Submodule ℂ (EuclideanSpace ℂ (Fin D)) :=
    fun γ => ⨅ idx, Module.End.eigenspace (T idx) (γ idx)
  have hFullOrtho :
      OrthogonalFamily ℂ (fun γ : ι → ℂ => V γ) fun γ => (V γ).subtypeₗᵢ := by
    simpa only using LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces (T := T) hTsymm
  have hFullTop : (⨆ γ : ι → ℂ, V γ) = ⊤ := by
    simpa only using LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (T := T) hTsymm hTcomm
  let σ : Type := ∀ idx : ι, Eigenvalues (T idx)
  let W : σ → Submodule ℂ (EuclideanSpace ℂ (Fin D)) :=
    fun α => ⨅ idx, Module.End.eigenspace (T idx) ((α idx : Eigenvalues (T idx)) : ℂ)
  have hWOrtho :
      OrthogonalFamily ℂ (fun α : σ => W α) fun α => (W α).subtypeₗᵢ := by
    let f : σ → ι → ℂ := fun α idx => ((α idx : Eigenvalues (T idx)) : ℂ)
    have hf : Function.Injective f := by
      intro α β h
      funext idx
      apply Subtype.ext
      exact congrFun h idx
    simpa only using hFullOrtho.comp (f := f) hf
  have hWleV : (⨆ α : σ, W α) ≤ ⨆ γ : ι → ℂ, V γ := by
    refine iSup_le ?_
    intro α
    exact le_iSup_of_le (fun idx => ((α idx : Eigenvalues (T idx)) : ℂ)) <| by
      simp only [le_refl, W, V]
  have hVleW : (⨆ γ : ι → ℂ, V γ) ≤ ⨆ α : σ, W α := by
    refine iSup_le ?_
    intro γ
    by_cases hγ : V γ = ⊥
    · simp only [hγ, bot_le]
    · have hEig : ∀ idx, Module.End.HasEigenvalue (T idx) (γ idx) := by
        intro idx
        apply Module.End.hasEigenvalue_iff.mpr
        intro hbot
        apply hγ
        apply le_antisymm
        · have hle : V γ ≤ Module.End.eigenspace (T idx) (γ idx) := by
            exact iInf_le (fun j => Module.End.eigenspace (T j) (γ j)) idx
          simpa only [le_bot_iff, hbot] using hle
        · exact bot_le
      let α : σ := fun idx => ⟨γ idx, hEig idx⟩
      exact le_iSup_of_le α <| by
        simp only [UnifEigenvalues.val_mk, le_refl, V, W, α]
  have hWTop : (⨆ α : σ, W α) = ⊤ := by
    calc
      (⨆ α : σ, W α) = ⨆ γ : ι → ℂ, V γ := by exact le_antisymm hWleV hVleW
      _ = ⊤ := hFullTop
  have hWInternal : DirectSum.IsInternal (fun α : σ => W α) := by
    apply hWOrtho.isInternal_iff.mpr
    rw [hWTop, Submodule.top_orthogonal_eq_bot]
  let s := Σ α : σ, Fin (Module.finrank ℂ (W α))
  let b : OrthonormalBasis s ℂ (EuclideanSpace ℂ (Fin D)) :=
    hWInternal.collectedOrthonormalBasis hWOrtho (fun α => stdOrthonormalBasis ℂ (W α))
  let χ : s → ι → ℂ := fun a idx => ((a.1 idx : Eigenvalues (T idx)) : ℂ)
  have hbmem (a : s) : b a ∈ W a.1 := by
    change
      (hWInternal.collectedOrthonormalBasis hWOrtho
        (fun α => stdOrthonormalBasis ℂ (W α)) a) ∈ W a.1
    exact hWInternal.collectedOrthonormalBasis_mem
      (hV := hWOrtho) (v := fun α => stdOrthonormalBasis ℂ (W α)) a
  have hTb (idx : ι) (a : s) : T idx (b a) = (χ a idx) • b a := by
    have hbmem' : b a ∈ ⨅ j, Module.End.eigenspace (T j) ((a.1 j : Eigenvalues (T j)) : ℂ) := by
      change b a ∈ W a.1
      exact hbmem a
    exact (Module.End.mem_eigenspace_iff).mp ((Submodule.mem_iInf _).mp hbmem' idx)
  let eig : s → Fin n → Fin n → ℂ := fun a i j =>
    χ a (Sum.inl (i, j)) + Complex.I * χ a (Sum.inr (i, j))
  have hM_decomp (i j : Fin n) : M i j = H i j + Complex.I • K i j := by
    ext r s
    simp only [one_div, smul_add, sub_eq_add_neg, smul_neg, add_apply, smul_apply, smul_eq_mul,
      conjTranspose_apply, RCLike.star_def, neg_apply, H, K]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have hMb (a : s) (i j : Fin n) :
      Matrix.toEuclideanLin (M i j) (b a) = eig a i j • b a := by
    have hlin : Matrix.toEuclideanLin (M i j) =
        Matrix.toEuclideanLin (H i j) + Complex.I • Matrix.toEuclideanLin (K i j) := by
      simpa only [one_div, smul_add, map_add, map_smul, map_sub] using
        congrArg Matrix.toEuclideanLin (hM_decomp i j)
    rw [hlin]
    calc
      Matrix.toEuclideanLin (H i j) (b a) + Complex.I • Matrix.toEuclideanLin (K i j) (b a)
          = χ a (Sum.inl (i, j)) • b a + Complex.I • (χ a (Sum.inr (i, j)) • b a) := by
              rw [hTb (Sum.inl (i, j)) a, hTb (Sum.inr (i, j)) a]
      _ = eig a i j • b a := by
            simp only [smul_smul, add_smul, eig]
  let ψE : Fin n → EuclideanSpace ℂ (Fin D) := fun i => WithLp.toLp 2 (ψ i)
  let c : Fin n → s → ℂ := fun i a => inner ℂ (b a) (ψE i)
  have hcoeff (i j : Fin n) (v : EuclideanSpace ℂ (Fin D)) (a : s) :
      inner ℂ (b a) (Matrix.toEuclideanLin (M i j) v) = eig a i j * inner ℂ (b a) v := by
    let v' : EuclideanSpace ℂ (Fin D) := ∑ x, inner ℂ (b x) v • b x
    have hv' : v' = v := by
      simpa only using b.sum_repr' v
    calc
      inner ℂ (b a) (Matrix.toEuclideanLin (M i j) v)
          = inner ℂ (b a) (Matrix.toEuclideanLin (M i j) v') := by rw [← hv']
      _ = inner ℂ (b a) (∑ x, (inner ℂ (b x) v * eig x i j) • b x) := by
            rw [show v' = ∑ x, inner ℂ (b x) v • b x by rfl, map_sum]
            apply congrArg (inner ℂ (b a))
            apply Finset.sum_congr rfl
            intro x _
            rw [map_smul, hMb x i j, smul_smul]
      _ = inner ℂ (b a) v * eig a i j := by
            simpa only using Orthonormal.inner_right_fintype (hv := b.orthonormal)
              (l := fun x => inner ℂ (b x) v * eig x i j) a
      _ = eig a i j * inner ℂ (b a) v := by ring
  have hformTerm (i j : Fin n) :
      star (ψ i) ⬝ᵥ (M i j).mulVec (ψ j) =
        inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j)) := by
    simp only [dotProduct_comm, Matrix.toLpLin_toLp, Matrix.toLin'_apply,
      EuclideanSpace.inner_eq_star_dotProduct, ψE]
  have hterm (i j : Fin n) :
      inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j)) =
        ∑ a : s, starRingEnd ℂ (c i a) * c j a * eig a i j := by
    calc
      inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j))
          = ∑ a : s, inner ℂ (ψE i) (b a) * inner ℂ (b a)
              (Matrix.toEuclideanLin (M i j) (ψE j)) := by
              symm
              exact b.sum_inner_mul_inner (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j))
      _ = ∑ a : s, starRingEnd ℂ (c i a) * (eig a i j * c j a) := by
            have hleft (a : s) : inner ℂ (ψE i) (b a) = starRingEnd ℂ (c i a) := by
              simp only [inner_conj_symm, c]
            have hright (a : s) :
                inner ℂ (b a) (Matrix.toEuclideanLin (M i j) (ψE j)) = eig a i j * c j a := by
              simpa only [c] using hcoeff i j (ψE j) a
            apply Finset.sum_congr rfl
            intro a _
            rw [hleft a, hright a]
      _ = ∑ a : s, starRingEnd ℂ (c i a) * c j a * eig a i j := by
            apply Finset.sum_congr rfl
            intro a _
            ring
  have hrewrite :
      ∑ i : Fin n, ∑ j : Fin n, inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j)) =
        ∑ a : s, ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j := by
    calc
      ∑ i : Fin n, ∑ j : Fin n, inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j))
          = ∑ i : Fin n, ∑ j : Fin n, ∑ a : s, starRingEnd ℂ (c i a) * c j a * eig a i j := by
              simp_rw [hterm]
      _ = ∑ i : Fin n, ∑ a : s, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
      _ = ∑ a : s, ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j := by
            rw [Finset.sum_comm]
  have heigScalar (a : s) (i j : Fin n) :
      star (b a).ofLp ⬝ᵥ (M i j).mulVec (b a).ofLp = eig a i j := by
    have hinner : inner ℂ (b a) (Matrix.toEuclideanLin (M i j) (b a)) = eig a i j := by
      rw [hMb a i j]
      simp only [inner_smul_right, inner_self_eq_norm_sq_to_K, OrthonormalBasis.norm_eq_one,
        coe_algebraMap, ofReal_one, one_pow, mul_one]
    simpa only [dotProduct_comm, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply] using hinner
  have hnonneg :
      0 ≤ ∑ a : s, ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j := by
    apply Finset.sum_nonneg
    intro a _
    have hs := hscalar (fun i => c i a) (b a).ofLp
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [heigScalar a i j]
  calc
    0 ≤ ∑ a : s, ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j :=
      hnonneg
    _ = ∑ i : Fin n, ∑ j : Fin n, inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j)) := by
      rw [← hrewrite]
    _ = ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (M i j).mulVec (ψ j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hformTerm i j]

set_option maxHeartbeats 1600000 in
-- Elaborating the simultaneous-diagonalization argument expands enough definitions
-- that the default heartbeat limit may time out.
theorem quadraticForm_nonneg_of_isPositiveMap_of_commuting_images
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T)
    {n : ℕ}
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ))
    (ha : BlockPositive a)
    (hcomm : PairwiseCommuteImages T a)
    (ψ : Fin n → Fin D → ℂ) :
    0 ≤ blockQuadraticForm T a ψ := by
  classical
  simp only [blockQuadraticForm]
  -- Step 1: Block Hermiticity
  have hBH : ∀ i j, (a j i)ᴴ = a i j := blockHermitian_of_blockPositive ha
  -- Step 2: T preserves adjoints, giving (T(a j i))ᴴ = T(a i j)
  have hTadj : ∀ i j, (T (a j i))ᴴ = T (a i j) := by
    intro i j
    conv_lhs => rw [(hBH j i).symm]
    simp only [hT.map_conjTranspose, conjTranspose_conjTranspose]
  -- Step 3: Apply the core lemma with M i j = T(a i j)
  apply blockForm_nonneg_of_scalarPSD_of_commuting (fun i j => T (a i j))
  · -- Block Hermiticity of images
    intro i j; exact hTadj i j
  · -- Pairwise commutativity
    intro i j k l; exact hcomm i j k l
  · -- Scalar PSD: for all w e, ∑ij conj(w i) w j ⟨e, T(a ij) e⟩ ≥ 0
    intro w e
    -- This equals ⟨e, T(B_w) e⟩ where B_w = ∑ij conj(w_i) w_j a_ij is PSD.
    have hpsd := hT _ (weighted_block_sum_posSemidef ha w)
    -- The sum equals star e ⬝ᵥ T(B_w).mulVec e where B_w is PSD.
    -- B_w = ∑ij conj(w_i) w_j • a_ij
    -- T(B_w) is PSD by positivity of T.
    -- We show the scalar quadratic form equals e† T(B_w) e ≥ 0.
    convert hpsd.dotProduct_mulVec_nonneg e using 1
    simp only [map_sum, LinearMap.map_smul]
    -- Need: ∑ij c_ij * (e† T(a_ij) e) = e† (∑ij c_ij • T(a_ij)) e
    -- The two sides are equal by linearity (rearranging finite sums).
    -- LHS: ∑_p ∑_q c_pq * (e† T(a_pq) e) where c_pq = conj(w_p)*w_q
    -- RHS: e† (∑_p ∑_q c_pq • T(a_pq)) e
    -- These are equal because scalar * dot-product = dot-product of scalar * matrix.
    simp only [dotProduct, mulVec, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    -- Rearrange sums: (q:n, p:n, r:D, s:D) → (r:D, s:D, p:n, q:n)
    -- by four applications of Finset.sum_comm
    -- Rearrange sum order: (n,n,D,D) → (D,D,n,n) via Finset.sum_comm
    -- Step 1: swap inner n↔D for each outer n
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    -- Step 2: swap outer n↔D
    rw [Finset.sum_comm]
    -- Step 3: swap inner n↔D for each outer D
    conv_lhs => arg 2; ext r; arg 2; ext x; rw [Finset.sum_comm]
    -- Step 4: swap second n↔D
    conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
    -- Now both sides sum over (D,D,n,n); match term-by-term
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring

/-- A positive map is positive on commuting block families.

This collects `quadraticForm_nonneg_of_isPositiveMap_of_commuting_images` into a
single reusable predicate. -/
private lemma isPositiveOnCommuting_of_isPositiveMap
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) :
    IsPositiveOnCommuting T := by
  intro n a ha hcomm ψ
  exact quadraticForm_nonneg_of_isPositiveMap_of_commuting_images hT a ha hcomm ψ

end PositiveOnAbelian
