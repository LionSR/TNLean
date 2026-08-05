/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.SchmidtRank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Schmidt decomposition of bipartite vectors (Wolf Chapter 1, Proposition 1.1)

This file proves the Schmidt decomposition of a vector in a finite bipartite
Hilbert space, Proposition 1.1 of Wolf's *Quantum Channels & Operations*
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 195–205).

A bipartite vector `ψ : Fin dA × Fin dB → ℂ` is read as its coefficient matrix
`Matrix.schmidtCoeffMatrix ψ`.  With `d = min dA dB`, the proposition provides
orthonormal bases `e` of `ℂ^dA` and `f` of `ℂ^dB` and nonnegative real
coefficients `λ j`, `j : Fin d`, such that
`ψ (a, b) = ∑ j, √(λ j) * e j a * f j b` and `∑ j, λ j = ∑ p, ‖ψ p‖ ^ 2`.
The number of nonzero `λ j` is the Schmidt rank of `ψ`, identified here with
the matrix rank of the coefficient matrix (`Matrix.schmidtRank`).

The proof applies the spectral theorem to the positive semidefinite matrix
`C * Cᴴ` (and to the transposed coefficient matrix when `dB < dA`), whose
eigenvector basis supplies one Schmidt basis; the normalized images of the
eigenvectors under `Cᴴ`, conjugated and completed to an orthonormal basis,
supply the other.  This is the SVD step of `TNLean.Channel.NormalForm`
(`Matrix.svd_of_posSemidef`) carried out for a rectangular, possibly singular
coefficient matrix, which is the generality of Wolf's Proposition 1.1.

## Main definitions

* `Matrix.IsSchmidtDecomposition`: orthonormal bases and nonnegative
  coefficients satisfying the decomposition and normalization of Wolf's
  Proposition 1.1 (lines 195–203).

## Main statements

* `Matrix.exists_schmidtDecomposition_of_le`: the `dA ≤ dB` case of the
  Schmidt decomposition.
* `Matrix.exists_isSchmidtDecomposition`: Wolf Chapter 1, Proposition 1.1
  (Schmidt decomposition), lines 195–203.
* `Matrix.IsSchmidtDecomposition.schmidtRank_eq_card_ne_zero`: the number of
  nonzero Schmidt coefficients is the Schmidt rank (line 204).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1,
  Proposition 1.1][Wolf2012QChannels]
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace Matrix

variable {dA dB : ℕ}

/-- The columns of the matrix `fun a j ↦ g (φ j) a` are orthonormal when `g` is
an orthonormal basis and `φ` is injective, so the matrix is an isometry. -/
theorem conjTranspose_mul_eq_one_of_orthonormal {ι : Type*} [DecidableEq ι]
    {d : ℕ} {φ : ι → Fin d} (hφ : Function.Injective φ)
    (g : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) :
    (Matrix.of fun a j ↦ g (φ j) a)ᴴ * (Matrix.of fun a j ↦ g (φ j) a) = 1 := by
  ext j k
  have hinner : ∑ a : Fin d, star (g (φ j) a) * g (φ k) a = ⟪g (φ j), g (φ k)⟫_ℂ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Pi.star_apply, mul_comm]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [hinner, orthonormal_iff_ite.mp g.orthonormal (φ j) (φ k)]
  simp only [hφ.eq_iff]

/-- The transpose of a matrix with orthonormal columns is an isometry on the
left: `Mᵀ * Mᵀᴴ = 1`. -/
theorem transpose_mul_conjTranspose_eq_one_of_orthonormal {ι : Type*}
    [DecidableEq ι] {d : ℕ} {φ : ι → Fin d} (hφ : Function.Injective φ)
    (g : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) :
    (Matrix.of fun a j ↦ g (φ j) a)ᵀ * ((Matrix.of fun a j ↦ g (φ j) a)ᵀ)ᴴ = 1 := by
  simpa [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.transpose_mul]
    using congrArg Matrix.transpose (conjTranspose_mul_eq_one_of_orthonormal hφ g)

/-- **Schmidt decomposition when the left factor is the smaller one.**
For `dA ≤ dB`, every `ψ : Fin dA × Fin dB → ℂ` decomposes as
`ψ (a, b) = ∑ j, √(λ j) * e j a * f j b` with orthonormal bases `e` of
`ℂ^dA` and `f` of `ℂ^dB`, nonnegative coefficients `λ`, and normalization
`∑ j, λ j = ∑ p, ‖ψ p‖ ^ 2`.

This is the `dA ≤ dB` case of Wolf Chapter 1, Proposition 1.1
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 195–203).
The spectral theorem applied to `C * Cᴴ` supplies the eigenbasis `e` and the
eigenvalues `λ`; the normalized images of the eigenvectors under `Cᴴ`,
conjugated and completed to an orthonormal basis, supply `f`. -/
theorem exists_schmidtDecomposition_of_le (h : dA ≤ dB) (ψ : Fin dA × Fin dB → ℂ) :
    ∃ (e : OrthonormalBasis (Fin dA) ℂ (EuclideanSpace ℂ (Fin dA)))
      (f : OrthonormalBasis (Fin dB) ℂ (EuclideanSpace ℂ (Fin dB)))
      (lam : Fin dA → ℝ),
      (∀ j, 0 ≤ lam j) ∧
        (∀ a b, ψ (a, b) =
          ∑ j : Fin dA, (Real.sqrt (lam j) : ℂ) * e j a * f (j.castLE h) b) ∧
        ∑ j : Fin dA, lam j = ∑ p : Fin dA × Fin dB, ‖ψ p‖ ^ 2 := by
  classical
  set C : Matrix (Fin dA) (Fin dB) ℂ := schmidtCoeffMatrix ψ with hC
  have hM : (C * Cᴴ).PosSemidef := posSemidef_self_mul_conjTranspose C
  set e := hM.isHermitian.eigenvectorBasis with he
  set lam : Fin dA → ℝ := hM.isHermitian.eigenvalues with hlam
  have hlam0 : ∀ j, 0 ≤ lam j := fun j ↦ hM.eigenvalues_nonneg j
  -- the images `w j = Cᴴ *ᵥ e j` are orthogonal with squared norms `lam j`
  set w : Fin dA → EuclideanSpace ℂ (Fin dB) := fun j ↦ WithLp.toLp 2 (Cᴴ *ᵥ ⇑(e j)) with hw
  have hgram : ∀ j k, ⟪w j, w k⟫_ℂ = if j = k then (lam j : ℂ) else 0 := by
    intro j k
    have hstep : ⟪w j, w k⟫_ℂ = (lam k : ℂ) * ⟪e j, e k⟫_ℂ := by
      simp only [hw]
      rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.star_mulVec,
        Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        hM.isHermitian.mulVec_eigenvectorBasis k, RCLike.real_smul_eq_coe_smul (K := ℂ),
        dotProduct_smul, smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct_comm]
      rfl
    rw [hstep, orthonormal_iff_ite.mp e.orthonormal j k]
    by_cases hjk : j = k <;> simp [hjk]
  -- pad the data to `Fin dB`; the zero-padded slots are never used
  set lamP : Fin dB → ℝ := fun k ↦ if hk : k.val < dA then lam ⟨k.val, hk⟩ else 0 with hlamP
  set wP : Fin dB → EuclideanSpace ℂ (Fin dB) :=
    fun k ↦ if hk : k.val < dA then w ⟨k.val, hk⟩ else 0 with hwP
  have hlamP_cast : ∀ j : Fin dA, lamP (j.castLE h) = lam j := fun j ↦ dif_pos j.isLt
  have hwP_cast : ∀ j : Fin dA, wP (j.castLE h) = w j := fun j ↦ dif_pos j.isLt
  -- the conjugated normalized images, extended by zero outside the support
  set v : Fin dB → EuclideanSpace ℂ (Fin dB) :=
    fun k ↦ WithLp.toLp 2 (star ((Real.sqrt (lamP k) : ℂ)⁻¹ • ⇑(wP k))) with hv
  set s : Set (Fin dB) := {k | lamP k ≠ 0} with hs
  have hvortho : Orthonormal ℂ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hks⟩ ⟨l, hls⟩
    have hks' : lamP k ≠ 0 := hks
    have hls' : lamP l ≠ 0 := hls
    have hk : k.val < dA := by
      by_contra hc
      exact hks' (dif_neg hc)
    have hl : l.val < dA := by
      by_contra hc
      exact hls' (dif_neg hc)
    have hlamk : lamP k = lam ⟨k.val, hk⟩ := dif_pos hk
    have hlaml : lamP l = lam ⟨l.val, hl⟩ := dif_pos hl
    have hlamk0 : lam ⟨k.val, hk⟩ ≠ 0 := by rw [← hlamk]; exact hks'
    have hlaml0 : lam ⟨l.val, hl⟩ ≠ 0 := by rw [← hlaml]; exact hls'
    have hwk : wP k = w ⟨k.val, hk⟩ := dif_pos hk
    have hwl : wP l = w ⟨l.val, hl⟩ := dif_pos hl
    have hsr : ∀ x : ℝ, star ((x : ℂ)) = (x : ℂ) := fun x ↦ by
      rw [Complex.star_def, Complex.conj_ofReal]
    have hinner : ⟪v k, v l⟫_ℂ =
        ((Real.sqrt (lam ⟨l.val, hl⟩) : ℂ))⁻¹ * ((Real.sqrt (lam ⟨k.val, hk⟩) : ℂ))⁻¹ *
          ⟪w ⟨l.val, hl⟩, w ⟨k.val, hk⟩⟫_ℂ := by
      simp only [hv]
      rw [EuclideanSpace.inner_toLp_toLp, star_star, star_smul, smul_dotProduct,
        dotProduct_smul, star_inv₀, hsr, hwk, hwl, hlamk, hlaml, dotProduct_comm,
        ← EuclideanSpace.inner_eq_star_dotProduct, smul_eq_mul, smul_eq_mul, mul_assoc]
    change ⟪v k, v l⟫_ℂ = _
    rw [hinner, hgram]
    rcases eq_or_ne k l with rfl | hkl
    · rw [if_pos rfl, if_pos rfl]
      have hpos : (0:ℝ) < lam ⟨k.val, hl⟩ := (hlam0 _).lt_of_ne (Ne.symm hlaml0)
      have hne : (Real.sqrt (lam ⟨k.val, hl⟩) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
      field_simp
      have h2 : (Real.sqrt (lam ⟨k.val, hl⟩) : ℂ) ^ 2 = (lam ⟨k.val, hl⟩ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (hlam0 _)]
      rw [h2]
    · have hlk : (⟨l.val, hl⟩ : Fin dA) ≠ ⟨k.val, hk⟩ := by
        intro hll
        exact hkl (Fin.ext (Fin.ext_iff.mp hll).symm)
      rw [if_neg hlk, if_neg (by simpa [Subtype.ext_iff] using hkl), mul_zero]
  -- extend the conjugated normalized images to an orthonormal basis of `ℂ^dB`
  obtain ⟨f, hf⟩ :=
    hvortho.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace
  -- the `b`-th Fourier coefficient of `C *ᵥ single b` in the basis `e`
  have hstar : ∀ x : Fin dA → ℂ, star (Cᴴ *ᵥ x) = star x ᵥ* C := fun x ↦ by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  have hcoeff : ∀ (j : Fin dA) (b : Fin dB),
      ⟪e j, WithLp.toLp 2 (C *ᵥ Pi.single b 1)⟫_ℂ =
        (Real.sqrt (lam j) : ℂ) * (f (j.castLE h)).ofLp b := by
    intro j b
    have h1 : ⟪e j, WithLp.toLp 2 (C *ᵥ Pi.single b 1)⟫_ℂ = star ((w j).ofLp b) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct_comm,
        Matrix.dotProduct_mulVec, ← hstar, dotProduct_single_one]
      simp only [hw, WithLp.ofLp_toLp, Pi.star_apply]
    rw [h1]
    by_cases hj : lam j = 0
    · have hwj : w j = 0 := by
        have hjj := hgram j j
        rw [if_pos rfl, hj, Complex.ofReal_zero] at hjj
        exact inner_self_eq_zero.mp hjj
      rw [hwj]
      simp [hj]
    · have hmem : j.castLE h ∈ s := by
        have hne : lamP (j.castLE h) ≠ 0 := by rw [hlamP_cast j]; exact hj
        exact hne
      have hsqrtne : (Real.sqrt (lam j) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr
          (Real.sqrt_pos.mpr ((hlam0 j).lt_of_ne (Ne.symm hj))).ne'
      have hsr : star ((Real.sqrt (lam j) : ℂ)) = (Real.sqrt (lam j) : ℂ) := by
        rw [Complex.star_def, Complex.conj_ofReal]
      rw [hf (j.castLE h) hmem]
      simp only [hv]
      rw [hlamP_cast j, hwP_cast j, WithLp.ofLp_toLp, Pi.star_apply, Pi.smul_apply,
        smul_eq_mul, star_mul, star_inv₀, hsr, mul_comm (star ((w j).ofLp b)),
        mul_inv_cancel_left₀ hsqrtne]
  -- assemble the entrywise decomposition
  have hpsi : ∀ a b, ψ (a, b) =
      ∑ j : Fin dA, (Real.sqrt (lam j) : ℂ) * e j a * (f (j.castLE h)).ofLp b := by
    intro a b
    have htoLp : WithLp.toLp 2 (C *ᵥ Pi.single b 1) =
        ∑ j : Fin dA, ((Real.sqrt (lam j) : ℂ) * (f (j.castLE h)).ofLp b) • e j := by
      rw [← e.sum_repr' (WithLp.toLp 2 (C *ᵥ Pi.single b 1))]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hcoeff j b]
    have hfun : (C *ᵥ Pi.single b 1) =
        ∑ j : Fin dA, ((Real.sqrt (lam j) : ℂ) * (f (j.castLE h)).ofLp b) • ⇑(e j) := by
      have h2 := congrArg (WithLp.addEquiv 2 (Fin dA → ℂ)) htoLp
      rw [map_sum, WithLp.coe_addEquiv, WithLp.ofLp_toLp] at h2
      rw [h2]
      exact Finset.sum_congr rfl fun j _ ↦ WithLp.ofLp_smul _ _ _
    have happ := congrFun hfun a
    rw [Finset.sum_apply] at happ
    simp only [Pi.smul_apply, smul_eq_mul] at happ
    have hCa : C a b = (C *ᵥ Pi.single b 1) a := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [show ψ (a, b) = C a b by rw [hC, schmidtCoeffMatrix_apply], hCa, happ]
    exact Finset.sum_congr rfl fun j _ ↦ mul_right_comm _ _ _
  -- normalization: the eigenvalues sum to the squared norm of `ψ`
  have htrace : (C * Cᴴ).trace = ∑ j : Fin dA, (lam j : ℂ) :=
    hM.isHermitian.trace_eq_sum_eigenvalues
  have htrace2 : (C * Cᴴ).trace = ((∑ p : Fin dA × Fin dB, ‖ψ p‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : (C * Cᴴ).trace = ∑ a : Fin dA, ∑ b : Fin dB, C a b * star (C a b) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h1, ← Finset.sum_product']
    push_cast
    apply Finset.sum_congr rfl
    rintro ⟨a, b⟩ _
    rw [hC, schmidtCoeffMatrix_apply, mul_comm, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
  have hsum : ∑ j : Fin dA, lam j = ∑ p : Fin dA × Fin dB, ‖ψ p‖ ^ 2 := by
    have h3 : (∑ j : Fin dA, (lam j : ℂ)) = ((∑ p : Fin dA × Fin dB, ‖ψ p‖ ^ 2 : ℝ) : ℂ) :=
      htrace.symm.trans htrace2
    exact_mod_cast h3
  exact ⟨e, f, lam, hlam0, hpsi, hsum⟩

/-- The data of Wolf's Schmidt decomposition, Proposition 1.1
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 195–203):
orthonormal bases `e` of `ℂ^dA` and `f` of `ℂ^dB` and nonnegative real
coefficients `λ j` indexed by `j : Fin (min dA dB)`, with
`ψ (a, b) = ∑ j, √(λ j) * e j a * f j b` and `∑ j, λ j = ∑ p, ‖ψ p‖ ^ 2`.
The coefficients `√(λ j)` are the Schmidt coefficients of `ψ`. -/
def IsSchmidtDecomposition {dA dB : ℕ} (ψ : Fin dA × Fin dB → ℂ)
    (e : OrthonormalBasis (Fin dA) ℂ (EuclideanSpace ℂ (Fin dA)))
    (f : OrthonormalBasis (Fin dB) ℂ (EuclideanSpace ℂ (Fin dB)))
    (lam : Fin (min dA dB) → ℝ) : Prop :=
  (∀ j, 0 ≤ lam j) ∧
    (∀ a b, ψ (a, b) =
      ∑ j : Fin (min dA dB), (Real.sqrt (lam j) : ℂ) *
        e (j.castLE (min_le_left dA dB)) a * f (j.castLE (min_le_right dA dB)) b) ∧
    ∑ j : Fin (min dA dB), lam j = ∑ p : Fin dA × Fin dB, ‖ψ p‖ ^ 2

/-- **Schmidt decomposition** (Wolf Chapter 1, Proposition 1.1;
`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 195–203).
For every vector `ψ` in a finite bipartite Hilbert space, with
`d = min dA dB`, there exist orthonormal bases `e` of `ℂ^dA` and `f` of
`ℂ^dB` and nonnegative coefficients `λ j`, `j : Fin d`, with
`ψ (a, b) = ∑ j, √(λ j) * e j a * f j b` and `∑ j, λ j = ∑ p, ‖ψ p‖ ^ 2`.

The case `dB < dA` is the case `dA ≤ dB` applied to the transposed
coefficient matrix, as in Wolf's proof sketch at line 207. -/
theorem exists_isSchmidtDecomposition (ψ : Fin dA × Fin dB → ℂ) :
    ∃ (e : OrthonormalBasis (Fin dA) ℂ (EuclideanSpace ℂ (Fin dA)))
      (f : OrthonormalBasis (Fin dB) ℂ (EuclideanSpace ℂ (Fin dB)))
      (lam : Fin (min dA dB) → ℝ), IsSchmidtDecomposition ψ e f lam := by
  rcases le_total dA dB with h | h
  · obtain ⟨e, f, lam, h0, heq, hnorm⟩ := exists_schmidtDecomposition_of_le h ψ
    refine ⟨e, f, fun j ↦ lam (j.cast (min_eq_left h)), fun j ↦ h0 _, ?_, ?_⟩
    · intro a b
      rw [heq a b]
      refine Fintype.sum_equiv (finCongr (min_eq_left h).symm) _ _ (fun j ↦ ?_)
      have e1 : (finCongr (min_eq_left h).symm j).cast (min_eq_left h) = j := Fin.ext rfl
      have e2 : (finCongr (min_eq_left h).symm j).castLE (min_le_left dA dB) = j :=
        Fin.ext rfl
      have e3 : (finCongr (min_eq_left h).symm j).castLE (min_le_right dA dB) =
          j.castLE h := Fin.ext rfl
      simp only [e1, e2, e3]
    · rw [← hnorm]
      refine Fintype.sum_equiv (finCongr (min_eq_left h)) _ _ (fun j ↦ ?_)
      rw [show j.cast (min_eq_left h) = finCongr (min_eq_left h) j from Fin.ext rfl]
  · obtain ⟨e', f', lam', h0, heq, hnorm⟩ :=
      exists_schmidtDecomposition_of_le h (fun p ↦ ψ p.swap)
    refine ⟨f', e', fun j ↦ lam' (j.cast (min_eq_right h)), fun j ↦ h0 _, ?_, ?_⟩
    · intro a b
      have h1 : ψ (a, b) =
          ∑ j : Fin dB, (Real.sqrt (lam' j) : ℂ) * e' j b * f' (j.castLE h) a :=
        heq b a
      rw [h1]
      refine Fintype.sum_equiv (finCongr (min_eq_right h).symm) _ _ (fun j ↦ ?_)
      have e1 : (finCongr (min_eq_right h).symm j).cast (min_eq_right h) = j :=
        Fin.ext rfl
      have e2 : (finCongr (min_eq_right h).symm j).castLE (min_le_left dA dB) =
          j.castLE h := Fin.ext rfl
      have e3 : (finCongr (min_eq_right h).symm j).castLE (min_le_right dA dB) = j :=
        Fin.ext rfl
      simp only [e1, e2, e3]
      rw [mul_right_comm]
    · have hsum : ∑ p : Fin dB × Fin dA, ‖(fun q ↦ ψ q.swap) p‖ ^ 2 =
          ∑ p : Fin dA × Fin dB, ‖ψ p‖ ^ 2 :=
        Fintype.sum_equiv (Equiv.prodComm (Fin dB) (Fin dA)) _ _ (fun p ↦ rfl)
      rw [← hsum, ← hnorm]
      refine Fintype.sum_equiv (finCongr (min_eq_right h)) _ _ (fun j ↦ ?_)
      rw [show j.cast (min_eq_right h) = finCongr (min_eq_right h) j from Fin.ext rfl]

/-- **The number of nonzero Schmidt coefficients is the Schmidt rank**
(`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, line 204).
For any Schmidt decomposition of `ψ` with coefficients `λ`, the number of
nonzero `λ j` equals `Matrix.schmidtRank ψ`, the matrix rank of the
coefficient matrix. -/
theorem IsSchmidtDecomposition.schmidtRank_eq_card_ne_zero {dA dB : ℕ}
    {ψ : Fin dA × Fin dB → ℂ}
    {e : OrthonormalBasis (Fin dA) ℂ (EuclideanSpace ℂ (Fin dA))}
    {f : OrthonormalBasis (Fin dB) ℂ (EuclideanSpace ℂ (Fin dB))}
    {lam : Fin (min dA dB) → ℝ} (h : IsSchmidtDecomposition ψ e f lam) :
    schmidtRank ψ = Fintype.card {j // lam j ≠ 0} := by
  classical
  obtain ⟨h0, heq, _⟩ := h
  set C : Matrix (Fin dA) (Fin dB) ℂ := schmidtCoeffMatrix ψ with hC
  set E : Matrix (Fin dA) (Fin (min dA dB)) ℂ :=
    Matrix.of fun a j ↦ e (j.castLE (min_le_left dA dB)) a with hE
  set F : Matrix (Fin dB) (Fin (min dA dB)) ℂ :=
    Matrix.of fun b j ↦ f (j.castLE (min_le_right dA dB)) b with hF
  set σ : Fin (min dA dB) → ℂ := fun j ↦ (Real.sqrt (lam j) : ℂ) with hσ
  -- the decomposition in matrix form: `C = E * diagonal σ * Fᵀ`
  have hCE : C = E * Matrix.diagonal σ * Fᵀ := by
    ext a b
    rw [show C a b = ψ (a, b) by rw [hC, schmidtCoeffMatrix_apply], heq a b]
    simp only [hE, hF, hσ, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
      Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq']
    apply Finset.sum_congr rfl
    intro j _
    rw [if_pos (Finset.mem_univ j)]
    ring
  have hE1 : Eᴴ * E = 1 :=
    conjTranspose_mul_eq_one_of_orthonormal (Fin.castLE_injective _) e
  have hF1 : Fᵀ * Fᵀᴴ = 1 :=
    transpose_mul_conjTranspose_eq_one_of_orthonormal (Fin.castLE_injective _) f
  have hsr : ∀ j, star (σ j) = σ j := fun j ↦ by
    rw [hσ, Complex.star_def, Complex.conj_ofReal]
  -- `C * Cᴴ = E * diagonal λ * Eᴴ`
  have hD : Matrix.diagonal σ * (Matrix.diagonal σ)ᴴ =
      Matrix.diagonal fun j ↦ (lam j : ℂ) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    change σ j * star (σ j) = (lam j : ℂ)
    rw [hsr j, hσ, ← Complex.ofReal_mul, Real.mul_self_sqrt (h0 j)]
  have hCC : C * Cᴴ = E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ := by
    calc C * Cᴴ = (E * Matrix.diagonal σ * Fᵀ) * (Fᵀᴴ * ((Matrix.diagonal σ)ᴴ * Eᴴ)) := by
          rw [hCE, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      _ = E * Matrix.diagonal σ * (Fᵀ * Fᵀᴴ) * (Matrix.diagonal σ)ᴴ * Eᴴ := by
          simp only [Matrix.mul_assoc]
      _ = E * Matrix.diagonal σ * (Matrix.diagonal σ)ᴴ * Eᴴ := by
          rw [hF1, Matrix.mul_one]
      _ = E * (Matrix.diagonal σ * (Matrix.diagonal σ)ᴴ) * Eᴴ := by
          simp only [Matrix.mul_assoc]
      _ = E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ := by rw [hD]
  -- rank comparison through the isometry `E`
  have hle1 : (E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ).rank ≤
      (Matrix.diagonal fun j ↦ (lam j : ℂ)).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hexpand : Eᴴ * (E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ) * E =
      Matrix.diagonal fun j ↦ (lam j : ℂ) := by
    rw [show Eᴴ * (E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ) * E =
        (Eᴴ * E) * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * (Eᴴ * E) by
      simp only [Matrix.mul_assoc], hE1, Matrix.one_mul, Matrix.mul_one]
  have hle2 : (Matrix.diagonal fun j ↦ (lam j : ℂ)).rank ≤
      (E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ).rank := by
    have h2 := (Matrix.rank_mul_le_left
        (Eᴴ * (E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ)) E).trans
      (Matrix.rank_mul_le_right Eᴴ (E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ))
    rwa [hexpand] at h2
  have hcard : Fintype.card {j // (lam j : ℂ) ≠ 0} = Fintype.card {j // lam j ≠ 0} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight fun j ↦ Complex.ofReal_ne_zero
  calc schmidtRank ψ = C.rank := by rw [schmidtRank, hC]
    _ = (C * Cᴴ).rank := (Matrix.rank_self_mul_conjTranspose C).symm
    _ = (E * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Eᴴ).rank := by rw [hCC]
    _ = (Matrix.diagonal fun j ↦ (lam j : ℂ)).rank := le_antisymm hle1 hle2
    _ = Fintype.card {j // (lam j : ℂ) ≠ 0} := Matrix.rank_diagonal _
    _ = Fintype.card {j // lam j ≠ 0} := hcard

end Matrix
