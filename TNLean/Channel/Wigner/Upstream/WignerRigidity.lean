/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import TNLean.Channel.Wigner.Upstream.ComplexReconstruction

/-!
# Projective Wigner rigidity: global-sign closure and the rigidity theorem

This module is adapted from
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/WignerRigidity.lean` in
`zblore/csd-lean4` at commit
`55ac6758832291c8b0fb94d78e10dc47b1cb8a06`, under the Apache License 2.0.
The upstream single source file was split mechanically at semantic section
boundaries, preserving declaration order, to satisfy TNLean's module-size policy.
Ordinary imports and public declarations replace the upstream module-system commands.
Further adaptations are limited to formatting, explicit qualification, documentation, and
style-linter compliance. Declaration order, theorem statements, and proof structure are
preserved.
-/

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {N : ℕ}
variable {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}

/-! ## Master witness and the global-sign closure -/

/-- Master witness vector: `∑ a, (1 + I·a) • b a`. All coordinates nonzero and
all pairwise imaginary relative phases nonzero. -/
noncomputable def masterVec
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    EuclideanSpace ℂ (Fin N) :=
  ∑ a : Fin N, (1 + Complex.I * ((a : ℕ) : ℂ)) • b a

lemma masterVec_repr
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (k : Fin N) :
    b.repr (masterVec b) k = 1 + Complex.I * ((k : ℕ) : ℂ) := by
  rw [b.repr_apply_apply]
  unfold masterVec
  rw [inner_sum, Finset.sum_eq_single k]
  · rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k k, if_pos rfl, mul_one]
  · intro j _ hjk
    rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k j, if_neg (Ne.symm hjk),
        mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma masterVec_coord_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (k : Fin N) :
    b.repr (masterVec b) k ≠ 0 := by
  rw [masterVec_repr]
  have hre : (1 + Complex.I * ((k : ℕ) : ℂ)).re = 1 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  intro h
  rw [h] at hre
  simp at hre

lemma masterVec_ne_zero
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (k : Fin N) :
    masterVec b ≠ 0 := by
  intro h
  exact masterVec_coord_ne_zero b k (by rw [h]; simp)

lemma masterVec_im_ne
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {a c : Fin N} (hac : a ≠ c) :
    ((starRingEnd ℂ) (b.repr (masterVec b) a) * b.repr (masterVec b) c).im ≠ 0 := by
  rw [masterVec_repr, masterVec_repr]
  have him :
      ((starRingEnd ℂ) (1 + Complex.I * ((a : ℕ) : ℂ)) *
        (1 + Complex.I * ((c : ℕ) : ℂ))).im
      = ((c : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    simp only [map_add, map_one, map_mul, Complex.conj_I, Complex.conj_natCast]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im]
    ring
  rw [him, sub_ne_zero]
  intro h
  exact hac (Fin.val_injective (Nat.cast_injective h)).symm

/-- The complex probe `mk (b i + I • b j)` and its conjugate `mk (b i - I • b j)`
are distinct projective points (their reps are orthogonal). -/
lemma Iprobe_ne_negIprobe
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) {i j : Fin N} (hij : i ≠ j) :
    Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij)
      ≠ Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij) := by
  intro h
  have h0 : transProb (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
      (Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij)) = 0 := by
    rw [transProb_mk_eq_zero_iff]
    have e1 : (inner ℂ (b i) (b i) : ℂ) = 1 := by
      rw [orthonormal_iff_ite.mp b.orthonormal i i, if_pos rfl]
    have e2 : (inner ℂ (b i) (b j) : ℂ) = 0 := by
      rw [orthonormal_iff_ite.mp b.orthonormal i j, if_neg hij]
    have e3 : (inner ℂ (b j) (b i) : ℂ) = 0 := by
      rw [orthonormal_iff_ite.mp b.orthonormal j i, if_neg (Ne.symm hij)]
    have e4 : (inner ℂ (b j) (b j) : ℂ) = 1 := by
      rw [orthonormal_iff_ite.mp b.orthonormal j j, if_pos rfl]
    rw [inner_add_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_right,
        inner_smul_left, inner_smul_right, e1, e2, e3, e4]
    simp [Complex.conj_I]
  rw [h, transProb_self] at h0
  exact one_ne_zero h0

/-- Abstract algebraic core of the global-sign linking: given the Gram equations
for three coordinates and the master genericity (imaginary relative phases
nonzero), the fixed/flipped sign of the pair `(a,b)` matches that of `(b,c)`. -/
lemma sign_link_core {cA cB cC dA dB dC : ℂ} {S F : ℝ}
    (hFpos : (0 : ℝ) < F)
    (hcA : cA ≠ 0) (hcB : cB ≠ 0) (hcC : cC ≠ 0)
    (hImAB : ((starRingEnd ℂ) cA * cB).im ≠ 0)
    (hImBC : ((starRingEnd ℂ) cB * cC).im ≠ 0)
    {Γab Γbc Γac : ℂ}
    (Eab : (starRingEnd ℂ) dA * dB * (S : ℂ) = Γab * (F : ℂ))
    (Ebc : (starRingEnd ℂ) dB * dC * (S : ℂ) = Γbc * (F : ℂ))
    (Eac : (starRingEnd ℂ) dA * dC * (S : ℂ) = Γac * (F : ℂ))
    (Ebb : (starRingEnd ℂ) dB * dB * (S : ℂ) = (starRingEnd ℂ) cB * cB * (F : ℂ))
    (hAB : Γab = (starRingEnd ℂ) cA * cB ∨
      Γab = (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB))
    (hBC : Γbc = (starRingEnd ℂ) cB * cC ∨
      Γbc = (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC))
    (hAC : Γac = (starRingEnd ℂ) cA * cC ∨
      Γac = (starRingEnd ℂ) ((starRingEnd ℂ) cA * cC)) :
    (Γab = (starRingEnd ℂ) cA * cB ↔ Γbc = (starRingEnd ℂ) cB * cC) := by
  have hFc : (F : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hFpos)
  have hdia : Γab * Γbc = Γac * ((starRingEnd ℂ) cB * cB) := by
    have hbase : ((starRingEnd ℂ) dA * dB * (S : ℂ)) * ((starRingEnd ℂ) dB * dC * (S : ℂ))
        = ((starRingEnd ℂ) dA * dC * (S : ℂ)) *
            ((starRingEnd ℂ) dB * dB * (S : ℂ)) := by ring
    rw [Eab, Ebc, Eac, Ebb] at hbase
    have h2 : Γab * Γbc * ((F : ℂ) * (F : ℂ))
        = Γac * ((starRingEnd ℂ) cB * cB) * ((F : ℂ) * (F : ℂ)) := by
          linear_combination hbase
    exact mul_right_cancel₀ (mul_ne_zero hFc hFc) h2
  have hsrc : ((starRingEnd ℂ) cA * cB) * ((starRingEnd ℂ) cB * cC)
      = ((starRingEnd ℂ) cA * cC) * ((starRingEnd ℂ) cB * cB) := by ring
  have hγab : (starRingEnd ℂ) cA * cB ≠ 0 := mul_ne_zero (by simpa using hcA) hcB
  have hγbc : (starRingEnd ℂ) cB * cC ≠ 0 := mul_ne_zero (by simpa using hcB) hcC
  have hγbb_real : (starRingEnd ℂ) ((starRingEnd ℂ) cB * cB) = (starRingEnd ℂ) cB * cB := by
    rw [map_mul, Complex.conj_conj, mul_comm]
  have hsrcC :
      (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB) *
        (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC)
      = (starRingEnd ℂ) ((starRingEnd ℂ) cA * cC) * ((starRingEnd ℂ) cB * cB) := by
    rw [← map_mul, hsrc, map_mul, hγbb_real]
  constructor
  · intro hABf
    by_contra hBCn
    have hBCflip : Γbc = (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC) := hBC.resolve_left hBCn
    rcases hAC with hACf | hACflip
    · rw [hABf, hBCflip, hACf] at hdia
      have hz : (starRingEnd ℂ) cA * cB
          * ((starRingEnd ℂ) ((starRingEnd ℂ) cB * cC) - (starRingEnd ℂ) cB * cC) = 0 := by
        linear_combination hdia - hsrc
      rcases mul_eq_zero.mp hz with h | h
      · exact hγab h
      · exact hImBC (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h))
    · rw [hABf, hBCflip, hACflip] at hdia
      have hz : ((starRingEnd ℂ) cA * cB - (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB))
          * (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC) = 0 := by
        linear_combination hdia - hsrcC
      rcases mul_eq_zero.mp hz with h | h
      · exact hImAB (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h).symm)
      · exact hγbc (by simpa only [starRingEnd_apply, star_eq_zero] using h)
  · intro hBCf
    by_contra hABn
    have hABflip : Γab = (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB) := hAB.resolve_left hABn
    rcases hAC with hACf | hACflip
    · rw [hABflip, hBCf, hACf] at hdia
      have hz : ((starRingEnd ℂ) ((starRingEnd ℂ) cA * cB) - (starRingEnd ℂ) cA * cB)
          * ((starRingEnd ℂ) cB * cC) = 0 := by
        linear_combination hdia - hsrc
      rcases mul_eq_zero.mp hz with h | h
      · exact hImAB (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h))
      · exact hγbc h
    · rw [hABflip, hBCf, hACflip] at hdia
      have hz : (starRingEnd ℂ) ((starRingEnd ℂ) cA * cB)
          * ((starRingEnd ℂ) cB * cC - (starRingEnd ℂ) ((starRingEnd ℂ) cB * cC)) = 0 := by
        linear_combination hdia - hsrcC
      rcases mul_eq_zero.mp hz with h | h
      · exact hγab (by simpa only [starRingEnd_apply, star_eq_zero] using h)
      · exact hImBC (Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h).symm)

/-- Abbreviation: the diagonally reduced map fixes the complex two-level ray `(i,j)`. -/
def CFixed (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) : Prop :=
  diagReducedMap hf b i₀
    (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij)

/-- Middle-index linking: the complex sign of `(a,bx)` matches that of `(bx,c)`. -/
theorem diagReducedMap_complexSign_link
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {a bx c : Fin N} (hab : a ≠ bx) (hbc : bx ≠ c) (hac : a ≠ c) :
    CFixed hf b i₀ hab ↔ CFixed hf b i₀ hbc := by
  have hψne : masterVec b ≠ 0 := masterVec_ne_zero b a
  have hφne : (diagReducedMap hf b i₀ (Projectivization.mk ℂ (masterVec b) hψne)).rep ≠ 0 :=
    Projectivization.rep_nonzero _
  have hFpos : (0 : ℝ)
      < ‖(diagReducedMap hf b i₀ (Projectivization.mk ℂ (masterVec b) hψne)).rep‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hφne) 2
  have Ebb := diagReducedMap_gram_diag hf b i₀ bx (ψ := masterVec b) hψne
  have hcA := masterVec_coord_ne_zero b a
  have hcB := masterVec_coord_ne_zero b bx
  have hcC := masterVec_coord_ne_zero b c
  have hImAB := masterVec_im_ne b hab
  have hImBC := masterVec_im_ne b hbc
  constructor
  · intro hAB
    rcases diagReducedMap_complex_probe_general hf b i₀ hbc with hBC | hBC
    · exact hBC
    · exfalso
      have Eab := diagReducedMap_gram_of_fixed hf b i₀ hab hAB (ψ := masterVec b) hψne
      have Ebc := diagReducedMap_gram_of_flips hf b i₀ hbc hBC (ψ := masterVec b) hψne
      rcases diagReducedMap_complex_probe_general hf b i₀ hac with hAC | hAC
      · have Eac := diagReducedMap_gram_of_fixed hf b i₀ hac hAC (ψ := masterVec b) hψne
        have hcore := sign_link_core hFpos hcA hcB hcC hImAB hImBC Eab Ebc Eac Ebb
          (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
        exact hImBC (Complex.conj_eq_iff_im.mp (hcore.mp rfl))
      · have Eac := diagReducedMap_gram_of_flips hf b i₀ hac hAC (ψ := masterVec b) hψne
        have hcore := sign_link_core hFpos hcA hcB hcC hImAB hImBC Eab Ebc Eac Ebb
          (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
        exact hImBC (Complex.conj_eq_iff_im.mp (hcore.mp rfl))
  · intro hBC
    rcases diagReducedMap_complex_probe_general hf b i₀ hab with hAB | hAB
    · exact hAB
    · exfalso
      have Eab := diagReducedMap_gram_of_flips hf b i₀ hab hAB (ψ := masterVec b) hψne
      have Ebc := diagReducedMap_gram_of_fixed hf b i₀ hbc hBC (ψ := masterVec b) hψne
      rcases diagReducedMap_complex_probe_general hf b i₀ hac with hAC | hAC
      · have Eac := diagReducedMap_gram_of_fixed hf b i₀ hac hAC (ψ := masterVec b) hψne
        have hcore := sign_link_core hFpos hcA hcB hcC hImAB hImBC Eab Ebc Eac Ebb
          (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
        exact hImAB (Complex.conj_eq_iff_im.mp (hcore.mpr rfl))
      · have Eac := diagReducedMap_gram_of_flips hf b i₀ hac hAC (ψ := masterVec b) hψne
        have hcore := sign_link_core hFpos hcA hcB hcC hImAB hImBC Eab Ebc Eac Ebb
          (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
        exact hImAB (Complex.conj_eq_iff_im.mp (hcore.mpr rfl))

/-- Order swap: the complex sign of `(i,j)` matches that of `(j,i)` (by injectivity). -/
theorem diagReducedMap_complexSign_swap
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) :
    CFixed hf b i₀ hij → CFixed hf b i₀ (Ne.symm hij) := by
  intro hfix
  rcases diagReducedMap_complex_probe_general hf b i₀ (Ne.symm hij) with hji | hji
  · exact hji
  · exfalso
    have hLvec : Complex.I • (b i - Complex.I • b j) = b j + Complex.I • b i := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]
    have hRvec : (-Complex.I) • (b i + Complex.I • b j) = b j - Complex.I • b i := by
      rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul, add_comm,
          ← sub_eq_add_neg]
    have hL : Projectivization.mk ℂ (b j + Complex.I • b i) (Iadd_basis_ne_zero b (Ne.symm hij))
        = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij) :=
      (Projectivization.mk_eq_mk_iff' ℂ (b j + Complex.I • b i) (b i - Complex.I • b j)
        (Iadd_basis_ne_zero b (Ne.symm hij)) (subI_basis_ne_zero b hij)).mpr ⟨Complex.I, hLvec⟩
    have hR : Projectivization.mk ℂ (b j - Complex.I • b i) (subI_basis_ne_zero b (Ne.symm hij))
        = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij) :=
      (Projectivization.mk_eq_mk_iff' ℂ (b j - Complex.I • b i) (b i + Complex.I • b j)
        (subI_basis_ne_zero b (Ne.symm hij)) (Iadd_basis_ne_zero b hij)).mpr ⟨-Complex.I, hRvec⟩
    rw [hL, hR] at hji
    have hginj := (diagReducedMap_transProbPreserving hf b i₀).injective
    have hReq := hginj (hji.trans hfix.symm)
    exact Iprobe_ne_negIprobe b hij hReq.symm

/-- Order swap as an iff. -/
theorem diagReducedMap_complexSign_swapIff
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) :
    CFixed hf b i₀ hij ↔ CFixed hf b i₀ (Ne.symm hij) :=
  ⟨diagReducedMap_complexSign_swap hf b i₀ hij,
   diagReducedMap_complexSign_swap hf b i₀ (Ne.symm hij)⟩

/-- Shared-first-index linking: the complex sign of `(a,bx)` matches that of `(a,c)`. -/
theorem diagReducedMap_complexSign_link'
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {a bx c : Fin N} (hab : a ≠ bx) (hac : a ≠ c) (hbc : bx ≠ c) :
    CFixed hf b i₀ hab ↔ CFixed hf b i₀ hac :=
  (diagReducedMap_complexSign_swapIff hf b i₀ hab).trans
    (diagReducedMap_complexSign_link hf b i₀ (Ne.symm hab) hac hbc)

/-- Global constancy: the complex sign is the same for every pair. -/
theorem diagReducedMap_complexSign_all
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N)
    {i j : Fin N} (hij : i ≠ j) {k l : Fin N} (hkl : k ≠ l) :
    CFixed hf b i₀ hij ↔ CFixed hf b i₀ hkl := by
  by_cases h1 : i = k
  · subst h1
    by_cases h2 : j = l
    · subst h2; exact Iff.rfl
    · exact diagReducedMap_complexSign_link' hf b i₀ hij hkl h2
  · by_cases h2 : i = l
    · subst h2
      by_cases h3 : j = k
      · subst h3; exact diagReducedMap_complexSign_swapIff hf b i₀ hij
      · exact (diagReducedMap_complexSign_link' hf b i₀ hij h1 h3).trans
          (diagReducedMap_complexSign_swapIff hf b i₀ h1)
    · by_cases h3 : j = k
      · subst h3
        exact (diagReducedMap_complexSign_swapIff hf b i₀ hij).trans
          (diagReducedMap_complexSign_link' hf b i₀ (Ne.symm hij) hkl h2)
      · by_cases h4 : j = l
        · subst h4
          exact (diagReducedMap_complexSign_swapIff hf b i₀ hij).trans
            ((diagReducedMap_complexSign_link' hf b i₀ (Ne.symm hij) (Ne.symm hkl) h1).trans
             (diagReducedMap_complexSign_swapIff hf b i₀ (Ne.symm hkl)))
        · exact (diagReducedMap_complexSign_link' hf b i₀ hij h1 h3).trans
            ((diagReducedMap_complexSign_swapIff hf b i₀ h1).trans
             (diagReducedMap_complexSign_link' hf b i₀ (Ne.symm h1) hkl h2))

/-- **HEADLINE (global-sign closure).** The per-pair `± I` complex-probe datum is
globally consistent: either every complex two-level ray is fixed, or every one is
flipped. Discharges the `hsign` hypothesis of
`diagReducedMap_dichotomy_of_complexSign` from transition-probability preservation
alone. -/
theorem diagReducedMap_complexSign_closure
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    (∀ i j (hij : i ≠ j),
        diagReducedMap hf b i₀
            (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
          = Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
    ∨ (∀ i j (hij : i ≠ j),
        diagReducedMap hf b i₀
            (Projectivization.mk ℂ (b i + Complex.I • b j) (Iadd_basis_ne_zero b hij))
          = Projectivization.mk ℂ (b i - Complex.I • b j) (subI_basis_ne_zero b hij)) := by
  rcases lt_or_ge N 2 with hN | hN
  · haveI : Subsingleton (Fin N) := Fin.subsingleton_iff_le_one.mpr (by omega)
    exact Or.inl (fun i j hij => absurd (Subsingleton.elim i j) hij)
  · have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by norm_num)
    rcases diagReducedMap_complex_probe_general hf b i₀ h01 with hfix | hflip
    · exact Or.inl (fun i j hij => (diagReducedMap_complexSign_all hf b i₀ h01 hij).mp hfix)
    · refine Or.inr (fun i j hij => ?_)
      rcases diagReducedMap_complex_probe_general hf b i₀ hij with hf2 | hf2
      · exact absurd ((diagReducedMap_complexSign_all hf b i₀ hij h01).mp hf2)
          (fun hcfix => Iprobe_ne_negIprobe b h01 (hcfix.symm.trans hflip))
      · exact hf2

/-- **HEADLINE (unconditional reduced-map dichotomy).** The diagonally reduced map
is globally the identity on rays, or globally coordinatewise conjugation in `b`.
The global-sign residual is discharged (`diagReducedMap_complexSign_closure`);
both branches are genuine and no ℂ-linearity is assumed. -/
theorem diagReducedMap_dichotomy
    (hf : TransProbPreserving f)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i₀ : Fin N) :
    (∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0),
        diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ) = Projectivization.mk ℂ ψ hψ)
    ∨ (∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ψ ≠ 0),
        diagReducedMap hf b i₀ (Projectivization.mk ℂ ψ hψ)
          = Projectivization.mk ℂ (bConjVec b ψ) (bConjVec_ne_zero b hψ)) :=
  diagReducedMap_dichotomy_of_complexSign hf b i₀ (diagReducedMap_complexSign_closure hf b i₀)

/-! ## STEP 2: proof of the Wigner rigidity theorem -/

section RigidityTheorem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `projMap` functoriality: composition of projective isometry maps. -/
lemma projMap_comp (e₁ e₂ : E ≃ₗᵢ[ℂ] E) (p : ℙ ℂ E) :
    projMap e₁ (projMap e₂ p) = projMap (e₂.trans e₁) p := by
  conv_lhs => rw [← p.mk_rep]
  conv_rhs => rw [← p.mk_rep]
  rw [projMap_mk e₂ p.rep p.rep_nonzero,
      projMap_mk e₁ (e₂ p.rep) (e₂.toLinearEquiv.map_ne_zero_iff.mpr p.rep_nonzero),
      projMap_mk (e₂.trans e₁) p.rep p.rep_nonzero]
  simp only [LinearIsometryEquiv.trans_apply]

/-- `projMap e` and `projMap e.symm` are inverse. -/
lemma projMap_symm_projMap (e : E ≃ₗᵢ[ℂ] E) (p : ℙ ℂ E) :
    projMap e (projMap e.symm p) = p := by
  conv_lhs => rw [← p.mk_rep]
  rw [projMap_mk e.symm p.rep p.rep_nonzero,
      projMap_mk e (e.symm p.rep) (e.symm.toLinearEquiv.map_ne_zero_iff.mpr p.rep_nonzero)]
  conv_rhs => rw [← p.mk_rep]
  congr 1
  exact e.apply_symm_apply p.rep

end RigidityTheorem

/-- Coordinatewise conjugation in the standard basis is `conjVec`. -/
lemma bConjVec_basisFun (ψ : EuclideanSpace ℂ (Fin N)) :
    bConjVec (EuclideanSpace.basisFun (Fin N) ℂ) ψ = conjVec ψ := by
  apply (EuclideanSpace.basisFun (Fin N) ℂ).repr.injective
  ext k
  rw [repr_bConjVec, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_repr]
  exact (conjVec_ofLp ψ k).symm

/-- **HEADLINE (Wigner / Fubini-Study rigidity converse).** Every
transition-probability-preserving self-map of `ℂℙ^{N-1}` is induced by a unitary
(`projMap e` for a `≃ₗᵢ[ℂ]` `e`) or by an antiunitary (`projMap e ∘ conjProj`).
ℂ-linearity of `e` is an OUTPUT of the construction (the reduced map lands on the
identity), never assumed; the antiunitary branch is genuinely present
(`conjProj`); the global unitary/antiunitary sign is forced from
transition-probability preservation alone. Foundational-triple only. -/
theorem wigner_rigidity
    (hf : TransProbPreserving f) :
    (∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
      ∀ p, f p = projMap e p)
    ∨ (∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        ∀ p, f p = projMap e (conjProj p)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact Or.inl ⟨LinearIsometryEquiv.refl ℂ _,
      fun p => absurd (Subsingleton.elim p.rep 0) p.rep_nonzero⟩
  · set b := EuclideanSpace.basisFun (Fin N) ℂ with hb
    set i₀ : Fin N := ⟨0, hN⟩ with hi0
    set U := candidateUnitary hf b with hU
    set D := diagUnitary b (twoLevelPhase hf b i₀) (twoLevelPhase_norm hf b i₀) with hD
    have hfe : ∀ p, f p = projMap U (projMap D (diagReducedMap hf b i₀ p)) := by
      intro p
      have h1 : reducedMap hf b p = projMap D (diagReducedMap hf b i₀ p) :=
        (projMap_symm_projMap D (reducedMap hf b p)).symm
      have h2 : f p = projMap U (reducedMap hf b p) :=
        (projMap_symm_projMap U (f p)).symm
      rw [h2, h1]
    rcases diagReducedMap_dichotomy hf b i₀ with hid | hconj
    · refine Or.inl ⟨D.trans U, fun p => ?_⟩
      have hthis : diagReducedMap hf b i₀ p = p := by
        have hp := hid p.rep p.rep_nonzero; rwa [p.mk_rep] at hp
      rw [hfe p, hthis, projMap_comp]
    · refine Or.inr ⟨D.trans U, fun p => ?_⟩
      have hthis : diagReducedMap hf b i₀ p = conjProj p := by
        have hp := hconj p.rep p.rep_nonzero
        rw [p.mk_rep] at hp
        rw [hp]
        refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, ?_⟩
        rw [one_smul, bConjVec_basisFun]
      rw [hfe p, hthis, projMap_comp]


/-! ## Stage 3 complete (W6): the Wigner / Fubini-Study rigidity converse

Stages 1-3 are proved with **no linearity assumed** on `f`, only
`TransProbPreserving`. Stage 3 piece 3 (W5) delivered the complex probe, both
reconstruction directions, and the reduced-map dichotomy conditional on the
global complex-sign closure. **W6 discharges that closure**
(`diagReducedMap_complexSign_closure`) from transition-probability preservation
alone: the per-pair `± I` datum is globally consistent (all complex two-level
rays fixed, or all flipped). The route is (a) the non-anchored per-pair `± I`
dichotomy (`diagReducedMap_complex_probe_general`); (b) the master witness
`masterVec` with every pairwise imaginary relative phase nonzero
(`masterVec_im_ne`); (c) the abstract Gram-triple core `sign_link_core`, ruling
out mixed signs via the rank-1 identity `g_ab g_bc = g_ac ‖d_b‖²` and the
imaginary relative phases; (d) order swap by injectivity
(`diagReducedMap_complexSign_swap`, distinct rays `mk (b i + I b j)` and
`mk (b i - I b j)`) plus index linking (`..._link` / `..._link'` / `..._all`).
Neither `Complex.arg` nor any linearity is used; both `±` branches stay alive
until the probes resolve them.

The unconditional `diagReducedMap_dichotomy` follows, and the headline
`wigner_rigidity` inverts the frame reductions
(`f = projMap (candidateUnitary hf b) ∘ projMap D ∘ diagReducedMap`, with
`b` the standard basis so `bConjVec b = conjVec`) to conclude that every
`TransProbPreserving` self-map of `ℂℙ^{N-1}` is `projMap e` for a `≃ₗᵢ[ℂ]` `e`
(**unitary**) or `projMap e ∘ conjProj` (**antiunitary**). The antiunitary
branch is genuinely present (`conjProj`); ℂ-linearity of `e` is an OUTPUT of the
dichotomy landing on the identity, never assumed; the global sign is forced, not
posited. Its only logical dependencies are the foundational triple
`propext`, `Classical.choice`, and `Quot.sound`.
-/

/-! ## The `Matrix.unitaryGroup` reformulation

`wigner_rigidity` produces a `≃ₗᵢ[ℂ]` witness `e` and states `f = projMap e`
(or `= projMap e ∘ conjProj`). This section restates the theorem in the classic
`∃ U : Matrix.unitaryGroup (Fin N) ℂ, f = U • ·` form, where `U • ·` is the exact
projective action used by `transProbPreserving_unitary` /
`transProb_smul_unitary` (the `MulAction.compHom` of
`Matrix.UnitaryGroup.toEuclideanLinearEquivHom`). The identification is the matrix of the
isometry in the standard basis: `unitaryOfIsometry e := toEuclideanLin.symm e`,
whose columns are `e (basisFun j)`, hence `star M * M = 1` by the isometry
property `e.inner_map_map` and orthonormality of `basisFun`. The antiunitary
branch is kept genuinely present as `U • conjProj p`. -/

/-- The matrix of a linear isometry equivalence in the standard basis of
`EuclideanSpace ℂ (Fin N)`, i.e. the inverse image under the linear equivalence
`Matrix.toEuclideanLin`. Its `toEuclideanLin` is `e` by construction
(`unitaryOfIsometry_toEuclideanLin`); it lies in `unitaryGroup`
(`unitaryOfIsometry_mem`). -/
noncomputable def unitaryOfIsometry
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.toEuclideanLin.symm (e : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))

/-- `toEuclideanLin (unitaryOfIsometry e) = e`: the matrix realises the isometry's
linear map. Immediate from `LinearEquiv.apply_symm_apply`. -/
lemma unitaryOfIsometry_toEuclideanLin
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin (unitaryOfIsometry e)
      = (e : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) :=
  LinearEquiv.apply_symm_apply _ _

/-- Column formula: the `(i, j)` entry of `unitaryOfIsometry e` is the `i`-th
coordinate of `e (basisFun j)`. Evaluate `toEuclideanLin (unitaryOfIsometry e)`
at the standard basis vector `basisFun j` (= `Pi.single j 1` after `ofLp`) and use
`unitaryOfIsometry_toEuclideanLin`. -/
lemma unitaryOfIsometry_apply
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) (i j : Fin N) :
    unitaryOfIsometry e i j = e (EuclideanSpace.basisFun (Fin N) ℂ j) i := by
  have h : Matrix.toEuclideanLin (unitaryOfIsometry e) (EuclideanSpace.basisFun (Fin N) ℂ j)
      = e (EuclideanSpace.basisFun (Fin N) ℂ j) := by
    rw [unitaryOfIsometry_toEuclideanLin]; rfl
  calc unitaryOfIsometry e i j
      = Matrix.mulVec (unitaryOfIsometry e) (Pi.single j (1 : ℂ)) i := by
          rw [Matrix.mulVec_single_one, Matrix.col_apply]
    _ = (Matrix.toEuclideanLin (unitaryOfIsometry e)
          (EuclideanSpace.basisFun (Fin N) ℂ j)).ofLp i := by
          rw [EuclideanSpace.basisFun_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
            PiLp.ofLp_single]
    _ = e (EuclideanSpace.basisFun (Fin N) ℂ j) i := by rw [h]

/-- `unitaryOfIsometry e` is a unitary matrix: `star M * M = 1`, because the
`(j, k)` entry of `star M * M` is `⟪e (basisFun j), e (basisFun k)⟫ =
⟪basisFun j, basisFun k⟫ = δ_{jk}` via `e.inner_map_map` and orthonormality of
`basisFun`. -/
lemma unitaryOfIsometry_mem
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    unitaryOfIsometry e ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  calc ∑ i, (star (unitaryOfIsometry e)) j i * unitaryOfIsometry e i k
      = ∑ i, (starRingEnd ℂ) (e (EuclideanSpace.basisFun (Fin N) ℂ j) i)
          * e (EuclideanSpace.basisFun (Fin N) ℂ k) i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Matrix.star_apply, unitaryOfIsometry_apply, unitaryOfIsometry_apply]
        rfl
    _ = (inner ℂ (e (EuclideanSpace.basisFun (Fin N) ℂ j))
          (e (EuclideanSpace.basisFun (Fin N) ℂ k)) : ℂ) := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [RCLike.inner_apply']
    _ = (inner ℂ (EuclideanSpace.basisFun (Fin N) ℂ j)
          (EuclideanSpace.basisFun (Fin N) ℂ k) : ℂ) := e.inner_map_map _ _
    _ = if j = k then 1 else 0 :=
        orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin N) ℂ).orthonormal j k

/-- The `unitaryGroup` element attached to a linear isometry equivalence. -/
noncomputable def unitaryGroupOfIsometry
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨unitaryOfIsometry e, unitaryOfIsometry_mem e⟩

/-- **Compatibility with the matrix action.** `projMap e` agrees with the `unitaryGroup` ray action
`unitaryGroupOfIsometry e • ·` used by `transProbPreserving_unitary`. Reduce `p`
to `mk p.rep`, push both sides through `projMap_mk` /
`smul_mk_eq_mk_toEuclideanLin`, and note the underlying vectors agree since
`toEuclideanLin (unitaryOfIsometry e) = e`. -/
theorem projMap_eq_smul_unitary
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    projMap e p = unitaryGroupOfIsometry e • p := by
  conv_lhs => rw [← p.mk_rep]
  conv_rhs => rw [← p.mk_rep]
  rw [projMap_mk e p.rep p.rep_nonzero,
      smul_mk_eq_mk_toEuclideanLin (unitaryGroupOfIsometry e) p.rep_nonzero]
  have hvec : Matrix.toEuclideanLin ((unitaryGroupOfIsometry e).val) p.rep = e p.rep := by
    change Matrix.toEuclideanLin (unitaryOfIsometry e) p.rep = e p.rep
    rw [unitaryOfIsometry_toEuclideanLin]; rfl
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨1, by rw [one_smul, hvec]⟩

/-- **HEADLINE (Wigner rigidity, `unitaryGroup` form).** The classic statement:
every transition-probability-preserving self-map of `ℂℙ^{N-1}` is `U • ·` for a
`U : Matrix.unitaryGroup (Fin N) ℂ` (the **unitary** branch) or `U • conjProj ·`
(the **antiunitary** branch), with `U • ·` the same `MulAction` used by
`transProbPreserving_unitary`. Reformulation of `wigner_rigidity` through the
isometry-to-matrix compatibility `projMap_eq_smul_unitary`; no ℂ-linearity is assumed on
`f`, the antiunitary branch is genuinely present, foundational-triple only. -/
theorem wigner_rigidity_unitaryGroup
    (hf : TransProbPreserving f) :
    (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, f p = U • p)
    ∨ (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, f p = U • conjProj p) := by
  rcases wigner_rigidity hf with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨unitaryGroupOfIsometry e,
      fun p => by rw [he p, projMap_eq_smul_unitary e p]⟩
  · exact Or.inr ⟨unitaryGroupOfIsometry e,
      fun p => by rw [he p, projMap_eq_smul_unitary e (conjProj p)]⟩

end Projectivization
