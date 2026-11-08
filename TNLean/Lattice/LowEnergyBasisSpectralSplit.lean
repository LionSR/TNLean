/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyBasisSimpleSpectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Spectral splits in the construction of a low-energy basis

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1698–1708, refines eigenspaces
of compressed local terms. Compressing two operators introduces cross terms in their
commutator. These terms must be retained in the refinement argument.

For every finite family of Hermitian operators, the module either proves that all operators
are scalar or constructs a proper orthogonal spectral projection. Choosing a term of maximal
spectral spread and combining the spread and commutator estimates removes the inverse spread
from the cross-block bound. The compression estimate retains both cross terms and replaces
the decay kernel by its square root. The full recursive basis construction is separate.

**Local fix (cross terms and decay rate):** Refinement retains the two cross terms omitted
from the source sketch and weakens the exponential rate at each step. Documented in
`docs/paper-gaps/hastings05_two_dim_ground_basis.tex`.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

section Compression

variable {A : Type*} [NormedRing A]

/-- The commutator of two compressions includes two cross terms.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem commutator_compression_eq (P B C : A) (hP : P * P = P) :
    P * B * P * (P * C * P) - P * C * P * (P * B * P) =
      P * (B * C - C * B) * P -
        (P * B * (1 - P)) * ((1 - P) * C * P) +
        (P * C * (1 - P)) * ((1 - P) * B * P) := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP]
  have h1 : P * B * P * (P * C * P) = P * B * (P * P) * C * P := by
    simp only [mul_assoc]
  have h2 : P * C * P * (P * B * P) = P * C * (P * P) * B * P := by
    simp only [mul_assoc]
  rw [h1, h2, hP]
  have h3 : (P * B * (1 - P)) * ((1 - P) * C * P) =
      P * B * ((1 - P) * (1 - P)) * C * P := by simp only [mul_assoc]
  have h4 : (P * C * (1 - P)) * ((1 - P) * B * P) =
      P * C * ((1 - P) * (1 - P)) * B * P := by simp only [mul_assoc]
  rw [h3, h4, hQ]
  noncomm_ring

/-- A contraction compression does not increase the operator norm.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_compression_le (P B : A) (hP : ‖P‖ ≤ 1) : ‖P * B * P‖ ≤ ‖B‖ := by
  calc ‖P * B * P‖ ≤ ‖P‖ * ‖B‖ * ‖P‖ := norm_mul₃_le
    _ ≤ 1 * ‖B‖ * 1 := by gcongr
    _ = ‖B‖ := by ring

/-- A scalar centre contributes no cross-block operator. The hypothesis `P c Q = 0`
is satisfied by scalar multiples of the identity for orthogonal projections.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_crossBlock_le_of_center (P Q B c : A) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hc : P * c * Q = 0) {ρ : ℝ} (hB : ‖B - c‖ ≤ ρ) : ‖P * B * Q‖ ≤ ρ := by
  have hid : P * (B - c) * Q = P * B * Q := by
    rw [mul_sub, sub_mul, hc, sub_zero]
  rw [← hid]
  calc ‖P * (B - c) * Q‖ ≤ ‖P‖ * ‖B - c‖ * ‖Q‖ := norm_mul₃_le
    _ ≤ 1 * ‖B - c‖ * 1 := by gcongr
    _ ≤ ρ := by simpa using hB

/-- The two cross terms bound the change in a compressed commutator.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_compression_le (P B C : A) (hPP : P * P = P)
    (hP : ‖P‖ ≤ 1) :
    ‖P * B * P * (P * C * P) - P * C * P * (P * B * P)‖ ≤
      ‖B * C - C * B‖ + ‖P * B * (1 - P)‖ * ‖(1 - P) * C * P‖ +
        ‖P * C * (1 - P)‖ * ‖(1 - P) * B * P‖ := by
  rw [commutator_compression_eq P B C hPP]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (norm_compression_le _ _ hP) (norm_mul_le _ _)))
    (norm_mul_le _ _))

end Compression

/-- Combining a spectral-spread bound and a commutator bound eliminates the spread
from the cross-block estimate. Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem le_sqrt_mul_of_le_spread {x ρ C f : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hf : 0 ≤ f) (hspread : x ≤ ρ) (hcomm : ρ * x ≤ C * f ^ 2) :
    x ≤ Real.sqrt C * f := by
  have hsq : x ^ 2 ≤ (Real.sqrt C * f) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    nlinarith [mul_le_mul_of_nonneg_right hspread hx]
  exact (pow_le_pow_iff_left₀ hx (mul_nonneg (Real.sqrt_nonneg _) hf) two_ne_zero).mp hsq

/-- The triangle inequality preserves exponential decay through the anchor of a split.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exp_dist_half_mul_le {ι : Type*} [PseudoMetricSpace ι] {γ : ℝ}
    (hγ : 0 ≤ γ) (i j k : ι) :
    Real.exp (-(γ * dist i j) / 2) * Real.exp (-(γ * dist j k) / 2) ≤
      Real.exp (-(γ * dist i k) / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (dist_triangle i j k) hγ]

/-- Compressing after a spectral split preserves a uniform exponential commutator
estimate, with half the decay rate. The two displayed cross-block estimates are the
inputs supplied by the spectral-spread and spectral-gap bounds.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_compression_le_exp {A ι : Type*} [NormedRing A]
    [PseudoMetricSpace ι] (P : A) (hPP : P * P = P) (hP : ‖P‖ ≤ 1)
    (B : ι → A) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {C D γ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hγ : 0 ≤ γ) (j : ι)
    (hcomm : ∀ i k, ‖B i * B k - B k * B i‖ ≤
      C * w i * w k * Real.exp (-(γ * dist i k)))
    (hcross : ∀ i, ‖P * B i * (1 - P)‖ ≤
      D * w i * Real.exp (-(γ * dist i j) / 2))
    (hcross' : ∀ i, ‖(1 - P) * B i * P‖ ≤
      D * w i * Real.exp (-(γ * dist i j) / 2)) (i k : ι) :
    ‖P * B i * P * (P * B k * P) - P * B k * P * (P * B i * P)‖ ≤
      (C + 2 * D ^ 2) * w i * w k * Real.exp (-(γ * dist i k) / 2) := by
  have hprod (a b : ι) :
      ‖P * B a * (1 - P)‖ * ‖(1 - P) * B b * P‖ ≤
        D ^ 2 * w a * w b * Real.exp (-(γ * dist a b) / 2) := by
    have hwa := hw a
    have hwb := hw b
    calc
      _ ≤ (D * w a * Real.exp (-(γ * dist a j) / 2)) *
          (D * w b * Real.exp (-(γ * dist b j) / 2)) :=
        mul_le_mul (hcross a) (hcross' b) (norm_nonneg _) (by positivity)
      _ = (D ^ 2 * w a * w b) *
          (Real.exp (-(γ * dist a j) / 2) * Real.exp (-(γ * dist j b) / 2)) := by
        rw [dist_comm b j]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_dist_half_mul_le hγ a j b) (by positivity)
  have hwi := hw i
  have hwk := hw k
  have hdecay : Real.exp (-(γ * dist i k)) ≤ Real.exp (-(γ * dist i k) / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hγ (dist_nonneg (x := i) (y := k))]
  have hc := (hcomm i k).trans
    (mul_le_mul_of_nonneg_left hdecay (by positivity : 0 ≤ C * w i * w k))
  have h1 := hprod i k
  have h2 := hprod k i
  rw [dist_comm k i] at h2
  exact (norm_commutator_compression_le P (B i) (B k) hPP hP).trans (by nlinarith)

/-- An adjacent gap is at least the total spread divided by the number of gaps.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exists_spread_div_le_adjacent_gap (r : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, (r 0 - r n) / n ≤ r k - r (k + 1) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨k, hk, hgap⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hn.ne')
    (f := fun _ ↦ (r 0 - r n) / n)
    (g := fun k ↦ r k - r (k + 1)) (by
      rw [Finset.sum_range_sub', Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact le_of_eq (mul_div_cancel₀ _ hnR))
  exact ⟨k, Finset.mem_range.mp hk, hgap⟩

/-- The adjacent-gap estimate for a finite ordered spectrum.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exists_adjacent_gap_fin {n : ℕ} (hn : 0 < n) (r : Fin (n + 1) → ℝ) :
    ∃ k : Fin n, (r 0 - r (Fin.last n)) / n ≤ r k.castSucc - r k.succ := by
  let g : ℕ → ℝ := fun k ↦ r ⟨min k n, Nat.lt_succ_of_le (Nat.min_le_right k n)⟩
  obtain ⟨k, hk, hgap⟩ := exists_spread_div_le_adjacent_gap g hn
  refine ⟨⟨k, hk⟩, ?_⟩
  simpa [g, Fin.last, Nat.min_eq_left (Nat.le_of_lt hk),
    Nat.min_eq_left (Nat.succ_le_of_lt hk)] using hgap

/-- An antitone nonconstant spectrum admits a nontrivial binary split whose cross
spectral gaps are at least the spread divided by the dimension minus one.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exists_antitone_spectral_split {n : ℕ} (hn : 0 < n)
    (r : Fin (n + 1) → ℝ) (hr : Antitone r) (hspread : r (Fin.last n) < r 0) :
    ∃ k : Fin n, 0 < (r 0 - r (Fin.last n)) / n ∧
      ∀ a b : Fin (n + 1), a.val ≤ k.val → k.val < b.val →
        (r 0 - r (Fin.last n)) / n ≤ r a - r b := by
  obtain ⟨k, hk⟩ := exists_adjacent_gap_fin hn r
  refine ⟨k, div_pos (sub_pos.mpr hspread) (by exact_mod_cast hn), ?_⟩
  intro a b ha hb
  have ha' : a ≤ k.castSucc := ha
  have hb' : k.succ ≤ b := by change k.val + 1 ≤ b.val; omega
  exact hk.trans (sub_le_sub (hr ha') (hr hb'))

section BasisProjection

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι] [DecidableEq ι]

/-- The orthogonal projection onto selected vectors of an orthonormal basis.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
noncomputable def basisSplitProjection (b : OrthonormalBasis ι ℂ E) (s : Finset ι) :
    E →L[ℂ] E := ∑ i ∈ s, InnerProductSpace.rankOne ℂ (b i) (b i)

omit [CompleteSpace E] [DecidableEq ι] in
open Classical in
/-- The selected-basis projection is the orthogonal projection onto its actual span.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem basisSplitProjection_eq_starProjection (b : OrthonormalBasis ι ℂ E)
    (s : Finset ι) :
    basisSplitProjection b s = (Submodule.span ℂ (s.image b : Set E)).starProjection := by
  classical
  have h := (OrthonormalBasis.span b.orthonormal s).starProjection_eq_sum_rankOne
  unfold basisSplitProjection
  rw [← Finset.sum_coe_sort s (fun i ↦ InnerProductSpace.rankOne ℂ (b i) (b i))]
  simpa only [OrthonormalBasis.span_apply] using h.symm

omit [CompleteSpace E] [DecidableEq ι] in
/-- Spectral splitting gives a contraction projection, without an assumed norm bound.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_basisSplitProjection_le (b : OrthonormalBasis ι ℂ E) (s : Finset ι) :
    ‖basisSplitProjection b s‖ ≤ 1 := by
  classical
  rw [basisSplitProjection_eq_starProjection]
  exact Submodule.starProjection_norm_le _

omit [CompleteSpace E] in
/-- The selected projection keeps exactly its recorded basis vectors.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
@[simp] theorem basisSplitProjection_apply_basis (b : OrthonormalBasis ι ℂ E)
    (s : Finset ι) (i : ι) :
    basisSplitProjection b s (b i) = if i ∈ s then b i else 0 := by
  simp [basisSplitProjection, _root_.sum_apply, InnerProductSpace.rankOne_apply,
    b.inner_eq_ite]

omit [DecidableEq ι] in
/-- The selected-basis projection is an orthogonal projection.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem isStarProjection_basisSplitProjection (b : OrthonormalBasis ι ℂ E)
    (s : Finset ι) : IsStarProjection (basisSplitProjection b s) := by
  classical
  rw [basisSplitProjection_eq_starProjection]
  exact isStarProjection_starProjection

omit [CompleteSpace E] in
/-- The remaining basis vectors span the orthogonal complementary projection.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem basisSplitProjection_compl (b : OrthonormalBasis ι ℂ E) (s : Finset ι) :
    basisSplitProjection b sᶜ = 1 - basisSplitProjection b s := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  change basisSplitProjection b sᶜ (b i) = (1 - basisSplitProjection b s) (b i)
  by_cases hi : i ∈ s <;> simp [hi]

omit [CompleteSpace E] in
/-- The cross-block operator is the actual sum of its matrix coefficients.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem basisSplitProjection_mul_mul_compl (b : OrthonormalBasis ι ℂ E)
    (s : Finset ι) (B : E →L[ℂ] E) :
    basisSplitProjection b s * B * (1 - basisSplitProjection b s) =
      ∑ a ∈ s, ∑ c ∈ sᶜ, ⟪b a, B (b c)⟫_ℂ •
        InnerProductSpace.rankOne ℂ (b a) (b c) := by
  rw [← basisSplitProjection_compl]
  have hterm (a c : ι) :
      InnerProductSpace.rankOne ℂ (b a) (b a) * B *
          InnerProductSpace.rankOne ℂ (b c) (b c) =
        ⟪b a, B (b c)⟫_ℂ • InnerProductSpace.rankOne ℂ (b a) (b c) := by
    ext x
    simp [mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      smul_smul, mul_comm]
  simp only [basisSplitProjection, Finset.sum_mul, Finset.mul_sum, hterm]
  exact Finset.sum_comm

omit [CompleteSpace E] in
/-- Separated spectral coefficients control the norm of the actual cross-block operator.
The dimension factor is the number of matrix coefficients across the cut.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_basisSplitProjection_mul_mul_compl_le (b : OrthonormalBasis ι ℂ E)
    (s : Finset ι) (B : E →L[ℂ] E) {m : ℝ}
    (hcoeff : ∀ a ∈ s, ∀ c ∈ sᶜ, ‖⟪b a, B (b c)⟫_ℂ‖ ≤ m) :
    ‖basisSplitProjection b s * B * (1 - basisSplitProjection b s)‖ ≤
      (s.card : ℝ) * (sᶜ.card : ℝ) * m := by
  rw [basisSplitProjection_mul_mul_compl]
  calc
    _ ≤ ∑ a ∈ s, ∑ c ∈ sᶜ,
        ‖⟪b a, B (b c)⟫_ℂ • InnerProductSpace.rankOne ℂ (b a) (b c)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _a ∈ s, ∑ _c ∈ sᶜ, m := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro c hc
      simpa only [norm_smul, InnerProductSpace.norm_rankOne,
        b.orthonormal.1 a, b.orthonormal.1 c, one_mul, mul_one] using hcoeff a ha c hc
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- A separated spectral cut bounds its actual cross-block operator by the commutator.
Repeated eigenvalues on either side of the cut are allowed.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_basisSplitProjection_cross_le_commutator {A : E →L[ℂ] E}
    (hA : IsSelfAdjoint A) (b : OrthonormalBasis ι ℂ E) (r : ι → ℝ)
    (hAv : ∀ a, A (b a) = (r a : ℂ) • b a) (s : Finset ι)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ a ∈ s, ∀ c ∈ sᶜ, δ ≤ |r a - r c|)
    (B : E →L[ℂ] E) :
    ‖basisSplitProjection b s * B * (1 - basisSplitProjection b s)‖ ≤
      (s.card : ℝ) * (sᶜ.card : ℝ) * (‖A * B - B * A‖ / δ) := by
  apply norm_basisSplitProjection_mul_mul_compl_le
  intro a ha c hc
  have hne : r a ≠ r c := by
    intro heq
    have hg := hgap a ha c hc
    rw [heq, sub_self, abs_zero] at hg
    linarith
  calc
    ‖⟪b a, B (b c)⟫_ℂ‖ ≤ ‖A * B - B * A‖ / |r a - r c| := by
      simpa only [b.orthonormal.1 a, b.orthonormal.1 c, mul_one] using
        norm_inner_le_norm_commutator_div hA B (hAv a) (hAv c) hne
    _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) hδ (hgap a ha c hc)

/-- A nonconstant self-adjoint operator has an actual nontrivial spectral projection
with a dimension-controlled commutator estimate across its two spectral blocks.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exists_selfAdjoint_spectral_split [FiniteDimensional ℂ E]
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {n : ℕ} (hn : 0 < n)
    (hdim : Module.finrank ℂ E = n + 1)
    (hspread : hA.isSymmetric.eigenvalues hdim (Fin.last n) <
      hA.isSymmetric.eigenvalues hdim 0) :
    ∃ P : E →L[ℂ] E, IsStarProjection P ∧ ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1 ∧
      P ≠ 0 ∧ P ≠ 1 ∧ ∀ B : E →L[ℂ] E,
        ‖P * B * (1 - P)‖ ≤
          ((n + 1 : ℕ) : ℝ) ^ 2 * n * ‖A * B - B * A‖ /
            (hA.isSymmetric.eigenvalues hdim 0 -
              hA.isSymmetric.eigenvalues hdim (Fin.last n)) := by
  classical
  let b := hA.isSymmetric.eigenvectorBasis hdim
  let r := hA.isSymmetric.eigenvalues hdim
  obtain ⟨k, hδ, hcut⟩ := exists_antitone_spectral_split hn r
    (hA.isSymmetric.eigenvalues_antitone hdim) hspread
  let s : Finset (Fin (n + 1)) := Finset.univ.filter fun a ↦ a.val ≤ k.val
  have h0 : (0 : Fin (n + 1)) ∈ s := by simp [s]
  have hlast : Fin.last n ∉ s := by simp only [s, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.val_last]; omega
  refine ⟨basisSplitProjection b s, isStarProjection_basisSplitProjection b s,
    norm_basisSplitProjection_le b s, ?_, ?_, ?_, ?_⟩
  · rw [← basisSplitProjection_compl]
    exact norm_basisSplitProjection_le b sᶜ
  · intro heq
    have hvec : b 0 = 0 := by
      simpa [h0] using congrArg (fun T : E →L[ℂ] E ↦ T (b 0)) heq
    have hnorm := b.orthonormal.1 0
    rw [hvec, norm_zero] at hnorm
    norm_num at hnorm
  · intro heq
    have hvec : b (Fin.last n) = 0 := by
      have he := congrArg (fun T : E →L[ℂ] E ↦ T (b (Fin.last n))) heq
      simpa [hlast] using he.symm
    have hnorm := b.orthonormal.1 (Fin.last n)
    rw [hvec, norm_zero] at hnorm
    norm_num at hnorm
  · intro B
    have hg : ∀ a ∈ s, ∀ c ∈ sᶜ, (r 0 - r (Fin.last n)) / n ≤ |r a - r c| := by
      intro a ha c hc
      have ha' := (Finset.mem_filter.mp ha).2
      have hc' : k.val < c.val := by
        have : c ∉ s := Finset.mem_compl.mp hc
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at this
        exact this
      exact (hcut a c ha' hc').trans (le_abs_self _)
    have hb := norm_basisSplitProjection_cross_le_commutator hA b r
      (hA.isSymmetric.apply_eigenvectorBasis hdim) s hδ hg B
    have hs : (s.card : ℝ) ≤ n + 1 := by
      exact_mod_cast (show s.card ≤ n + 1 by simpa using s.card_le_univ)
    have hsc : (sᶜ.card : ℝ) ≤ n + 1 := by
      exact_mod_cast (show sᶜ.card ≤ n + 1 by simpa using sᶜ.card_le_univ)
    have hd : 0 < r 0 - r (Fin.last n) := sub_pos.mpr hspread
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    calc
      _ ≤ (s.card : ℝ) * (sᶜ.card : ℝ) * (‖A * B - B * A‖ / ((r 0 - r (Fin.last n)) / n)) := hb
      _ ≤ (n + 1 : ℝ) ^ 2 * (‖A * B - B * A‖ / ((r 0 - r (Fin.last n)) / n)) := by
        gcongr
        nlinarith [mul_le_mul hs hsc (Nat.cast_nonneg sᶜ.card) (by positivity : (0 : ℝ) ≤ n + 1)]
      _ = _ := by
        dsimp only [r]
        push_cast
        field_simp

omit [CompleteSpace E] in
/-- A diagonal operator is bounded by the largest modulus of its diagonal entries.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_le_of_diagonal_basis {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℂ E)
    (T : E →L[ℂ] E) (r : Fin (n + 1) → ℂ) (hT : ∀ a, T (b a) = r a • b a)
    {M : ℝ} (hM : 0 ≤ M) (hr : ∀ a, ‖r a‖ ≤ M) : ‖T‖ ≤ M := by
  have heq : shiftPart b T 0 = T := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro a
    change shiftPart b T 0 (b a) = T (b a)
    simp [shiftPart_apply, b.inner_eq_ite, hT, inner_smul_right]
  rw [← heq]
  apply norm_shiftPart_le b.orthonormal T 0 hM
  intro a
  simpa [hT, inner_smul_right] using hr a

/-- Subtracting the least eigenvalue leaves norm at most the full spectral spread.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_sub_min_eigenvalue_le_spread [FiniteDimensional ℂ E]
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {n : ℕ}
    (hdim : Module.finrank ℂ E = n + 1) :
    ‖A - (hA.isSymmetric.eigenvalues hdim (Fin.last n) : ℂ) • 1‖ ≤
      hA.isSymmetric.eigenvalues hdim 0 - hA.isSymmetric.eigenvalues hdim (Fin.last n) := by
  let b := hA.isSymmetric.eigenvectorBasis hdim
  let r := hA.isSymmetric.eigenvalues hdim
  have hr := hA.isSymmetric.eigenvalues_antitone hdim
  have hlast (a : Fin (n + 1)) : r (Fin.last n) ≤ r a := hr (Fin.le_last a)
  have hfirst (a : Fin (n + 1)) : r a ≤ r 0 := hr (Fin.zero_le a)
  apply norm_le_of_diagonal_basis b _ (fun a ↦ ((r a - r (Fin.last n) : ℝ) : ℂ))
  · intro a
    have hab : A (b a) = (r a : ℂ) • b a :=
      hA.isSymmetric.apply_eigenvectorBasis hdim a
    change A (b a) - (r (Fin.last n) : ℂ) • b a =
      ((r a - r (Fin.last n) : ℝ) : ℂ) • b a
    rw [hab, Complex.ofReal_sub, sub_smul]
  · exact sub_nonneg.mpr (hfirst (Fin.last n))
  · intro a
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hlast a))]
      using sub_le_sub_right (hfirst a) (r (Fin.last n))

/-- A finite normalized Hermitian family either consists of scalars or admits a
proper spectral split with a uniform square-root commutator bound. No inverse spectral
spread occurs in the conclusion. Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem exists_family_spectral_split [FiniteDimensional ℂ E]
    {κ : Type*} [Finite κ] (B : κ → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i))
    {n : ℕ} (hn : 0 < n) (hdim : Module.finrank ℂ E = n + 1)
    {C : ℝ} (hC : 0 ≤ C) (f : κ → κ → ℝ) (hf : ∀ i j, 0 ≤ f i j)
    (hsymm : ∀ i j, f i j = f j i)
    (hcomm : ∀ i j, ‖B i * B j - B j * B i‖ ≤ C * f i j) :
    (∀ i, ∃ c : ℝ, B i = (c : ℂ) • 1) ∨
      ∃ (P : E →L[ℂ] E) (j : κ), IsStarProjection P ∧ ‖P‖ ≤ 1 ∧ ‖1 - P‖ ≤ 1 ∧
        P ≠ 0 ∧ P ≠ 1 ∧ ∀ i,
          ‖P * B i * (1 - P)‖ ≤
            Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 3 * C) * Real.sqrt (f i j) ∧
          ‖(1 - P) * B i * P‖ ≤
            Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 3 * C) * Real.sqrt (f i j) := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  by_cases hκ : Nonempty κ
  · let _ := hκ
    let r (i : κ) := (hB i).isSymmetric.eigenvalues hdim
    let spread (i : κ) := r i 0 - r i (Fin.last n)
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ spread Finset.univ_nonempty
    have hmax (i : κ) : spread i ≤ spread j := hj i (Finset.mem_univ i)
    have hcenter (i : κ) : ‖B i - (r i (Fin.last n) : ℂ) • 1‖ ≤ spread j :=
      (norm_sub_min_eigenvalue_le_spread (hB i) hdim).trans (hmax i)
    by_cases hρ : 0 < spread j
    · right
      obtain ⟨P, hP, hPn, hQn, hP0, hP1, hcross⟩ :=
        exists_selfAdjoint_spectral_split (hB j) hn hdim (sub_pos.mp hρ)
      have hPP : P * P = P := hP.isIdempotentElem.eq
      have hbound (i : κ) : ‖P * B i * (1 - P)‖ ≤
          Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 3 * C) * Real.sqrt (f i j) := by
        have hc : P * ((r i (Fin.last n) : ℂ) • 1) * (1 - P) = 0 := by
          ext x
          have hPx : P (P x) = P x := congrArg (fun T : E →L[ℂ] E ↦ T x) hPP
          change P ((r i (Fin.last n) : ℂ) • (x - P x)) = 0
          rw [map_smul, map_sub, hPx, sub_self, smul_zero]
        have hsmall := norm_crossBlock_le_of_center P (1 - P) (B i)
          ((r i (Fin.last n) : ℂ) • 1) hPn hQn hc (hcenter i)
        have hlarge : spread j * ‖P * B i * (1 - P)‖ ≤
            (((n + 1 : ℕ) : ℝ) ^ 3 * C) * f i j := by
          have h := (le_div_iff₀ hρ).mp (hcross (B i))
          have hcomm' := hcomm j i
          rw [hsymm j i] at hcomm'
          have hdim' : ((n + 1 : ℕ) : ℝ) ^ 2 * n ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := by
            push_cast
            nlinarith [sq_nonneg (n : ℝ)]
          calc
            _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * n * ‖B j * B i - B i * B j‖ := by
              simpa only [mul_comm, spread, r] using h
            _ ≤ (((n + 1 : ℕ) : ℝ) ^ 2 * n) * (C * f i j) :=
              mul_le_mul_of_nonneg_left hcomm' (by positivity)
            _ ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * (C * f i j) :=
              mul_le_mul_of_nonneg_right hdim' (mul_nonneg hC (hf i j))
            _ = _ := by ring
        apply le_sqrt_mul_of_le_spread (norm_nonneg _) (by positivity) (Real.sqrt_nonneg _)
          hsmall
        simpa only [Real.sq_sqrt (hf i j)] using hlarge
      refine ⟨P, j, hP, hPn, hQn, hP0, hP1, fun i ↦ ⟨hbound i, ?_⟩⟩
      have hrev : (1 - P) * B i * P = star (P * B i * (1 - P)) := by
        simp only [star_mul, star_sub, star_one, hP.isSelfAdjoint.star_eq, (hB i).star_eq]
        simp only [mul_assoc]
      rw [hrev, ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
      exact hbound i
    · left
      intro i
      refine ⟨r i (Fin.last n), sub_eq_zero.mp (norm_eq_zero.mp ?_)⟩
      exact le_antisymm ((hcenter i).trans (le_of_not_gt hρ)) (norm_nonneg _)
  · left
    intro i
    exact (hκ ⟨i⟩).elim

end BasisProjection

/-- Compression preserves a symmetric decay kernel after taking its square root.
The multiplicative triangle inequality also covers disconnected graph metrics.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem norm_commutator_compression_le_kernel {A ι : Type*} [NormedRing A]
    (P : A) (hPP : P * P = P) (hP : ‖P‖ ≤ 1) (B : ι → A)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (f : ι → ι → ℝ)
    (hf0 : ∀ i k, 0 ≤ f i k) (hf1 : ∀ i k, f i k ≤ 1)
    (hsymm : ∀ i k, f i k = f k i)
    (htriangle : ∀ i j k, f i j * f j k ≤ f i k) (j : ι)
    (hcomm : ∀ i k, ‖B i * B k - B k * B i‖ ≤ C * f i k)
    (hcross : ∀ i, ‖P * B i * (1 - P)‖ ≤ D * Real.sqrt (f i j))
    (hcross' : ∀ i, ‖(1 - P) * B i * P‖ ≤ D * Real.sqrt (f i j)) (i k : ι) :
    ‖P * B i * P * (P * B k * P) - P * B k * P * (P * B i * P)‖ ≤
      (C + 2 * D ^ 2) * Real.sqrt (f i k) := by
  have hprod (a b : ι) :
      ‖P * B a * (1 - P)‖ * ‖(1 - P) * B b * P‖ ≤
        D ^ 2 * Real.sqrt (f a b) := by
    calc
      _ ≤ (D * Real.sqrt (f a j)) * (D * Real.sqrt (f b j)) :=
        mul_le_mul (hcross a) (hcross' b) (norm_nonneg _) (by positivity)
      _ = D ^ 2 * Real.sqrt (f a j * f j b) := by
        rw [hsymm b j, Real.sqrt_mul (hf0 a j)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (htriangle a j b)) (sq_nonneg D)
  have hc := (hcomm i k).trans
    (mul_le_mul_of_nonneg_left (Real.le_sqrt_self_iff.mpr (hf1 i k)) hC)
  have h1 := hprod i k
  have h2 := hprod k i
  rw [hsymm k i] at h2
  exact (norm_commutator_compression_le P (B i) (B k) hPP hP).trans (by nlinarith)

end TNLean.Lattice
