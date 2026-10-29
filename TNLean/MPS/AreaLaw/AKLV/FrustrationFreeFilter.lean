/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.FrustrationFreeClipping
import TNLean.MPS.AreaLaw.AKLV.ClippedHamiltonian
import TNLean.MPS.AreaLaw.AKLV.ChebyshevFilter

/-!
# A physical Chebyshev filter for the original frustration-free ground vector

Separate exterior clipping fixes the original zero-energy vector and retains
half its projector gap. The actual clipping has both the spatial decomposition
and the spectral ceiling needed to construct a Chebyshev polynomial with a rank
bound for that same operator at the original central cut. No clipped target,
first excitation, decomposition, norm bound or filter is supplied.

Source: AKLV, arXiv:1301.1162v1, Section 4, the polynomial construction and
Lemma `l:agsp`, lines 530–663, and frustration-free clipping before Theorem
`t:ent`, lines 810–818.

**Scope restriction (window):** The original window has at least six
interactions and fits in the chain, as in
`docs/paper-gaps/aklv13_two_block_robustness.tex`. The inverse-gap cutoff is
`t ≥ 1024/g`; no final sharp entropy rate without inverse-gap logarithms is
asserted. The corrected polynomial word count is recorded at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
-/

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Classical in
private theorem ff_clipped_hamiltonian_eq {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (t : ℝ) :
    let α : Fin (L - 1) := ⟨a + 1, by omega⟩
    let β : Fin (L - 1) := ⟨a + s - 2, by omega⟩
    aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h (fun _ ↦ 0) t Finset.univ =
      AKLV.twoSidedEnergyTruncation (AKLV.leftCutBlock h α 0)
        (AKLV.middleCutBlock h α β 0 + (h α + h β)) (AKLV.rightCutBlock h β 0) t := by
  intro α β
  let C := aklvRegionalHamiltonians (a + 2) (a + s - 1) h
  have hleft : AKLV.leftCutBlock h α 0 = C 0 := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val < a + 1), h i) -
      (0 : ℂ) • 1 = ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ 0 ≤ i.val ∧ i.val + 1 < a + 2), h i
    simp only [zero_smul, sub_zero]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hmiddle : AKLV.middleCutBlock h α β 0 = C 1 := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      a + 1 < i.val ∧ i.val < a + s - 2), h i) - (0 : ℂ) • 1 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        a + 2 ≤ i.val ∧ i.val + 1 < a + s - 1), h i
    simp only [zero_smul, sub_zero]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hright : AKLV.rightCutBlock h β 0 = C 2 := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦ a + s - 2 < i.val), h i) -
      (0 : ℂ) • 1 = ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        a + s - 1 ≤ i.val ∧ i.val + 1 < L), h i
    simp only [zero_smul, sub_zero]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := i.isLt
    omega
  have hcross : Finset.univ.filter (fun i : Fin (L - 1) ↦
      i.val + 1 ∈ ({a + 2, a + s - 1} : Finset ℕ)) = {α, β} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    change (i.val + 1 = a + 2 ∨ i.val + 1 = a + s - 1) ↔
      i.val = a + 1 ∨ i.val = a + s - 2
    omega
  have hne : α ≠ β := by
    intro heq
    have hv := congrArg Fin.val heq
    change a + 1 = a + s - 2 at hv
    omega
  have hselector : (Finset.univ : Finset (Fin 2)).image
      (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3)) = {0, 2} := by decide
  dsimp only [aklvTwoBlockHamiltonian]
  rw [hselector, Fin.sum_univ_three, hcross, Finset.sum_pair hne]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self,
    or_false, or_true, ite_true, ite_false, zero_add, Complex.ofReal_zero, zero_smul,
    sub_zero]
  rw [AKLV.twoSidedEnergyTruncation, hleft, hmiddle, hright]
  change cfc (fun x : ℝ ↦ min x t) (C 0) + C 1 +
      cfc (fun x : ℝ ↦ min x t) (C 2) + (h α + h β) =
    energyTruncation (C 0) t + (C 1 + (h α + h β)) + energyTruncation (C 2) t
  unfold energyTruncation
  abel

private theorem ff_shorter_window_div_le {s ell : ℕ} (hs : 6 ≤ s) :
    ell / (s - 2) ≤ 2 * (ell / s) + 1 := by
  have hrem : ell < (ell / s + 1) * s :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < s)).mp (Nat.lt_succ_self (ell / s))
  have hs' : s ≤ 2 * (s - 2) := by omega
  have hmul : (ell / s + 1) * s ≤ (2 * (ell / s) + 2) * (s - 2) := by
    nlinarith [Nat.mul_le_mul_left (ell / s + 1) hs']
  have hdiv : ell / (s - 2) < 2 * (ell / s) + 2 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < s - 2)).mpr (hrem.trans_le hmul)
  omega

open Classical in
/-- The original frustration-free unit vector is fixed by one actual physical
Chebyshev filter with both its shrinking and same-cut operator Schmidt rank
bounds. All clipping, support, gap and spectral ceiling data are derived from
the original nearest-neighbour positive contractions.
AKLV, arXiv:1301.1162v1, Section 4, Lemma `l:agsp`, lines 530–663,
and the clipping preceding Theorem `t:ent`, lines 810–818. -/
theorem exists_aklv_frustrationFree_chebyshev_filter {L q a s : ℕ}
    (hq : 1 ≤ q) (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (g t : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) (ht : 1024 / g ≤ t)
    (hzero : (∑ i, h i) *ᵥ WithLp.ofLp Ω = 0)
    (hgap : ((∑ i, h i) - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef) :
    let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h (fun _ ↦ 0) t Finset.univ
    B.PosSemidef ∧ B ≤ ∑ i, h i ∧ ‖B‖ ≤ 2 * t + s ∧
      B *ᵥ WithLp.ofLp Ω = 0 ∧
      (B - ((g / 2 : ℝ) : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef ∧
      ∀ ell : ℕ, ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval 0 = 1 ∧
        let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
        toEuclideanLin K Ω = Ω ∧
        ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
          2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((g / 2) / (2 * t + s))) ∧
        operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
          (leftBlock L (a + s / 2)) K) ≤
            (q * (ell + 1)) ^ (16 * (ell / (s - 2) + Nat.sqrt ell + 1)) ∧
        operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
          (leftBlock L (a + s / 2)) K) ≤
            (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1)) ∧
        ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
          ⟪Ω, toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖toEuclideanLin K ψ‖ ^ 2 ≤
            (2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((g / 2) / (2 * t + s)))) ^ 2 := by
  intro B
  let α : Fin (L - 1) := ⟨a + 1, by omega⟩
  let β : Fin (L - 1) := ⟨a + s - 2, by omega⟩
  have heq := ff_clipped_hamiltonian_eq hs ha h t
  obtain ⟨hBpos, hBH, hBΩ, hBgap⟩ :=
    AKLV.frustrationFree_twoSidedEnergyTruncation_ground_gap h hsupp h0 h1 α β
      (by dsimp only [α, β]; omega) Ω hΩ g t hg hg1 ht hzero hgap
  rw [← heq] at hBpos hBH hBΩ hBgap
  have ht0 : 0 ≤ t := le_trans (by positivity : 0 ≤ 1024 / g) ht
  have he (j : Fin 3) : (aklvNormalizationHamiltonians a s h j -
      (((fun _ : Fin 3 ↦ (0 : ℝ)) j) : ℂ) • 1).PosSemidef := by
    simp only [Complex.ofReal_zero, zero_smul, sub_zero]
    exact Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)
  have hBnorm := (aklv_clipped_hamiltonian_posSemidef_norm_le hs ha h h0 h1
    (fun _ ↦ 0) he le_rfl ht0).2
  have hupper (x : ℝ) (hx : x ∈ spectrum ℝ B) : x ≤ 2 * t + s :=
    (le_abs_self x).trans ((by simpa only [Real.norm_eq_abs] using
      spectrum.norm_le_norm_of_mem hx : |x| ≤ ‖B‖).trans hBnorm)
  have ht1 : 1 ≤ t :=
    (show (1 : ℝ) ≤ 1024 / g from (le_div_iff₀ hg).mpr (by linarith)).trans ht
  have hgu : 0 + g / 2 ≤ 2 * t + s := by
    have hs0 : (0 : ℝ) ≤ s := by positivity
    linarith
  refine ⟨hBpos, hBH, hBnorm, hBΩ, hBgap, ?_⟩
  intro ell
  let H := fun j : Fin (s - 2) ↦ h ⟨a + 1 + j.val, by omega⟩
  obtain ⟨HL, HR, hL, hR, hmiddle, hdecomp, hcenter⟩ :=
    aklv_clipped_hamiltonian_decomposition hs ha h hsupp (fun _ ↦ 0) t
  have hR' : Entropy.IsSupportedOn HR (interval L (a + 1 + (s - 2)) L) := by
    convert hR using 1
    congr 1
    omega
  obtain ⟨p, hdegree, hp0, hfix, herr, hrank, horth⟩ :=
    exists_aklv_chebyshev_filter (E0 := 0) (gap := g / 2) (u := 2 * t + s)
      hq (by omega : 0 < s - 2)
      (by omega : a + 1 + (s - 2) + 1 ≤ L) H hmiddle HL HR
      (by simpa only [Nat.add_assoc] using hL) hR'
      (by rwa [← hdecomp]) hΩ
      (by simpa only [← hdecomp, Complex.ofReal_zero, zero_smul] using hBΩ)
      (by simpa only [← hdecomp, Complex.ofReal_zero, zero_smul, sub_zero] using hBgap)
      (by positivity : 0 < g / 2) hgu (by rwa [← hdecomp]) ell
  rw [← hdecomp] at hfix herr hrank horth
  rw [hcenter] at hrank
  have hexponent : 16 * (ell / (s - 2) + Nat.sqrt ell + 1) ≤
      32 * (ell / s + Nat.sqrt ell + 1) := by
    have := ff_shorter_window_div_le (ell := ell) hs
    omega
  refine ⟨p, hdegree, hp0, hfix, ?_, hrank,
    hrank.trans (Nat.pow_le_pow_right (by nlinarith : 1 ≤ q * (ell + 1)) hexponent), ?_⟩
  · simpa only [sub_zero] using herr
  · intro ψ hψ hperp
    simpa only [sub_zero] using horth ψ hψ hperp

end TNLean.MPS.AreaLaw
