/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChebyshevAGSP.ClippedHamiltonian
import TNLean.MPS.AreaLaw.ChebyshevAGSP.SchmidtRank.PolynomialRank
import TNLean.MPS.AreaLaw.ChebyshevAGSP.NormalizedChain
import QICLean.ManyBody.Hamiltonian.FrustrationFree

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

It also contains the following results.

* `TNLean.MPS.AreaLaw.AKLV.frustrationFree_twoSidedEnergyTruncation_ground_gap`: exact ground-vector
  preservation for frustration-free clipping.
-/

open ManyBody (interval)

section FrustrationFreeClipping

/-!
## Exact ground-vector preservation for frustration-free clipping

The actual separate exterior clipping of a positive nearest-neighbour chain
preserves its original zero-energy unit ground vector exactly. At cutoff
`t ≥ 1024/g`, the same vector has projector gap at least `g/2` for the clipped
Hamiltonian. Regional positivity, commutation, reconstruction and the clipped
order comparison are derived from the original supported positive contractions.

Source: AKLV, arXiv:1301.1162v1, Section 4, frustration-free clipping preceding
Theorem 4.3 (`t:ent`), `1dfrustrated34.tex`, lines 810–818. The inverse-gap cutoff
uses the accepted Theorem 6.1(a) estimate at original energy zero. This result
asserts no final entropy rate, parameter optimization, or detectability argument.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- Separate exterior clipping preserves the original frustration-free ground
vector and gives a gap of at least half the original gap at cutoff `1024/g`.
The boundary bonds `a < b` are retained, the bonds strictly before `a` and
strictly after `b` form the clipped exteriors, and the intervening bonds are
unchanged. All three existing cut blocks have zero regional shift.

Source: AKLV, arXiv:1301.1162v1, Section 4, lines 810–818, and Theorem 6.1(a).
The source's unique-ground-vector setting is expressed by the original
projector-gap hypothesis; no gap or comparison for the clipped operator is supplied. -/
lemma frustrationFree_twoSidedEnergyTruncation_ground_gap {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (g t : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) (ht : 1024 / g ≤ t)
    (hzero : Ω ∈ Φ.zeroSpace)
    (hgap : (Φ.hamiltonian - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef) :
    let X := leftCutBlock Φ a 0
    let N := middleCutBlock Φ a b 0
    let Y := rightCutBlock Φ b 0
    let K := Matrix.twoSidedEnergyTruncation X (N + (Φ.term a + Φ.term b)) Y t
    K.PosSemidef ∧ K ≤ Φ.hamiltonian ∧ K *ᵥ WithLp.ofLp Ω = 0 ∧
      (K - ((g / 2 : ℝ) : ℂ) •
        (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
  replace hzero : Φ.hamiltonian *ᵥ WithLp.ofLp Ω = 0 :=
    (ManyBody.Interaction.mem_zeroSpace_iff_hamiltonian_mulVec_eq_zero
      fun j ↦ Matrix.nonneg_iff_posSemidef.mp (h0 j)).mp hzero
  intro X N Y K
  classical
  let H := Φ.hamiltonian
  let A := Φ.term a + Φ.term b
  let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
  have hsumpos (S : Finset (Fin (L - 1))) : (Φ.partialHamiltonian S).PosSemidef :=
    Matrix.posSemidef_sum S fun i _ ↦ Matrix.nonneg_iff_posSemidef.mp (h0 i)
  have hX : X.PosSemidef := by
    simpa only [X, leftCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      hsumpos (Finset.univ.filter fun i ↦ i.val < a.val)
  have hN : N.PosSemidef := by
    simpa only [N, middleCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      hsumpos (Finset.univ.filter fun i ↦ a.val < i.val ∧ i.val < b.val)
  have hY : Y.PosSemidef := by
    simpa only [Y, rightCutBlock, Complex.ofReal_zero, zero_smul, sub_zero] using
      hsumpos (Finset.univ.filter fun i ↦ b.val < i.val)
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (add_nonneg (h0 a) (h0 b))
  have hAcap : A ≤ (2 : ℂ) • 1 := by
    simpa only [A, two_smul] using add_le_add (h1 a) (h1 b)
  obtain ⟨hXN, hXY, hNY⟩ := normalizedCutBlock_commutations Φ a b hab 0 0 0
  have hsum : X + N + Y + A = H := by
    simpa only [H, X, N, Y, A, zero_add, Complex.ofReal_zero, zero_smul, sub_zero] using
      normalizedCutBlock_sum Φ a b hab 0 0 0
  have hH : X + (N + A) + Y = H := by rw [← hsum]; abel
  have ht0 : 0 < t := (div_pos (by norm_num : (0 : ℝ) < 1024) hg).trans_le ht
  obtain ⟨hK, hKle⟩ := Matrix.twoSidedEnergyTruncation_posSemidef_le X (N + A) Y
    hX (hN.add hA) hY t ht0.le
  rw [hH] at hKle
  have hKzero : K *ᵥ WithLp.ofLp Ω = 0 := by
    have hz := Matrix.mulVec_eq_smul_of_order_sandwich H K 0 (WithLp.ofLp Ω)
      (by simpa only [Complex.ofReal_zero, zero_smul] using hK.nonneg) hKle
      (by simpa only [H, Complex.ofReal_zero, zero_smul] using hzero)
    simpa only [Complex.ofReal_zero, zero_smul] using hz
  have hgap0 : (H - (0 : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    simpa only [H, zero_smul, sub_zero] using hgap
  have hcut : 1024 * (0 + g) ≤ t * g ^ 2 := by
    have htg := (div_le_iff₀ hg).mp ht
    have hmul := mul_le_mul_of_nonneg_right htg hg.le
    nlinarith
  have horth := Matrix.orthogonal_clipped_energy_ge X N Y A hX hN hY hA hXN hXY hNY hAcap
    Ω hΩ 0 g t (by norm_num) (by norm_num) hg hg1 ht0 hcut
    (by
      intro v
      simpa only [hH, ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
        ContinuousLinearMap.coe_coe] using hgap0.gap_le v)
  have hKΩ : ι K Ω = (0 : ℂ) • Ω := by
    change WithLp.toLp 2 (K *ᵥ WithLp.ofLp Ω) = _
    rw [hKzero]
    simp
  refine ⟨hK, hKle, hKzero, ?_⟩
  suffices hfull : (K - (0 : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef by
    simpa only [zero_smul, sub_zero] using hfull
  apply (hK.isHermitian.posSemidef_gap_iff 0 (g / 2) Ω).2
  intro v
  let α := ⟪Ω, v⟫_ℂ
  let w := v - α • Ω
  have hself : ⟪Ω, Ω⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hΩ]; norm_num
  have hw : ⟪Ω, w⟫_ℂ = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, hself, mul_one, α, sub_self]
  have hv : v = α • Ω + w := by dsimp only [w]; module
  have hn : ‖v‖ ^ 2 = ‖α‖ ^ 2 + ‖w‖ ^ 2 := by
    have hi : ⟪α • Ω, w⟫_ℂ = 0 := by rw [inner_smul_left, hw, mul_zero]
    conv_lhs => rw [hv]
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi, norm_smul, hΩ]
    ring
  have he : (⟪v, ι K v⟫_ℂ).re = (⟪w, ι K w⟫_ℂ).re := by
    conv_lhs => rw [hv]
    simpa only [mul_zero, zero_add] using
      re_inner_smul_add_eigenvector hK.isPositive_toEuclideanCLM.isSymmetric hΩ hKΩ hw α
  have hlower := horth w hw
  change (g / 2) * (‖v‖ ^ 2 - ‖α‖ ^ 2) ≤ (⟪v, ι K v⟫_ℂ).re - 0 * ‖v‖ ^ 2
  rw [hn, he]
  simpa only [zero_add, add_sub_cancel_left, zero_mul, sub_zero] using hlower

end TNLean.MPS.AreaLaw.AKLV

end

end FrustrationFreeClipping

section FrustrationFreeFilter

open Matrix Polynomial
open scoped BigOperators InnerProductSpace Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Classical in
private theorem ff_clipped_hamiltonian_eq {L q a s : ℕ}
    (hs : 6 ≤ s) (ha : a + s + 1 ≤ L)
    (Φ : ManyBody.BondInteraction L q) (t : ℝ) :
    let α : Fin (L - 1) := ⟨a + 1, by omega⟩
    let β : Fin (L - 1) := ⟨a + s - 2, by omega⟩
    ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
      (a + 2) (a + s - 1) Φ (fun _ ↦ 0) t Finset.univ =
      Matrix.twoSidedEnergyTruncation (AKLV.leftCutBlock Φ α 0)
        (AKLV.middleCutBlock Φ α β 0 + (Φ.term α + Φ.term β)) (AKLV.rightCutBlock Φ β 0) t := by
  intro α β
  let C := ManyBody.BondInteraction.threeRegionHamiltonians (a + 2) (a + s - 1) Φ
  have hleft : AKLV.leftCutBlock Φ α 0 = C 0 := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val < a + 1), Φ.term i) -
      (0 : ℂ) • 1 = ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ 0 ≤ i.val ∧ i.val + 1 < a + 2), Φ.term i
    simp only [zero_smul, sub_zero]
    congr 1
  have hmiddle : AKLV.middleCutBlock Φ α β 0 = C 1 := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      a + 1 < i.val ∧ i.val < a + s - 2), Φ.term i) - (0 : ℂ) • 1 =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        a + 2 ≤ i.val ∧ i.val + 1 < a + s - 1), Φ.term i
    simp only [zero_smul, sub_zero]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hright : AKLV.rightCutBlock Φ β 0 = C 2 := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦ a + s - 2 < i.val), Φ.term i) -
      (0 : ℂ) • 1 = ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        a + s - 1 ≤ i.val ∧ i.val + 1 < L), Φ.term i
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
      (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3)) = {0, 2} := by
    ext x
    fin_cases x <;> simp
  dsimp only [ManyBody.BondInteraction.twoBlockTruncatedHamiltonian]
  rw [hselector, Fin.sum_univ_three, hcross, Finset.sum_pair hne]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self,
    or_false, or_true, ite_true, ite_false, zero_add, Complex.ofReal_zero, zero_smul,
    sub_zero]
  rw [Matrix.twoSidedEnergyTruncation, hleft, hmiddle, hright]
  change cfc (fun x : ℝ ↦ min x t) (C 0) + C 1 +
      cfc (fun x : ℝ ↦ min x t) (C 2) + (Φ.term α + Φ.term β) =
    energyTruncation (C 0) t + (C 1 + (Φ.term α + Φ.term β)) + energyTruncation (C 2) t
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
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (g t : ℝ) (hg : 0 < g) (hg1 : g ≤ 1) (ht : 1024 / g ≤ t)
    (hzero : Ω ∈ Φ.zeroSpace)
    (hgap : (Φ.hamiltonian - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef) :
    let B := ManyBody.BondInteraction.twoBlockTruncatedHamiltonian
      (a + 2) (a + s - 1) Φ (fun _ ↦ 0) t Finset.univ
    B.PosSemidef ∧ B ≤ Φ.hamiltonian ∧ ‖B‖ ≤ 2 * t + s ∧
      B *ᵥ WithLp.ofLp Ω = 0 ∧
      (B - ((g / 2 : ℝ) : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef ∧
      ∀ ell : ℕ, ∃ p : Polynomial ℝ, p.natDegree = ell ∧ p.eval 0 = 1 ∧
        let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
        toEuclideanLin K Ω = Ω ∧
        ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
          2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((g / 2) / (2 * t + s))) ∧
        operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
          (interval L 0 (a + s / 2)) K) ≤
            (q * (ell + 1)) ^ (16 * (ell / (s - 2) + Nat.sqrt ell + 1)) ∧
        operatorSchmidtRank (ManyBody.cutOperator (X := fun _ ↦ Fin q)
          (interval L 0 (a + s / 2)) K) ≤
            (q * (ell + 1)) ^ (32 * (ell / s + Nat.sqrt ell + 1)) ∧
        ∀ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
          ⟪Ω, toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖toEuclideanLin K ψ‖ ^ 2 ≤
            (2 * Real.exp (-2 * (ell : ℝ) * Real.sqrt ((g / 2) / (2 * t + s)))) ^ 2 := by
  intro B
  let α : Fin (L - 1) := ⟨a + 1, by omega⟩
  let β : Fin (L - 1) := ⟨a + s - 2, by omega⟩
  have heq := ff_clipped_hamiltonian_eq hs ha Φ t
  obtain ⟨hBpos, hBH, hBΩ, hBgap⟩ :=
    AKLV.frustrationFree_twoSidedEnergyTruncation_ground_gap Φ h0 h1 α β
      (by dsimp only [α, β]; omega) Ω hΩ g t hg hg1 ht hzero hgap
  rw [← heq] at hBpos hBH hBΩ hBgap
  have ht0 : 0 ≤ t := le_trans (by positivity : 0 ≤ 1024 / g) ht
  have he (j : Fin 3) : (aklvNormalizationHamiltonians a s Φ j -
      (((fun _ : Fin 3 ↦ (0 : ℝ)) j) : ℂ) • 1).PosSemidef := by
    simp only [Complex.ofReal_zero, zero_smul, sub_zero]
    exact Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)
  have hBnorm := (aklv_clipped_hamiltonian_posSemidef_norm_le (by omega) ha Φ h0 h1
    (fun _ ↦ 0) he le_rfl ht0).2
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
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
  let H := fun j : Fin (s - 2) ↦ Φ.term ⟨a + 1 + j.val, by omega⟩
  obtain ⟨HL, HR, hL, hR, hmiddle, hdecomp, hcenter⟩ :=
    aklv_clipped_hamiltonian_decomposition (by omega) ha Φ (fun _ ↦ 0) t
  have hR' : ManyBody.IsSupportedOn HR (interval L (a + 1 + (s - 2)) L) := by
    convert hR using 1
    congr 1
    omega
  obtain ⟨p, hdegree, hp0, hfix, herr, hrank, horth⟩ :=
    exists_aklv_chebyshev_filter (E0 := 0) (gap := g / 2) (u := 2 * t + s)
      hq (by omega : 0 < s - 2)
      (by omega : a + 1 + (s - 2) + 1 ≤ L) H hmiddle HL HR
      (by simpa only [Nat.add_assoc] using hL) hR'
      (by rw [← hdecomp]; exact hBpos.isHermitian) hΩ
      (by rw [← hdecomp]; simpa only [Complex.ofReal_zero, zero_smul] using hBΩ)
      (by rw [← hdecomp]; simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using hBgap)
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

end FrustrationFreeFilter
