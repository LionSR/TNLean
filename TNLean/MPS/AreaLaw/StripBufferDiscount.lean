/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.StripGeometry

/-!
# Buffered discount and entropy bound for a strip

This is a strip extension of the one-dimensional note. The proof applies the arbitrary-site
logarithmic buffered discount to the actual lattice Hamiltonian, with uniform weights
`2/m`, and derives the energy bound `Δ/2` from its cut budget. The Araki–Lieb closure uses
at most `2mRw` physical sites in the buffer. The constants are fixed before either side
length, the Hamiltonian, and its ground vector.

Source: one-dimensional note, `part1_arealaw.tex`, Lemma `lem:buffer`, Section 5,
and Remark `rem:sharper`, lines 405–409, 648–679, and 702–748. The strip conclusion
extends the note. The gap is the unique-ground-vector projector gap of the note's
preamble, lines 193–206; a degenerate ground-space gap is not sufficient here.
-/

open Matrix TNLean.Lattice
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The width coefficient of the strip logarithmic cut budget. -/
noncomputable def stripBudgetConst (q R : ℕ) : ℝ :=
  1 + stripCrossConst R *
    Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2

/-- The cut budget coefficient is at least one. -/
theorem one_le_stripBudgetConst (q R : ℕ) : 1 ≤ stripBudgetConst q R := by
  unfold stripBudgetConst
  exact le_add_of_nonneg_right (by positivity)

/-- Uniform linear-width budget for every column interval. -/
theorem cutLogBudget_stripInterval_le_mul {q w : ℕ} (hq : 1 ≤ q) (hw : 1 ≤ w)
    (L R a b : ℕ) :
    Entropy.cutLogBudget
      (Entropy.crossingTerms (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1)
        (stripInterval L w a b))
      (Entropy.supportDim (fun _ : Site (stripDomain L w) ↦ q) ∘ fun X ↦ X.1) ≤
      stripBudgetConst q R * w := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  refine (cutLogBudget_stripInterval_le hq L w R a b).trans ?_
  simp only [stripBudgetConst, Nat.cast_mul]
  nlinarith

/-- The shell count has a linear energy threshold and a square-root tail threshold. -/
noncomputable def stripShellCount (q R w : ℕ) (J Δ : ℝ) : ℕ :=
  ⌈4 + 64 * Real.exp 1 * (J / Δ) * (stripBudgetConst q R * w) +
    128 * Real.sqrt ((1 + J / Δ) * (stripBudgetConst q R * w))⌉₊

/-- Uniform shells are the actual column enlargements, without repeated terminal shells. -/
def stripShell (L w R a b j : ℕ) : Finset (Site (stripDomain L w)) :=
  stripInterval L w (a - (j + 1) * R) (b + (j + 1) * R) \ stripInterval L w a b

/-- Adding a shell gives the enlarged column interval. -/
theorem union_stripShell (L w R a b j : ℕ) :
    stripInterval L w a b ∪ stripShell L w R a b j =
      stripInterval L w (a - (j + 1) * R) (b + (j + 1) * R) :=
  Finset.union_sdiff_of_subset (stripInterval_mono (Nat.sub_le _ _) (Nat.le_add_right _ _))

set_option maxHeartbeats 800000 in
-- The finite-site discount elaborates support and configuration indices for the same lattice.
/-- The buffered discount with energy derived from the original interactions. -/
theorem two_mul_condEntropy_stripInterval_le {L w q R : ℕ} {J Δ : ℝ}
    (hq : 1 ≤ q) (hw : 1 ≤ w) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : LocalHamiltonian (stripDomain L w) q R J) {E₀ : ℝ}
    {Ω : StateSpace (stripDomain L w) q}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (a b : ℕ) :
    let m := stripShellCount q R w J Δ
    let T := stripInterval L w (a - m * R) (b + m * R) \ stripInterval L w a b
    2 * (Entropy.regionEntropy (n := fun _ : Site (stripDomain L w) ↦ q)
          (stripInterval L w a b ∪ T) Ω - Entropy.regionEntropy T Ω) ≤
      Entropy.regionEntropy (stripInterval L w a b) Ω +
        4096 * Real.exp 1 * (J / Δ) * (stripBudgetConst q R * w) / m +
        m * Real.log 2 := by
  classical
  intro m Tbuf
  let B : ℝ := stripBudgetConst q R * w
  have hB1 : 1 ≤ B := by
    have h₁ := one_le_stripBudgetConst q R
    have h₂ : (1 : ℝ) ≤ w := by exact_mod_cast hw
    dsimp [B]
    nlinarith
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hm : 4 + 64 * Real.exp 1 * (J / Δ) * B +
      128 * Real.sqrt ((1 + J / Δ) * B) ≤ m := Nat.le_ceil _
  have hm4 : (4 : ℝ) ≤ m := by
    have : 0 ≤ 64 * Real.exp 1 * (J / Δ) * B := by positivity
    linarith [Real.sqrt_nonneg ((1 + J / Δ) * B)]
  have hmpos : (0 : ℝ) < m := by linarith
  have hmE : 64 * Real.exp 1 * (J / Δ) * B ≤ m := by
    linarith [Real.sqrt_nonneg ((1 + J / Δ) * B)]
  have hmT : 128 * Real.sqrt ((1 + J / Δ) * B) ≤ m := by
    have : 0 ≤ 64 * Real.exp 1 * (J / Δ) * B := by positivity
    linarith
  let X := stripInterval L w a b
  let T := stripShell L w R a b
  let S := fun Y : AdmissibleSupport (stripDomain L w) R ↦ Y.1
  let weights : ℕ → ℝ := fun _ ↦ 2 / m
  have hweights : ∀ j, 0 < weights j := fun _ ↦ by dsimp [weights]; positivity
  have hhalf : ∀ j, weights j ≤ 1 / 2 := fun _ ↦ by
    simpa only [weights, mul_one] using Entropy.harmonic_weight_le_half hm4 (le_refl (1 : ℝ))
  have hmass : ∑ j ∈ Finset.range m, weights j = 2 := by
    simp only [weights, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hbudget : ∀ j, Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
      (Entropy.supportDim (fun _ : Site (stripDomain L w) ↦ q) ∘ S) ≤ B := by
    intro j
    rw [show X ∪ T j = _ from union_stripShell L w R a b j]
    exact cutLogBudget_stripInterval_le_mul hq hw L R _ _
  have hsingle : ∀ Y j j', ((∃ v ∈ S Y, v ∈ X ∪ T j) ∧ ∃ v ∈ S Y, v ∉ X ∪ T j) →
      ((∃ v ∈ S Y, v ∈ X ∪ T j') ∧ ∃ v ∈ S Y, v ∉ X ∪ T j') → j = j' := by
    intro Y j j' hj hj'
    rw [show X ∪ T j = _ from union_stripShell L w R a b j] at hj
    rw [show X ∪ T j' = _ from union_stripShell L w R a b j'] at hj'
    exact strip_single_splitting Y hj hj'
  have henergy : ∑ j ∈ Finset.range m, 8 * Real.exp 1 * weights j ^ 2 *
      ∑ Y ∈ Entropy.crossingTerms S (X ∪ T j),
        Real.log (Real.exp 1 * Entropy.supportDim
          (fun _ : Site (stripDomain L w) ↦ q) (S Y)) ^ 2 * J ≤ Δ / 2 := by
    have hsum (j : ℕ) : ∑ Y ∈ Entropy.crossingTerms S (X ∪ T j),
        Real.log (Real.exp 1 * Entropy.supportDim
          (fun _ : Site (stripDomain L w) ↦ q) (S Y)) ^ 2 * J ≤ B * J := by
      rw [← Finset.sum_mul]
      have hb := hbudget j
      unfold Entropy.cutLogBudget at hb
      simp only [Function.comp_apply] at hb
      exact mul_le_mul_of_nonneg_right (by linarith) hJ
    have hterm : ∀ j ∈ Finset.range m, 8 * Real.exp 1 * weights j ^ 2 *
        ∑ Y ∈ Entropy.crossingTerms S (X ∪ T j),
          Real.log (Real.exp 1 * Entropy.supportDim
            (fun _ : Site (stripDomain L w) ↦ q) (S Y)) ^ 2 * J ≤
        32 * Real.exp 1 * (B * J) / (m : ℝ) ^ 2 := by
      intro j _
      calc _ ≤ 8 * Real.exp 1 * weights j ^ 2 * (B * J) :=
          mul_le_mul_of_nonneg_left (hsum j) (by positivity)
        _ = _ := by dsimp [weights]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [show (m : ℝ) * (32 * Real.exp 1 * (B * J) / (m : ℝ) ^ 2) =
      32 * Real.exp 1 * (B * J) / m by field_simp]
    rw [div_le_iff₀ hmpos]
    have hE' : 64 * Real.exp 1 * J * B ≤ m * Δ := by
      apply (div_le_iff₀ hΔ).mp
      convert hmE using 1
      ring
    nlinarith only [hE']
  have hu : ∀ j < m, weights j / (1 - weights j) ≤
      Entropy.tailRadius (J / Δ) (Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site (stripDomain L w) ↦ q) ∘ S)) := by
    intro j _
    have h₁ := Entropy.harmonic_weight_ratio_le hm4 (le_refl (1 : ℝ))
    have h₂ := Entropy.le_tailRadius_of_le (c := 1) hmT hmpos le_rfl hθ
      (Entropy.one_le_cutLogBudget _ _) (by simpa using hbudget j)
    simpa only [weights, mul_one] using h₁.trans h₂
  have hmono : ∀ i j, i ≤ j → T i ⊆ T j := by
    intro i j hij
    have hd : (i + 1) * R ≤ (j + 1) * R :=
      Nat.mul_le_mul_right R (Nat.succ_le_succ hij)
    exact Finset.sdiff_subset_sdiff (stripInterval_mono (by omega) (by omega)) le_rfl
  have hbuf : ∀ j < m, T j ⊆ Tbuf := by
    intro j hj
    have hd : (j + 1) * R ≤ m * R := Nat.mul_le_mul_right R hj
    exact Finset.sdiff_subset_sdiff (stripInterval_mono (by omega) (by omega)) le_rfl
  obtain ⟨hΩ, heig, hgap⟩ := hgs
  change toEuclideanLin (∑ Y, h.term Y) Ω = (E₀ : ℂ) • Ω at heig
  have key := Entropy.two_mul_condEntropy_le_logarithmic
    (n := fun _ : Site (stripDomain L w) ↦ q) X T hmono
    (fun _ ↦ Finset.disjoint_sdiff) weights hweights hhalf hΩ h.term S
    (fun Y ↦ QuantumCircuit.isSupportedOn_of_mem_supportedOperators (h.supported Y))
    h.hermitian hJ h.norm_le hsingle hΔ heig hgap (E := Δ / 2)
    (by linarith) henergy hu hmass Finset.disjoint_sdiff hbuf
  have herr : ∑ j ∈ Finset.range m, 1024 * Real.exp 1 * (J / Δ) *
      Entropy.cutLogBudget (Entropy.crossingTerms S (X ∪ T j))
        (Entropy.supportDim (fun _ : Site (stripDomain L w) ↦ q) ∘ S) * weights j ^ 2 ≤
      4096 * Real.exp 1 * (J / Δ) * B / m := by
    calc _ ≤ ∑ j ∈ Finset.range m,
        1024 * Real.exp 1 * (J / Δ) * B * weights j ^ 2 := by
          gcongr with j
          exact hbudget j
      _ = _ := by
        simp only [weights, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
        ring
  have hlog : (m : ℝ) * Real.log (1 - Δ / 2 / Δ) = -(m * Real.log 2) := by
    have hhalf : 1 - Δ / 2 / Δ = (2 : ℝ)⁻¹ := by field_simp; norm_num
    rw [hhalf, Real.log_inv, mul_neg]
  rw [hlog] at key
  linarith only [key, herr]

/-- A coefficient for the shell count, depending only on local dimension and range. -/
noncomputable def stripShellConst (q R : ℕ) : ℝ :=
  5 + (64 * Real.exp 1 + 128) * stripBudgetConst q R

/-- The shell count is linear in width and in one plus the inverse relative gap. -/
theorem stripShellCount_le {q R w : ℕ} {J Δ : ℝ} (hw : 1 ≤ w)
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    (stripShellCount q R w J Δ : ℝ) ≤ stripShellConst q R * (1 + J / Δ) * w := by
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hb := one_le_stripBudgetConst q R
  let B : ℝ := stripBudgetConst q R * w
  have hB1 : 1 ≤ B := by dsimp [B]; nlinarith
  have htB : 1 ≤ (1 + J / Δ) * B := by nlinarith
  have hsqrt : Real.sqrt ((1 + J / Δ) * B) ≤ (1 + J / Δ) * B := by
    calc _ ≤ Real.sqrt (((1 + J / Δ) * B) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith only [htB])
      _ = _ := Real.sqrt_sq (by positivity)
  have hc : (stripShellCount q R w J Δ : ℝ) ≤
      5 + 64 * Real.exp 1 * (J / Δ) * B + 128 * Real.sqrt ((1 + J / Δ) * B) := by
    have hnonneg : 0 ≤ 4 + 64 * Real.exp 1 * (J / Δ) * B +
        128 * Real.sqrt ((1 + J / Δ) * B) := by positivity
    exact (Nat.ceil_lt_add_one hnonneg).le.trans_eq (by ring)
  have he : 0 ≤ 64 * Real.exp 1 := by positivity
  have h₁ : 64 * Real.exp 1 * (J / Δ) * B ≤
      64 * Real.exp 1 * ((1 + J / Δ) * B) := by nlinarith
  have h₂ : 5 ≤ 5 * ((1 + J / Δ) * w) := by nlinarith
  dsimp only [B] at *
  unfold stripShellConst
  nlinarith only [hc, hsqrt, h₁, h₂]

/-- The explicit entropy coefficient in the strip extension. -/
noncomputable def stripAreaLawConst (q R : ℕ) : ℝ :=
  (8 * R * Real.log q + Real.log 2) * stripShellConst q R +
    1024 * Real.exp 1 * stripBudgetConst q R

/-- Scalar relaxation of the actual shell and discount costs. -/
private theorem stripEntropyBound_le {q R w : ℕ} {J Δ : ℝ}
    (hq : 1 ≤ q) (hw : 1 ≤ w) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    let m := stripShellCount q R w J Δ
    8 * (m : ℝ) * R * w * Real.log q +
      4096 * Real.exp 1 * (J / Δ) * (stripBudgetConst q R * w) / m + m * Real.log 2 ≤
      stripAreaLawConst q R * (1 + J / Δ) * (w : ℝ) ^ 2 := by
  intro m
  let B : ℝ := stripBudgetConst q R * w
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hB1 : 1 ≤ B := by
    have := one_le_stripBudgetConst q R
    dsimp [B]
    nlinarith
  have hm4 : (4 : ℝ) ≤ m := by
    have hc : 4 + 64 * Real.exp 1 * (J / Δ) * B +
        128 * Real.sqrt ((1 + J / Δ) * B) ≤ m := Nat.le_ceil _
    have : 0 ≤ 64 * Real.exp 1 * (J / Δ) * B := by positivity
    linarith [Real.sqrt_nonneg ((1 + J / Δ) * B)]
  have hmpos : (0 : ℝ) < m := by linarith only [hm4]
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have herr : 4096 * Real.exp 1 * (J / Δ) * B / m ≤
      1024 * Real.exp 1 * stripBudgetConst q R * (1 + J / Δ) * (w : ℝ) ^ 2 := by
    rw [div_le_iff₀ hmpos]
    have hcoef : 0 ≤ 1024 * Real.exp 1 * B := by positivity
    have ht : J / Δ ≤ (1 + J / Δ) * w := by
      calc _ ≤ 1 + J / Δ := by linarith only [hθ]
        _ ≤ _ := le_mul_of_one_le_right (by linarith only [hθ]) hw'
    have hh := mul_le_mul_of_nonneg_left ht hcoef
    have hp := mul_le_mul_of_nonneg_left hm4
      (show 0 ≤ 1024 * Real.exp 1 * B * ((1 + J / Δ) * w) by positivity)
    dsimp only [B] at *
    nlinarith only [hh, hp]
  have hmle := stripShellCount_le (q := q) (R := R) hw hJ hΔ
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hgeom := mul_le_mul_of_nonneg_right hmle
    (show 0 ≤ 8 * (R : ℝ) * w * Real.log q by positivity)
  have hmass := mul_le_mul_of_nonneg_right hmle hlog2
  have hlast : stripShellConst q R * (1 + J / Δ) * w * Real.log 2 ≤
      stripShellConst q R * (1 + J / Δ) * (w : ℝ) ^ 2 * Real.log 2 := by
    have hnonneg : 0 ≤ stripShellConst q R := by
      have := one_le_stripBudgetConst q R
      unfold stripShellConst
      positivity
    have hww : (w : ℝ) ≤ (w : ℝ) ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hww
      (mul_nonneg (mul_nonneg hnonneg
        (show 0 ≤ 1 + J / Δ by linarith only [hθ])) hlog2)
    nlinarith only [hh]
  unfold stripAreaLawConst
  nlinarith only [herr, hgeom, hmass, hlast]


/-- The entropy of every column interval has the claimed quadratic width bound.
This uses the original lattice Hamiltonian and its unique-vector projector gap. -/
theorem regionEntropy_stripInterval_le {L w q R : ℕ} {J Δ : ℝ}
    (hq : 1 ≤ q) (hw : 1 ≤ w) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : LocalHamiltonian (stripDomain L w) q R J) {E₀ : ℝ}
    {Ω : StateSpace (stripDomain L w) q}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (a b : ℕ) :
    Entropy.regionEntropy (n := fun _ : Site (stripDomain L w) ↦ q)
      (stripInterval L w a b) Ω ≤ stripAreaLawConst q R * (1 + J / Δ) * (w : ℝ) ^ 2 := by
  let m := stripShellCount q R w J Δ
  let B : ℝ := stripBudgetConst q R * w
  let T := stripInterval L w (a - m * R) (b + m * R) \ stripInterval L w a b
  have hdisc := two_mul_condEntropy_stripInterval_le hq hw hJ hΔ h hgs a b
  change 2 * (Entropy.regionEntropy (stripInterval L w a b ∪ T) Ω -
    Entropy.regionEntropy T Ω) ≤ Entropy.regionEntropy (stripInterval L w a b) Ω +
      4096 * Real.exp 1 * (J / Δ) * B / m + m * Real.log 2 at hdisc
  have hAL := regionEntropy_le_union_add hgs.1
    (show Disjoint (stripInterval L w a b) T from Finset.disjoint_sdiff)
  have hT := regionEntropy_le_card_mul_log hgs.1 T
  have hcard : (T.card : ℝ) ≤ 2 * (m : ℝ) * R * w := by
    have hc := card_stripInterval_enlargement_sdiff_le L w a b (m * R)
    change T.card ≤ _ at hc
    have hc' : (T.card : ℝ) ≤ 2 * ((m : ℝ) * R) * w := by exact_mod_cast hc
    simpa only [mul_assoc] using hc'
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hTb := hT.trans (mul_le_mul_of_nonneg_right hcard hlog)
  have hint : Entropy.regionEntropy (stripInterval L w a b) Ω ≤
      8 * (m : ℝ) * R * w * Real.log q +
        4096 * Real.exp 1 * (J / Δ) * B / m + m * Real.log 2 := by
    linarith only [hdisc, hAL, hTb]
  exact hint.trans (stripEntropyBound_le hq hw hJ hΔ)

/-- Uniform strip area law with the constant quantified before the geometry and state. -/
theorem stripAreaLaw (q R : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L w : ℕ, 1 ≤ L → 1 ≤ w → 1 ≤ q →
      ∀ J Δ : ℝ, 0 ≤ J → 0 < Δ →
      ∀ h : LocalHamiltonian (stripDomain L w) q R J, ∀ E₀ : ℝ,
      ∀ Ω : StateSpace (stripDomain L w) q,
      Matrix.IsGappedGroundState h.operator E₀ Ω Δ → ∀ a b : ℕ,
      Entropy.regionEntropy (n := fun _ : Site (stripDomain L w) ↦ q)
        (stripInterval L w a b) Ω ≤ C * (1 + J / Δ) * (w : ℝ) ^ 2 := by
  refine ⟨stripAreaLawConst q R, ?_, ?_⟩
  · unfold stripAreaLawConst stripShellConst stripBudgetConst
    positivity
  · intro L w _ hw hq J Δ hJ hΔ h E₀ Ω hgs a b
    exact regionEntropy_stripInterval_le hq hw hJ hΔ h hgs a b

end TNLean.MPS.AreaLaw
