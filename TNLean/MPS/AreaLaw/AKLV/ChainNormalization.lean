/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.DisjointGroundEnergy
import TNLean.MPS.AreaLaw.AKLV.NormalizedChain
import TNLean.Algebra.MatrixHermitianSum

/-!
# Regional scalar normalization of an original nearest-neighbour chain

Removing two bonds leaves three operators on disjoint site regions. Their
ground energies provide actual scalar shifts making all three blocks positive,
with a common zero-energy test. The two positive connecting bonds then bound
the normalized ground energy by two, hence by six as required in AKLV,
arXiv:1301.1162v1, Section 6.1, lines 901–925. Scalar shifts preserve the
ground vector and the full-system projector gap.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

private theorem isSupportedOn_bond_sum {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (I : Finset (Fin (L - 1))) (S : Finset (Fin L))
    (hIS : ∀ i ∈ I, interval L i.val (i.val + 2) ⊆ S) :
    Entropy.IsSupportedOn (n := fun _ ↦ q) (∑ i ∈ I, h i) S := by
  exact QuantumCircuit.isSupportedOn_of_mem_supportedOperators
    (Submodule.sum_mem _ fun i hi ↦
      QuantumCircuit.mem_supportedOperators_of_isSupportedOn ((hs i).mono (hIS i hi)))

/-- The original positive nearest-neighbour chain admits the regional shifts
and bounded ground energy used in the truncation proof. The shifts, positive
blocks and normalized energy are derived, rather than supplied.
AKLV, Section 6.1. The sharper bound two uses the two removed connecting bonds. -/
theorem exists_chain_normalization {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ ↦ q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (E₀ g : ℝ) (hg : 0 ≤ g)
    (heig : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (∑ i, h i) Ω =
      (E₀ : ℂ) • Ω)
    (hgap : ((∑ i, h i) - (E₀ : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef) :
    ∃ x m y e : ℝ,
      (leftCutBlock h a x).PosSemidef ∧ (middleCutBlock h a b m).PosSemidef ∧
      (rightCutBlock h b y).PosSemidef ∧ 0 ≤ e ∧ e ≤ 2 ∧ (0 ≤ x ∧ 0 ≤ m ∧ 0 ≤ y) ∧
      (let H := (∑ i, h i) - ((x + m + y : ℝ) : ℂ) • 1
       Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H Ω = (e : ℂ) • Ω ∧
       (H - (e : ℂ) • 1 - (g : ℂ) •
         (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef) := by
  classical
  let S := interval L 0 (a.val + 1)
  let T := interval L (a.val + 1) (b.val + 1)
  let U := interval L (b.val + 1) L
  let I := Finset.univ.filter fun i : Fin (L - 1) ↦ i.val < a.val
  let J := Finset.univ.filter fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val
  let K := Finset.univ.filter fun i : Fin (L - 1) ↦ b.val < i.val
  let X := ∑ i ∈ I, h i
  let N := ∑ i ∈ J, h i
  let Y := ∑ i ∈ K, h i
  have hSX : Entropy.IsSupportedOn (n := fun _ ↦ q) X S :=
    isSupportedOn_bond_sum h hs I S (by
      intro i hi v hv
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [S, mem_interval] at hv ⊢
      omega)
  have hTN : Entropy.IsSupportedOn (n := fun _ ↦ q) N T :=
    isSupportedOn_bond_sum h hs J T (by
      intro i hi v hv
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [T, mem_interval] at hv ⊢
      omega)
  have hUY : Entropy.IsSupportedOn (n := fun _ ↦ q) Y U :=
    isSupportedOn_bond_sum h hs K U (by
      intro i hi v hv
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [U, mem_interval] at hv ⊢
      omega)
  have hST : Disjoint S T := disjoint_interval_interval _ _ _
  have hTU : Disjoint T U := disjoint_interval_interval _ _ _
  have hSU : Disjoint S U := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    simp only [S, U, mem_interval] at hv hw
    omega
  have hh (i) : (h i).IsHermitian := IsSelfAdjoint.of_nonneg (h0 i)
  have hX : X.IsHermitian := Matrix.isHermitian_sum _ fun i _ ↦ hh i
  have hN : N.IsHermitian := Matrix.isHermitian_sum _ fun i _ ↦ hh i
  have hY : Y.IsHermitian := Matrix.isHermitian_sum _ fun i _ ↦ hh i
  have hΩne : Ω ≠ 0 := by intro hz; simp [hz] at hΩ
  have hrawne : WithLp.ofLp Ω ≠ 0 := fun hz ↦ hΩne ((WithLp.ofLp_eq_zero (p := 2)).mp hz)
  obtain ⟨σ₀, _⟩ := Function.ne_iff.mp hrawne
  obtain ⟨x, m, y, w, hXlow, hNlow, hYlow, hwunit, hxn, hmn, hyn, hwzero⟩ :=
    exists_three_disjoint_ground_shifts S T U hST hSU hTU X N Y hSX hTN hUY hX hN hY σ₀
  have hXpos : X.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ ↦ h0 i)
  have hNpos : N.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ ↦ h0 i)
  have hYpos : Y.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun i _ ↦ h0 i)
  let H := (∑ i, h i) - ((x + m + y : ℝ) : ℂ) • 1
  let e := E₀ - (x + m + y)
  have hH : leftCutBlock h a x + middleCutBlock h a b m + rightCutBlock h b y +
      (h a + h b) = H := normalizedCutBlock_sum h a b hab x m y
  have hnewEig : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) H Ω = (e : ℂ) • Ω := by
    apply WithLp.ofLp_injective 2
    simp only [H, Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    have hh := congrArg WithLp.ofLp heig
    simp only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] at hh
    rw [hh, ← sub_smul]
    simp only [e, Complex.ofReal_sub]
  have hnewGap : (H - (e : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    convert hgap using 1
    dsimp only [H, e]
    rw [Complex.ofReal_sub, sub_smul]
    abel
  have hP := Matrix.one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one (WithLp.ofLp Ω)
    (by rw [← EuclideanSpace.norm_sq_eq, hΩ]; norm_num)
  have hHlow : (H - (e : ℂ) • 1).PosSemidef := by
    convert hnewGap.add (hP.smul (Complex.zero_le_real.mpr hg)) using 1
    abel
  have hrawunit : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hΩ]
    norm_num
  have hA : (h a + h b).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (add_nonneg (h0 a) (h0 b))
  have hAcap : h a + h b ≤ (2 : ℂ) • 1 := by
    simpa only [two_smul] using add_le_add (h1 a) (h1 b)
  have he := Matrix.groundEnergy_bounds_of_positive_boundary_and_zero_test
    ((X - (x : ℂ) • 1) + (N - (m : ℂ) • 1) + (Y - (y : ℂ) • 1)) (h a + h b) 2 e
    ((hXlow.add hNlow).add hYlow) hA hAcap w (WithLp.ofLp Ω) hwzero hwunit
    (by
      have hh := congrArg WithLp.ofLp hnewEig
      simp only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] at hh
      exact hH ▸ hh)
    hrawunit (by exact hH ▸ hHlow)
  exact ⟨x, m, y, e, hXlow, hNlow, hYlow, he.1, he.2,
    ⟨hxn hXpos, hmn hNpos, hyn hYpos⟩, hnewEig, hnewGap⟩

/-- The derived nonnegative middle shift leaves its operator bounded by
its window length. AKLV, Section 6.1, the norm cap before Chebyshev filtering. -/
theorem middleCutBlock_le_window {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h1 : ∀ i, h i ≤ 1) (a b : Fin (L - 1)) (m : ℝ) (hm : 0 ≤ m) :
    middleCutBlock h a b m ≤ (((b.val - a.val : ℕ) : ℝ) : ℂ) • 1 := by
  classical
  let J := Finset.univ.filter fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val
  have hcard : J.card ≤ b.val - a.val := by
    have hh := Finset.card_le_card_of_injOn (s := J) (t := Finset.Ico a.val b.val) Fin.val
      (by
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        exact Finset.mem_Ico.mpr ⟨hi'.1.le, hi'.2⟩)
      (by intro i _ j _ hij; exact Fin.ext hij)
    simpa only [Nat.card_Ico] using hh
  have hsum : (∑ i ∈ J, h i) ≤ (J.card : ℂ) • 1 := by
    simpa only [Nat.cast_smul_eq_nsmul ℂ] using Finset.sum_le_card_nsmul J h 1
      (fun i _ ↦ h1 i)
  have hshift : 0 ≤ (m : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :=
    (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hm)).nonneg
  calc
    middleCutBlock h a b m ≤ ∑ i ∈ J, h i := sub_le_self _ hshift
    _ ≤ (J.card : ℂ) • 1 := hsum
    _ ≤ _ := by
      apply Matrix.le_iff.mpr
      have hc : (J.card : ℝ) ≤ (b.val - a.val : ℕ) := by exact_mod_cast hcard
      have hp := (Matrix.PosSemidef.one :
        (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ).PosSemidef).smul
          (Complex.zero_le_real.mpr (sub_nonneg.mpr hc))
      simpa only [Complex.ofReal_sub, Complex.ofReal_natCast, sub_smul] using hp

end TNLean.MPS.AreaLaw.AKLV
