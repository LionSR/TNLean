/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ChebyshevAGSP.Robustness

/-!
# AKLV robustness on the normalized nearest-neighbour chain

The two removed boundary bonds determine the three disconnected regional
blocks. Their commutations and their sum are derived from the original
chain supports. The only regional order assumptions are the positivity
obtained by the normalization in AKLV, arXiv:1301.1162v1, Section 6.1.
No commutator, tail, residual, or gap of the clipped operator is assumed.
-/

open ManyBody (interval mem_interval)

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- The shifted left exterior, including the bond immediately before
the removed boundary bond. AKLV, Section 6.1: `H_L + H_1`. -/
def leftCutBlock {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (a : Fin (L - 1)) (z : ℝ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  Φ.partialHamiltonian (Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val < a.val)) - (z : ℂ) • 1

/-- The shifted middle after removing the two boundary bonds.
AKLV, Section 6.3: `H_3 + ⋯ + H_(s-2)`. -/
def middleCutBlock {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (a b : Fin (L - 1)) (z : ℝ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  Φ.partialHamiltonian
      (Finset.univ.filter (fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val)) -
    (z : ℂ) • 1

/-- The shifted right exterior after the second removed boundary bond.
AKLV, Section 6.1: `H_s + H_R`. -/
def rightCutBlock {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (b : Fin (L - 1)) (z : ℝ) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  Φ.partialHamiltonian (Finset.univ.filter (fun i : Fin (L - 1) ↦ b.val < i.val)) - (z : ℂ) • 1

/-- Regional sums separated by a missing bond commute by their original
two-site supports. Auxiliary to the source normalization of AKLV. -/
private theorem commute_separated_bond_sums {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (S T : Finset (Fin (L - 1)))
    (hsep : ∀ i ∈ S, ∀ j ∈ T, i.val + 1 < j.val) :
    Commute (Φ.partialHamiltonian S) (Φ.partialHamiltonian T) := by
  apply Commute.sum_left
  intro i hi
  apply Commute.sum_right
  intro j hj
  have hdist := hsep i hi j hj
  have hd : Disjoint (interval L i.val (i.val + 2)) (interval L j.val (j.val + 2)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rw [mem_interval] at hv hw
    omega
  exact ManyBody.commute_of_mem_supportedOperators_of_disjoint ((Φ.mem i)) ((Φ.mem j)) hd

/-- Scalar energy shifts preserve pairwise commutation. -/
private theorem commute_sub_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hXY : Commute X Y) (x y : ℝ) :
    Commute (X - (x : ℂ) • 1) (Y - (y : ℂ) • 1) :=
  (hXY.sub_left ((Commute.one_left Y).smul_left (x : ℂ))).sub_right
    ((Commute.one_right _).smul_right (y : ℂ))

/-- Commutation of the three normalized blocks is a consequence of the
nearest-neighbour supports and the two removed bonds. AKLV, Section 6.3. -/
theorem normalizedCutBlock_commutations {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (x m y : ℝ) :
    Commute (leftCutBlock Φ a x) (middleCutBlock Φ a b m) ∧
      Commute (leftCutBlock Φ a x) (rightCutBlock Φ b y) ∧
      Commute (middleCutBlock Φ a b m) (rightCutBlock Φ b y) := by
  have hleftmid := commute_separated_bond_sums Φ
    (Finset.univ.filter fun i : Fin (L - 1) ↦ i.val < a.val)
    (Finset.univ.filter fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val)
    (by intro i hi j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj; omega)
  have hleftright := commute_separated_bond_sums Φ
    (Finset.univ.filter fun i : Fin (L - 1) ↦ i.val < a.val)
    (Finset.univ.filter fun i : Fin (L - 1) ↦ b.val < i.val)
    (by intro i hi j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj; omega)
  have hmidright := commute_separated_bond_sums Φ
    (Finset.univ.filter fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val)
    (Finset.univ.filter fun i : Fin (L - 1) ↦ b.val < i.val)
    (by intro i hi j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj; omega)
  exact ⟨commute_sub_smul_one hleftmid x m, commute_sub_smul_one hleftright x y,
    commute_sub_smul_one hmidright m y⟩

/-- The three normalized blocks and the two removed boundary bonds
reconstruct the original normalized Hamiltonian. AKLV, Section 6.1. -/
theorem normalizedCutBlock_sum {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (x m y : ℝ) :
    leftCutBlock Φ a x + middleCutBlock Φ a b m + rightCutBlock Φ b y + (Φ.term a + Φ.term b) =
      Φ.hamiltonian - ((x + m + y : ℝ) : ℂ) • 1 := by
  classical
  have hpoint (i : Fin (L - 1)) :
      (if i.val < a.val then Φ.term i else 0) +
      (if a.val < i.val ∧ i.val < b.val then Φ.term i else 0) +
      (if b.val < i.val then Φ.term i else 0) +
      (if i = a then Φ.term i else 0) + (if i = b then Φ.term i else 0) = Φ.term i := by
    by_cases hia : i = a
    · subst i
      have hne : a ≠ b := fun heq ↦ (lt_irrefl a.val) (heq ▸ hab)
      simp [hab, hne, not_lt.mpr hab.le]
    by_cases hib : i = b
    · subst i
      have hne : b ≠ a := fun heq ↦ (lt_irrefl b.val) (heq ▸ hab)
      simp [hab, hne, not_lt.mpr hab.le]
    have ha : i.val ≠ a.val := fun heq ↦ hia (Fin.ext heq)
    have hb : i.val ≠ b.val := fun heq ↦ hib (Fin.ext heq)
    simp only [ite_eq_right hia, ite_eq_right hib, add_zero]
    split_ifs <;> simp_all <;> omega
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hsum
  simp only [← Finset.sum_filter] at hsum
  dsimp [leftCutBlock, middleCutBlock, rightCutBlock, ManyBody.Interaction.partialHamiltonian,
    ManyBody.Interaction.hamiltonian]
  simp only [add_smul]
  rw [← hsum]
  abel

/-- The three normalized blocks are the sum of the original terms over the
bonds other than the two removed ones, shifted by `x+m+y`. AKLV, Section 6.1. -/
theorem exists_normalizedCutBlock_eq_sum_sub {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (x m y : ℝ) :
    ∃ I : Finset (Fin (L - 1)),
      leftCutBlock Φ a x + middleCutBlock Φ a b m + rightCutBlock Φ b y =
        Φ.partialHamiltonian I - ((x + m + y : ℝ) : ℂ) • 1 := by
  classical
  let S := Finset.univ.filter fun i : Fin (L - 1) ↦ i.val < a.val
  let T := Finset.univ.filter fun i : Fin (L - 1) ↦ a.val < i.val ∧ i.val < b.val
  let U := Finset.univ.filter fun i : Fin (L - 1) ↦ b.val < i.val
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    omega
  have hSU : Disjoint S U := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [S, U, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    omega
  have hTU : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [T, U, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    omega
  refine ⟨(S ∪ T) ∪ U, ?_⟩
  dsimp only [leftCutBlock, middleCutBlock, rightCutBlock, ManyBody.Interaction.partialHamiltonian]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hSU, hTU⟩), Finset.sum_union hST]
  simp only [Complex.ofReal_add, add_smul]
  abel

/-- The quadratic gap bound of a two-sided clipping is the operator gap inequality
`K - e' I ≥ g' (I - |φ⟩⟨φ|)`. The clipping is Hermitian because its middle block and the
removed bonds are, so this repackaging does not depend on the cutoff that produced the
bound. Auxiliary to AKLV, arXiv:1301.1162v1, Theorem 6.1. -/
theorem posSemidef_gap_twoSidedEnergyTruncation_of_quadratic {n : Type*} [Fintype n]
    [DecidableEq n] (X N Y A : Matrix n n ℂ) (hN : N.IsHermitian) (hA : A.IsHermitian)
    (t e' g' : ℝ) (φ : EuclideanSpace ℂ n)
    (hquad : ∀ v : EuclideanSpace ℂ n,
      g' * (‖v‖ ^ 2 - ‖⟪φ, v⟫_ℂ‖ ^ 2) ≤
        (⟪v, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
          (twoSidedEnergyTruncation X (N + A) Y t) v⟫_ℂ).re - e' * ‖v‖ ^ 2) :
    (twoSidedEnergyTruncation X (N + A) Y t - (e' : ℂ) • 1 - (g' : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef := by
  have hKHerm : (twoSidedEnergyTruncation X (N + A) Y t).IsHermitian :=
    ((Matrix.isHermitian_energyTruncation X t).add (hN.add hA)).add
      (Matrix.isHermitian_energyTruncation Y t)
  apply (hKHerm.posSemidef_gap_iff e' g' φ).mpr
  intro v
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (twoSidedEnergyTruncation X (N + A) Y t)]
  exact hquad v

/-- **AKLV Theorem 6.1 on the normalized nearest-neighbour chain.**
For `t ≥ 32768 (e+g)/g²`, separate clipping of the exterior blocks has
an actual unit ground vector, gap at least `g/2`, and phase-aligned
squared distance at most `exp(-t/16)` from the original ground vector.
The regional positivity and `0 ≤ e ≤ 6` are precisely the normalization
of Section 6.1; commutations, decompositions and all analytic estimates
are derived. Source: arXiv:1301.1162v1, Theorem 6.1 and Section 6.3. -/
theorem normalized_chain_robustness {L q : ℕ}
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val < b.val) (x m y e g t : ℝ)
    (hX : (leftCutBlock Φ a x).PosSemidef)
    (hN : (middleCutBlock Φ a b m).PosSemidef)
    (hY : (rightCutBlock Φ b y).PosSemidef)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (he0 : 0 ≤ e) (he6 : e ≤ 6) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 32768 * (e + g) / g ^ 2 ≤ t) :
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let X := leftCutBlock Φ a x
    let N := middleCutBlock Φ a b m
    let Y := rightCutBlock Φ b y
    let H := Φ.hamiltonian - ((x + m + y : ℝ) : ℂ) • 1
    let K := twoSidedEnergyTruncation X (N + (Φ.term a + Φ.term b)) Y t
    ι H Ω = (e : ℂ) • Ω →
    (H - (e : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
    ∃ (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
      ‖φ‖ = 1 ∧ ι K φ = (e' : ℂ) • φ ∧ 0 ≤ e' ∧ e' ≤ e ∧
      (K - (e' : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
        (1 - Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
      ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  intro ι X N Y H _ heig hgap
  obtain ⟨I, hB⟩ := exists_normalizedCutBlock_eq_sum_sub Φ a b hab x m y
  obtain ⟨hXN, hXY, hNY⟩ := normalizedCutBlock_commutations Φ a b hab x m y
  have hH : X + N + Y + (Φ.term a + Φ.term b) = H := normalizedCutBlock_sum Φ a b hab x m y
  obtain ⟨e', φ, hφ, hφeig, he'0, he'e, hquad, θ, hθ⟩ :=
    exists_robust_ground_twoSidedEnergyTruncation I Φ h0 h1 a b (x + m + y) e g t
    X N Y hX hN hY hXN hXY hNY hB Ω hΩ he0 he6 hg hg1 ht
    (by simpa only [hH] using heig) (by
      intro v
      have hv := hgap.gap_le v
      rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin H] at hv
      change g * (‖v‖ ^ 2 - ‖⟪Ω, v⟫_ℂ‖ ^ 2) ≤ (⟪v, ι H v⟫_ℂ).re - e * ‖v‖ ^ 2 at hv
      simpa only [hH] using hv)
  have hAHerm : (Φ.term a + Φ.term b).IsHermitian := IsSelfAdjoint.of_nonneg
    (add_nonneg (h0 a) (h0 b))
  exact ⟨e', φ, hφ, hφeig, he'0, he'e,
    posSemidef_gap_twoSidedEnergyTruncation_of_quadratic X N Y (Φ.term a + Φ.term b)
      hN.isHermitian hAHerm t e' (g / 2) φ hquad, θ, hθ⟩

end TNLean.MPS.AreaLaw.AKLV
