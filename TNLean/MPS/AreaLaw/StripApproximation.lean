/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.StripBufferDiscount
import TNLean.MPS.AreaLaw.MPSApproximation
import QICLean.Entropy.RegionCovariance

/-!
# Physical-site snake prefixes of a bounded-width strip

The ordering lists columns consecutively and reverses the row order in every second
column. The number of physical sites remains `L*w`, each of local dimension `q`.
The entropy and marginal-tail inputs below concern the actual lattice ground vector.

This develops the strip extension proposed in issue #9552, using the one-dimensional
note's marginal tail bound and sequential truncation argument. It does not treat the
strip as a chain of `q^w`-dimensional sites.
-/

open Matrix TNLean.Lattice

namespace TNLean.MPS.AreaLaw

/-- Reverse the rows in odd columns. -/
def stripSnakeRows (L w : ℕ) : Equiv.Perm (Fin L × Fin w) where
  toFun x := (x.1, if Even x.1.val then x.2 else x.2.rev)
  invFun x := (x.1, if Even x.1.val then x.2 else x.2.rev)
  left_inv x := by by_cases hx : Even x.1.val <;> simp [hx]
  right_inv x := by by_cases hx : Even x.1.val <;> simp [hx]

/-- Column-snake order on the actual physical sites. -/
def stripSnakeEquiv (L w : ℕ) : Fin (L * w) ≃ Site (stripDomain L w) :=
  finProdFinEquiv.symm.trans ((stripSnakeRows L w).trans (stripSiteEquiv L w))

/-- A chain position belongs to its quotient column, including the reversed columns. -/
theorem stripColumn_stripSnakeEquiv {L w : ℕ} (i : Fin (L * w)) :
    stripColumn (stripSnakeEquiv L w i) = i.val / w := by
  change ((i.val / w : ℕ) : ℤ).toNat = i.val / w
  simp only [Int.toNat_natCast]

/-- The physical region of a snake prefix. -/
def stripSnakePrefix (L w k : ℕ) : Finset (Site (stripDomain L w)) :=
  (leftBlock (L * w) k).map (stripSnakeEquiv L w).toEmbedding

/-- A snake prefix contains every earlier column. -/
theorem stripInterval_subset_snakePrefix {L w k : ℕ} (hw : 1 ≤ w) :
    stripInterval L w 0 (k / w) ⊆ stripSnakePrefix L w k := by
  intro x hx
  let i := (stripSnakeEquiv L w).symm x
  have hi : stripColumn x = i.val / w := by
    simpa only [i, Equiv.apply_symm_apply] using stripColumn_stripSnakeEquiv i
  have hx' := (mem_stripInterval.mp hx).2
  have hik : i.val < k := by
    have hiw := Nat.mod_add_div i.val w
    have hkw := Nat.mod_add_div k w
    have hmod := Nat.mod_lt i.val (by omega : 0 < w)
    rw [hi] at hx'
    have hstep := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hx')
    simp only [Nat.succ_eq_add_one, mul_add, mul_one] at hstep
    nlinarith only [hiw, hkw, hmod, hstep, Nat.zero_le (k % w)]
  apply Finset.mem_map.mpr
  exact ⟨i, by simpa using hik, (stripSnakeEquiv L w).apply_symm_apply x⟩

/-- A snake prefix uses no column beyond its last partial column. -/
theorem snakePrefix_subset_stripInterval {L w k : ℕ} (_hw : 1 ≤ w) :
    stripSnakePrefix L w k ⊆ stripInterval L w 0 (k / w + 1) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  have hik : i.val < k := by simpa using hi
  rw [mem_stripInterval]
  change 0 ≤ stripColumn (stripSnakeEquiv L w i) ∧ _
  rw [stripColumn_stripSnakeEquiv]
  exact ⟨Nat.zero_le _, Nat.lt_succ_of_le (Nat.div_le_div_right hik.le)⟩

/-- The snake prefix differs from a whole-column prefix in at most `w` sites. -/
theorem card_snakePrefix_sdiff_le {L w k : ℕ} (hw : 1 ≤ w) :
    (stripSnakePrefix L w k \ stripInterval L w 0 (k / w)).card ≤ w := by
  classical
  have hsub : stripSnakePrefix L w k \ stripInterval L w 0 (k / w) ⊆
      stripInterval L w (k / w) (k / w + 1) := by
    intro x hx
    have hcol := mem_stripInterval.mp (snakePrefix_subset_stripInterval hw
      (Finset.mem_sdiff.mp hx).1)
    have hn := (Finset.mem_sdiff.mp hx).2
    simp only [mem_stripInterval] at hn ⊢
    omega
  exact (Finset.card_le_card hsub).trans (by
    simpa using card_stripInterval_le L w (k / w) (k / w + 1))

/-- Entropy of an actual snake prefix, including the partial final column. -/
theorem regionEntropy_stripSnakePrefix_le {L w q R : ℕ} {J Δ : ℝ}
    (hq : 1 ≤ q) (hw : 1 ≤ w) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : LocalHamiltonian (stripDomain L w) q R J) {E₀ : ℝ}
    {Ω : StateSpace (stripDomain L w) q}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (k : ℕ) :
    Entropy.regionEntropy (n := fun _ : Site (stripDomain L w) ↦ q)
      (stripSnakePrefix L w k) Ω ≤
      stripAreaLawConst q R * (1 + J / Δ) * (w : ℝ) ^ 2 + w * Real.log q := by
  let P := stripInterval L w 0 (k / w)
  let D := stripSnakePrefix L w k \ P
  have hPD : P ∪ D = stripSnakePrefix L w k :=
    Finset.union_sdiff_of_subset (stripInterval_subset_snakePrefix hw)
  have hu := regionEntropy_union_le hgs.1 (show Disjoint P D from Finset.disjoint_sdiff)
  rw [hPD] at hu
  have hP := regionEntropy_stripInterval_le hq hw hJ hΔ h hgs 0 (k / w)
  have hD := regionEntropy_le_card_mul_log hgs.1 D
  have hcard : (D.card : ℝ) ≤ w := by exact_mod_cast card_snakePrefix_sdiff_le hw
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hb := hD.trans (mul_le_mul_of_nonneg_right hcard hlog)
  linarith only [hu, hP, hb]

/-- A uniform coefficient for the logarithmic budget of arbitrary partial-column prefixes. -/
noncomputable def stripPrefixBudgetConst (q R : ℕ) : ℝ :=
  1 + ((R + 1) * 2 ^ (2 * R * (R + 1)) : ℕ) *
    Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))) ^ 2

/-- Prefix budgets grow linearly in width, including cuts inside a column. -/
theorem cutLogBudget_stripSnakePrefix_le {q w : ℕ} (hq : 1 ≤ q) (hw : 1 ≤ w)
    (L R k : ℕ) :
    Entropy.cutLogBudget
      (Entropy.crossingTerms (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1)
        (stripSnakePrefix L w k))
      (Entropy.supportDim (fun _ : Site (stripDomain L w) ↦ q) ∘ fun X ↦ X.1) ≤
      stripPrefixBudgetConst q R * w := by
  have hc : ((Entropy.crossingTerms
      (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1)
      (stripSnakePrefix L w k)).card : ℝ) ≤
      (((R + 1) * 2 ^ (2 * R * (R + 1))) * w : ℕ) := by
    exact_mod_cast card_crossingTerms_stripPrefix_le (stripSnakePrefix L w k)
      (stripInterval_subset_snakePrefix hw) (snakePrefix_subset_stripInterval hw)
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  refine (TNLean.PEPS.AreaLaw.cutLogBudget_le_card hq _).trans ?_
  unfold stripPrefixBudgetConst
  push_cast at hc ⊢
  nlinarith only [mul_le_mul_of_nonneg_right hc
    (sq_nonneg (Real.log (Real.exp 1 * (q : ℝ) ^ (1 + 2 * R * (R + 1))))), hw']

open scoped Matrix.Norms.L2Operator in
/-- The actual lattice marginal at every snake prefix has the gap-controlled tail. -/
theorem surprisalTail_stripSnakePrefix_le {L w q R : ℕ} {J Δ : ℝ}
    (hq : 1 ≤ q) (hw : 1 ≤ w) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : LocalHamiltonian (stripDomain L w) q R J) {E₀ : ℝ}
    {Ω : StateSpace (stripDomain L w) q}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    Entropy.surprisalTail
      (Entropy.regionState_isHermitian (n := fun _ : Site (stripDomain L w) ↦ q)
        (stripSnakePrefix L w k) Ω).eigenvalues
      (Entropy.regionEntropy (stripSnakePrefix L w k) Ω) u ≤
      2 * Real.exp (Real.exp 1 / 2) * Real.exp
        (-(u / (32 * Real.sqrt ((1 + J / Δ) * (stripPrefixBudgetConst q R * w))))) := by
  let A := stripSnakePrefix L w k
  let budget := Entropy.cutLogBudget
    (Entropy.crossingTerms (fun X : AdmissibleSupport (stripDomain L w) R ↦ X.1) A)
    (Entropy.supportDim (fun _ : Site (stripDomain L w) ↦ q) ∘ fun X ↦ X.1)
  have hb := cutLogBudget_stripSnakePrefix_le hq hw L R k
  have hb1 : 1 ≤ budget := Entropy.one_le_cutLogBudget _ _
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hs : 0 < Real.sqrt ((1 + J / Δ) * budget) := Real.sqrt_pos.mpr (by nlinarith)
  obtain ⟨hΩ, heig, hgap⟩ := hgs
  change toEuclideanLin (∑ X, h.term X) Ω = (E₀ : ℂ) • Ω at heig
  have ht := Entropy.surprisalTail_cut_le (n := fun _ : Site (stripDomain L w) ↦ q)
    (h := h.term) (D := fun X ↦ X.1) (B := A)
    (fun X ↦ QuantumCircuit.isSupportedOn_of_mem_supportedOperators (h.supported X))
    h.hermitian hJ h.norm_le hΩ hΔ heig hgap rfl
    (Entropy.regionState_isHermitian A Ω) u
  refine (ht.trans (min_le_right _ _)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_left hu (mul_pos (by norm_num) hs)
  gcongr

/-- Surprisal tails are invariant under a bijective matrix reindexing. -/
private theorem surprisalTail_submatrix_equiv
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {ρ : Matrix α α ℂ} (hρ : ρ.IsHermitian) (e : β ≃ α) (S u : ℝ) :
    Entropy.surprisalTail (hρ.submatrix e).eigenvalues S u =
      Entropy.surprisalTail hρ.eigenvalues S u := by
  have hc : (ρ.submatrix e e).charpoly = ρ.charpoly :=
    Matrix.charpoly_reindex e.symm ρ
  have he : Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ (hρ.submatrix e).eigenvalues) Finset.univ.val =
      Multiset.map ((RCLike.ofReal : ℝ → ℂ) ∘ hρ.eigenvalues) Finset.univ.val := by
    rw [← (hρ.submatrix e).roots_charpoly_eq_eigenvalues,
      ← hρ.roots_charpoly_eq_eigenvalues, hc]
  have hf := congrArg (fun t : Multiset ℂ ↦
    (t.map fun z ↦ if u < |-Real.log z.re - S| then z.re else 0).sum) he
  simpa only [Entropy.surprisalTail, Finset.sum, Multiset.map_map, Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using hf

/-- The physical ground vector, expressed on the `L*w` sites of the snake chain. -/
noncomputable def stripSnakeState {L w : ℕ} (q : ℕ)
    (Ω : StateSpace (stripDomain L w) q) : EuclideanSpace ℂ (Fin (L * w) → Fin q) :=
  Entropy.relabelVector (n := fun _ : Site (stripDomain L w) ↦ q)
    (n' := fun _ : Fin (L * w) ↦ q) (stripSnakeEquiv L w).symm (fun _ ↦ Equiv.refl _) Ω

/-- Snake relabelling preserves the normalization of the original lattice vector. -/
theorem norm_stripSnakeState {L w q : ℕ} (Ω : StateSpace (stripDomain L w) q) :
    ‖stripSnakeState q Ω‖ = ‖Ω‖ := Entropy.norm_relabelVector _ _ Ω

/-- Regional entropy on the snake chain is the entropy of the actual physical prefix. -/
theorem regionEntropy_stripSnakeState {L w q : ℕ} (Ω : StateSpace (stripDomain L w) q)
    (k : ℕ) :
    Entropy.regionEntropy (n := fun _ : Fin (L * w) ↦ q) (leftBlock (L * w) k)
      (stripSnakeState q Ω) = Entropy.regionEntropy (stripSnakePrefix L w k) Ω := by
  apply Entropy.regionEntropy_relabel
    (stripSnakePrefix L w k) (leftBlock (L * w) k) (stripSnakeEquiv L w).symm
    (fun x ↦ by simp [stripSnakePrefix]) (fun _ ↦ Equiv.refl _)

/-- The actual chain marginal inherits the physical prefix tail under the snake bijection. -/
theorem surprisalTail_stripSnakeState_le {L w q R : ℕ} {J Δ : ℝ}
    (hq : 1 ≤ q) (hw : 1 ≤ w) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : LocalHamiltonian (stripDomain L w) q R J) {E₀ : ℝ}
    {Ω : StateSpace (stripDomain L w) q}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    Entropy.surprisalTail
      (Entropy.regionState_isHermitian (n := fun _ : Fin (L * w) ↦ q)
        (leftBlock (L * w) k) (stripSnakeState q Ω)).eigenvalues
      (Entropy.regionEntropy (leftBlock (L * w) k) (stripSnakeState q Ω)) u ≤
      2 * Real.exp (Real.exp 1 / 2) * Real.exp
        (-(u / (32 * Real.sqrt ((1 + J / Δ) * (stripPrefixBudgetConst q R * w))))) := by
  let A := stripSnakePrefix L w k
  let P := leftBlock (L * w) k
  let e := (stripSnakeEquiv L w).symm
  have hA : ∀ x, x ∈ A ↔ e x ∈ P := fun x ↦ by simp [A, P, e, stripSnakePrefix]
  let eA := Entropy.regionConfigurationEquiv (n := fun _ : Site (stripDomain L w) ↦ q)
    (n' := fun _ : Fin (L * w) ↦ q) A P e hA (fun _ ↦ Equiv.refl _)
  have hrho := Entropy.regionState_relabel (n := fun _ : Site (stripDomain L w) ↦ q)
    (n' := fun _ : Fin (L * w) ↦ q) A P e hA (fun _ ↦ Equiv.refl (Fin q)) Ω
  have he : (Entropy.regionState_isHermitian P (stripSnakeState q Ω)).eigenvalues =
      ((Entropy.regionState_isHermitian A Ω).submatrix eA.symm).eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).mpr
    exact congrArg Matrix.charpoly hrho
  rw [he, surprisalTail_submatrix_equiv, regionEntropy_stripSnakeState]
  exact surprisalTail_stripSnakePrefix_le hq hw hJ hΔ h hgs k u hu

/-- Sequential truncation and normalization from uniform prefix entropy bounds and the
two-sided surprisal tail at the chosen width. Source: the one-dimensional note,
Section 7, proof of Theorem B, with abstract entropy and concentration constants. -/
private theorem strip_approximation_of_prefix_bounds
    {q : ℕ} {C s : ℝ} (hC : 0 ≤ C) (hs : 0 < s)
    {L : ℕ} (hL : 1 ≤ L)
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hS : ∀ k : ℕ,
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω ≤ C)
    (htail :
      let w : ℝ := 64 * s * Real.log (2 * (L : ℝ) * tailPrefactorRoot / ε)
      0 ≤ w → ∀ k ∈ Finset.Ico 1 L,
        Entropy.surprisalTail
          (Entropy.regionState_isHermitian
            (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω).eigenvalues
          (Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω) w ≤
          2 * Real.exp (Real.exp 1 / 2) * Real.exp (-(w / (32 * s)))) :
    ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
      IsOpenMPS L q
        ⌊Real.exp (C + 64 * s * Real.log (2 * (L : ℝ) * tailPrefactorRoot / ε))⌋₊
        (fun x ↦ Φ x) ∧ ‖Φ - Ω‖ ≤ ε := by
  classical
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  set y : ℝ := 2 * (L : ℝ) * tailPrefactorRoot / ε
  have hy : 1 < y := by
    dsimp [y]
    apply (lt_div_iff₀ hε).2
    have hroot := one_lt_tailPrefactorRoot
    have := mul_le_mul_of_nonneg_right hL' tailPrefactorRoot_pos.le
    nlinarith
  set w : ℝ := 64 * s * Real.log y
  have hw0 : 0 ≤ w := by
    dsimp [w]
    exact mul_nonneg (by positivity) (Real.log_nonneg hy.le)
  -- the sequential truncation
  obtain ⟨Φ₀, hrank, hdist⟩ := exists_sequentialTruncation Ω hΩ w
  -- the distance
  have hsum : ∑ k ∈ Finset.Ico 1 L, Real.sqrt (Entropy.surprisalTail
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω).eigenvalues
      (Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω) w) ≤
      ((L : ℝ) - 1) * (ε / (2 * (L : ℝ))) := by
    have hone : Real.sqrt (2 * Real.exp (Real.exp 1 / 2) * Real.exp (-(w / (32 * s)))) =
        ε / (2 * (L : ℝ)) := by
      have hexp : Real.exp (-(w / (32 * s))) = y⁻¹ ^ 2 := by
        have hw : w / (32 * s) = 2 * Real.log y := by
          dsimp [w]
          field_simp
          ring
        rw [hw, show -(2 * Real.log y) = Real.log (y⁻¹ ^ 2) by
          rw [Real.log_pow, Real.log_inv]; push_cast; ring,
          Real.exp_log (by positivity)]
      rw [hexp, ← tailPrefactorRoot_sq]
      have hroot := tailPrefactorRoot_pos
      have : tailPrefactorRoot ^ 2 * y⁻¹ ^ 2 = (ε / (2 * (L : ℝ))) ^ 2 := by
        dsimp [y]
        field_simp
      rw [this, Real.sqrt_sq (by positivity)]
    have hterm : ∀ k ∈ Finset.Ico 1 L, Real.sqrt (Entropy.surprisalTail
        (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω).eigenvalues
        (Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω) w) ≤
        ε / (2 * (L : ℝ)) := fun k hk ↦ by
      rw [← hone]
      exact Real.sqrt_le_sqrt (htail hw0 k hk)
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hL, Nat.cast_one]
  have hδ : ‖Ω - Φ₀‖ ≤ ε / 2 := by
    refine hdist.trans (hsum.trans ?_)
    rw [show ((L : ℝ) - 1) * (ε / (2 * (L : ℝ))) =
        ((L : ℝ) - 1) * ε / (2 * (L : ℝ)) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hδ' : ε / 2 ≤ 1 / 2 := by linarith
  -- normalization
  have hΦ₀norm : 1 - ε / 2 ≤ ‖Φ₀‖ := by
    have := norm_sub_norm_le Ω Φ₀
    linarith
  have hΦ₀pos : 0 < ‖Φ₀‖ := by linarith
  set Φ₁ : EuclideanSpace ℂ (Fin L → Fin q) := (‖Φ₀‖ : ℂ)⁻¹ • Φ₀ with hΦ₁def
  have hΦ₁norm : ‖Φ₁‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) (norm_pos_iff.mp hΦ₀pos)
  have hΦ₁dist : ‖Φ₁ - Ω‖ ≤ ε := by
    have h := norm_inv_norm_smul_sub_le_two_mul hΩ (norm_pos_iff.mp hΦ₀pos)
    rw [← hΦ₁def, norm_sub_rev Φ₀ Ω] at h
    linarith
  -- the matrix product structure
  have hD : ∀ k, (cutMatrix Φ₀ k).rank ≤ ⌊Real.exp (C + w)⌋₊ := by
    intro k
    apply Nat.le_floor
    refine (hrank k).trans (max_le ?_ ?_)
    · exact Real.one_le_exp (by linarith)
    · exact Real.exp_le_exp.mpr (by linarith [hS k])
  have hmps₀ := isOpenMPS_of_cutMatrix_rank_le Φ₀ hD
  refine ⟨Φ₁, hΦ₁norm, ?_, hΦ₁dist⟩
  have := hmps₀.smul (‖Φ₀‖ : ℂ)⁻¹
  convert this using 2 with x
  simp [hΦ₁def]

/-- The coefficient of the polynomial length exponent in the strip MPS bound. -/
noncomputable def stripApproximationExponent (q R : ℕ) : ℝ :=
  128 * Real.sqrt (stripPrefixBudgetConst q R)

/-- The coefficient in the exponential width factor of the strip MPS bound. -/
noncomputable def stripApproximationConst (q R : ℕ) : ℝ :=
  stripAreaLawConst q R + Real.log q +
    64 * Real.sqrt (stripPrefixBudgetConst q R) * (Real.log (2 * tailPrefactorRoot) + 1)

/-- The explicit truncation bond has the required separation of width and length. -/
private theorem strip_bond_bound {q R L w : ℕ} {J Δ : ℝ}
    (hL : 1 ≤ L) (hw : 1 ≤ w) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    Real.exp (stripAreaLawConst q R * (1 + J / Δ) * (w : ℝ) ^ 2 + w * Real.log q +
      64 * Real.sqrt ((1 + J / Δ) * (stripPrefixBudgetConst q R * w)) *
        Real.log (2 * ((L * w : ℕ) : ℝ) * tailPrefactorRoot / (1 / (L : ℝ)))) ≤
      Real.exp (stripApproximationConst q R * (1 + J / Δ) * (w : ℝ) ^ 2) *
        (L : ℝ) ^ (stripApproximationExponent q R * Real.sqrt (1 + J / Δ) * w) := by
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have ht : 1 ≤ 1 + J / Δ := by linarith only [hθ]
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hLp : (0 : ℝ) < L := by linarith only [hL']
  have hwp : (0 : ℝ) < w := by linarith only [hw']
  let b := stripPrefixBudgetConst q R
  have hb : 1 ≤ b := by
    unfold b stripPrefixBudgetConst
    exact le_add_of_nonneg_right (by positivity)
  let t := 1 + J / Δ
  have ht0 : 0 ≤ t := by dsimp [t]; linarith only [ht]
  have hst : Real.sqrt t ≤ t := by
    calc _ ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt (by dsimp [t]; nlinarith only [ht])
      _ = t := Real.sqrt_sq ht0
  have hsw : Real.sqrt (w : ℝ) ≤ w := by
    calc _ ≤ Real.sqrt ((w : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith only [hw'])
      _ = _ := Real.sqrt_sq (Nat.cast_nonneg _)
  let s := Real.sqrt (t * (b * w))
  have hsf : s = Real.sqrt b * Real.sqrt t * Real.sqrt w := by
    dsimp only [s]
    rw [Real.sqrt_mul ht0, Real.sqrt_mul (by linarith only [hb])]
    ring
  have hs₁ : s ≤ Real.sqrt b * Real.sqrt t * w := by rw [hsf]; gcongr
  have hs₂ : s ≤ Real.sqrt b * t * w := by
    refine hs₁.trans ?_
    gcongr
  have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL'
  have hlogw : 0 ≤ Real.log (w : ℝ) := Real.log_nonneg hw'
  have hlogw' : Real.log (w : ℝ) ≤ w :=
    (Real.log_le_sub_one_of_pos hwp).trans (by linarith)
  let K := Real.log (2 * tailPrefactorRoot)
  have hK : 0 ≤ K := by
    apply Real.log_nonneg
    have hroot := one_lt_tailPrefactorRoot
    linarith only [hroot]
  have hroot := tailPrefactorRoot_pos
  have hlog : Real.log (2 * ((L * w : ℕ) : ℝ) * tailPrefactorRoot / (1 / (L : ℝ))) =
      2 * Real.log (L : ℝ) + Real.log (w : ℝ) + K := by
    rw [show 2 * ((L * w : ℕ) : ℝ) * tailPrefactorRoot / (1 / (L : ℝ)) =
        (2 * tailPrefactorRoot) * (L : ℝ) ^ 2 * w by push_cast; field_simp]
    rw [Real.log_mul (by positivity) hwp.ne',
      Real.log_mul (by positivity) (pow_ne_zero _ hLp.ne'), Real.log_pow]
    dsimp [K]
    ring
  have hlen := mul_le_mul_of_nonneg_right hs₁ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) hlogL)
  have hrest := mul_le_mul_of_nonneg_right hs₂
    (show 0 ≤ 64 * (Real.log (w : ℝ) + K) by positivity)
  have hwidth : 64 * (Real.sqrt b * t * w) * (Real.log (w : ℝ) + K) ≤
      64 * Real.sqrt b * (K + 1) * t * (w : ℝ) ^ 2 := by
    have hKwidth : Real.log (w : ℝ) + K ≤ (K + 1) * w := by
      nlinarith only [hlogw', mul_nonneg hK (sub_nonneg.mpr hw')]
    have hh := mul_le_mul_of_nonneg_left hKwidth
      (show 0 ≤ 64 * Real.sqrt b * t * w by positivity)
    nlinarith only [hh]
  have hqlog : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hwθ : (w : ℝ) ≤ t * (w : ℝ) ^ 2 := by
    calc _ ≤ (w : ℝ) ^ 2 := by nlinarith only [hw']
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) ht
  have hsites := mul_le_mul_of_nonneg_right hwθ hqlog
  rw [Real.rpow_def_of_pos hLp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  unfold stripApproximationConst stripApproximationExponent
  change _ ≤ (stripAreaLawConst q R + Real.log q + 64 * Real.sqrt b * (K + 1)) *
    t * (w : ℝ) ^ 2 + Real.log (L : ℝ) * (128 * Real.sqrt b * Real.sqrt t * w)
  dsimp only [s] at hlen hrest
  dsimp only [t, b] at hlen hrest hwidth hsites ⊢
  nlinarith only [hlen, hrest, hwidth, hsites]

/-- Normalized MPS approximation of the physical strip ground vector. The bond is on
`L*w` sites of dimension `q` in the explicit column-snake order, and the error is measured
in the original lattice Hilbert space. -/
theorem exists_stripMPS_norm_sub_le {L w q R : ℕ} {J Δ : ℝ}
    (hL : 1 ≤ L) (hw : 1 ≤ w) (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : LocalHamiltonian (stripDomain L w) q R J) {E₀ : ℝ}
    {Ω : StateSpace (stripDomain L w) q}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) :
    ∃ (D : ℕ) (Φ : StateSpace (stripDomain L w) q), ‖Φ‖ = 1 ∧
      IsOpenMPS (L * w) q D (fun x ↦ stripSnakeState q Φ x) ∧ ‖Φ - Ω‖ ≤ 1 / (L : ℝ) ∧
      (D : ℝ) ≤ Real.exp (stripApproximationConst q R * (1 + J / Δ) * (w : ℝ) ^ 2) *
        (L : ℝ) ^ (stripApproximationExponent q R * Real.sqrt (1 + J / Δ) * w) := by
  let C := stripAreaLawConst q R * (1 + J / Δ) * (w : ℝ) ^ 2 + w * Real.log q
  let s := Real.sqrt ((1 + J / Δ) * (stripPrefixBudgetConst q R * w))
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hB : 1 ≤ stripPrefixBudgetConst q R := by
    unfold stripPrefixBudgetConst
    exact le_add_of_nonneg_right (by positivity)
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hA : 0 ≤ stripAreaLawConst q R := by
      unfold stripAreaLawConst stripShellConst stripBudgetConst
      positivity
    positivity
  have hs : 0 < s := by
    apply Real.sqrt_pos.mpr
    have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
    have : 0 < 1 + J / Δ := by linarith only [hθ]
    positivity
  have hN : 1 ≤ L * w := (Nat.mul_le_mul hL hw)
  have hΩ : ‖stripSnakeState q Ω‖ = 1 := (norm_stripSnakeState Ω).trans hgs.1
  have hLp : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hε : 0 < 1 / (L : ℝ) := one_div_pos.mpr hLp
  have hε1 : 1 / (L : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hLp).mpr
    simpa using (show (1 : ℝ) ≤ L by exact_mod_cast hL)
  have hS : ∀ k : ℕ, Entropy.regionEntropy (n := fun _ : Fin (L * w) ↦ q)
      (leftBlock (L * w) k) (stripSnakeState q Ω) ≤ C := by
    intro k
    rw [regionEntropy_stripSnakeState]
    exact regionEntropy_stripSnakePrefix_le hq hw hJ hΔ h hgs k
  obtain ⟨Ψ, hΨ, hmps, hdist⟩ := strip_approximation_of_prefix_bounds hC hs hN hΩ hε hε1 hS
    (fun hu k _ ↦ surprisalTail_stripSnakeState_le hq hw hJ hΔ h hgs k _ hu)
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Entropy.siteConfigurationEquiv (n := fun _ : Site (stripDomain L w) ↦ q)
      (n' := fun _ : Fin (L * w) ↦ q) (stripSnakeEquiv L w).symm (fun _ ↦ Equiv.refl _))
  let Φ := U.symm Ψ
  have hΦ : stripSnakeState q Φ = Ψ := U.apply_symm_apply Ψ
  let D := ⌊Real.exp (C + 64 * s * Real.log
    (2 * ((L * w : ℕ) : ℝ) * tailPrefactorRoot / (1 / (L : ℝ))))⌋₊
  refine ⟨D, Φ, (U.symm.norm_map Ψ).trans hΨ, ?_, ?_, ?_⟩
  · simpa only [hΦ] using hmps
  · have hn : ‖Φ - Ω‖ = ‖Ψ - stripSnakeState q Ω‖ := by
      rw [← U.norm_map (Φ - Ω), map_sub, show U Φ = Ψ from U.apply_symm_apply Ψ]
      rfl
    exact hn.trans_le hdist
  · exact (Nat.floor_le (Real.exp_pos _).le).trans (strip_bond_bound hL hw hJ hΔ)

/-- The constants in the complete strip MPS theorem precede both dimensions and all
Hamiltonian data. This is the MPS approximation extension requested by issue #9552. -/
theorem stripMPSApproximation (q R : ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ L w : ℕ, 1 ≤ L → 1 ≤ w → 1 ≤ q →
      ∀ J Δ : ℝ, 0 ≤ J → 0 < Δ →
      ∀ h : LocalHamiltonian (stripDomain L w) q R J, ∀ E₀ : ℝ,
      ∀ Ω : StateSpace (stripDomain L w) q,
      Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      ∃ (D : ℕ) (Φ : StateSpace (stripDomain L w) q), ‖Φ‖ = 1 ∧
        IsOpenMPS (L * w) q D (fun x ↦ stripSnakeState q Φ x) ∧ ‖Φ - Ω‖ ≤ 1 / (L : ℝ) ∧
        (D : ℝ) ≤ Real.exp (C * (1 + J / Δ) * (w : ℝ) ^ 2) *
          (L : ℝ) ^ (c * Real.sqrt (1 + J / Δ) * w) := by
  refine ⟨stripApproximationConst q R, stripApproximationExponent q R, ?_, ?_, ?_⟩
  · unfold stripApproximationConst stripAreaLawConst stripShellConst stripBudgetConst
    have hroot := one_lt_tailPrefactorRoot
    have hlog : 0 ≤ Real.log (2 * tailPrefactorRoot) :=
      Real.log_nonneg (by linarith only [hroot])
    positivity
  · unfold stripApproximationExponent
    positivity
  · intro L w hL hw hq J Δ hJ hΔ h E₀ Ω hgs
    exact exists_stripMPS_norm_sub_le hL hw hq hJ hΔ h hgs

end TNLean.MPS.AreaLaw
