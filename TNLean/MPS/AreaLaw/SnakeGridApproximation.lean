/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SnakeGridGeometry
import TNLean.MPS.AreaLaw.SnakeGridParameters
import TNLean.MPS.AreaLaw.SequentialTruncation
import TNLean.PEPS.AreaLaw.TailParameter
import TNLean.PEPS.AreaLaw.TheoremStatements
import QICLean.Entropy.RegionCovariance

/-!
# Snake-order matrix product approximation on an open square

The uniform area law and the actual finite-range marginal-tail estimate give
a normalized open MPS with error `1/L` and bond at most `exp (C L)`. The
constant is chosen before the square size, Hamiltonian and ground vector.
There are `L² - 1` internal cuts. Each has at most `L + 1` boundary edges;
the finite-range logarithmic budget is therefore linear in `L`.

Source: the square-grid comparison in the polynomial-PEPS manuscript,
Section 1, and the one-dimensional note,
`part2a_mps_information.tex`, `sec:shortcut`, `thm:Bshort`, lines 73–92.
The older reference to Part IIb, Section 7, does not locate this argument.
-/

open Matrix TNLean.Lattice

namespace TNLean.MPS.AreaLaw

private theorem trace_reindexed_complement_mul {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (Q ρ : Matrix m m ℂ) :
    ((1 - Q.submatrix e.symm e.symm) * ρ.submatrix e.symm e.symm).trace =
      ((1 - Q) * ρ).trace := by
  have hsub : 1 - Q.submatrix e.symm e.symm = (1 - Q).submatrix e.symm e.symm := by
    rw [← Matrix.submatrix_one_equiv e.symm]
    rfl
  rw [hsub, Matrix.submatrix_mul_equiv, Matrix.trace_submatrix_equiv]

/-- The physical square vector in actual snake coordinates. This is a linear
isometry, so the vector error is the error on the original open square.
Source: the tensor-factor relabelling in the square-grid MPS comparison of
the polynomial-PEPS manuscript, Section 1. -/
noncomputable def snakeGridStateEquiv (L q : ℕ) :
    StateSpace (PEPS.AreaLaw.rectangularDomain L L) q ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (L * L) → Fin q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Entropy.siteConfigurationEquiv (n := fun _ ↦ q) (n' := fun _ ↦ q)
      (snakeGridEquiv L).symm (fun _ ↦ Equiv.refl _))

/-- A one-site square vector already has a bond-one open MPS representation.
There are no internal cuts. -/
theorem isOpenMPS_snakeGridStateEquiv_one (q : ℕ)
    (Ω : StateSpace (PEPS.AreaLaw.rectangularDomain 1 1) q) :
    IsOpenMPS (1 * 1) q 1 (fun x ↦ snakeGridStateEquiv 1 q Ω x) := by
  apply isOpenMPS_of_internal_cutMatrix_rank_le
  intro k hk hkL
  omega

/-- The actual finite-range tail budget of every snake prefix is linear in
the side length. No entropy or interaction-count estimate is assumed.
Source: area-law `eq:initial-local-tail-parameter` and the square-grid
cutwidth comparison in the polynomial-PEPS manuscript, Section 1. -/
theorem cutLogBudget_snakeGridPrefix_le {q : ℕ} (hq : 1 ≤ q) (R L k : ℕ) :
    cutLogBudget (PEPS.AreaLaw.rectangularDomain L L) q R (snakeGridPrefix L k) ≤
      PEPS.AreaLaw.tailParameterConstant q R * ((L : ℝ) + 2) := by
  have hC := PEPS.AreaLaw.one_le_tailParameterConstant hq R
  have hcard : ((edgeBoundary (PEPS.AreaLaw.rectangularDomain L L)
      (snakeGridPrefix L k)).card : ℝ) ≤ (L : ℝ) + 1 := by
    exact_mod_cast card_edgeBoundary_snakeGridPrefix_le L k
  exact (PEPS.AreaLaw.cutLogBudget_le_edgeBoundary hq R _).trans
    (mul_le_mul_of_nonneg_left (by linarith) (by linarith))

/-- A uniform area law implies the normalized snake MPS approximation, with
the exponential constant chosen before the square, Hamiltonian and ground
vector. All Hamiltonian assumptions are those of the finite-range lattice
model. Source: the square-grid comparison in the polynomial-PEPS manuscript,
Section 1, using `part2a_mps_information.tex`,
`sec:shortcut`, proof of `thm:Bshort`, lines 73–92. -/
theorem exists_snakeGridMPS_of_uniformAreaLaw (harea : PEPS.AreaLaw.UniformAreaLaw)
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 2 ≤ L →
      ∀ H : LocalHamiltonian (PEPS.AreaLaw.rectangularDomain L L) q R J,
      ∀ E₀ : ℝ, ∀ Ω : StateSpace (PEPS.AreaLaw.rectangularDomain L L) q,
        IsGappedGroundState _ q H.operator E₀ Ω Δ →
        ∃ (D : ℕ) (Φ : StateSpace (PEPS.AreaLaw.rectangularDomain L L) q),
          ‖Φ‖ = 1 ∧ IsOpenMPS (L * L) q D (fun x ↦ snakeGridStateEquiv L q Φ x) ∧
          ‖Φ - Ω‖ ≤ 1 / (L : ℝ) ∧ (D : ℝ) ≤ Real.exp (C * L) := by
  classical
  obtain ⟨C₀, hC₀, harea⟩ := harea q hq R J Δ hJ hΔ
  let b : ℝ := Real.sqrt (2 * Real.exp (Real.exp 1 / 2))
  have hb : 1 ≤ b := by
    have h := Real.one_le_exp (by positivity : 0 ≤ Real.exp 1 / 2)
    have : (1 : ℝ) ≤ 2 * Real.exp (Real.exp 1 / 2) := by linarith
    simpa [b] using Real.sqrt_le_sqrt this
  have hbpos : 0 < b := by linarith
  have hb2 : b ^ 2 = 2 * Real.exp (Real.exp 1 / 2) := Real.sq_sqrt (by positivity)
  let a : ℝ := (1 + J / Δ) * PEPS.AreaLaw.tailParameterConstant q R
  have ha : 0 < a := by
    have hbudget := PEPS.AreaLaw.one_le_tailParameterConstant hq R
    dsimp [a]
    positivity
  let C : ℝ := 2 * C₀ + 64 * Real.sqrt (2 * a) * (Real.log (2 * b) + 6)
  have hC : 0 ≤ C := by
    have hlog : 0 ≤ Real.log (2 * b) := Real.log_nonneg (by linarith)
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro L hL H E₀ Ω hgs
  have hLreal : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hN : 1 ≤ L * L := by nlinarith
  have hNreal : (1 : ℝ) ≤ (L * L : ℕ) := by exact_mod_cast hN
  let ε : ℝ := 1 / (L : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by dsimp [ε]; rw [div_le_iff₀ hLpos]; linarith
  let s : ℝ := Real.sqrt (a * ((L : ℝ) + 2))
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  let y : ℝ := 2 * ((L * L : ℕ) : ℝ) * b / ε
  have hy : 1 < y := by
    dsimp [y]
    apply (lt_div_iff₀ hε).2
    nlinarith
  let w : ℝ := 64 * s * Real.log y
  have hw : 0 ≤ w := mul_nonneg (by positivity) (Real.log_nonneg hy.le)
  let ψ := snakeGridStateEquiv L q Ω
  have hψ : ‖ψ‖ = 1 := (snakeGridStateEquiv L q).norm_map Ω |>.trans hgs.1
  let A := snakeGridPrefix L
  let S : ℕ → ℝ := fun k ↦ regionalEntropy _ q Ω (A k)
  let ρ := fun k ↦ reducedState _ q Ω (A k)
  let e := (snakeGridEquiv L).symm
  have hA (k : ℕ) (v : Site (PEPS.AreaLaw.rectangularDomain L L)) :
      v ∈ A k ↔ e v ∈ leftBlock (L * L) k := by simp [A, e]
  let f := fun k ↦ Entropy.regionConfigurationEquiv (n := fun _ ↦ q) (n' := fun _ ↦ q)
    (A k) (leftBlock (L * L) k) e (hA k) (fun _ ↦ Equiv.refl _)
  let Q := fun k ↦ spectralProjectionGE (ρ k) (Real.exp (-(S k + w)))
  let P : ∀ k, LeftBlockMatrix (L * L) q k :=
    fun k ↦ (Q k).submatrix (f k).symm (f k).symm
  have hQ (k : ℕ) : IsStarProjection (Q k) :=
    (reducedState_isHermitian _ q Ω (A k)).isStarProjection_spectralProjectionGE _
  have hP (k : ℕ) : IsStarProjection (P k) :=
    (hQ k).map (Matrix.reindexStarAlgEquiv (f k))
  have hρ (k : ℕ) : Entropy.regionState (leftBlock (L * L) k) ψ =
      (ρ k).submatrix (f k).symm (f k).symm := by
    rw [show ρ k = Entropy.regionState (A k) Ω from reducedState_eq_regionState _ _]
    exact Entropy.regionState_relabel _ _ e (hA k) _ Ω
  have hS (k : ℕ) : S k ≤ C₀ * ((L : ℝ) + 1) := by
    have h := harea _ H E₀ Ω hgs (A k)
    have hc : ((edgeBoundary _ (A k)).card : ℝ) ≤ (L : ℝ) + 1 := by
      exact_mod_cast card_edgeBoundary_snakeGridPrefix_le L k
    exact h.trans (mul_le_mul_of_nonneg_left hc hC₀)
  have hbudget (k : ℕ) :
      Real.sqrt ((1 + J / Δ) * cutLogBudget _ q R (A k)) ≤ s := by
    apply Real.sqrt_le_sqrt
    dsimp [a]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (cutLogBudget_snakeGridPrefix_le hq R L k)
      (by positivity)
  have hmass (k : ℕ) :
      (((1 - P k) * Entropy.regionState (leftBlock (L * L) k) ψ).trace.re) ≤
        2 * Real.exp (Real.exp 1 / 2) * Real.exp (-(w / (32 * s))) := by
    have htrace : ((1 - P k) * Entropy.regionState (leftBlock (L * L) k) ψ).trace =
        ((1 - Q k) * ρ k).trace := by
      rw [hρ]
      exact trace_reindexed_complement_mul (f k) (Q k) (ρ k)
    rw [htrace]
    refine (Matrix.PosSemidef.trace_complement_spectralProjectionGE_le_surprisalTail
      (reducedState_posSemidef _ q Ω (A k)) (S k) w).trans ?_
    refine (H.surprisalTail_reducedState_le hJ.le hΔ hgs (A k) w |>.trans
      (min_le_right _ _)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have ht : 0 < Real.sqrt ((1 + J / Δ) * cutLogBudget _ q R (A k)) := by
      have hb' := Entropy.one_le_cutLogBudget
        (Entropy.crossingTerms (fun X : AdmissibleSupport _ R ↦ X.1) (A k))
        (Entropy.supportDim (fun _ ↦ q) ∘ fun X : AdmissibleSupport _ R ↦ X.1)
      change 1 ≤ cutLogBudget _ q R (A k) at hb'
      apply Real.sqrt_pos.mpr
      positivity
    exact div_le_div_of_nonneg_left hw (by positivity)
      (mul_le_mul_of_nonneg_left (hbudget k) (by norm_num))
  have hone : Real.sqrt (2 * Real.exp (Real.exp 1 / 2) *
      Real.exp (-(w / (32 * s)))) = ε / (2 * ((L * L : ℕ) : ℝ)) := by
    have hexp : Real.exp (-(w / (32 * s))) = y⁻¹ ^ 2 := by
      have hw' : w / (32 * s) = 2 * Real.log y := by dsimp [w]; field_simp; ring
      rw [hw', show -(2 * Real.log y) = Real.log (y⁻¹ ^ 2) by
        rw [Real.log_pow, Real.log_inv]; push_cast; ring,
        Real.exp_log (by positivity)]
    rw [hexp, ← hb2]
    have ht : b ^ 2 * y⁻¹ ^ 2 = (ε / (2 * ((L * L : ℕ) : ℝ))) ^ 2 := by
      dsimp [y]
      field_simp
    rw [ht, Real.sqrt_sq (by positivity)]
  obtain ⟨hrank, herr⟩ := sequentialTruncation_prefix_rank_error P ψ hP
  let Ψ := sequentialTruncation P (L * L - 1) ψ
  have hsum : ‖ψ - Ψ‖ ≤ ε / 2 := by
    refine herr.trans ?_
    have hterm (k : ℕ) (_ : k ∈ Finset.Ico 1 (L * L)) :
        Real.sqrt (((1 - P k) * Entropy.regionState (leftBlock (L * L) k) ψ).trace.re)
          ≤ ε / (2 * ((L * L : ℕ) : ℝ)) := by
      rw [← hone]
      exact Real.sqrt_le_sqrt (hmass k)
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hN, Nat.cast_one]
    calc
      _ ≤ ((L * L : ℕ) : ℝ) * (ε / (2 * ((L * L : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ε / 2 := by field_simp
  have hpos : 0 < ‖Ψ‖ := by
    have ht := norm_sub_norm_le ψ Ψ
    rw [hψ] at ht
    linarith
  let χ := (‖Ψ‖ : ℂ)⁻¹ • Ψ
  have hχ : ‖χ‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) (norm_pos_iff.mp hpos)
  have hχerr : ‖χ - ψ‖ ≤ ε := by
    have hd : ‖χ - Ψ‖ = |1 - ‖Ψ‖| := by
      rw [show χ - Ψ = ((‖Ψ‖⁻¹ - 1 : ℝ) : ℂ) • Ψ by simp [χ, sub_smul],
        norm_smul, Complex.norm_real, Real.norm_eq_abs, ← abs_of_nonneg (norm_nonneg Ψ),
        ← abs_mul]
      congr 1
      rw [abs_of_nonneg (norm_nonneg Ψ)]
      field_simp
    have hn : |1 - ‖Ψ‖| ≤ ‖ψ - Ψ‖ := by
      simpa only [hψ] using abs_norm_sub_norm_le ψ Ψ
    have ht := norm_sub_le_norm_sub_add_norm_sub χ Ψ ψ
    rw [hd, norm_sub_rev Ψ ψ] at ht
    linarith
  let D : ℕ := ⌊Real.exp (C₀ * ((L : ℝ) + 1) + w)⌋₊
  have hmps : IsOpenMPS (L * L) q D (fun x ↦ Ψ x) := by
    apply isOpenMPS_of_internal_cutMatrix_rank_le
    intro k hk hkN
    apply Nat.le_floor
    have hr : ((cutMatrix Ψ k).rank : ℝ) ≤ ((P k).rank : ℝ) := by
      exact_mod_cast hrank k hk hkN
    refine hr.trans ?_
    have htrace : (ρ k).trace = 1 := by
      rw [show ρ k = Entropy.regionState (A k) Ω from reducedState_eq_regionState _ _]
      exact Entropy.trace_regionState_eq_one hgs.1
    change (((Q k).submatrix (f k).symm (f k).symm).rank : ℝ) ≤ _
    rw [Matrix.rank_submatrix]
    exact ((reducedState_posSemidef _ q Ω (A k)).rank_spectralProjectionGE_exp_le
      htrace (S k) w).trans (Real.exp_le_exp.mpr (by linarith [hS k]))
  have hmpsχ : IsOpenMPS (L * L) q D (fun x ↦ χ x) := hmps.smul _
  have hDbound : (D : ℝ) ≤ Real.exp (C * L) := by
    refine (Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr ?_)
    have hy' : y = 2 * (L : ℝ) ^ 3 * b := by
      dsimp [y, ε]
      push_cast
      field_simp
    have hwindow := snakeGrid_window_le_linear ha.le hb hLreal
    dsimp [w, s]
    rw [hy']
    dsimp [C]
    nlinarith
  refine ⟨D, (snakeGridStateEquiv L q).symm χ, ?_, ?_, ?_, hDbound⟩
  · exact ((snakeGridStateEquiv L q).symm.norm_map χ).trans hχ
  · simpa only [LinearIsometryEquiv.apply_symm_apply] using hmpsχ
  · rw [← (snakeGridStateEquiv L q).norm_map, map_sub,
      LinearIsometryEquiv.apply_symm_apply]
    exact hχerr

end TNLean.MPS.AreaLaw
