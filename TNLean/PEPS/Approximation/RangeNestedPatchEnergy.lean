/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NestedPatchEnergy
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.AreaLaw.Geometry.RangeNestedPatches

/-!
# Energy of minimizing nested patch filters at interaction range `R`

For a Hamiltonian of range `R ≥ 1` on a finite induced lattice domain, with one Hermitian
term of norm at most `J` per admissible support, the normalized output at any feasible
minimum of the regularized patch objective, on the range-`R` nested squares with equal
weights `κ / m`, has excitation energy at most `C_E κ²`, where
`C_E = 18 s_R R μ_R q^(2(v_R - 1)) J`, `s_R = 2 ⌈R / 2⌉`, `v_R = 1 + 2 R (R + 1)` and
`μ_R = 2^(v_R - 1)`.

The argument is the nearest-neighbour one of `NestedPatchEnergy`, with three changes.
Each support is split by at most one selected square because the radii are spaced by
`s_R ≥ R`. A support split by a square has at most `v_R - 1` sites inside it. A split
support contains a site of the inner layer of width `R`, so at most
`R (16 u + 4) μ_R` supports are split by each square.

The filter exponent `κ_R = min (1 / 2) (√(Δ / (1024 C_E)))` keeps the form of the source
choice with `C_E` in place of `36 q² J`.

**Extension beyond the source:** the source proves the energy bound for on-site and
nearest-neighbour interactions with `C_E = 36 q² J`; the range-`R` statement and its
constant are not in the source. The nearest-neighbour theorem
`SquareHamiltonian.nestedPatch_minimizer_energy_le` is unchanged.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
Proposition 4.1, `03-patches.tex`, lines 213–343, `eq:patch-energy-bound` and
`eq:patch-kappa-choice`, read with interactions of range `R` as in *A two-dimensional
area law from a global spectral gap*, `eq:hamiltonian`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean text is reused.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.Approximation

/-- The energy coefficient `C_E = 18 s_R R μ_R q^(2(v_R - 1)) J` of the range-`R` patch
construction, with `s_R = 2 ⌈R / 2⌉`, `v_R = 1 + 2 R (R + 1)` and `μ_R = 2^(v_R - 1)`. -/
noncomputable def rangePatchEnergyConstant (q R : ℕ) (J : ℝ) : ℝ :=
  18 * AreaLaw.Geometry.rangePatchSpacing R * R * 2 ^ (2 * R * (R + 1)) *
    (q : ℝ) ^ (2 * (2 * R * (R + 1))) * J

/-- The energy coefficient is nonnegative when `J` is. -/
theorem rangePatchEnergyConstant_nonneg (q R : ℕ) {J : ℝ} (hJ : 0 ≤ J) :
    0 ≤ rangePatchEnergyConstant q R J := by
  unfold rangePatchEnergyConstant
  positivity

/-- The energy coefficient is positive for positive range, local dimension and `J`. -/
theorem rangePatchEnergyConstant_pos {q R : ℕ} {J : ℝ} (hq : 0 < q) (hR : 1 ≤ R)
    (hJ : 0 < J) : 0 < rangePatchEnergyConstant q R J := by
  have hs : (0 : ℝ) < AreaLaw.Geometry.rangePatchSpacing R := by
    exact_mod_cast (show 0 < AreaLaw.Geometry.rangePatchSpacing R from
      lt_of_lt_of_le (by norm_num) (AreaLaw.Geometry.two_le_rangePatchSpacing hR))
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold rangePatchEnergyConstant
  positivity

/-- At most `R (16 u + 4) μ_R` supports of range `R` are split by a selected range-`R`
square, each with an inside configuration space of dimension at most `q^(v_R - 1)`.
The weighted crossing sum of one square is therefore at most
`R (16 u + 4) μ_R q^(2(v_R - 1)) J`. -/
theorem sum_crossingTerms_rangeNestedPatch_le {Λ : Finset (ℤ × ℤ)} (q R : ℕ) {J : ℝ}
    (hJ : 0 ≤ J) (c : ℝ × ℝ) {u : ℝ} (hu : 0 ≤ u) {j : ℕ}
    (hj : j < AreaLaw.Geometry.rangeNestedPatchCount R u) :
    ∑ X ∈ Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1)
        (AreaLaw.Geometry.rangeNestedPatch Λ c R u j),
      (Fintype.card (Entropy.InnerConfig (fun _ : Site Λ ↦ q)
        (AreaLaw.Geometry.rangeNestedPatch Λ c R u j) X.1) : ℝ) ^ 2 * J ≤
      R * (16 * u + 4) * 2 ^ (2 * R * (R + 1)) * (q : ℝ) ^ (2 * (2 * R * (R + 1))) * J := by
  classical
  set D := AreaLaw.Geometry.rangeNestedPatch Λ c R u j
  set C := Entropy.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) D
  set N := AreaLaw.Geometry.squareLayer Λ c (AreaLaw.Geometry.rangeNestedPatchRadius R u j) R
  have hmemC : ∀ X ∈ C, (∃ v ∈ X.1, v ∈ D) ∧ ∃ v ∈ X.1, v ∉ D := fun X hX ↦
    (Finset.mem_filter.mp hX).2
  -- Each split support has an inside dimension at most `q ^ (v_R - 1)`.
  have hdim : ∀ X ∈ C, (Fintype.card (Entropy.InnerConfig (fun _ : Site Λ ↦ q) D X.1) : ℝ)
      ≤ (q : ℝ) ^ (2 * R * (R + 1)) := by
    intro X hX
    obtain ⟨⟨v, hvX, hvD⟩, ⟨w, hwX, hwD⟩⟩ := hmemC X hX
    have hcard : Fintype.card (Entropy.InnerConfig (fun _ : Site Λ ↦ q) D X.1) =
        q ^ (X.1 ∩ D).card := by
      rw [Entropy.card_innerConfig, Finset.prod_const]
    have hpos : 1 ≤ (X.1 ∩ D).card :=
      Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hvX, hvD⟩⟩
    have hlt : (X.1 ∩ D).card < X.1.card :=
      Finset.card_lt_card ⟨Finset.inter_subset_left, fun h ↦ hwD
        (Finset.mem_inter.mp (h hwX)).2⟩
    have hdiam := AreaLaw.card_support_le_diamond (G := domainGraph Λ) Subtype.val
      Subtype.val_injective (fun _ _ h ↦ AreaLaw.latticeL1Distance_le_one_of_adj h) X.1 R
      X.2.2
    have hle : (X.1 ∩ D).card ≤ 2 * R * (R + 1) := by omega
    rw [hcard, Nat.cast_pow]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp [zero_pow (Nat.one_le_iff_ne_zero.mp hpos)]
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) hle
  -- Each split support contains a site of the inner layer.
  have hsub : C ⊆ N.biUnion fun v ↦
      Finset.univ.filter fun X : AdmissibleSupport Λ R ↦ v ∈ X.1 := by
    intro X hX
    obtain ⟨⟨v, hvX, hvD⟩, ⟨w, hwX, hwD⟩⟩ := hmemC X hX
    have hv : v ∈ N := AreaLaw.Geometry.mem_squareLayer_of_split
      (fun x hx y hy ↦ AreaLaw.Geometry.abs_squareRadius_sub_le_of_isAdmissibleSupport c X.2
        hx hy) hvX hvD hwX hwD
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvX⟩⟩
  have hcount : (C.card : ℝ) ≤ R * (16 * u + 4) * 2 ^ (2 * R * (R + 1)) := by
    have h := (Finset.card_le_card hsub).trans
      (Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦
        AreaLaw.card_admissibleSupport_containing_le (R := R) v)
    have hN := AreaLaw.Geometry.card_squareLayer_rangeNestedPatch_le Λ c hu hj
    have hexp : 1 + 2 * R * (R + 1) - 1 = 2 * R * (R + 1) := by omega
    rw [hexp] at h
    have h' : (C.card : ℝ) ≤ (N.card : ℝ) * 2 ^ (2 * R * (R + 1)) := by exact_mod_cast h
    exact h'.trans (mul_le_mul_of_nonneg_right hN (by positivity))
  calc
    _ ≤ ∑ _X ∈ C, ((q : ℝ) ^ (2 * R * (R + 1))) ^ 2 * J := by
      apply Finset.sum_le_sum
      intro X hX
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdim X hX) 2) hJ
    _ = (C.card : ℝ) * ((q : ℝ) ^ (2 * (2 * R * (R + 1))) * J) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← pow_mul, mul_comm (2 * R * (R + 1)) 2]
    _ ≤ (R * (16 * u + 4) * 2 ^ (2 * R * (R + 1))) *
        ((q : ℝ) ^ (2 * (2 * R * (R + 1))) * J) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

open Classical in
/-- The normalized regularized output of every feasible patch minimum on the range-`R`
nested squares has excitation energy at most `C_E κ²`, with
`C_E = rangePatchEnergyConstant q R J`, for a range-`R` Hamiltonian on any finite induced
domain with a gapped ground vector.

The regions are the selected range-`R` squares, including repeated clipped regions, and
the weights are exactly `κ / m`. At `R = 1` the squares are the source squares.

Extension of polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 213–336,
`eq:patch-energy-bound`, to interactions of range `R` (area-law `eq:hamiltonian`). -/
theorem LocalHamiltonian.rangeNestedPatch_minimizer_energy_le
    {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J E₀ Δ : ℝ} (H : LocalHamiltonian Λ q R J)
    (hR : 1 ≤ R) (hJ : 0 ≤ J) (Ψ : Lattice.StateSpace Λ q)
    (hgs : Lattice.IsGappedGroundState Λ q H.operator E₀ Ψ Δ)
    (center : ℝ × ℝ) (u κ b : ℝ) (hu : 0 ≤ u) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hb : 0 < b) :
    letI : LinearOrder (Lattice.Site Λ) :=
      (Fintype.equivFin (Lattice.Site Λ)).linearOrder
    let m := AreaLaw.Geometry.rangeNestedPatchCount R u
    let regions : Fin m → Finset (Lattice.Site Λ) :=
      fun j ↦ AreaLaw.Geometry.rangeNestedPatch Λ center R u j
    let a : Fin m → ℝ := fun _ ↦ κ / (m : ℝ)
    let U := dependentGlobalConfigIsometry
      (V := Lattice.Site Λ) (Out := fun _ ↦ Fin q)
    let Ψᵤ := U.symm Ψ
    ∀ x : ∀ j, Matrix ((v : regions j) → Fin q) ((v : regions j) → Fin q) ℂ,
      x ∈ regularizedPatchDomain (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions →
      IsMinOn
        (regularizedPatchObjective (Out := fun _ : Lattice.Site Λ ↦ Fin q)
          regions a b Ψᵤ)
        (regularizedPatchDomain (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions) x →
      let φ : Lattice.StateSpace Λ q := U
        (normalizedRegularizedPatchOutput (Out := fun _ : Lattice.Site Λ ↦ Fin q)
          regions a b Ψᵤ x)
      (inner ℂ φ (Matrix.toEuclideanLin H.operator φ)).re - E₀ ≤
        rangePatchEnergyConstant q R J * κ ^ 2 := by
  intro m regions a U Ψᵤ x hx hmin φ
  have hm : (0 : ℝ) < m :=
    Nat.cast_pos.mpr (AreaLaw.Geometry.rangeNestedPatchCount_pos R u)
  have ha : ∀ j, 0 < a j := fun _ ↦ div_pos hκ hm
  have hΨᵤ : ‖Ψᵤ‖ = 1 := (U.symm.norm_map _).trans hgs.1
  let : LinearOrder (Lattice.Site Λ) := (Fintype.equivFin (Lattice.Site Λ)).linearOrder
  have hnorm := norm_normalizedRegularizedPatchOutput
    (Out := fun _ : Lattice.Site Λ ↦ Fin q) regions a (fun j ↦ (ha j).le) hb Ψᵤ hΨᵤ hx
  have hφ : ‖φ‖ = 1 := (U.norm_map _).trans hnorm
  have hregions : Monotone regions := fun i j hij ↦
    AreaLaw.Geometry.rangeNestedPatch_mono Λ center R u hij
  have hcl := exists_clipped_filter_of_isMinOn_regularizedPatchObjective
    (n := fun _ : Lattice.Site Λ ↦ q) regions hregions a ha hb Ψᵤ hΨᵤ x hx hmin
  let T : AdmissibleSupport Λ R → Matrix (Lattice.Configuration Λ q) (Lattice.Configuration Λ q) ℂ := H.term
  let S : AdmissibleSupport Λ R → Finset (Lattice.Site Λ) := fun X ↦ X.1
  have hsupp : ∀ X, Entropy.IsSupportedOn (n := fun _ : Lattice.Site Λ ↦ q) (T X) (S X) :=
    fun X ↦ QuantumCircuit.isSupportedOn_of_mem_supportedOperators (H.supported X)
  let D : ℕ → Finset (Lattice.Site Λ) := AreaLaw.Geometry.rangeNestedPatch Λ center R u
  let K : (j : Fin m) → Matrix (Entropy.RegionConfig (fun _ : Lattice.Site Λ ↦ q) (D j))
      (Entropy.RegionConfig (fun _ : Lattice.Site Λ ↦ q) (D j)) ℂ :=
    fun j ↦ (x j + b • 1) ^ (-(a j) / 2)
  have hunit : ∀ j, IsUnit (K j).det := fun j ↦
    (Matrix.isUnit_iff_isUnit_det _).mp (((hx j).1.add_smul_one_posDef hb).rpow _).isUnit
  have ha₁ : ∀ j, a j ≤ 1 := fun _ ↦
    (div_nat_le_self_of_nonnneg hκ.le m).trans hκ₁
  have hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j := fun _ _ hij ↦ hregions hij
  have hφpatch := dependentGlobalConfigIsometry_normalizedRegularizedPatchOutput
    (n := fun _ : Lattice.Site Λ ↦ q) (fun j : Fin m ↦ D j) a b Ψᵤ x
  change φ = Entropy.patchState b (regularizedPatchFactorList (fun j : Fin m ↦ D j) a x)
    (U (U.symm Ψ)) at hφpatch
  simp only [U.apply_symm_apply, Entropy.patchState, Entropy.patchOutput,
    map_filter_regularizedPatchFactorList_eq_chainList] at hφpatch
  have hinv : Entropy.liftProdInv (Entropy.chainList D K fun _ ↦ True) *
      Entropy.liftProd (Entropy.chainList D K fun _ ↦ True) = 1 :=
    Entropy.liftProdInv_mul_liftProd_of_isUnit fun p hp ↦
      (List.mem_map.mp hp).elim fun i hi ↦ hi.2 ▸ hunit i
  have hop : H.operator = ∑ X, T X := rfl
  have heig₀ : Matrix.toEuclideanLin (∑ X, T X) Ψ = (E₀ : ℂ) • Ψ := by
    rw [← hop]
    exact hgs.2.1
  have heig := Entropy.toEuclideanLin_conj_apply_eq heig₀ hinv
    (((‖Matrix.toEuclideanLin (Entropy.liftProd (Entropy.chainList D K fun _ ↦ True))
      Ψ‖⁻¹ : ℝ) : ℂ))
  rw [← hφpatch] at heig
  have hφne : φ ≠ 0 := norm_ne_zero_iff.mp (hφ.trans_ne one_ne_zero)
  obtain ⟨σ₀, _⟩ := Function.ne_iff.mp (show (φ : _ → ℂ) ≠ 0 from by
    intro hzero; apply hφne; simpa using congrArg (WithLp.toLp 2) hzero)
  have hsingle : ∀ X : AdmissibleSupport Λ R,
      ∀ j ∈ Entropy.splitIndices (S X) D m, ∀ k ∈ Entropy.splitIndices (S X) D m,
        j = k := fun X j hj k hk ↦
    Fin.ext (AreaLaw.Geometry.rangeNestedPatch_split_unique
      (fun y hy z hz ↦
        AreaLaw.Geometry.abs_squareRadius_sub_le_of_isAdmissibleSupport center X.2 hy hz)
      (Entropy.mem_splitIndices.mp hj) (Entropy.mem_splitIndices.mp hk))
  have henergy := Entropy.re_inner_sub_le_of_chain_sharp D hD K hunit hφ a ha₁ hcl
    T S hsupp H.hermitian σ₀ H.norm_le hsingle heig
  have hbudget : ∀ j : Fin m,
      a j ^ 2 * ∑ X ∈ Entropy.crossingTerms S (D j),
        (Fintype.card (Entropy.InnerConfig (fun _ : Lattice.Site Λ ↦ q) (D j) (S X)) : ℝ) ^ 2 *
          J ≤
      (κ / m) ^ 2 * (R * (16 * u + 4) * 2 ^ (2 * R * (R + 1)) *
        (q : ℝ) ^ (2 * (2 * R * (R + 1))) * J) := fun j ↦
    mul_le_mul_of_nonneg_left
      (sum_crossingTerms_rangeNestedPatch_le q R hJ center hu j.isLt) (sq_nonneg _)
  have hquad := AreaLaw.Geometry.rangeNestedPatch_quadratic_budget hR u κ
  have hP : (0 : ℝ) ≤ R * 2 ^ (2 * R * (R + 1)) * (q : ℝ) ^ (2 * (2 * R * (R + 1))) * J := by
    positivity
  rw [hop]
  calc
    _ ≤ _ := henergy
    _ ≤ ∑ _j : Fin m, (κ / m) ^ 2 * (R * (16 * u + 4) * 2 ^ (2 * R * (R + 1)) *
        (q : ℝ) ^ (2 * (2 * R * (R + 1))) * J) := by
      exact Finset.sum_le_sum fun j _ ↦ hbudget j
    _ = ((16 * u + 4) * ∑ _j : Fin m, (κ / m) ^ 2) *
        (R * 2 ^ (2 * R * (R + 1)) * (q : ℝ) ^ (2 * (2 * R * (R + 1))) * J) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ (18 * AreaLaw.Geometry.rangePatchSpacing R * κ ^ 2) *
        (R * 2 ^ (2 * R * (R + 1)) * (q : ℝ) ^ (2 * (2 * R * (R + 1))) * J) :=
      mul_le_mul_of_nonneg_right hquad hP
    _ = rangePatchEnergyConstant q R J * κ ^ 2 := by
      unfold rangePatchEnergyConstant
      ring

/-- The filter exponent `κ_R = min {1/2, √(Δ / (1024 C_E))}` of the range-`R` patch
construction, with `C_E = rangePatchEnergyConstant q R J`.

Extension of polynomial-PEPS `eq:patch-kappa-choice`, `03-patches.tex`, lines 338–343,
to interactions of range `R`. -/
noncomputable def rangePatchFilterExponent (q R : ℕ) (J Δ : ℝ) : ℝ :=
  min (1 / 2) (Real.sqrt (Δ / (1024 * rangePatchEnergyConstant q R J)))

/-- The range-`R` filter exponent is at most one half. -/
theorem rangePatchFilterExponent_le_half (q R : ℕ) (J Δ : ℝ) :
    rangePatchFilterExponent q R J Δ ≤ 1 / 2 :=
  min_le_left _ _

/-- The range-`R` filter exponent is positive for positive range, local dimension,
interaction bound and gap. -/
theorem rangePatchFilterExponent_pos {q R : ℕ} {J Δ : ℝ} (hq : 0 < q) (hR : 1 ≤ R)
    (hJ : 0 < J) (hΔ : 0 < Δ) : 0 < rangePatchFilterExponent q R J Δ :=
  lt_min (by norm_num) (Real.sqrt_pos.mpr
    (div_pos hΔ (mul_pos (by norm_num) (rangePatchEnergyConstant_pos hq hR hJ))))

/-- Every parameter between zero and the range-`R` filter exponent has quadratic energy
`C_E κ²` at most one 1024th of the gap.

Extension of polynomial-PEPS `eq:patch-kappa-choice` and `eq:patch-marginal-closeness`,
`03-patches.tex`, lines 338–365, to interactions of range `R`. -/
theorem mul_sq_le_div_1024_of_le_rangePatchFilterExponent {q R : ℕ} {J Δ κ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 ≤ Δ) (hκ : 0 ≤ κ) (hle : κ ≤ rangePatchFilterExponent q R J Δ) :
    rangePatchEnergyConstant q R J * κ ^ 2 ≤ Δ / 1024 := by
  have hC := rangePatchEnergyConstant_nonneg q R hJ
  rcases hC.eq_or_lt with hC | hC
  · rw [← hC, zero_mul]
    positivity
  · have hsq : κ ^ 2 ≤ Δ / (1024 * rangePatchEnergyConstant q R J) :=
      (pow_le_pow_left₀ hκ (hle.trans (min_le_right _ _)) 2).trans_eq
        (Real.sq_sqrt (by positivity))
    rw [div_mul_eq_div_div, le_div_iff₀' hC] at hsq
    exact hsq

end TNLean.PEPS.Approximation
